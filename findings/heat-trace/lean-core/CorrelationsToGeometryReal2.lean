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

/-! ## (H5) for the linearised defect of the paper, and the reduction for samples without a remaining hypothesis
(`torus_reduction_paper`). The pointwise weight `p_{6m}` of the paper is NOT formalised; the bound enters in supremum form. -/

namespace H5

open CTG.Reals.TorusReduction TorusReductionL1

/-! ### NEW (A20): the linearised defect `ĥ` of Step 2 of `prop:reduction` and (H5) -/

/-- **The linearised defect of the paper** (Step 2 of `prop:reduction`):
    `ĥ_m^{(i)}(b) = ∑_j P̃_{bj} (1 - ε_j) (p_m(x_j - x_i) - p_{m+1}(x_b - x_i))`, with
    `P̃_{bj} = p(x_b - x_j)/N` and `ε_j = ρ_j - 1` (so that `∑_j P̃_{bj} = 1 + ε_b`). -/
noncomputable def torusHhat (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (m : ℕ)
    (i b : Fin N) : ℝ :=
  ∑ j : Fin N, torusK d σ N x b j / (N : ℝ) * (1 - (torusRho d σ N x j - 1))
    * (torusQ d σ N x m j i - torusQ d σ N x (m + 1) b i)

/-- `u = 1/(1+ε)` for `|ε| ≤ δ ≤ 1/8`. -/
theorem inv_one_add {e δ : ℝ} (he : |e| ≤ δ) (hδ : δ ≤ 1 / 8) :
    |1 / (1 + e) - 1| ≤ 8 / 7 * δ ∧ 8 / 9 ≤ 1 / (1 + e)
      ∧ |1 / (1 + e) - 1 + e| ≤ 8 / 7 * δ ^ 2 := by
  have h := abs_le.mp he
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans he
  have hpos : 0 < 1 + e := by linarith
  have e1 : 1 / (1 + e) - 1 = -e / (1 + e) := by field_simp; ring
  have e2 : 1 / (1 + e) - 1 + e = e ^ 2 / (1 + e) := by field_simp; ring
  have hp : 0 ≤ δ * (1 + e - 7 / 8) := mul_nonneg hδ0 (by linarith)
  have hp2 : 0 ≤ δ ^ 2 * (1 + e - 7 / 8) := mul_nonneg (_root_.sq_nonneg δ) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
    nlinarith
  · rw [le_div_iff₀ hpos]; linarith
  · have hsq : e ^ 2 ≤ δ ^ 2 := sq_le_sq' (by linarith) (by linarith)
    rw [e2, abs_div, abs_of_pos hpos, abs_of_nonneg (_root_.sq_nonneg e), div_le_iff₀ hpos]
    nlinarith

/-- A weighted sum with bounded factors. -/
theorem wsum_abs_le {n : Type} [Fintype n] (Pt w y : n → ℝ) {κ : ℝ} (hPt : ∀ j, 0 ≤ Pt j)
    (hw : ∀ j, |w j| ≤ κ) :
    |∑ j, Pt j * w j * y j| ≤ κ * ∑ j, Pt j * |y j| := by
  calc |∑ j, Pt j * w j * y j| ≤ ∑ j, |Pt j * w j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, κ * (Pt j * |y j|) := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_mul, abs_of_nonneg (hPt j)]
        have h1 := mul_le_mul_of_nonneg_left (hw j) (hPt j)
        have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (y j))
        linarith
    _ = κ * ∑ j, Pt j * |y j| := by rw [Finset.mul_sum]

/-- Arithmetic of Step 2. -/
theorem hhat_arith {r T H S A δ : ℝ} (hδ0 : 0 ≤ δ) (hA : 0 ≤ A) (hr : 7 / 9 ≤ r)
    (hr1 : |r - 1| ≤ 16 / 7 * δ) (hTH : |T - H| ≤ 8 / 7 * δ ^ 2 * A) (hHS : |H - S| ≤ δ * A) :
    |T / r - H| ≤ 3 * δ * |S| + 5 * δ ^ 2 * A ∧ |H| ≤ |S| + δ * A := by
  have hrpos : 0 < r := by linarith
  have e : T / r - H = (T - r * H) / r := by field_simp
  have hS1 := le_abs_self S
  have hS2 := neg_abs_le S
  have hHS' := abs_le.mp hHS
  have hH : |H| ≤ |S| + δ * A := abs_le.mpr ⟨by linarith, by linarith⟩
  have hB0 : 0 ≤ |S| + δ * A := by positivity
  have h3 : |(r - 1) * H| ≤ 16 / 7 * δ * (|S| + δ * A) := by
    rw [abs_mul]
    exact mul_le_mul hr1 hH (abs_nonneg _) (by positivity)
  have h3' := abs_le.mp h3
  have hTH' := abs_le.mp hTH
  have h1 : |T - r * H| ≤ 8 / 7 * δ ^ 2 * A + 16 / 7 * δ * (|S| + δ * A) := by
    have e2 : T - r * H = (T - H) - (r - 1) * H := by ring
    rw [e2]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨?_, hH⟩
  rw [e, abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
  have hx : 0 ≤ δ * |S| := by positivity
  have hy : 0 ≤ δ ^ 2 * A := by positivity
  nlinarith [mul_nonneg hx (show (0 : ℝ) ≤ r - 7 / 9 by linarith),
    mul_nonneg hy (show (0 : ℝ) ≤ r - 7 / 9 by linarith)]

/-- **Step 2 of `prop:reduction`, deterministic and abstract, for general factors `u`.** -/
theorem hhat_det_u {n : Type} [Fintype n] (Pt u ε g : n → ℝ) (c δ εb : ℝ)
    (hPt : ∀ j, 0 ≤ Pt j) (hε : ∀ j, |ε j| ≤ δ) (hδ : δ ≤ 1 / 8)
    (hu1 : ∀ j, |u j - 1| ≤ 8 / 7 * δ) (hu2 : ∀ j, 8 / 9 ≤ u j)
    (hu3 : ∀ j, |u j - 1 + ε j| ≤ 8 / 7 * δ ^ 2)
    (hsum : ∑ j, Pt j = 1 + εb) (hεb : |εb| ≤ δ) :
    |(∑ j, Pt j * u j / (∑ l, Pt l * u l) * g j - c) - ∑ j, Pt j * (1 - ε j) * (g j - c)|
        ≤ 3 * δ * |∑ j, Pt j * (g j - c)| + 5 * δ ^ 2 * ∑ j, Pt j * |g j - c|
      ∧ |∑ j, Pt j * (1 - ε j) * (g j - c)|
        ≤ |∑ j, Pt j * (g j - c)| + δ * ∑ j, Pt j * |g j - c| := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hεb
  have hb := abs_le.mp hεb
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ∑ l, Pt l * u l := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j, Pt j * |g j - c| := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, Pt j * (g j - c) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ∑ j, Pt j * (1 - ε j) * (g j - c) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ j, Pt j * u j * (g j - c) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg fun j _ => mul_nonneg (hPt j) (abs_nonneg _)
  have hrge : 7 / 9 ≤ r := by
    have h1 : ∑ l, Pt l * (8 / 9) ≤ ∑ l, Pt l * u l :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hu2 l) (hPt l)
    rw [← Finset.sum_mul, hsum] at h1
    rw [hr]; linarith
  have hr1 : |r - 1| ≤ 16 / 7 * δ := by
    have e : r - 1 = ∑ j, Pt j * (u j - 1) * (1 : ℝ) + εb := by
      have e0 : ∑ j, Pt j * (u j - 1) * (1 : ℝ) = ∑ j, Pt j * u j - ∑ j, Pt j := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e0, hsum, hr]; ring
    have h1 := wsum_abs_le Pt (fun j => u j - 1) (fun _ => (1 : ℝ)) hPt hu1
    have e1 : ∑ j, Pt j * |(1 : ℝ)| = 1 + εb := by
      rw [abs_one]; simp only [mul_one]; exact hsum
    rw [e1] at h1
    have h1' := abs_le.mp h1
    have hp : 0 ≤ δ * (1 / 8 - εb) := mul_nonneg hδ0 (by linarith)
    rw [e]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hTH : |T - H| ≤ 8 / 7 * δ ^ 2 * A := by
    have e : T - H = ∑ j, Pt j * (u j - 1 + ε j) * (g j - c) := by
      rw [hT, hH, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, hA]
    exact wsum_abs_le Pt (fun j => u j - 1 + ε j) (fun j => g j - c) hPt hu3
  have hHS : |H - S| ≤ δ * A := by
    have e : H - S = ∑ j, Pt j * (-ε j) * (g j - c) := by
      rw [hH, hS, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, hA]
    exact wsum_abs_le Pt (fun j => -ε j) (fun j => g j - c) hPt
      (fun j => by rw [abs_neg]; exact hε j)
  have hrpos : 0 < r := by linarith
  have e1 : ∑ j, Pt j * u j / r * g j - c = T / r := by
    have hsumT : T = ∑ j, Pt j * u j * g j - c * r := by
      rw [hT, hr, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsumT, sub_div, mul_div_cancel_right₀ _ hrpos.ne', Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [← hr, ← hS, ← hA, ← hH, e1]
  exact hhat_arith hδ0 hA0 hrge hr1 hTH hHS

/-- **Step 2 of `prop:reduction`, deterministic and abstract** (`u_j = 1/(1+ε_j)`): with
    `S₁ = ∑_j P̃_j (g_j - c)` and `A = ∑_j P̃_j |g_j - c|`,
    `|h - ĥ| ≤ 3δ|S₁| + 5δ²A` and `|ĥ| ≤ |S₁| + δA`. -/
theorem hhat_det {n : Type} [Fintype n] (Pt ε g : n → ℝ) (c δ εb : ℝ)
    (hPt : ∀ j, 0 ≤ Pt j) (hε : ∀ j, |ε j| ≤ δ) (hδ : δ ≤ 1 / 8)
    (hsum : ∑ j, Pt j = 1 + εb) (hεb : |εb| ≤ δ) :
    |(∑ j, Pt j * (1 / (1 + ε j)) / (∑ l, Pt l * (1 / (1 + ε l))) * g j - c)
          - ∑ j, Pt j * (1 - ε j) * (g j - c)|
        ≤ 3 * δ * |∑ j, Pt j * (g j - c)| + 5 * δ ^ 2 * ∑ j, Pt j * |g j - c|
      ∧ |∑ j, Pt j * (1 - ε j) * (g j - c)|
        ≤ |∑ j, Pt j * (g j - c)| + δ * ∑ j, Pt j * |g j - c| :=
  hhat_det_u Pt (fun j => 1 / (1 + ε j)) ε g c δ εb hPt hε hδ
    (fun j => (inv_one_add (hε j) hδ).1) (fun j => (inv_one_add (hε j) hδ).2.1)
    (fun j => (inv_one_add (hε j) hδ).2.2) hsum hεb

/-- Arithmetic: from the raw bounds to the defect bound. -/
theorem final_arith {Nr δ S A s a : ℝ} (hN : 0 < Nr) (hδ : 0 ≤ δ) (hS : |S| ≤ s / Nr)
    (hA : A ≤ a / Nr) (ha : 0 ≤ a) :
    3 * δ * |S| + 5 * δ ^ 2 * A ≤ δ * ((s + 2 * δ * a) / (Nr * (1 / 3)))
      ∧ |S| + δ * A ≤ (s + 2 * δ * a) / (Nr * (1 / 3)) := by
  have e : (s + 2 * δ * a) / (Nr * (1 / 3)) = 3 * (s / Nr) + 6 * δ * (a / Nr) := by
    first | (field_simp; done) | (field_simp; ring)
  rw [e]
  have hp : 0 ≤ s / Nr := (abs_nonneg _).trans hS
  have hq : 0 ≤ a / Nr := div_nonneg ha hN.le
  have h1 : δ * |S| ≤ δ * (s / Nr) := mul_le_mul_of_nonneg_left hS hδ
  have h2 : δ ^ 2 * A ≤ δ ^ 2 * (a / Nr) := mul_le_mul_of_nonneg_left hA (_root_.sq_nonneg δ)
  have h3 : δ * A ≤ δ * (a / Nr) := mul_le_mul_of_nonneg_left hA hδ
  have h4 : 0 ≤ δ ^ 2 * (a / Nr) := by positivity
  have h5 : 0 ≤ δ * (a / Nr) := by positivity
  constructor
  · nlinarith
  · linarith [abs_nonneg S]

/-- **Stage 1 for the torus graph (pointwise (H5a), (H5c)).** On the normalisation event
    `|ρ_a - 1| ≤ δ ≤ 1/8` and the two Bernstein events of the pair `(b, i)` at step `m`
    (for `S₁ = (1/N)∑_j Y_j` and for `A = (1/N)∑_j |Y_j|`):
    `|h - ĥ| ≤ δ · heatDefBound(x_b - x_i)` and `|ĥ| ≤ heatDefBound(x_b - x_i)`. -/
theorem hhat_point {σ : ℝ} (hσ : 0 < σ) (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m)
    (x : ℕ → FlatTorus d) {M L δ : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M) (hδ : δ ≤ 1 / 8)
    (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ) (b i : Fin N)
    (H1 : |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
      ≤ heatThr d σ ((m : ℝ) * σ) M L N (x b - x i))
    (H2 : |∑ j ∈ ((Finset.range N).erase b).erase i, heatYc d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
      ≤ heatThr d σ ((m : ℝ) * σ) M L N (x b - x i)) :
    |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
          - torusQ d σ N x (m + 1) b i) - torusHhat d σ N x m i b|
        ≤ δ * heatDefBound d σ N m M L δ (x b - x i)
      ∧ |torusHhat d σ N x m i b| ≤ heatDefBound d σ N m M L δ (x b - x i) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hσs : σ ≤ (m : ℝ) * σ := by nlinarith
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hρ b)
  have hρpos : ∀ a : Fin N, 0 < heatRho d σ N x a := fun a => by
    have := (abs_le.mp (hρ a)).1
    linarith
  have hPt : ∀ j : Fin N, 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ) :=
    fun j => div_nonneg (heatTorus_nonneg hcσ d _) hNpos.le
  have hsum : ∑ j : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ)
      = 1 + (heatRho d σ N x b - 1) := by
    rw [← Finset.sum_div,
      Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l)) N]
    unfold heatRho; ring
  have key := hhat_det (fun j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ))
    (fun j : Fin N => heatRho d σ N x j - 1) (fun j : Fin N => heatP d σ m (x j - x i))
    (heatP d σ (m + 1) (x b - x i)) δ (heatRho d σ N x b - 1) hPt hρ hδ hsum (hρ b)
  beta_reduce at key
  have hrow : ∀ j : Fin N, torusWalk d σ N x b j
      = heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ)
          * (1 / (1 + (heatRho d σ N x j - 1)))
        / (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / (N : ℝ)
            * (1 / (1 + (heatRho d σ N x l - 1)))) := by
    intro j
    have e : ∀ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / (N : ℝ)
          * (1 / (1 + (heatRho d σ N x l - 1)))
        = (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / heatRho d σ N x l) / (N : ℝ) := by
      intro l
      rw [show 1 + (heatRho d σ N x l - 1) = heatRho d σ N x l by ring]
      ring
    rw [Finset.sum_congr rfl (fun l _ => e l), e j, ← Finset.sum_div,
      div_div_div_cancel_right₀ hNpos.ne']
    exact walkMatrix_apply' (torusK d σ N x) (torusRho d σ N x) b j (hρpos b).ne'
  -- the raw sums
  obtain ⟨y, hyd⟩ : ∃ y : ℕ → ℝ,
      y = fun j => heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j) := ⟨_, rfl⟩
  have hy' : ∀ j, y j = heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j) := fun j => by rw [hyd]
  have hterm : ∀ j : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ)
        * (heatP d σ m (x j - x i) - heatP d σ (m + 1) (x b - x i)) = y j / N := by
    intro j
    rw [hy', heatP_of_ne d σ (by omega : m ≠ 0), heatP_succ]
    unfold heatY
    ring
  have hyb : ∀ j, |y j| ≤ heatB d σ ((m : ℝ) * σ) M (x b - x i) := fun j => by
    rw [hy']; exact heatY_abs_le hσ hs d (x b) (x i) (x j) hMσ
  have H1' : |∑ j ∈ ((Finset.range N).erase b).erase i, y j|
      ≤ heatThr d σ ((m : ℝ) * σ) M L N (x b - x i) := by rw [hyd]; exact H1
  have H2' : |∑ j ∈ ((Finset.range N).erase b).erase i,
        (|y j| - heatYmean d σ ((m : ℝ) * σ) (x b) (x i))|
      ≤ heatThr d σ ((m : ℝ) * σ) M L N (x b - x i) := by rw [hyd]; exact H2
  have he0 : 0 ≤ heatYmean d σ ((m : ℝ) * σ) (x b) (x i) := by
    rw [heatYmean_eq]; exact integral_nonneg fun z => abs_nonneg _
  have heV : heatYmean d σ ((m : ℝ) * σ) (x b) (x i)
      ≤ Real.sqrt (heatV d σ ((m : ℝ) * σ) (x b - x i)) := by
    rw [heatYmean_eq]; exact heatY_abs_integral_sharp hσ hs hσs d (x b) (x i)
  have hthr0 : 0 ≤ heatThr d σ ((m : ℝ) * σ) M L N (x b - x i) := (abs_nonneg _).trans H1
  have hB0 : 0 ≤ heatB d σ ((m : ℝ) * σ) M (x b - x i) := (abs_nonneg _).trans (hyb 0)
  have hS : |∑ j : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ)
        * (heatP d σ m (x j - x i) - heatP d σ (m + 1) (x b - x i))|
      ≤ (heatThr d σ ((m : ℝ) * σ) M L N (x b - x i)
          + 2 * heatB d σ ((m : ℝ) * σ) M (x b - x i)) / N := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div,
      Fin.sum_univ_eq_sum_range y N, abs_div, abs_of_pos hNpos]
    apply div_le_div_of_nonneg_right _ hNpos.le
    have := abs_sum_le_erase2 (Finset.range N) y b i
    linarith [hyb b, hyb i]
  have hA : ∑ j : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ)
        * |heatP d σ m (x j - x i) - heatP d σ (m + 1) (x b - x i)|
      ≤ (N * Real.sqrt (heatV d σ ((m : ℝ) * σ) (x b - x i))
          + heatThr d σ ((m : ℝ) * σ) M L N (x b - x i)
          + 2 * heatB d σ ((m : ℝ) * σ) M (x b - x i)) / N := by
    have hterm2 : ∀ j : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / (N : ℝ)
        * |heatP d σ m (x j - x i) - heatP d σ (m + 1) (x b - x i)| = |y j| / N := by
      intro j
      have h := hterm j
      have e : |y j| / N = |y j / N| := by rw [abs_div, abs_of_pos hNpos]
      rw [e, ← h, abs_mul, abs_of_nonneg (hPt j)]
    rw [Finset.sum_congr rfl (fun j _ => hterm2 j), ← Finset.sum_div,
      Fin.sum_univ_eq_sum_range (fun j => |y j|) N]
    apply div_le_div_of_nonneg_right _ hNpos.le
    have h := sum_abs_le_erase2 (Finset.range N) y b i he0
    rw [Finset.card_range] at h
    have h2 := mul_le_mul_of_nonneg_left heV hNpos.le
    linarith [hyb b, hyb i]
  have hsA : 0 ≤ N * Real.sqrt (heatV d σ ((m : ℝ) * σ) (x b - x i))
      + heatThr d σ ((m : ℝ) * σ) M L N (x b - x i)
      + 2 * heatB d σ ((m : ℝ) * σ) M (x b - x i) := by positivity
  have fin := final_arith hNpos hδ0 hS hA hsA
  unfold heatDefBound
  constructor
  · simp only [hrow]
    exact key.1.trans fin.1
  · exact key.2.trans fin.2

/-- The conclusions (H5a)--(H5d) for the linearised defect of the paper, in terms of the
    supremum bound `heatDefSup` and the mean bound `heatEtaBar` of the defect. -/
def H5Good (d : ℕ) (σ M L δ : ℝ) (N K : ℕ) (x : ℕ → FlatTorus d) : Prop :=
  ∀ m, 1 ≤ m → m ≤ K →
    (∀ i b : Fin N,
      |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
          - torusQ d σ N x (m + 1) b i) - torusHhat d σ N x m i b|
        ≤ δ * heatDefSup d σ N m M L δ) ∧
    (∀ i : Fin N,
      ∑ b : Fin N, |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
          - torusQ d σ N x (m + 1) b i) - torusHhat d σ N x m i b|
        ≤ (N : ℝ) * (δ * heatEtaBar d σ N m M L δ δ)) ∧
    (∀ i b : Fin N, |torusHhat d σ N x m i b| ≤ heatDefSup d σ N m M L δ) ∧
    (∀ i : Fin N, ∑ b : Fin N, |torusHhat d σ N x m i b|
        ≤ (N : ℝ) * heatEtaBar d σ N m M L δ δ)

/-- **Stages 1 and 2, deterministic.** Normalisation, the two Bernstein events for all triples
    `(b, i, m)`, `m ≤ K`, and the four kernel sums (estimate (iii) at the times `(m+2)σ`,
    `(m+1)σ`, `6mσ`, `12mσ`) give (H5a)--(H5d) for the `ĥ` of the paper. -/
theorem h5_det {σ : ℝ} (hσ : 0 < σ) (d N K : ℕ) (hN : 0 < N) (x : ℕ → FlatTorus d)
    {M L δ : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M) (hL : 0 < L)
    (hδ : δ ≤ 1 / 8) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ)
    (H1 : ∀ m, 1 ≤ m → m ≤ K → ∀ b, b < N → ∀ i, i < N →
      |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
        ≤ heatThr d σ ((m : ℝ) * σ) M L N (x b - x i))
    (H2 : ∀ m, 1 ≤ m → m ≤ K → ∀ b, b < N → ∀ i, i < N →
      |∑ j ∈ ((Finset.range N).erase b).erase i, heatYc d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
        ≤ heatThr d σ ((m : ℝ) * σ) M L N (x b - x i))
    (hA : ∀ m, 1 ≤ m → m ≤ K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) (x b - x i)
        ≤ N * (1 + δ))
    (hB : ∀ m, 1 ≤ m → m ≤ K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
        ≤ N * (1 + δ))
    (hC : ∀ m, 1 ≤ m → m ≤ K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ))
    (hC12 : ∀ m, 1 ≤ m → m ≤ K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ)) :
    H5Good d σ M L δ N K x := by
  intro m hm hmK
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hρ ⟨0, hN⟩)
  have hM0 : 0 ≤ M := (heatTorus_nonneg hcσ d 0).trans (hMσ 0)
  have hpt := fun i b : Fin N => hhat_point hσ d N m hN hm x (L := L) hMσ hδ hρ b i
    (H1 m hm hmK b b.2 i i.2) (H2 m hm hmK b b.2 i i.2)
  have hsup : ∀ u, heatDefBound d σ N m M L δ u ≤ heatDefSup d σ N m M L δ :=
    heatDefBound_le_sup hσ hM0 hL.le hδ0 d N m hN hm
  have hmean : ∀ i : Fin N, ∑ b : Fin N, heatDefBound d σ N m M L δ (x b - x i)
      ≤ N * heatEtaBar d σ N m M L δ δ := by
    intro i
    have e := Fin.sum_univ_eq_sum_range (fun b => heatDefBound d σ N m M L δ (x b - x i)) N
    exact le_trans (le_of_eq e) (heat_defect_mean_det_min hσ hM0 hL.le hδ0 d N m hN hm x i hδ0
      (hA m hm hmK i i.2) (hB m hm hmK i i.2) (hC m hm hmK i i.2) (hC12 m hm hmK i i.2))
  refine ⟨fun i b => ?_, fun i => ?_, fun i b => ?_, fun i => ?_⟩
  · exact (hpt i b).1.trans (mul_le_mul_of_nonneg_left (hsup _) hδ0)
  · calc ∑ b : Fin N, |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
            - torusQ d σ N x (m + 1) b i) - torusHhat d σ N x m i b|
        ≤ ∑ b : Fin N, δ * heatDefBound d σ N m M L δ (x b - x i) :=
          Finset.sum_le_sum fun b _ => (hpt i b).1
      _ = δ * ∑ b : Fin N, heatDefBound d σ N m M L δ (x b - x i) := by rw [Finset.mul_sum]
      _ ≤ δ * (N * heatEtaBar d σ N m M L δ δ) := mul_le_mul_of_nonneg_left (hmean i) hδ0
      _ = (N : ℝ) * (δ * heatEtaBar d σ N m M L δ δ) := by ring
  · exact (hpt i b).2.trans (hsup _)
  · exact (Finset.sum_le_sum fun b _ => (hpt i b).2).trans (hmean i)


/-- **Stage 3, events.** HYPOTHESIS `hBn`: the normalisation event at every time `τ ≥ σ` has
    probability at most `pn` (the conclusion of `heat_normalisation_whp`). Then (H5a)--(H5d) in
    the form `H5Good` fail with probability at most `pn + 2 · K N² · 2e^{-L} + 4 K pn`. -/
theorem h5_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {M L epsn pn : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M) (hL : 0 < L)
    (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 8)
    (hBn : ∀ τ, σ ≤ τ → μ.real {ω | ∃ x : FlatTorus d,
        epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} ≤ pn) :
    μ.real {ω | ¬ H5Good d σ M L (epsn / N) N K (fun j => X j ω)}
      ≤ pn + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))) + (K : ℝ) * (4 * pn) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : ℝ → Set Ω, Bn = fun τ => {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} := ⟨_, rfl⟩
  have hBnP : ∀ τ, σ ≤ τ → μ.real (Bn τ) ≤ pn := fun τ hτ => by rw [hBnd]; exact hBn τ hτ
  have hBnc : ∀ τ ω, ω ∉ Bn τ → ∀ y : FlatTorus d,
      |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (y - X j ω) - N| ≤ epsn := by
    intro τ ω hω y
    by_contra h
    rw [hBnd] at hω
    exact hω ⟨y, not_le.mp h⟩
  obtain ⟨E1, hE1d⟩ : ∃ E1 : Set Ω, E1 = {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N,
      ∃ i ∈ Finset.range N,
        2 * heatB d σ ((m : ℝ) * σ) M (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (M * heatV d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} := ⟨_, rfl⟩
  have hE1P : μ.real E1 ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
    rw [hE1d]; exact heat_consistency_all_steps hσ d X h_indep hX hlaw N K hMσ hL
  obtain ⟨E2, hE2d⟩ : ∃ E2 : Set Ω, E2 = {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N,
      ∃ i ∈ Finset.range N,
        heatThr d σ ((m : ℝ) * σ) M L N (X b ω - X i ω)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} := ⟨_, rfl⟩
  have hE2P : μ.real E2 ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
    rw [hE2d]; exact heat_abs_consistency_all_steps hσ d X h_indep hX hlaw N K hMσ hL
  obtain ⟨A, hAd⟩ : ∃ A : ℕ → Set Ω, A = fun m : ℕ =>
      Bn ((m : ℝ) * σ + 2 * σ) ∪ (Bn (σ + (m : ℝ) * σ)
        ∪ (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ)))) := ⟨_, rfl⟩
  have hAP : ∀ m ∈ Finset.Icc 1 K, μ.real (A m) ≤ 4 * pn := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have t1 : σ ≤ (m : ℝ) * σ + 2 * σ := by nlinarith
    have t2 : σ ≤ σ + (m : ℝ) * σ := by nlinarith
    have t3 : σ ≤ 6 * ((m : ℝ) * σ) := by nlinarith
    have t4 : σ ≤ 12 * ((m : ℝ) * σ) := by nlinarith
    rw [hAd]
    have u1 := measureReal_union_le (μ := μ) (Bn ((m : ℝ) * σ + 2 * σ))
      (Bn (σ + (m : ℝ) * σ) ∪ (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ))))
    have u2 := measureReal_union_le (μ := μ) (Bn (σ + (m : ℝ) * σ))
      (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ)))
    have u3 := measureReal_union_le (μ := μ) (Bn (6 * ((m : ℝ) * σ))) (Bn (12 * ((m : ℝ) * σ)))
    linarith [hBnP _ t1, hBnP _ t2, hBnP _ t3, hBnP _ t4]
  have hUP : μ.real (⋃ m ∈ Finset.Icc 1 K, A m) ≤ (K : ℝ) * (4 * pn) := by
    calc μ.real (⋃ m ∈ Finset.Icc 1 K, A m) ≤ ∑ m ∈ Finset.Icc 1 K, μ.real (A m) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, 4 * pn := Finset.sum_le_sum hAP
      _ = (K : ℝ) * (4 * pn) := by simp
  have hsub : {ω | ¬ H5Good d σ M L (epsn / N) N K (fun j => X j ω)}
      ⊆ Bn σ ∪ E1 ∪ E2 ∪ ⋃ m ∈ Finset.Icc 1 K, A m := by
    intro ω hbad
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨⟨hn, hE1⟩, hE2⟩, hAm⟩ := hcon
    apply hbad
    have hδ8 : epsn / N ≤ 1 / 8 := by rw [div_le_iff₀ hNpos]; linarith
    have hρ : ∀ j, |heatRho d σ N (fun j => X j ω) j - 1| ≤ epsn / N := by
      intro j
      have h := hBnc σ ω hn (X j ω)
      have e : heatRho d σ N (fun j => X j ω) j - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    have hmem : ∀ m, 1 ≤ m → m ≤ K → m ∈ Finset.Icc 1 K := fun m h1 h2 =>
      Finset.mem_Icc.mpr ⟨h1, h2⟩
    refine h5_det hσ d N K hN (fun j => X j ω) hMσ hL hδ8 (fun a => hρ a) ?_ ?_ ?_ ?_ ?_ ?_
    · intro m hm hmK b hb i hi
      by_contra h
      rw [hE1d] at hE1
      exact hE1 ⟨m, hmem m hm hmK, b, Finset.mem_range.mpr hb, i, Finset.mem_range.mpr hi,
        (not_le.mp h).le⟩
    · intro m hm hmK b hb i hi
      by_contra h
      rw [hE2d] at hE2
      exact hE2 ⟨m, hmem m hm hmK, b, Finset.mem_range.mpr hb, i, Finset.mem_range.mpr hi,
        (not_le.mp h).le⟩
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.2.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.2.2) i
  have v1 := measureReal_union_le (μ := μ) (Bn σ ∪ E1 ∪ E2) (⋃ m ∈ Finset.Icc 1 K, A m)
  have v2 := measureReal_union_le (μ := μ) (Bn σ ∪ E1) E2
  have v3 := measureReal_union_le (μ := μ) (Bn σ) E1
  have v0 : μ.real {ω | ¬ H5Good d σ M L (epsn / N) N K (fun j => X j ω)}
      ≤ μ.real (Bn σ ∪ E1 ∪ E2 ∪ ⋃ m ∈ Finset.Icc 1 K, A m) :=
    measureReal_mono hsub (measure_ne_top μ _)
  linarith [hBnP σ le_rfl]

/-- **Stage 3 with explicit parameters** (grid `g`, tolerance `ε`, level `L`),
    `δ = (ε + 2 N Lip/g)/N ≤ 1/8`. No hypothesis on events. -/
theorem h5_sample_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε δ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N) :
    μ.real {ω | ¬ H5Good d σ M L δ N K (fun j => X j ω)}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
            + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))))
        + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))) := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  have hconst : ∀ τ, σ ≤ τ →
      (∀ u, heatTorus d (2 * Real.pi ^ 2 * τ) u ≤ M)
      ∧ (∀ u u', |heatTorus d (2 * Real.pi ^ 2 * τ) u - heatTorus d (2 * Real.pi ^ 2 * τ) u'|
          ≤ Lip * dist u u') := by
    intro τ hτ
    have hcτ : 0 < 2 * Real.pi ^ 2 * τ := by have := lt_of_lt_of_le hσ hτ; positivity
    have hcc : 2 * Real.pi ^ 2 * σ ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    obtain ⟨a1, a2⟩ := heat_consts_anti hcσ hcc d
    constructor
    · intro u; rw [hMdef]; exact (heatTorus_le hcτ d u).trans a1
    · intro u u'; rw [hLipdef]
      exact (heatTorus_lipschitz hcτ d u u').trans (mul_le_mul_of_nonneg_right a2 dist_nonneg)
  have hepsn0 : 0 ≤ ε + 2 * (N * Lip) * (1 / g) := by positivity
  subst hδ
  exact h5_whp hσ d X h_indep hX hlaw N K hN (hconst σ le_rfl).1 hL hepsn0 hsmall
    (fun τ hτ => heat_normalisation_whp (lt_of_lt_of_le hσ hτ) d X h_indep hX hlaw N hg
      (hconst τ hτ).1 (hconst τ hτ).2 hLip0 hε)

/-- (H5a)--(H5d) for the `ĥ` of the paper in closed form, with the uniform bound `heatMu` of
    the kernel as weight. -/
def H5Closed (d : ℕ) (σ : ℝ) (N K : ℕ) (x : ℕ → FlatTorus d) (cδ cA cB η : ℝ) : Prop :=
  ∀ m, 1 ≤ m → m ≤ K →
    (∀ i b : Fin N,
      |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
          - torusQ d σ N x (m + 1) b i) - torusHhat d σ N x m i b|
        ≤ cδ * η * (cB * η * heatMu d σ m * (1 / Real.sqrt m))) ∧
    (∀ i : Fin N,
      ∑ b : Fin N, |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
          - torusQ d σ N x (m + 1) b i) - torusHhat d σ N x m i b|
        ≤ (N : ℝ) * (cδ * η * (cA * η * (1 / Real.sqrt m)))) ∧
    (∀ i b : Fin N, |torusHhat d σ N x m i b| ≤ cB * η * heatMu d σ m * (1 / Real.sqrt m)) ∧
    (∀ i : Fin N, ∑ b : Fin N, |torusHhat d σ N x m i b|
        ≤ (N : ℝ) * (cA * η * (1 / Real.sqrt m)))

/-- Constant of the normalisation against the `δ'` of the main file. -/
noncomputable def h5cD (d : ℕ) : ℝ := 6 * Real.sqrt (3 * (d : ℝ) + 5)

/-- Constant of the mean bound of the defect against the `δ'` of the main file. -/
noncomputable def h5cA (d : ℕ) : ℝ :=
  3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d)

/-- Constant of the supremum bound of the defect against the `δ'` of the main file. -/
noncomputable def h5cB (d : ℕ) : ℝ :=
  3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d)

theorem h5c_nonneg (d : ℕ) : 0 ≤ h5cD d ∧ 0 ≤ h5cB d ∧ h5cB d ≤ h5cA d := by
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hX : 0 ≤ (5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold h5cD; positivity
  · unfold h5cB; positivity
  · unfold h5cA h5cB; linarith

set_option maxHeartbeats 6400000 in
/-- **(H5) with probability, against the `δ'` of the main file** (`M = (1 + (2πσ)^(-1/2))^d`,
    `δ' = √(M log N/N)`), under the hypotheses of `l1_g3`: except on an event of probability at
    most `2/N³`, `H5Closed` holds with `c_δ = h5cD d`, `c_A = h5cA d`, `c_B = h5cB d`. -/
theorem h5_g3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
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
    μ.real {ω | ¬ H5Closed d σ N K (fun j => X j ω) (h5cD d) (h5cA d) (h5cB d) δp}
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
  obtain ⟨cB, hcB⟩ : ∃ cB : ℝ, cB = 3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d) := ⟨_, rfl⟩
  have hcB0 : 0 ≤ cB := by rw [hcB]; positivity
  have habB := (rate_ab_bound hδ00 hδ08 hδ0le' hθ0 hθle hS0 hSle hRA0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).2
  have hB : heatRateB' d N M L δ0 θ ≤ cB * δp := by
    rw [hcB]; unfold heatRateB'; rw [← hS]; exact habB
  have ecD : h5cD d = 6 * Aa := by rw [hAa]; rfl
  have ecA : h5cA d = cA := by rw [hcA, hAa]; rfl
  have ecB : h5cB d = cB := by rw [hcB, hAa]; rfl
  have h := h5_sample_all hσ d X h_indep hX hlaw N K hN (pow_pos hN 3) hMdef
    hLipdef hLpos hε hsmall' hδ0def
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (h.trans ?_)
  · intro ω hω hgood
    apply hω
    rw [ecD, ecA, ecB]
    intro m hm hmK
    obtain ⟨ha, hb, hc', hd'⟩ := hgood m hm hmK
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
    have hθm : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N := by
      have h1 : Real.sqrt m ≤ Real.sqrt K := Real.sqrt_le_sqrt (by exact_mod_cast hmK)
      have h2 : 0 ≤ (2 * L + 2) * (heatKbar d σ + M) := by positivity
      exact (mul_le_mul_of_nonneg_left h1 h2).trans hθ'
    have hSup := heatDefSup_closed_all hσ hσ1 hMpos.le hLpos.le hδ00 d N hN m hm hθm
    have hEta := heatEtaBar_closed_all hσ hσ1 hMpos.le hLpos.le hδ00 d N hN m hm hθm
    have hmu0 := heatMu_nonneg d σ m
    have ht0 : 0 ≤ 1 / Real.sqrt m := by positivity
    have hSup' : heatDefSup d σ N m M L δ0 ≤ cB * δp * heatMu d σ m * (1 / Real.sqrt m) := by
      refine hSup.trans ?_
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hmu0) ht0
    have hEta' : heatEtaBar d σ N m M L δ0 δ0 ≤ cA * δp * (1 / Real.sqrt m) := by
      refine hEta.trans ?_
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right hA ht0
    have hY0 : 0 ≤ cB * δp * heatMu d σ m * (1 / Real.sqrt m) := by positivity
    have hZ0 : 0 ≤ cA * δp * (1 / Real.sqrt m) := by positivity
    refine ⟨fun i b => ?_, fun i => ?_, fun i b => ?_, fun i => ?_⟩
    · exact (ha i b).trans ((mul_le_mul_of_nonneg_left hSup' hδ00).trans
        (mul_le_mul_of_nonneg_right hδ0le' hY0))
    · exact (hb i).trans (mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hEta' hδ00).trans
          (mul_le_mul_of_nonneg_right hδ0le' hZ0)) hNpos.le)
    · exact (hc' i b).trans hSup'
    · exact (hd' i).trans (mul_le_mul_of_nonneg_left hEta' hNpos.le)
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
    have hpn0 : 0 ≤ Gd * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))) := by positivity
    rw [hq, e3]
    nlinarith [hp, hpn0]

set_option maxHeartbeats 6400000 in
/-- The numerical setup of `good_events` (third file): from the hypotheses of
    `kernel_theorem_G28` to those of `l1_g3`/`h5_g3`. -/
theorem h5_setup {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    ∃ ML Lip δL : ℝ, ML = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d
      ∧ Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
          * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d
      ∧ δL = Real.sqrt (ML * Real.log N / N)
      ∧ 12 ≤ N ∧ K ≤ N
      ∧ 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * ML * Real.log N))
      ∧ rateCfin3 d * δL * Real.sqrt K ≤ 1
      ∧ δL ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d * δp ∧ 0 ≤ δL ∧ 0 ≤ δp := by
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
  exact ⟨ML, Lip, δL, hML, hLip, hδLdef, hN12, hKN, hLipc, by rw [← hC]; exact hsmallL,
    by rw [← hA]; exact hδLle, hδL0, hδp0⟩

/-- Doubling six times: `m_l ≤ (√6)^d m_{6l}` (from (P1)). -/
theorem torusM_six {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l : ℕ} (hl : 1 ≤ l) :
    torusM d σ l ≤ (Real.sqrt 6) ^ d * torusM d σ (6 * l) := by
  have hpi := Real.pi_pos
  have hl' : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk6 : ((6 * l : ℕ) : ℝ) = 6 * (l : ℝ) := by push_cast; ring
  have hk' : (0 : ℝ) < ((6 * l : ℕ) : ℝ) := by rw [hk6]; positivity
  have h2pi : 0 ≤ 2 * Real.pi ^ 2 := by positivity
  have hca : 0 < 2 * Real.pi ^ 2 * ((l : ℝ) * σ) := by positivity
  have hct : 0 < 2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ) := by positivity
  have hlk : (l : ℝ) ≤ ((6 * l : ℕ) : ℝ) := by rw [hk6]; linarith
  have hat : 2 * Real.pi ^ 2 * ((l : ℝ) * σ) ≤ 2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlk hσ.le) h2pi
  have h1 : heatTorus d (2 * Real.pi ^ 2 * ((l : ℝ) * σ)) 0
      ≤ (((2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ)) / (2 * Real.pi ^ 2 * ((l : ℝ) * σ)))
          ^ (1 / 2 : ℝ)) ^ d
        * heatTorus d (2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ)) 0 := heatTorus_P1 hca hat d 0
  have hmk : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ)) 0 :=
    (heatTorus_zero_pos hct d).le
  have hratio : (2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ)) / (2 * Real.pi ^ 2 * ((l : ℝ) * σ))
      ≤ 6 := by
    rw [div_le_iff₀ hca, hk6]
    exact le_of_eq (by ring)
  have hroot : ((2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ)) / (2 * Real.pi ^ 2 * ((l : ℝ) * σ)))
      ^ (1 / 2 : ℝ) ≤ Real.sqrt 6 := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hratio
  have hroot0 : 0 ≤ ((2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ))
      / (2 * Real.pi ^ 2 * ((l : ℝ) * σ))) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (div_nonneg hct.le hca.le) _
  have hpow := pow_le_pow_left₀ hroot0 hroot d
  have h2 := mul_le_mul_of_nonneg_right hpow hmk
  show heatTorus d (2 * Real.pi ^ 2 * ((l : ℝ) * σ)) 0
      ≤ (Real.sqrt 6) ^ d * heatTorus d (2 * Real.pi ^ 2 * (((6 * l : ℕ) : ℝ) * σ)) 0
  exact h1.trans h2

/-- The four conversions from the weight `heatMu` and `δ_L` to `m_{6m}` and `δ'`. -/
theorem conv_arith {c6 cB cA A s6 δL δp mu m6 t Ca Cb : ℝ} (hc6 : 0 ≤ c6) (hcB : 0 ≤ cB)
    (hcBA : cB ≤ cA) (hA : 1 ≤ A) (hs6 : 1 ≤ s6) (hδL : 0 ≤ δL) (hδp : 0 ≤ δp)
    (hδ : δL ≤ A * δp) (hmu0 : 0 ≤ mu) (hm6 : 0 ≤ m6) (hmu : mu ≤ A * s6 * m6) (ht : 0 ≤ t)
    (hCa : Ca = c6 * cA * A ^ 3 * s6) (hCb : Cb = cA * A ^ 2 * s6) :
    c6 * δL * (cB * δL * mu * t) ≤ Ca * δp ^ 2 * t * m6
      ∧ c6 * δL * (cA * δL * t) ≤ Ca * δp ^ 2 * t
      ∧ cB * δL * mu * t ≤ Cb * δp * t * m6
      ∧ cA * δL * t ≤ Cb * δp * t := by
  have hA0 : 0 ≤ A := by linarith
  have hs60 : 0 ≤ s6 := by linarith
  have hcA0 : 0 ≤ cA := by linarith
  have h1 : δL * δL ≤ (A * δp) * (A * δp) := mul_le_mul hδ hδ hδL (by positivity)
  have h2 : δL * δL * mu ≤ (A * δp) * (A * δp) * (A * s6 * m6) :=
    mul_le_mul h1 hmu hmu0 (by positivity)
  have h3 : cB * (δL * δL * mu) ≤ cA * ((A * δp) * (A * δp) * (A * s6 * m6)) :=
    mul_le_mul hcBA h2 (by positivity) hcA0
  have h4 : δL * mu ≤ (A * δp) * (A * s6 * m6) := mul_le_mul hδ hmu hmu0 (by positivity)
  have h5 : cB * (δL * mu) ≤ cA * ((A * δp) * (A * s6 * m6)) :=
    mul_le_mul hcBA h4 (by positivity) hcA0
  have hA2 : A ≤ A ^ 2 := by nlinarith
  have hA3 : A * A ≤ A ^ 3 * s6 := by
    have h : A * A ≤ A ^ 3 := by nlinarith [mul_nonneg (mul_nonneg hA0 hA0) (sub_nonneg.mpr hA)]
    have h' : A ^ 3 ≤ A ^ 3 * s6 := le_mul_of_one_le_right (by positivity) hs6
    linarith
  have hA4 : A ≤ A ^ 2 * s6 := by
    have h' : A ^ 2 ≤ A ^ 2 * s6 := le_mul_of_one_le_right (by positivity) hs6
    linarith
  subst hCa hCb
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc c6 * δL * (cB * δL * mu * t) = c6 * t * (cB * (δL * δL * mu)) := by ring
      _ ≤ c6 * t * (cA * ((A * δp) * (A * δp) * (A * s6 * m6))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = c6 * cA * A ^ 3 * s6 * δp ^ 2 * t * m6 := by ring
  · calc c6 * δL * (cA * δL * t) = c6 * cA * t * (δL * δL) := by ring
      _ ≤ c6 * cA * t * ((A * δp) * (A * δp)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c6 * cA * t * δp ^ 2 * (A * A) := by ring
      _ ≤ c6 * cA * t * δp ^ 2 * (A ^ 3 * s6) := mul_le_mul_of_nonneg_left hA3 (by positivity)
      _ = c6 * cA * A ^ 3 * s6 * δp ^ 2 * t := by ring
  · calc cB * δL * mu * t = t * (cB * (δL * mu)) := by ring
      _ ≤ t * (cA * ((A * δp) * (A * s6 * m6))) := mul_le_mul_of_nonneg_left h5 ht
      _ = cA * A ^ 2 * s6 * δp * t * m6 := by ring
  · calc cA * δL * t ≤ cA * (A * δp) * t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ hcA0) ht
      _ = cA * δp * t * A := by ring
      _ ≤ cA * δp * t * (A ^ 2 * s6) := mul_le_mul_of_nonneg_left hA4 (by positivity)
      _ = cA * A ^ 2 * s6 * δp * t := by ring

/-- The constant `c_α` of (H5a), (H5b) against `δ' = √(p_σ(0) log N/N)`. -/
noncomputable def h5Ca (d : ℕ) : ℝ :=
  h5cD d * h5cA d * ((1 + Real.sqrt (2 * Real.pi)) ^ d) ^ 3 * (Real.sqrt 6) ^ d

/-- The constant `c_β` of (H5c), (H5d) against `δ' = √(p_σ(0) log N/N)`. -/
noncomputable def h5Cb (d : ℕ) : ℝ :=
  h5cA d * ((1 + Real.sqrt (2 * Real.pi)) ^ d) ^ 2 * (Real.sqrt 6) ^ d

theorem h5C_nonneg (d : ℕ) : 0 ≤ h5Ca d ∧ 0 ≤ h5Cb d := by
  obtain ⟨h1, h2, h3⟩ := h5c_nonneg d
  have h4 : 0 ≤ h5cA d := h2.trans h3
  constructor
  · unfold h5Ca; positivity
  · unfold h5Cb; positivity

/-- **(H5) for the `ĥ` of the paper, with probability.** Under the hypotheses of
    `kernel_theorem_G28`: except on an event of probability at most `2/N³`, (H5a)--(H5d)
    (`RemainingH5`, `η = δ'`) hold for the linearised defect `torusHhat` of the paper, for
    every `k ≤ K`, with the constants `h5Ca d`, `h5Cb d`. -/
theorem h5_events {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        RemainingH5 d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))
          (h5Ca d) (h5Cb d) δp}
      ≤ 2 / (N : ℝ) ^ 3 := by
  obtain ⟨ML, Lip, δL, hML, hLip, hδL, hN12, hKN, hLipc, hsmallL, hδLle, hδL0, hδp0⟩ :=
    h5_setup hσ hσ1 d hd N K hN2 hK hMp hδp hrange
  have hE := h5_g3 hσ hσ1 d X h_indep hX hlaw N K hN12 hK hKN hML hLip hδL hLipc hsmallL
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) hE
  intro ω hω hgood
  apply hω
  intro k hk hkK
  obtain ⟨hD0, hB0, hBA⟩ := h5c_nonneg d
  have hA1 : (1 : ℝ) ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d :=
    one_le_pow₀ (by linarith [Real.sqrt_nonneg (2 * Real.pi)])
  have hs61 : (1 : ℝ) ≤ (Real.sqrt 6) ^ d :=
    one_le_pow₀ (Real.one_le_sqrt.mpr (by norm_num))
  have hconv : ∀ m, 1 ≤ m →
      h5cD d * δL * (h5cB d * δL * heatMu d σ m * (1 / Real.sqrt m))
          ≤ h5Ca d * δp ^ 2 * (1 / Real.sqrt m) * torusM d σ (6 * m)
        ∧ h5cD d * δL * (h5cA d * δL * (1 / Real.sqrt m)) ≤ h5Ca d * δp ^ 2 * (1 / Real.sqrt m)
        ∧ h5cB d * δL * heatMu d σ m * (1 / Real.sqrt m)
          ≤ h5Cb d * δp * (1 / Real.sqrt m) * torusM d σ (6 * m)
        ∧ h5cA d * δL * (1 / Real.sqrt m) ≤ h5Cb d * δp * (1 / Real.sqrt m) := by
    intro m hm
    have hmu0 := heatMu_nonneg d σ m
    have hm6 : 0 ≤ torusM d σ (6 * m) := (torusM_pos hσ d (by omega : 1 ≤ 6 * m)).le
    have hmu : heatMu d σ m
        ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d * (Real.sqrt 6) ^ d * torusM d σ (6 * m) := by
      have h1 := heatMu_le_m_all hσ d m hm
      have h2 := torusM_six hσ d hm
      have h3 : (1 + Real.sqrt (2 * Real.pi)) ^ d * torusM d σ m
          ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d * ((Real.sqrt 6) ^ d * torusM d σ (6 * m)) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      calc heatMu d σ m ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d * torusM d σ m := h1
        _ ≤ _ := h3
        _ = _ := by ring
    have ht : 0 ≤ 1 / Real.sqrt m := by positivity
    exact conv_arith hD0 hB0 hBA hA1 hs61 hδL0 hδp0 hδLle hmu0 hm6 hmu ht rfl rfl
  refine ⟨fun m hm hmk i b => ?_, fun m hm hmk i => ?_, fun m hm hmk i b => ?_,
    fun m hm hmk i => ?_⟩
  · exact ((hgood m hm (hmk.trans hkK)).1 i b).trans (hconv m hm).1
  · exact ((hgood m hm (hmk.trans hkK)).2.1 i).trans
      (mul_le_mul_of_nonneg_left (hconv m hm).2.1 (Nat.cast_nonneg N))
  · exact ((hgood m hm (hmk.trans hkK)).2.2.1 i b).trans (hconv m hm).2.2.1
  · exact ((hgood m hm (hmk.trans hkK)).2.2.2 i).trans
      (mul_le_mul_of_nonneg_left (hconv m hm).2.2.2 (Nat.cast_nonneg N))

/-- **The reduction for a random sample on the flat torus with the `Π_k` of the paper, no
    remaining hypothesis.** Under the hypotheses of `kernel_theorem_G28` (`d ≥ 1`, `σ = ξ² ≤ 1`,
    `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`, `kernelC1 d · δ' √K ≤ 1`): except on an event of
    probability at most `8/N³`, for every `1 ≤ k ≤ K`,
    `|Tr P^{k+1} - m_{k+1} - Π_k| ≤ C δ'² k m_{k+1}`, where `Π_k = torusPi … torusHhat` is built
    from `θ¹` and the linearised defect `ĥ` of Step 2 of `prop:reduction`, and `C` is the
    explicit constant below (depending only on `d`). The smallness of `δ'` used in the paper
    (`6δ' ≤ 1/8`) is not a separate hypothesis: it follows from `hrange`, because `kernelC1 d ≥ 48`. -/
theorem torus_reduction_paper {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)
            - torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|
          ≤ (Real.sqrt 2) ^ d
              * (2 * (4 * normC d) * kernelC1 d + 2 * (14 * normC d ^ 2) + h5Ca d
                  + 2 * (2 * (Real.sqrt 2) ^ d * h5Ca d + h5Ca d
                      + (Real.sqrt 2) ^ d * kernelC1 d * h5Cb d + h4C d * h5Cb d))
              * δp ^ 2 * k * torusM d σ (k + 1)}
      ≤ 8 / (N : ℝ) ^ 3 := by
  have h1 := torus_reduction_sample_l1 hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have h2 := h5_events hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have key := (measureReal_union_le _ _).trans (add_le_add h1 h2)
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (key.trans (le_of_eq (by ring)))
  intro ω hbad
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  obtain ⟨g1, g2⟩ := hcon
  apply hbad
  intro k hk hkK
  exact g1 k hk hkK (h5Ca d) (h5Cb d) (torusHhat d σ N (fun j => X j ω))
    (h5C_nonneg d).1 (h5C_nonneg d).2 (g2 k hk hkK)



end H5

namespace EigenspaceSample

/-! ## `cor:eigspace` for random samples (free `k`, explicit gap) -/

open EigenspaceSteps

/-- The position, in decreasing order of the eigenvalues, of the index `i` of the eigenbasis of
    Mathlib: `hS.eigenvalues i = hS.eigenvalues₀ (ord N i)`, and `evec hS i` is the eigenvector
    belonging to it. -/
noncomputable def ord (N : ℕ) (i : Fin N) : Fin (Fintype.card (Fin N)) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm i

theorem eigenvalues_ord {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.IsHermitian) (i : Fin N) :
    hS.eigenvalues i = hS.eigenvalues₀ (ord N i) := rfl

/-- The indices `i` of the eigenbasis whose ordered position (from zero) lies in `[lo, hi]`.
    For a shell: `lo = 1 + 2 #{lexPos, |n|² < r}`, `hi = 2 #{lexPos, |n|² ≤ r}`. -/
noncomputable def shellSet (N lo hi : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => lo ≤ (ord N i).val ∧ (ord N i).val ≤ hi

theorem mem_shellSet {N lo hi : ℕ} (i : Fin N) :
    i ∈ shellSet N lo hi ↔ lo ≤ (ord N i).val ∧ (ord N i).val ≤ hi := by
  unfold shellSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **Separation of the cluster of a shell (deterministic).** HYPOTHESIS `hi`: part (i) of the
    eigenvalue theorem at one step `k` for all indices (top eigenvalue `1`; every index of a shell
    `q` has `|s_j^k - a_q^k| ≤ E`, `a_q = e^{-c q}`). `r⁻ < r < r⁺` with `r⁻ ≥ 0` such that no
    lattice point (lexicographically positive) has `|n|²` strictly between `r⁻` and `r` or between
    `r` and `r⁺`. Then the indices of the shell `r` have `|s^k - a_r^k| ≤ E`, and every other index
    has `|s^k - a_r^k| ≥ g` for every `g ≤ min(a_{r⁻}^k - a_r^k, a_r^k - a_{r⁺}^k) - E`. -/
theorem shell_separation {d N : ℕ} (hd : 1 ≤ d) (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : S.IsHermitian) (k : ℕ) {c E : ℝ} (hc : 0 < c)
    (hi : ∀ j : Fin (Fintype.card (Fin N)), (j.val = 0 → hS.eigenvalues₀ j = 1)
      ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
          |hS.eigenvalues₀ j ^ k - Real.exp (-c * r) ^ k| ≤ E)
    {r rm rp : ℝ} (hrm0 : 0 ≤ rm) (hrm : rm < r) (hrp : r < rp)
    (hgap : ∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
        ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (Hlt Hle : Finset (Fin d → ℤ))
    (hlt : ∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r)
    (hle : ∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) {g : ℝ}
    (hg1 : g ≤ Real.exp (-c * rm) ^ k - Real.exp (-c * r) ^ k - E)
    (hg2 : g ≤ Real.exp (-c * r) ^ k - Real.exp (-c * rp) ^ k - E) (hE : 0 ≤ E) :
    (∀ i ∈ shellSet N (1 + 2 * Hlt.card) (2 * Hle.card),
        |hS.eigenvalues i ^ k - Real.exp (-c * r) ^ k| ≤ E)
    ∧ (∀ i, i ∉ shellSet N (1 + 2 * Hlt.card) (2 * Hle.card) →
        g ≤ |hS.eigenvalues i ^ k - Real.exp (-c * r) ^ k|) := by
  classical
  have hanti : ∀ {x y : ℝ}, x ≤ y → Real.exp (-c * y) ^ k ≤ Real.exp (-c * x) ^ k := by
    intro x y hxy
    exact pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by nlinarith)) k
  have hle1 : ∀ x : ℝ, 0 ≤ x → Real.exp (-c * x) ^ k ≤ 1 := by
    intro x hx
    exact pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by nlinarith))
  constructor
  · intro i hi'
    rw [mem_shellSet] at hi'
    exact (hi (ord N i)).2 r (by linarith) Hlt Hle hlt hle hi'.1 hi'.2
  · intro i hi'
    have hmem : ¬ (1 + 2 * Hlt.card ≤ (ord N i).val ∧ (ord N i).val ≤ 2 * Hle.card) := by
      intro h; exact hi' ((mem_shellSet i).mpr h)
    show g ≤ |hS.eigenvalues₀ (ord N i) ^ k - Real.exp (-c * r) ^ k|
    obtain ⟨h0, hsh⟩ := hi (ord N i)
    by_cases hj0 : (ord N i).val = 0
    · rw [h0 hj0, one_pow]
      have h1 := hle1 rm hrm0
      exact le_trans (by linarith) (le_abs_self _)
    · obtain ⟨q, hq, Hlt', Hle', hlt', hle', hj1, hj2⟩ :=
        shell_cover hd (ord N i).val (by omega)
      have hb := hsh (q : ℝ) (by exact_mod_cast hq) Hlt' Hle' hlt' hle' hj1 hj2
      have hcard : Hlt'.card < Hle'.card := by omega
      obtain ⟨n, hn1, hn2⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      rw [hle'] at hn1
      have hnq : ∑ i, ((n i : ℤ) : ℝ) ^ 2 = (q : ℝ) := by
        have h3 : ¬ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < (q : ℝ) := fun h => hn2 ((hlt' n).mpr ⟨hn1.1, h⟩)
        exact le_antisymm hn1.2 (not_lt.mp h3)
      rcases hgap n hn1.1 with h | h | h
      · rw [hnq] at h
        have h4 := hanti h
        have hb' := (abs_le.mp hb).1
        exact le_trans (by linarith) (le_abs_self _)
      · exfalso
        rw [hnq] at h
        apply hmem
        have e1 : Hlt' = Hlt := by
          ext n'; rw [hlt', hlt, h]
        have e2 : Hle' = Hle := by
          ext n'; rw [hle', hle, h]
        rw [← e1, ← e2]; exact ⟨hj1, hj2⟩
      · rw [hnq] at h
        have h4 := hanti h
        have hb' := (abs_le.mp hb).2
        exact le_trans (by linarith) (neg_le_abs _)

/-- Under the separation, the set of indices of the shell is exactly the set of indices whose
    eigenvalue power lies within `g` of `a_r^k`; in particular it is a union of full classes of
    equal eigenvalues, so that `specProj hS J` is the spectral projection of `S^k` for the interval
    `(α - g, α + g)` and does not depend on the choice of the eigenbasis. -/
theorem cluster_iff {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.IsHermitian) (k : ℕ)
    (J : Finset (Fin N)) {α E g : ℝ} (hEg : E < g)
    (h1 : ∀ i ∈ J, |hS.eigenvalues i ^ k - α| ≤ E)
    (h2 : ∀ i, i ∉ J → g ≤ |hS.eigenvalues i ^ k - α|) (i : Fin N) :
    i ∈ J ↔ |hS.eigenvalues i ^ k - α| < g := by
  constructor
  · intro h; exact lt_of_le_of_lt (h1 i h) hEg
  · intro h; by_contra hc; exact absurd (h2 i hc) (not_le.mpr h)

theorem cluster_full {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (hS : S.IsHermitian) (k : ℕ)
    (J : Finset (Fin N)) {α E g : ℝ} (hEg : E < g)
    (h1 : ∀ i ∈ J, |hS.eigenvalues i ^ k - α| ≤ E)
    (h2 : ∀ i, i ∉ J → g ≤ |hS.eigenvalues i ^ k - α|) (i i' : Fin N)
    (he : hS.eigenvalues i = hS.eigenvalues i') (hi : i ∈ J) : i' ∈ J := by
  rw [cluster_iff S hS k J hEg h1 h2] at hi ⊢
  rw [← he]; exact hi

/-- **Stage 1 (deterministic).** Part (i) at the step `k` for all indices (HYPOTHESIS `hi`) and an
    approximate eigenvector `w` of `S^k` for `a_r^k` (HYPOTHESIS `hres`) give
    `‖w - Π_J w‖² ≤ ε²/g²`, where `Π_J` is the projection onto the eigenvectors of `S` whose
    ordered index lies in the shell `r`. -/
theorem eigspace_stage1 {d N : ℕ} (hd : 1 ≤ d) (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : S.IsHermitian) (k : ℕ) {c E : ℝ} (hc : 0 < c)
    (hi : ∀ j : Fin (Fintype.card (Fin N)), (j.val = 0 → hS.eigenvalues₀ j = 1)
      ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
          |hS.eigenvalues₀ j ^ k - Real.exp (-c * r) ^ k| ≤ E)
    {r rm rp : ℝ} (hrm0 : 0 ≤ rm) (hrm : rm < r) (hrp : r < rp)
    (hgap : ∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
        ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (Hlt Hle : Finset (Fin d → ℤ))
    (hlt : ∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r)
    (hle : ∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) {g : ℝ} (hg : 0 < g)
    (hg1 : g ≤ Real.exp (-c * rm) ^ k - Real.exp (-c * r) ^ k - E)
    (hg2 : g ≤ Real.exp (-c * r) ^ k - Real.exp (-c * rp) ^ k - E) (hE : 0 ≤ E)
    (w : Fin N → ℝ) {ε : ℝ}
    (hres : ∑ a, (((S ^ k) *ᵥ w) a - Real.exp (-c * r) ^ k * w a) ^ 2 ≤ ε ^ 2) :
    (w - specProj hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) w)
        ⬝ᵥ (w - specProj hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) w)
      ≤ ε ^ 2 / g ^ 2 :=
  spectral_proj S hS k w hg hres _
    (shell_separation hd S hS k hc hi hrm0 hrm hrp hgap Hlt Hle hlt hle hg1 hg2 hE).2

/-- Matrix form of stage 2 (modelled on `eig_sample_i_kern`): row sums of `S^{k+1} - X Xᵀ` from the
    kernel bound, the normalisation and the Fourier tail; then `eigspace_from_gram`. -/
theorem eigspace_sample_kern {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    [Nonempty n]
    (pk : ℕ → n → n → ℝ) (mu : ℕ → ℝ) (P : Matrix n n ℝ)
    (hp0 : ∀ m b i, 0 ≤ pk m b i) (hpmu : ∀ m b i, pk m b i ≤ mu m)
    (k : ℕ)
    (S : Matrix n n ℝ) (hS : S.IsHermitian)
    (r : n → ℝ) (hr : ∀ i, 0 < r i) (hSP : ∀ i l, S i l = r i * P i l / r l)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ i l, |r i / r l - 1| ≤ θ)
    (v : Matrix n F ℝ) (a : F → ℝ) (ha : ∀ f, 0 ≤ a f) {eta t Dk eps : ℝ}
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta)
    (htail : ∀ i l, |pk (k + 1) i l - (Fintype.card n : ℝ) *
        ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
          (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t)
    (hkern : ∀ a' i, |(Fintype.card n : ℝ) * (P ^ (k + 1)) a' i - pk (k + 1) a' i| ≤ Dk)
    (heps : θ * (mu (k + 1) + Dk) + Dk + t ≤ eps)
    (f0 : F) (J : Finset n) {g : ℝ} (hg : 0 < g)
    (hJ : ∀ i, i ∉ J → g ≤ |hS.eigenvalues i ^ (k + 1) - a f0|) :
    ((fun j => v j f0) - specProj hS J (fun j => v j f0))
        ⬝ᵥ ((fun j => v j f0) - specProj hS J (fun j => v j f0))
      ≤ ((1 + eta) * (eps + eta * ∑ f, |a f|)) ^ 2 / g ^ 2 := by
  have hNpos : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hrow : ∀ i, ∑ l, |(S ^ (k + 1)) i l - ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ eps := by
    intro i
    refine (row_sums_from_kernel (S ^ (k + 1)) (P ^ (k + 1)) _ (Matrix.of fun i l => pk (k + 1) i l)
      (fun i l => r i / r l) hNpos rfl hθ0 (fun i l => ?_) hθ (fun i l => hkern i l)
      (fun i l => ?_) (fun i l => htail i l) i).trans heps
    · rw [conj_pow_entry S P r hr hSP (k + 1) i l]; ring
    · show |pk (k + 1) i l| ≤ mu (k + 1)
      rw [abs_of_nonneg (hp0 _ _ _)]; exact hpmu _ _ _
  have heps0 : 0 ≤ eps := by
    obtain ⟨i⟩ := ‹Nonempty n›
    exact le_trans (Finset.sum_nonneg fun l _ => abs_nonneg _) (hrow i)
  exact eigspace_from_gram S _ hS (k + 1) v a (fun i j => finite_rank_kernel_entry v a ha i j) f0
    heps0 hg hG hrow J hJ

set_option maxHeartbeats 3200000 in
/-- Modified copy of `heatTorus_eig_i_det` (same hypotheses on the point tuple): the sampled real
    Fourier mode `w = (φ_{f0}(x_i)/√N)_i`, `f0 ∈ modeSet d H`, against an arbitrary set `J` of
    indices of the eigenbasis outside of which `|s_i^{k+1} - a_{f0}| ≥ g`. -/
theorem heatTorus_eigspace_det {c : ℝ} (hc : 0 < c) (d N : ℕ) [NeZero N] (x : Fin N → FlatTorus d)
    (k : ℕ) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {R delta eta t Dk eps : ℝ}
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 8) (heta : 0 ≤ eta)
    (hnorm : ∀ b, |(∑ l, heatTorus d c (x b - x l)) / N - 1| ≤ delta)
    (hgram : ∀ f g : modeSet d H, |∑ i, torusMode d f.1 (x i) * torusMode d g.1 (x i)
        - N * (if f = g then (1 : ℝ) else 0)| ≤ N * eta)
    (ht : Real.exp (-((k + 1 : ℕ) * c) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k + 1 : ℕ) * c))) ^ d ≤ t)
    (hkern : ∀ a i : Fin N, |(N : ℝ) * ((walkMatrix (fun i j : Fin N => heatTorus d c (x i - x j))
        (fun i => (∑ l, heatTorus d c (x i - x l)) / N)) ^ (k + 1)) a i
      - heatTorus d ((k + 1 : ℕ) * c) (x a - x i)| ≤ Dk)
    (heps : 3 * delta * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + Dk) + Dk + t ≤ eps)
    (hS : (symGraph (fun i j : Fin N => heatTorus d c (x i - x j))
      (fun i => (∑ l, heatTorus d c (x i - x l)) / N)).IsHermitian)
    (f0 : modeSet d H) (J : Finset (Fin N)) {g : ℝ} (hg : 0 < g)
    (hJ : ∀ i, i ∉ J → g ≤ |hS.eigenvalues i ^ (k + 1) - modeCoeff d ((k + 1 : ℕ) * c) f0.1|) :
    ((fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N)
        - specProj hS J (fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N))
      ⬝ᵥ ((fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N)
        - specProj hS J (fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N))
      ≤ ((1 + eta) * (eps + eta * ∑ f : modeSet d H, |modeCoeff d ((k + 1 : ℕ) * c) f.1|)) ^ 2
          / g ^ 2 := by
  classical
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp
  set K : Fin N → Fin N → ℝ := fun i j => heatTorus d c (x i - x j) with hKdef
  set rho : Fin N → ℝ := fun i => (∑ l, heatTorus d c (x i - x l)) / N with hrhodef
  set pk : ℕ → Fin N → Fin N → ℝ := fun m b i =>
    if m = 0 then 0 else heatTorus d ((m : ℕ) * c) (x b - x i) with hpkdef
  set mu : ℕ → ℝ := fun m => if m = 0 then 0 else (1 + Real.sqrt (Real.pi / ((m : ℕ) * c))) ^ d
    with hmudef
  have hmc : ∀ m : ℕ, m ≠ 0 → 0 < (m : ℝ) * c := fun m hm =>
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hc
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => heatTorus_nonneg hc d _
  have hrho1 : ∀ b, |rho b - 1| ≤ delta := hnorm
  have hrhoeq : ∀ b, (Fintype.card (Fin N) : ℝ) * rho b = ∑ l, K b l := fun b => by
    rw [hcard]; simp only [hrhodef, hKdef]; field_simp
  have hDb := fun i => graph_degree_bounds K hK0 rho hd0 hd hrhoeq hrho1 i
  have hDpos : ∀ i, 0 < ∑ l, K i l / (rho i * rho l) := fun i =>
    lt_of_lt_of_le (div_pos (by rw [hcard]; exact hNpos) (by linarith)) (hDb i).1
  -- kernel-matrix factor
  set a : modeSet d H → ℝ := fun f => modeCoeff d ((k + 1 : ℕ) * c) f.1 with hadef
  set v : Matrix (Fin N) (modeSet d H) ℝ :=
    Matrix.of fun i f => torusMode d f.1 (x i) / Real.sqrt N with hvdef
  have ha : ∀ f, 0 ≤ a f := fun f => modeCoeff_nonneg d _ f.1
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hsqpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
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
  have htail : ∀ i l, |pk (k + 1) i l - (Fintype.card (Fin N) : ℝ) *
      ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t := by
    intro i l
    rw [finite_rank_kernel_entry v a ha i l, hcard]
    have e : (N : ℝ) * ∑ f, a f * v i f * v l f
        = 1 + ∑ n ∈ H, 2 * Real.exp (-((k + 1 : ℕ) * c) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
            * (torusChar d n (x i - x l)).re := by
      rw [← modeSet_kernel d ((k + 1 : ℕ) * c) H (x i) (x l),
        ← Finset.sum_coe_sort (modeSet d H), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [hvdef, hadef, of_apply]
      field_simp
      rw [Real.sq_sqrt hNpos.le]; ring
    rw [e]
    have hp : pk (k + 1) i l = heatTorus d ((k + 1 : ℕ) * c) (x i - x l) := by
      simp [hpkdef]
    rw [hp]
    exact (heatTorus_truncation_half (hmc (k + 1) (Nat.succ_ne_zero k)) d H hH0 hH2 hR _).trans ht
  have hmain := eigspace_sample_kern pk mu (walkMatrix K rho)
    (fun m b i => by
      simp only [hpkdef]; split_ifs with h
      · exact le_rfl
      · exact heatTorus_nonneg (hmc m h) d _)
    (fun m b i => by
      simp only [hpkdef, hmudef]; split_ifs with h
      · exact le_rfl
      · exact heatTorus_le (hmc m h) d _) k
    (symGraph K rho) hS
    (fun i => Real.sqrt (∑ l, K i l / (rho i * rho l))) (fun i => Real.sqrt_pos.mpr (hDpos i))
    (symGraph_conj K rho hDpos) (θ := 3 * delta) (by linarith)
    (fun i l => sqrt_ratio_bound (by rw [hcard]; exact hNpos) hd0 hd (hDb i) (hDb l))
    v a ha (Dk := Dk) (eps := eps) (t := t) hG htail
    (by
      intro a' i
      have := hkern a' i
      simp only [hpkdef, hcard, Nat.succ_ne_zero, if_false]
      exact this)
    (by simpa [hmudef] using heps) f0 J hg hJ
  exact hmain

set_option maxHeartbeats 3200000 in
/-- **Stage 2 (deterministic, on a point tuple).** Modified copy of `heat_eig_i_det`: for every
    `1 ≤ k ≤ K`, every mode `f0` of `modeSet d H` and every set `J` of indices of the eigenbasis
    outside of which `|s_i^k - a_{f0}^{(k)}| ≥ g > 0`:
    `‖w - Π_J w‖² ≤ ((1+η)(err_k + η Σ_f |a_f|))²/g²`, `w = (φ_{f0}(x_i)/√N)_i`. HYPOTHESES:
    normalisation `hnorm`, Gram matrix `hgram`, kernel bound `hkern`. -/
theorem heat_eigspace_det {σ δ η R : ℝ} (hσ : 0 < σ) (d N K : ℕ) [NeZero N]
    (x : ℕ → FlatTorus d) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0)
    (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hδ0 : 0 ≤ δ) (hδ8 : δ ≤ 1 / 8) (hη0 : 0 ≤ η)
    (hnorm : ∀ j, |heatRho d σ N x j - 1| ≤ δ)
    (hgram : ∀ f g : modeSet d H, |∑ i : Fin N, torusMode d f.1 (x i) * torusMode d g.1 (x i)
        - N * (if f = g then (1 : ℝ) else 0)| ≤ N * η)
    (Dk : ℕ → ℝ)
    (hkern : ∀ k, 1 ≤ k → k ≤ K → ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ k) a i - heatP d σ k (x a - x i)| ≤ Dk k)
    (k : ℕ) (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hS : (symGraph (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j))
      (fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N)).IsHermitian)
    (f0 : modeSet d H) (J : Finset (Fin N)) {g : ℝ} (hg : 0 < g)
    (hJ : ∀ i, i ∉ J →
      g ≤ |hS.eigenvalues i ^ k - modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) f0.1|) :
    ((fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N)
        - specProj hS J (fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N))
      ⬝ᵥ ((fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N)
        - specProj hS J (fun i : Fin N => torusMode d f0.1 (x i) / Real.sqrt N))
      ≤ ((1 + η) * (heatEigErr d σ k δ (Dk k) R
            + η * ∑ f : modeSet d H, |modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) f.1|)) ^ 2
          / g ^ 2 := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have e1 : (fun a : Fin N => heatRho d σ N x a)
      = fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N := by
    funext a
    unfold heatRho
    rw [Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) N]
  have hnorm' : ∀ b : Fin N,
      |(∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l)) / N - 1| ≤ δ := by
    intro b
    have h := hnorm b
    have e := congrFun e1 b
    simp only at e
    rw [e] at h
    exact h
  have hkern' : ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j))
          (fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N))
            ^ (k0 + 1)) a i
        - heatTorus d ((k0 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) (x a - x i)| ≤ Dk (k0 + 1) := by
    intro a i
    have h := hkern (k0 + 1) hk1 hkK a i
    have e2 : heatP d σ (k0 + 1) (x a - x i)
        = heatTorus d ((k0 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) (x a - x i) := by
      rw [heatP_of_ne d σ (by omega)]
      congr 1
      ring
    rw [e1, e2] at h
    exact h
  exact heatTorus_eigspace_det hc d N (fun i : Fin N => x i) k0 H hH0 hH2 hR
    hδ0 hδ8 hη0 hnorm' hgram le_rfl hkern'
    (eps := heatEigErr d σ (k0 + 1) δ (Dk (k0 + 1)) R) (by unfold heatEigErr; exact le_rfl) hS
    f0 J hg hJ

/-! ### Arithmetic for the sample statement -/

theorem heatEigErr_nonneg (d : ℕ) (σ : ℝ) (k : ℕ) {δ D R : ℝ} (hδ : 0 ≤ δ) (hD : 0 ≤ D) :
    0 ≤ heatEigErr d σ k δ D R := by
  unfold heatEigErr
  have h1 : 0 ≤ (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d := by
    positivity
  have h2 : 0 ≤ Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
      * (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d := by positivity
  have h3 : 0 ≤ 3 * δ * ((1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d + D) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

theorem final_arith {η X Sa Ss E g Y : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hX : 0 ≤ X)
    (hSa0 : 0 ≤ Sa) (hSa : Sa ≤ Ss) (hXE : X + η * 1 * Ss ≤ E) (hg : 0 < g)
    (hY : Y ≤ ((1 + η) * (X + η * Sa)) ^ 2 / g ^ 2) : Y ≤ (2 * E) ^ 2 / g ^ 2 := by
  have h4 := mul_le_mul_of_nonneg_left hSa hη0
  have h1 : X + η * Sa ≤ E := by linarith
  have h0 : 0 ≤ X + η * Sa := add_nonneg hX (mul_nonneg hη0 hSa0)
  have h5 : 0 ≤ (X + η * Sa) * (1 - η) := mul_nonneg h0 (by linarith)
  have h2 : (1 + η) * (X + η * Sa) ≤ 2 * E := by nlinarith
  have h3 : 0 ≤ (1 + η) * (X + η * Sa) := mul_nonneg (by linarith) h0
  exact hY.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ h3 h2 2) (by positivity))

theorem eta_le_one (d : ℕ) {δL : ℝ} (hδL0 : 0 ≤ δL)
    (h48 : 48 * Real.sqrt (3 * (d : ℝ) + 5) * δL ≤ 1) :
    Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) * δL ≤ 1 := by
  have h1 : Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ)))
      ≤ 48 * Real.sqrt (3 * (d : ℝ) + 5) := by
    have e : 48 * Real.sqrt (3 * (d : ℝ) + 5) = Real.sqrt (48 ^ 2 * (3 * (d : ℝ) + 5)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [e]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  exact (mul_le_mul_of_nonneg_right h1 hδL0).trans h48

theorem r_lt_R {c r R : ℝ} (hc : 0 < c) (h : 2 * c * r ≤ 1) (hR : 1 / c ≤ R) : r < R := by
  have h1 : r ≤ (1 / 2) / c := by rw [le_div_iff₀ hc]; linarith
  have h2 : (1 / 2 : ℝ) / c < 1 / c := div_lt_div_of_pos_right (by norm_num) hc
  linarith

theorem modeCoeff_le_one (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (f : Option ((Fin d → ℤ) × Bool)) :
    modeCoeff d c f ≤ 1 := by
  rcases f with _ | ⟨n, b⟩
  · simp [modeCoeff]
  · simp only [modeCoeff]
    apply Real.exp_le_one_iff.mpr
    have h1 : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
    nlinarith [mul_nonneg hc h1]

theorem modeCoeff_abs_sum_le (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (H : Finset (Fin d → ℤ)) :
    ∑ f : modeSet d H, |modeCoeff d c f.1| ≤ ∑ f : modeSet d H, Real.sqrt (modeCoeff d c f.1) := by
  refine Finset.sum_le_sum fun f _ => ?_
  have h0 := modeCoeff_nonneg d c f.1
  have h1 := modeCoeff_le_one d hc f.1
  rw [abs_of_nonneg h0]
  have hs0 := Real.sqrt_nonneg (modeCoeff d c f.1)
  have hs1 : Real.sqrt (modeCoeff d c f.1) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
  have e := Real.mul_self_sqrt h0
  nlinarith

set_option maxHeartbeats 6400000 in
/-- **Corollary "Eigenspaces on a flat torus", first half, for random samples (stage 3).**
    Independent uniform points on the flat torus of dimension `d ≥ 1`, periodised Gaussian kernel
    of variance `σ = ξ² ≤ 1`, graph with self-loops, `N ≥ 2`, `M = p(0)`, `δ' = √(M log N/N)`,
    `m_k = p_{kσ}(0)`, `K ≥ 1` with `C₁ δ' √K ≤ 1`. Except on an event of probability at most
    `6/N³`, for ALL `1 ≤ k ≤ K`, every shell `|n|² = r` with `4π²σ r ≤ 1` (`Λ = 4π² r ≤ ξ⁻²`), all
    `0 ≤ r⁻ < r < r⁺` such that no lattice point has `|n|²` strictly between `r⁻` and `r` or between
    `r` and `r⁺`, and every `g > 0` with
    `g ≤ min(a_{r⁻}^k - a_r^k, a_r^k - a_{r⁺}^k) - E_k`, `a_q = e^{-2π²σ q}`,
    `E_k = C₃ δ' √k m_k`:
    (1) the eigenvalues of `S` with ordered index in the shell have `|s^k - a_r^k| ≤ E_k`;
    (2) all other eigenvalues have `|s^k - a_r^k| ≥ g`;
    (3) for every lattice point `n` of the shell and both real modes (`b = false`: `√2 cos`,
    `b = true`: `√2 sin`), the sampled mode `w = (φ_{n,b}(x_a)/√N)_a` satisfies
    `‖w - Π_J w‖² ≤ (2 E_k)²/g²`, where `Π_J` is the orthogonal projection onto the span of the
    eigenvectors of `S` whose ordered index lies in the shell. -/
theorem eigspace_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N] (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (r rm rp : ℝ), 0 ≤ rm → rm < r → r < rp → 4 * Real.pi ^ 2 * σ * r ≤ 1 →
          (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
              ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) →
          ∀ Hlt Hle : Finset (Fin d → ℤ),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          ∀ g : ℝ, 0 < g →
          g ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * rm) ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k
                - eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 →
          g ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * rp) ^ k
                - eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 →
          (∀ i ∈ (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)),
              |hS.eigenvalues i ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
                ≤ eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
          ∧ (∀ i, i ∉ (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) →
              g ≤ |hS.eigenvalues i ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|)
          ∧ ∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r → ∀ b : Bool,
              ((fun i : Fin N => torusMode d (some (n, b)) (X i ω) / Real.sqrt N)
                  - specProj hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card))
                      (fun i : Fin N => torusMode d (some (n, b)) (X i ω) / Real.sqrt N))
                ⬝ᵥ ((fun i : Fin N => torusMode d (some (n, b)) (X i ω) / Real.sqrt N)
                  - specProj hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card))
                      (fun i : Fin N => torusMode d (some (n, b)) (X i ω) / Real.sqrt N))
              ≤ (2 * (eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)) ^ 2
                  / g ^ 2}
      ≤ 6 / (N : ℝ) ^ 3 := by
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
      _ = A * δp := by rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA0, hδp]
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
  have hδL2 : δL ^ 2 = ML * Real.log N / N := by rw [hδL, Real.sq_sqrt (by positivity)]
  have h2d : (2 : ℝ) ^ d ≤ N := (rateCfin3_ge d).2.trans hCN
  have hMLlg : (1 / 2 : ℝ) ≤ ML * Real.log N := by
    have := mul_le_mul hML1 hlg (by norm_num) (by linarith : (0 : ℝ) ≤ ML)
    linarith
  have hδN : 1 / (N : ℝ) ≤ δL := by
    have hNr12 : (12 : ℝ) ≤ N := by exact_mod_cast hN12
    have h1 : (1 / (N : ℝ)) ^ 2 ≤ ML * Real.log N / N := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) hNpos]
      nlinarith
    calc 1 / (N : ℝ) = Real.sqrt ((1 / (N : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (ML * Real.log N / N) := Real.sqrt_le_sqrt h1
      _ = δL := hδL.symm
  obtain ⟨hR0, hRm, hF, htail, hRbig⟩ := g38_cutoff hσ d N hN12 h1σ h2d hδN
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.log (2 ^ d * (N : ℝ)) / (2 * Real.pi ^ 2 * σ) := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = Nat.ceil (Real.sqrt R) := ⟨_, rfl⟩
  rw [← hRdef] at hR0 hRm hF htail hRbig
  rw [← hmdef] at hRm hF
  -- the normalisation parameters
  have hMLpos : 0 < ML := by linarith
  have hLip0 : 0 ≤ Lip := by rw [hLip]; positivity
  have h48 : 48 * Real.sqrt (3 * (d : ℝ) + 5) * δL ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right (rateCfin3_ge d).1 hδL0
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * ML
      * Real.log ((2 + 4 * ((1 : ℕ) : ℝ)) * (2 * ((N ^ 3 : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨p1, p2, p3, p4⟩ :=
    param_choice3 d N 1 hN12 one_pos (by omega) hMLpos hLip0 hδL hLipc h48 hε
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = (ε + 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ))) / N := ⟨_, rfl⟩
  rw [← hδdef] at p2 p3
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  -- the Gram tolerance
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) * δL :=
    ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  obtain ⟨q1, q2, q3, q4⟩ := halfFreq_props d m hRm
  have hcard : Fintype.card (modeSet d (halfFreq d m R)) ≤ N ^ (3 * d + 1) :=
    (modeSet_card_le d (halfFreq d m R)).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_left 2 q4) 1).trans hF)
  have hgc := gram_choice hN2 hcard hML1 hδL
  rw [← hηdef] at hgc
  -- the bound of the error
  have hbound : ∀ k : ℕ, 1 ≤ k → k ≤ K →
      heatEigErr d σ k δ
          (kernelC1 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0) R
        + η * 1 * ∑ g : modeSet d (halfFreq d m R),
            Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
      ≤ eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by
    intro k hk1 hkK
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkKr : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hkK
    have hsk1 : 1 ≤ Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hk1r
    have hD1 : kernelC1 d * δp * Real.sqrt k ≤ 1 :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkKr) (mul_nonneg hC1nn hδp0)).trans hrange
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
    have hC3 : eigC3 d = kernelC1 d + (6 * (6 * Real.sqrt (3 * (d : ℝ) + 5)) + 2
        + Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) * (1 + 2 * s2 ^ d)) * A ^ 2 := by
      unfold eigC3; rw [hA, hs2]
    obtain ⟨mk, hmk⟩ : ∃ mk : ℝ, mk = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := ⟨_, rfl⟩
    have hmk1 : 1 ≤ mk := by rw [hmk]; exact heatTorus_zero_ge_one (by positivity) d
    have hmuA0 : (1 + Real.sqrt (Real.pi / ((k : ℝ) * (2 * Real.pi ^ 2 * σ)))) ^ d ≤ A * mk := by
      have h := heatMu_le_m_all hσ d k hk1
      unfold heatMu heatM at h
      rw [if_neg (by omega)] at h
      rw [hA, hmk, show (k : ℝ) * (2 * Real.pi ^ 2 * σ) = 2 * Real.pi ^ 2 * ((k : ℝ) * σ) by ring]
      exact h
    have hSg0 : 0 ≤ ∑ g : modeSet d (halfFreq d m R),
        Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1) :=
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
    have huW : u * s2 ^ d ≤ 2 * δL := by
      by_contra hcon
      have hlt : 2 * δL < u * s2 ^ d := lt_of_not_ge hcon
      have h1 : (2 * δL) * (2 * δL) < (u * s2 ^ d) * (u * s2 ^ d) :=
        mul_self_lt_mul_self (by positivity) hlt
      have h2 : (u * s2 ^ d) * (u * s2 ^ d) = 1 / (N : ℝ) := by
        have e : (u * s2 ^ d) * (u * s2 ^ d) = (u * u) * (s2 ^ d * s2 ^ d) := by ring
        rw [e, huu, hWW, div_mul_eq_mul_div, one_mul,
          div_eq_div_iff (by positivity) (by positivity)]
        ring
      have h3 : 1 / (N : ℝ) ≤ (2 * δL) * (2 * δL) := by
        have e : (2 * δL) * (2 * δL) = 4 * (ML * Real.log N) / N := by
          have : (2 * δL) * (2 * δL) = 4 * δL ^ 2 := by ring
          rw [this, hδL2]; ring
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) hNpos.le
      linarith
    obtain ⟨ck, hck⟩ : ∃ ck : ℝ, ck = (k : ℝ) * (2 * Real.pi ^ 2 * σ) := ⟨_, rfl⟩
    have hck0 : 0 < ck := by rw [hck]; positivity
    rw [← hck] at hmuA0 hSg1 hSg0 hle1
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt (Real.pi / ck) := ⟨_, rfl⟩
    have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
    rw [← hy] at hmuA0
    have hmu1 : 1 ≤ (1 + y) ^ d := one_le_pow₀ (by linarith)
    have hbig : (1 + s2 * y) ^ d ≤ s2 ^ d * (1 + y) ^ d := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : s2 * (1 + y) = s2 + s2 * y := by ring
      linarith
    have hT : Real.exp (-ck * R / 2) * (1 + Real.sqrt (2 * Real.pi / ck)) ^ d
        ≤ 2 * δL * (1 + y) ^ d := by
      have e1 : 2 * Real.pi / ck = 2 * (Real.pi / ck) := by ring
      rw [e1, hsq2, ← hy]
      have hle : Real.exp (-ck * R / 2) ≤ u := by
        rw [hu]; apply Real.exp_le_exp.mpr
        linarith
      calc Real.exp (-ck * R / 2) * (1 + s2 * y) ^ d
          ≤ u * (s2 ^ d * (1 + y) ^ d) := mul_le_mul hle hbig (by positivity) hu0
        _ = (u * s2 ^ d) * (1 + y) ^ d := by ring
        _ ≤ 2 * δL * (1 + y) ^ d := mul_le_mul_of_nonneg_right huW (by positivity)
    have hSg : ∑ g : modeSet d (halfFreq d m R), Real.sqrt (modeCoeff d ck g.1)
        ≤ (1 + 2 * s2 ^ d) * (1 + y) ^ d := by
      have e1 : Real.pi / (ck / 2) = 2 * (Real.pi / ck) := by
        rw [div_div_eq_mul_div]; ring
      rw [e1, hsq2, ← hy] at hSg1
      have e2 : (1 + 2 * s2 ^ d) * (1 + y) ^ d = (1 + y) ^ d + 2 * (s2 ^ d * (1 + y) ^ d) := by
        ring
      rw [e2]
      linarith
    unfold heatEigErr
    rw [hC3, ← hck, ← hmk, ← hy]
    exact eig_i_arith hA1 hδ0 hδL0 hδp0 hη0 (c1 := 6 * Real.sqrt (3 * (d : ℝ) + 5))
      (by positivity) (c2 := Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))))
      (Real.sqrt_nonneg _) hW0 hC1nn hsk1 (by linarith) (by positivity) p2 (le_of_eq hηdef)
      hδLle hmuA0 hD1 hT hSg0 hSg
  -- the three events
  have hM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ ML := fun u => by
    rw [hML]; exact heatTorus_le hcσ d u
  have hLipf : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u
      - heatTorus d (2 * Real.pi ^ 2 * σ) u'| ≤ Lip * dist u u' := fun u u' => by
    rw [hLip]; exact heatTorus_lipschitz hcσ d u u'
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
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : Set Ω, Bn = {ω | ∃ x : FlatTorus d,
      ε + 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ))
      < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} := ⟨_, rfl⟩
  have hBn : μ.real Bn ≤ 1 / (N : ℝ) ^ 3 := by
    rw [hBnd]
    exact (heat_normalisation_whp hσ d X h_indep hX hlaw N (g := N ^ 3) (pow_pos hN 3) hM hLipf
      hLip0 p1).trans p4
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
  refine le_trans (measureReal_mono (s₂ := (Bk ∪ Bn) ∪ Bg) ?_ (measure_ne_top μ _)) ?_
  · intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨hk, hn⟩, hgm⟩ := hcon
    rw [hBkd] at hk
    rw [hBnd] at hn
    rw [hBgd] at hgm
    have hkern := not_not.mp hk
    apply hω
    intro k hk1 hkK hS r rm rp hrm0 hrm hrp hΛ hgap Hlt Hle hlt hle g hg hg1 hg2
    have hnormω : ∀ b, |heatRho d σ N (fun j => X j ω) b - 1| ≤ δ := by
      intro b
      have h : |∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X l ω) - N|
          ≤ ε + 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) := by
        by_contra h; exact hn ⟨X b ω, not_le.mp h⟩
      have e : heatRho d σ N (fun j => X j ω) b - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos, hδdef]
      exact div_le_div_of_nonneg_right h hNpos.le
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
    have hη1 : η ≤ 1 := by rw [hηdef]; exact eta_le_one d hδL0 h48
    have hDk0 : 0 ≤ kernelC1 d * δp * Real.sqrt k
        * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by
      have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC1nn hδp0) (Real.sqrt_nonneg _))
        (heatTorus_nonneg (by positivity) d 0)
    have hck0 : (0 : ℝ) ≤ (k : ℕ) * (2 * Real.pi ^ 2 * σ) := by positivity
    have hSs0 : 0 ≤ ∑ g : modeSet d (halfFreq d m R),
        Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1) :=
      Finset.sum_nonneg fun g _ => Real.sqrt_nonneg _
    have hX0 := heatEigErr_nonneg d σ k (R := R) hδ0 hDk0
    have hbk := hbound k hk1 hkK
    have hE0 : 0 ≤ eigC3 d * δp * Real.sqrt k
        * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by
      have := mul_nonneg (mul_nonneg hη0 zero_le_one) hSs0
      linarith
    have hi : ∀ j : Fin (Fintype.card (Fin N)), (j.val = 0 → hS.eigenvalues₀ j = 1)
        ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
          |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
            ≤ eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by
      intro j
      obtain ⟨key1, key2⟩ := heat_eig_i_shell hσ d N K m (fun j => X j ω) hRm hR0 hδ0 p3 hη0
        hnormω hgramω
        (fun k => kernelC1 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
        hkern k hk1 hkK hDk0 hS j
      exact ⟨key1, fun r hr Hlt Hle hlt hle hj1 hj2 =>
        (key2 r hr Hlt Hle hlt hle hj1 hj2).trans hbk⟩
    obtain ⟨sep1, sep2⟩ := shell_separation hd _ hS k hcσ hi hrm0 hrm hrp hgap Hlt Hle hlt hle
      hg1 hg2 hE0
    refine ⟨sep1, sep2, ?_⟩
    intro n hn hnr b
    have hrR : r < R := r_lt_R hcσ (by linarith) hRbig
    have hnH : n ∈ halfFreq d m R := (mem_halfFreq hRm n).mpr ⟨hn, by rw [hnr]; exact hrR⟩
    have hf0 : some (n, b) ∈ modeSet d (halfFreq d m R) := (mem_modeSet d _ n b).mpr hnH
    have hcoef : modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) (some (n, b))
        = Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k := by
      show Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) = _
      rw [hnr, ← Real.exp_nat_mul]; congr 1; ring
    have hdet := heat_eigspace_det hσ d N K (fun j => X j ω) (halfFreq d m R) q1 q2 q3 hδ0 p3 hη0
      hnormω hgramω
      (fun k => kernelC1 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
      hkern k hk1 hkK hS ⟨some (n, b), hf0⟩ (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) hg
      (fun i hiJ => by rw [hcoef]; exact sep2 i hiJ)
    exact final_arith hη0 hη1 hX0
      (Finset.sum_nonneg fun f _ => abs_nonneg _)
      (modeCoeff_abs_sum_le d hck0 (halfFreq d m R)) hbk hg hdet
  · calc μ.real ((Bk ∪ Bn) ∪ Bg) ≤ μ.real (Bk ∪ Bn) + μ.real Bg := measureReal_union_le _ _
      _ ≤ (μ.real Bk + μ.real Bn) + μ.real Bg := add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ 3 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3 + 2 / (N : ℝ) ^ 3 := by linarith
      _ = 6 / (N : ℝ) ^ 3 := by ring



end EigenspaceSample

/-! ## The graph without self-loops (`cor:kernel-noloops`) by perturbation of the walk with loops.
NOT the proof of the paper (which redoes the induction); the additional term is `96 (M/N) ∑_{l≤k} m_l`. -/

namespace NoLoops

/-! ### Stage 1a: two matrices that are close in a relative sense have close powers -/

theorem stoch_mul_sup {n : Type} [Fintype n] (Q X : Matrix n n ℝ) (hQ0 : ∀ a b, 0 ≤ Q a b)
    (hQ1 : ∀ a, ∑ b, Q a b = 1) {c : ℝ} (hX : ∀ b i, |X b i| ≤ c) (a i : n) :
    |(Q * X) a i| ≤ c := by
  rw [Matrix.mul_apply]
  calc |∑ b, Q a b * X b i| ≤ ∑ b, |Q a b * X b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, Q a b * c := Finset.sum_le_sum fun b _ => by
        rw [abs_mul, abs_of_nonneg (hQ0 a b)]
        exact mul_le_mul_of_nonneg_left (hX b i) (hQ0 a b)
    _ = c := by rw [← Finset.sum_mul, hQ1, one_mul]

theorem E_mul_sup {n : Type} [Fintype n] [DecidableEq n] (Q P Y : Matrix n n ℝ) {κ c : ℝ}
    (hκ : 0 ≤ κ) (hQ0 : ∀ a b, 0 ≤ Q a b) (hQ1 : ∀ a, ∑ b, Q a b = 1)
    (hE : ∀ b i, |Q b i - P b i| ≤ κ * (Q b i + if b = i then 1 else 0))
    (hY : ∀ b i, |Y b i| ≤ c) (a i : n) : |((Q - P) * Y) a i| ≤ 2 * κ * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans (hY a i)
  have hone : ∑ b, (if a = b then (1 : ℝ) else 0) = 1 := by simp
  rw [Matrix.mul_apply]
  calc |∑ b, (Q - P) a b * Y b i| ≤ ∑ b, |(Q - P) a b * Y b i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, κ * (Q a b + if a = b then 1 else 0) * c := Finset.sum_le_sum fun b _ => by
        rw [abs_mul, Matrix.sub_apply]
        refine mul_le_mul (hE a b) (hY b i) (abs_nonneg _) (mul_nonneg hκ (add_nonneg (hQ0 a b) ?_))
        split_ifs <;> norm_num
    _ = 2 * κ * c := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib, hQ1, hone]; ring

theorem pow_mul_E {n : Type} [Fintype n] [DecidableEq n] (Q P : Matrix n n ℝ) {κ : ℝ}
    (hQ0 : ∀ a b, 0 ≤ Q a b)
    (hE : ∀ b i, |Q b i - P b i| ≤ κ * (Q b i + if b = i then 1 else 0)) (m : ℕ) (a i : n) :
    |(Q ^ m * (Q - P)) a i| ≤ κ * ((Q ^ (m + 1)) a i + (Q ^ m) a i) := by
  have hn0 := pow_entries_nonneg Q hQ0 m
  have hone : ∑ b, (Q ^ m) a b * (if b = i then (1 : ℝ) else 0) = (Q ^ m) a i := by simp
  rw [Matrix.mul_apply, pow_succ, Matrix.mul_apply]
  calc |∑ b, (Q ^ m) a b * (Q - P) b i| ≤ ∑ b, |(Q ^ m) a b * (Q - P) b i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, (Q ^ m) a b * (κ * (Q b i + if b = i then 1 else 0)) :=
        Finset.sum_le_sum fun b _ => by
          rw [abs_mul, abs_of_nonneg (hn0 a b), Matrix.sub_apply]
          exact mul_le_mul_of_nonneg_left (hE b i) (hn0 a b)
    _ = κ * (∑ b, (Q ^ m) a b * Q b i + (Q ^ m) a i) := by
        rw [← hone, ← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

theorem R_identity {n : Type} [Fintype n] [DecidableEq n] (Q P : Matrix n n ℝ) (m : ℕ) :
    Q ^ (m + 1 + 1) - P ^ (m + 1 + 1) - Q ^ (m + 1) * (Q - P)
      = Q * (Q ^ (m + 1) - P ^ (m + 1) - Q ^ m * (Q - P)) + (Q - P) * P ^ (m + 1) := by
  rw [pow_succ' Q (m + 1), pow_succ' P (m + 1), pow_succ' Q m]
  noncomm_ring

theorem arith_step {x κ A bn bn1 : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 6) (hA : 0 ≤ A)
    (hbn1 : 0 ≤ bn1) (hbn : bn ≤ A) (hx : 0 ≤ x)
    (h : x ≤ 2 * κ * A + κ * (bn1 + x + bn + 2 * A)) : x ≤ 6 * κ * (A + bn1) := by
  have h1 := mul_le_mul_of_nonneg_right hκ hx
  have h2 := mul_le_mul_of_nonneg_left hbn hκ0
  have h3 := mul_nonneg hκ0 hA
  have h4 := mul_nonneg hκ0 hbn1
  nlinarith

theorem base_arith {q p κ b t : ℝ} (hq : 0 ≤ q) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 6) (hκb : κ ≤ b)
    (ht : t ≤ 1) (hp : |p| ≤ b) (h : |q - p| ≤ κ * (q + t)) : |q - p| ≤ 2 * b := by
  have hp' := abs_le.mp hp
  have h' := abs_le.mp h
  have h1 := mul_le_mul_of_nonneg_right hκ hq
  have h2 := mul_le_mul_of_nonneg_left ht hκ0
  have h5 : κ * (q + t) = κ * q + κ * t := by ring
  rw [h5] at h h'
  refine h.trans ?_
  linarith [h'.2, hp'.2]

section Compare

variable {n : Type} [Fintype n] [DecidableEq n] (Q P : Matrix n n ℝ) {κ : ℝ} {b : ℕ → ℝ} {K : ℕ}

theorem R_bound (hκ0 : 0 ≤ κ) (hQ0 : ∀ a b, 0 ≤ Q a b) (hQ1 : ∀ a, ∑ b, Q a b = 1)
    (hE : ∀ b i, |Q b i - P b i| ≤ κ * (Q b i + if b = i then 1 else 0))
    (hB : ∀ l, 1 ≤ l → l ≤ K → ∀ a i, |(P ^ l) a i| ≤ b l) :
    ∀ m, m + 1 ≤ K → ∀ a i,
      |(Q ^ (m + 1) - P ^ (m + 1) - Q ^ m * (Q - P)) a i|
        ≤ 2 * κ * ∑ l ∈ Finset.range m, b (l + 1) := by
  intro m
  induction m with
  | zero => intro _ a i; simp
  | succ m ih =>
    intro hm a i
    rw [R_identity, Matrix.add_apply, Finset.sum_range_succ]
    have h1 := stoch_mul_sup Q _ hQ0 hQ1 (ih (by omega)) a i
    have h2 := E_mul_sup Q P (P ^ (m + 1)) hκ0 hQ0 hQ1 hE (hB (m + 1) (by omega) (by omega)) a i
    have h3 := abs_add_le
      ((Q * (Q ^ (m + 1) - P ^ (m + 1) - Q ^ m * (Q - P))) a i) (((Q - P) * P ^ (m + 1)) a i)
    linarith

theorem pow_compare_step (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 6) (hb0 : ∀ l, 0 ≤ b l)
    (hQ0 : ∀ a b, 0 ≤ Q a b) (hQ1 : ∀ a, ∑ b, Q a b = 1)
    (hE : ∀ b i, |Q b i - P b i| ≤ κ * (Q b i + if b = i then 1 else 0))
    (hB : ∀ l, 1 ≤ l → l ≤ K → ∀ a i, |(P ^ l) a i| ≤ b l) (m : ℕ) (hm : m + 1 + 1 ≤ K)
    (ih : ∀ a i, |(Q ^ (m + 1) - P ^ (m + 1)) a i| ≤ 2 * ∑ l ∈ Finset.range (m + 1), b (l + 1)) :
    ∀ a i, |(Q ^ (m + 1 + 1) - P ^ (m + 1 + 1)) a i|
      ≤ 6 * κ * ∑ l ∈ Finset.range (m + 1 + 1), b (l + 1) := by
  intro a i
  have hR := R_bound Q P hκ0 hQ0 hQ1 hE hB (m + 1) hm a i
  have hEn := pow_mul_E Q P hQ0 hE (m + 1) a i
  have hih := ih a i
  have hv := hB (m + 1 + 1) (by omega) hm a i
  have hv0 := hB (m + 1) (by omega) (by omega) a i
  simp only [Matrix.sub_apply] at hR hih ⊢
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ l ∈ Finset.range (m + 1), b (l + 1) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.sum_nonneg fun l _ => hb0 _
  have hbA : b (m + 1) ≤ A := by
    rw [hA, Finset.sum_range_succ]
    have : 0 ≤ ∑ l ∈ Finset.range m, b (l + 1) := Finset.sum_nonneg fun l _ => hb0 _
    linarith
  rw [Finset.sum_range_succ, ← hA]
  rw [← hA] at hR hih
  have hu0 : (Q ^ (m + 1)) a i ≤ b (m + 1) + 2 * A := by
    have := (abs_le.mp hih).2
    have := (abs_le.mp hv0).2
    linarith
  have hu : (Q ^ (m + 1 + 1)) a i
      ≤ b (m + 1 + 1) + |(Q ^ (m + 1 + 1)) a i - (P ^ (m + 1 + 1)) a i| := by
    have := le_abs_self ((Q ^ (m + 1 + 1)) a i - (P ^ (m + 1 + 1)) a i)
    have := (abs_le.mp hv).2
    linarith
  have hsum : (Q ^ (m + 1 + 1)) a i + (Q ^ (m + 1)) a i
      ≤ b (m + 1 + 1) + |(Q ^ (m + 1 + 1)) a i - (P ^ (m + 1 + 1)) a i| + b (m + 1) + 2 * A := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hκ0
  have htri : |(Q ^ (m + 1 + 1)) a i - (P ^ (m + 1 + 1)) a i|
      ≤ |(Q ^ (m + 1 + 1)) a i - (P ^ (m + 1 + 1)) a i - (Q ^ (m + 1) * (Q - P)) a i|
        + |(Q ^ (m + 1) * (Q - P)) a i| := by
    have := abs_add_le ((Q ^ (m + 1 + 1)) a i - (P ^ (m + 1 + 1)) a i
      - (Q ^ (m + 1) * (Q - P)) a i) ((Q ^ (m + 1) * (Q - P)) a i)
    simpa using this
  refine arith_step hκ0 hκ hA0 (hb0 _) hbA (abs_nonneg _) ?_
  linarith

theorem pow_compare_two (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 6) (hκb : κ ≤ b 1) (hb0 : ∀ l, 0 ≤ b l)
    (hQ0 : ∀ a b, 0 ≤ Q a b) (hQ1 : ∀ a, ∑ b, Q a b = 1)
    (hE : ∀ b i, |Q b i - P b i| ≤ κ * (Q b i + if b = i then 1 else 0))
    (hB : ∀ l, 1 ≤ l → l ≤ K → ∀ a i, |(P ^ l) a i| ≤ b l) :
    ∀ m, m + 1 ≤ K → ∀ a i,
      |(Q ^ (m + 1) - P ^ (m + 1)) a i| ≤ 2 * ∑ l ∈ Finset.range (m + 1), b (l + 1) := by
  intro m
  induction m with
  | zero =>
    intro h1 a i
    have hp := hB 1 le_rfl h1 a i
    rw [pow_one] at hp
    simp only [zero_add, pow_one, Finset.range_one, Finset.sum_singleton, Matrix.sub_apply]
    refine base_arith (hQ0 a i) hκ0 hκ hκb ?_ hp (hE a i)
    split_ifs <;> norm_num
  | succ m ih =>
    intro hm a i
    have h := pow_compare_step Q P hκ0 hκ hb0 hQ0 hQ1 hE hB m hm (ih (by omega)) a i
    have hS : 0 ≤ ∑ l ∈ Finset.range (m + 1 + 1), b (l + 1) :=
      Finset.sum_nonneg fun l _ => hb0 _
    have := mul_le_mul_of_nonneg_right hκ hS
    linarith

/-- **Powers of two close matrices.** `Q` nonnegative with row sums one, and
    `|Q_{bi} - P_{bi}| ≤ κ (Q_{bi} + 1_{b=i})`, `κ ≤ 1/6`, `κ ≤ b_1`, `|(P^l)_{ai}| ≤ b_l` for
    `1 ≤ l ≤ K`. Then for `2 ≤ k ≤ K`: `|(Q^k - P^k)_{ai}| ≤ 6 κ ∑_{l=1}^k b_l`. -/
theorem pow_compare (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 6) (hκb : κ ≤ b 1) (hb0 : ∀ l, 0 ≤ b l)
    (hQ0 : ∀ a b, 0 ≤ Q a b) (hQ1 : ∀ a, ∑ b, Q a b = 1)
    (hE : ∀ b i, |Q b i - P b i| ≤ κ * (Q b i + if b = i then 1 else 0))
    (hB : ∀ l, 1 ≤ l → l ≤ K → ∀ a i, |(P ^ l) a i| ≤ b l) :
    ∀ k, 2 ≤ k → k ≤ K → ∀ a i,
      |(Q ^ k - P ^ k) a i| ≤ 6 * κ * ∑ l ∈ Finset.range k, b (l + 1) := by
  intro k hk hkK
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + 1 := ⟨k - 2, by omega⟩
  exact pow_compare_step Q P hκ0 hκ hb0 hQ0 hQ1 hE hB m hkK
    (pow_compare_two Q P hκ0 hκ hκb hb0 hQ0 hQ1 hE hB m (by omega))

end Compare

/-! ### Stage 1b: removing the diagonal of the kernel changes the walk by `O(M/N)` -/

theorem term_bounds {k ρ h : ℝ} (hk : 0 ≤ k) (h7 : 7 / 8 ≤ ρ) (hh0 : 0 ≤ h) (hh : h ≤ 1 / 24) :
    k / ρ ≤ k / (ρ - h) ∧ k / (ρ - h) ≤ (1 + 2 * h) * (k / ρ) := by
  have hρ : 0 < ρ := by linarith
  have hρh : 0 < ρ - h := by linarith
  refine ⟨div_le_div_of_nonneg_left hk hρh (by linarith), ?_⟩
  rw [div_le_iff₀ hρh]
  have hq : 0 ≤ k / ρ := div_nonneg hk hρ.le
  have hfac : ρ ≤ (1 + 2 * h) * (ρ - h) := by
    nlinarith [mul_nonneg hh0 (show (0 : ℝ) ≤ 2 * ρ - 1 - 2 * h by linarith)]
  calc k = k / ρ * ρ := (div_mul_cancel₀ k hρ.ne').symm
    _ ≤ k / ρ * ((1 + 2 * h) * (ρ - h)) := mul_le_mul_of_nonneg_left hfac hq
    _ = (1 + 2 * h) * (k / ρ) * (ρ - h) := by ring

theorem ratio_bound {p p' s s' h : ℝ} (hp : 0 ≤ p) (hs : 0 < s) (hs' : 0 < s') (hh0 : 0 ≤ h)
    (hh : h ≤ 1 / 24) (h1 : p ≤ p') (h2 : p' ≤ (1 + 2 * h) * p) (h3 : s' ≤ (1 + 2 * h) * s)
    (h4 : (1 - 5 / 3 * h) * s ≤ s') : |p' / s' - p / s| ≤ 4 * h * (p' / s') := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = p' / s' := ⟨_, rfl⟩
  have hQ : 0 ≤ q := by rw [hq]; exact div_nonneg (hp.trans h1) hs'.le
  have e : q * s' = p' := by rw [hq]; exact div_mul_cancel₀ _ hs'.ne'
  rw [← hq]
  have hup : p / s ≤ (1 + 2 * h) * q := by
    rw [div_le_iff₀ hs]
    have := mul_le_mul_of_nonneg_left h3 hQ
    nlinarith
  have hlow : (1 - 4 * h) * q ≤ p / s := by
    rw [le_div_iff₀ hs]
    have a1 := mul_le_mul_of_nonneg_left h4 hQ
    have hy : 0 ≤ q * s := mul_nonneg hQ hs.le
    have hc : (1 + 2 * h) * (1 - 4 * h) ≤ 1 - 5 / 3 * h := by nlinarith [mul_nonneg hh0 hh0]
    have a2 := mul_le_mul_of_nonneg_right hc hy
    have key : (1 + 2 * h) * ((1 - 4 * h) * q * s) ≤ (1 + 2 * h) * p := by nlinarith
    exact le_of_mul_le_mul_left key (by linarith)
  have hhq := mul_nonneg hh0 hQ
  rw [abs_le]
  constructor <;> nlinarith

/-- **The walk without self-loops against the walk with self-loops.** `K ≥ 0` with constant
    diagonal `M`, `∑_l K_{al} = N ρ_a`, `|ρ_a - 1| ≤ δ ≤ 1/8`, `h = M/N ≤ 1/24`. The walk `Q`
    built from the kernel with the diagonal removed and the normalisation `ρ_a - h` is
    nonnegative, row-stochastic, has zero diagonal, and
    `|Q_{bi} - P_{bi}| ≤ 4h (Q_{bi} + 1_{b=i})`. -/
theorem noloop_compare {n : Type} [Fintype n] [DecidableEq n] (K : n → n → ℝ) (ρ : n → ℝ)
    {Nr M δ h : ℝ} (hNr : 0 < Nr) (hK : ∀ a j, 0 ≤ K a j) (hd : ∀ a, K a a = M)
    (hsum : ∀ a, ∑ l, K a l = Nr * ρ a) (hδ : δ ≤ 1 / 8) (hρ : ∀ a, |ρ a - 1| ≤ δ)
    (hh : h = M / Nr) (hh24 : h ≤ 1 / 24) :
    (∀ a j, 0 ≤ walkMatrix (fun a j => if a = j then 0 else K a j) (fun a => ρ a - h) a j) ∧
    (∀ a, ∑ j, walkMatrix (fun a j => if a = j then 0 else K a j) (fun a => ρ a - h) a j = 1) ∧
    (∀ a, walkMatrix (fun a j => if a = j then 0 else K a j) (fun a => ρ a - h) a a = 0) ∧
    (∀ b i, |walkMatrix (fun a j => if a = j then 0 else K a j) (fun a => ρ a - h) b i
          - walkMatrix K ρ b i|
        ≤ 4 * h * (walkMatrix (fun a j => if a = j then 0 else K a j) (fun a => ρ a - h) b i
            + if b = i then 1 else 0)) := by
  have h7 : ∀ a, 7 / 8 ≤ ρ a := fun a => by have := (abs_le.mp (hρ a)).1; linarith
  have h9 : ∀ a, ρ a ≤ 9 / 8 := fun a => by have := (abs_le.mp (hρ a)).2; linarith
  have key : ∀ b, 0 ≤ h ∧ 0 < ∑ l, K b l / ρ l
      ∧ 0 < ∑ l, (if b = l then 0 else K b l) / (ρ l - h)
      ∧ ∑ l, (if b = l then 0 else K b l) / (ρ l - h) ≤ (1 + 2 * h) * ∑ l, K b l / ρ l
      ∧ (1 - 5 / 3 * h) * ∑ l, K b l / ρ l ≤ ∑ l, (if b = l then 0 else K b l) / (ρ l - h)
      ∧ M / ρ b ≤ 4 * h * ∑ l, K b l / ρ l := by
    intro b
    have hM0 : 0 ≤ M := by rw [← hd b]; exact hK b b
    have hh0 : 0 ≤ h := by rw [hh]; exact div_nonneg hM0 hNr.le
    have hMh : M = h * Nr := by rw [hh]; field_simp
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ∑ l, K b l / ρ l := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ l, K b l / (ρ l - h) := ⟨_, rfl⟩
    have hsT : s ≤ T := by
      rw [hs, hT]
      exact Finset.sum_le_sum fun l _ => (term_bounds (hK b l) (h7 l) hh0 hh24).1
    have hTs : T ≤ (1 + 2 * h) * s := by
      rw [hs, hT, Finset.mul_sum]
      exact Finset.sum_le_sum fun l _ => (term_bounds (hK b l) (h7 l) hh0 hh24).2
    have hslow : 7 / 9 * Nr ≤ s := by
      have h1 : ∑ l, K b l * (8 / 9) ≤ s := by
        rw [hs]
        refine Finset.sum_le_sum fun l _ => ?_
        rw [le_div_iff₀ (by linarith [h7 l])]
        nlinarith [mul_nonneg (hK b l) (show (0 : ℝ) ≤ 9 / 8 - ρ l by linarith [h9 l])]
      rw [← Finset.sum_mul, hsum b] at h1
      nlinarith [mul_nonneg hNr.le (show (0 : ℝ) ≤ ρ b - 7 / 8 by linarith [h7 b])]
    have hs0 : 0 < s := by linarith
    have hmm := term_bounds hM0 (h7 b) hh0 hh24
    have hMρ : M / ρ b ≤ 8 / 7 * M := by
      rw [div_le_iff₀ (by linarith [h7 b])]
      nlinarith [mul_nonneg hM0 (show (0 : ℝ) ≤ ρ b - 7 / 8 by linarith [h7 b])]
    have hMρ0 : 0 ≤ M / ρ b := div_nonneg hM0 (by linarith [h7 b])
    have hhs : h * (7 / 9 * Nr) ≤ h * s := mul_le_mul_of_nonneg_left hslow hh0
    have hmm2 : M / (ρ b - h) ≤ 13 / 12 * (8 / 7 * M) := by
      refine hmm.2.trans ?_
      exact mul_le_mul (by linarith) hMρ hMρ0 (by norm_num)
    have es : ∑ l, (if b = l then 0 else K b l) / (ρ l - h) = T - M / (ρ b - h) := by
      have e1 : ∀ l, (if b = l then 0 else K b l) / (ρ l - h)
          = K b l / (ρ l - h) - (if b = l then K b l / (ρ l - h) else 0) := by
        intro l; split_ifs <;> simp
      simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hd b, hT]
    rw [es, ← hs]
    have hmm0 : 0 ≤ M / (ρ b - h) := hMρ0.trans hmm.1
    have hhN : h * Nr ≤ 1 / 24 * Nr := mul_le_mul_of_nonneg_right hh24 hNr.le
    have hhN0 : 0 ≤ h * Nr := mul_nonneg hh0 hNr.le
    refine ⟨hh0, hs0, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · linarith
  have hρh : ∀ a, ρ a - h ≠ 0 := fun a => by
    have := (key a).1; have := h7 a; intro h0; linarith
  have hρ0 : ∀ a, ρ a ≠ 0 := fun a => by have := h7 a; intro h0; linarith
  have hQ : ∀ b i, walkMatrix (fun a j => if a = j then 0 else K a j) (fun a => ρ a - h) b i
      = ((if b = i then 0 else K b i) / (ρ i - h))
        / ∑ l, (if b = l then 0 else K b l) / (ρ l - h) := fun b i =>
    walkMatrix_apply' (fun a j => if a = j then 0 else K a j) (fun a => ρ a - h) b i (hρh b)
  have hP : ∀ b i, walkMatrix K ρ b i = (K b i / ρ i) / ∑ l, K b l / ρ l := fun b i =>
    walkMatrix_apply' K ρ b i (hρ0 b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a j
    obtain ⟨hh0, hs0, hs0', -, -, -⟩ := key a
    rw [hQ]
    refine div_nonneg (div_nonneg ?_ ?_) hs0'.le
    · split_ifs
      · exact le_rfl
      · exact hK a j
    · have := h7 j; linarith
  · intro a
    obtain ⟨hh0, hs0, hs0', -, -, -⟩ := key a
    simp only [hQ]
    rw [← Finset.sum_div]
    exact div_self hs0'.ne'
  · intro a
    rw [hQ]; simp
  · intro b i
    obtain ⟨hh0, hs0, hs0', hup, hlow, hdiag⟩ := key b
    rw [hQ, hP]
    by_cases hbi : b = i
    · subst hbi
      have hM0 : 0 ≤ M := by rw [← hd b]; exact hK b b
      simp only [eq_self_iff_true, if_true, zero_div, zero_sub, abs_neg, zero_add, mul_one, hd b]
      rw [abs_of_nonneg (div_nonneg (div_nonneg hM0 (by linarith [h7 b])) hs0.le),
        div_le_iff₀ hs0]
      exact hdiag
    · simp only [if_neg hbi, add_zero]
      have ht := term_bounds (hK b i) (h7 i) hh0 hh24
      exact ratio_bound (div_nonneg (hK b i) (by linarith [h7 i])) hs0 hs0' hh0 hh24 ht.1 ht.2
        hup hlow


/-! ### Stage 2: the sample statements -/

/-- The constant of the normalisation (copy of `normC` of the third file). -/
noncomputable def normC (d : ℕ) : ℝ :=
  6 * Real.sqrt (3 * (d : ℝ) + 5) * (1 + Real.sqrt (2 * Real.pi)) ^ d

set_option maxHeartbeats 6400000 in
/-- The normalisation event under the hypotheses of `kernel_theorem_G28` (the first two parts
    are a copy of the proof of `good_events` of the third file, without its `ℓ¹` part), and
    `1152 · p_σ(0) ≤ N`. -/
theorem norm_event {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    normC d * δp ≤ 1 / 8 ∧
    μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ normC d * δp}
      ≤ 1 / (N : ℝ) ^ 3 ∧
    1152 * Mp ≤ N := by
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
  have hM1152 : 1152 * Mp ≤ N := by
    have hMLlg0 : 0 ≤ ML * lg := by linarith
    have h30 : 2304 * (ML * lg) ≤ C ^ 2 * (ML * lg) := mul_le_mul_of_nonneg_right hC2 hMLlg0
    have h31 : ML * (1 / 2) ≤ ML * lg := mul_le_mul_of_nonneg_left hlg (by linarith)
    linarith
  exact ⟨hn8, hPN, hM1152⟩

/-- `m_l = p_{lσ}(0)` for `l ≥ 1` (and `0` for `l = 0`, the convention of `heatP`). -/
noncomputable def mS (d : ℕ) (σ : ℝ) (l : ℕ) : ℝ := heatP d σ l 0

theorem mS_one (d : ℕ) (σ : ℝ) : mS d σ 1 = heatTorus d (2 * Real.pi ^ 2 * σ) 0 :=
  heatP_one d σ 0

/-- For `l ≥ 1`, `mS d σ l = p_{lσ}(0)` (the kernel of variance `lσ` at `0`). -/
theorem mS_of_pos (d : ℕ) (σ : ℝ) {l : ℕ} (hl : 1 ≤ l) :
    mS d σ l = heatTorus d (2 * Real.pi ^ 2 * ((l : ℝ) * σ)) 0 :=
  heatP_of_ne d σ (by omega) 0

/-- The walk of the graph WITHOUT self-loops: kernel `p_σ(x_a - x_j)` for `a ≠ j` and `0` on the
    diagonal, normalisation `ρ°_a = (1/N) ∑_{l ≠ a} p_σ(x_a - x_l) = ρ_a - p_σ(0)/N`. -/
noncomputable def noloopWalk (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) :
    Matrix (Fin N) (Fin N) ℝ :=
  walkMatrix (fun a j : Fin N => if a = j then 0 else heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
    (fun a : Fin N => heatRho d σ N x a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N)

/-- The walk with self-loops (the matrix of `kernel_theorem_G28`). -/
noncomputable def loopWalk (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) :
    Matrix (Fin N) (Fin N) ℝ :=
  walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
    (fun a : Fin N => heatRho d σ N x a)

/-- **One step, deterministic.** On the normalisation event and for `24 p_σ(0) ≤ N`: the walk
    without self-loops is nonnegative and row-stochastic, its diagonal vanishes, and
    `|P°_{bi} - P_{bi}| ≤ 4 (M/N) (P°_{bi} + 1_{b=i})`. -/
theorem noloop_one_step {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 1 ≤ N) (x : ℕ → FlatTorus d)
    {δ : ℝ} (hδ : δ ≤ 1 / 8) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ)
    (hMN : 24 * heatTorus d (2 * Real.pi ^ 2 * σ) 0 ≤ N) :
    (∀ a j, 0 ≤ noloopWalk d σ N x a j) ∧
    (∀ a, ∑ j, noloopWalk d σ N x a j = 1) ∧
    (∀ a, noloopWalk d σ N x a a = 0) ∧
    (∀ b i, |noloopWalk d σ N x b i - loopWalk d σ N x b i|
        ≤ 4 * (heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N)
          * (noloopWalk d σ N x b i + if b = i then 1 else 0)) := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsum : ∀ a : Fin N, ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)
      = (N : ℝ) * heatRho d σ N x a := by
    intro a
    unfold heatRho
    rw [Finset.sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l))]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hNpos.ne']
  have h24 : heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N ≤ 1 / 24 := by
    rw [div_le_iff₀ hNpos]; linarith
  exact noloop_compare (M := heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (h := heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N)
    (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
    (fun a : Fin N => heatRho d σ N x a) hNpos (fun a j => heatTorus_nonneg hcσ d _)
    (fun a => by simp) hsum hδ hρ rfl h24

/-- **Stage 1 for the sample graph, deterministic.** Let the kernel estimate hold for the walk
    WITH self-loops, `|N P^k(a,i) - p_k(x_a - x_i)| ≤ e_k m_k` with `0 ≤ e_k ≤ 1` for `1 ≤ k ≤ K`,
    let `|ρ_a - 1| ≤ δ ≤ 1/8` and `24 p_σ(0) ≤ N`. Then for the walk WITHOUT self-loops and all
    `2 ≤ k ≤ K`:
    `|N P°^k(a,i) - N P^k(a,i)| ≤ 96 (M/N) ∑_{l=1}^k m_l` and
    `|N P°^k(a,i) - p_k(x_a - x_i)| ≤ e_k m_k + 96 (M/N) ∑_{l=1}^k m_l`. -/
theorem noloop_kernel_det {σ : ℝ} (hσ : 0 < σ) (d N K : ℕ) (hN : 1 ≤ N) (x : ℕ → FlatTorus d)
    {δ : ℝ} (hδ : δ ≤ 1 / 8) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ)
    (hMN : 24 * heatTorus d (2 * Real.pi ^ 2 * σ) 0 ≤ N) {e : ℕ → ℝ}
    (he : ∀ k, 1 ≤ k → k ≤ K → 0 ≤ e k ∧ e k ≤ 1)
    (hG : ∀ k, 1 ≤ k → k ≤ K → ∀ a i : Fin N,
      |(N : ℝ) * ((loopWalk d σ N x) ^ k) a i - heatP d σ k (x a - x i)| ≤ e k * mS d σ k) :
    ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
      |(N : ℝ) * ((noloopWalk d σ N x) ^ k) a i - (N : ℝ) * ((loopWalk d σ N x) ^ k) a i|
          ≤ 96 * (heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N) * ∑ l ∈ Finset.range k, mS d σ (l + 1)
      ∧ |(N : ℝ) * ((noloopWalk d σ N x) ^ k) a i - heatP d σ k (x a - x i)|
          ≤ e k * mS d σ k
            + 96 * (heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N)
              * ∑ l ∈ Finset.range k, mS d σ (l + 1) := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨hQ0, hQ1, -, hE⟩ := noloop_one_step hσ d N hN x hδ hρ hMN
  obtain ⟨Mp, hMp⟩ : ∃ Mp : ℝ, Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0 := ⟨_, rfl⟩
  rw [← hMp] at hE hMN ⊢
  have hMp0 : 0 ≤ Mp := by rw [hMp]; exact heatTorus_nonneg hcσ d 0
  have hm0 : ∀ l, 0 ≤ mS d σ l := fun l => heatP_nonneg hσ d l 0
  have hκ0 : 0 ≤ 4 * (Mp / N) := mul_nonneg (by norm_num) (div_nonneg hMp0 hNpos.le)
  have hκ : 4 * (Mp / N) ≤ 1 / 6 := by
    have : Mp / N ≤ 1 / 24 := by rw [div_le_iff₀ hNpos]; linarith
    linarith
  have hκb : 4 * (Mp / N) ≤ (fun l => 4 * mS d σ l / N) 1 := by
    show 4 * (Mp / N) ≤ 4 * mS d σ 1 / N
    rw [mS_one, ← hMp]
    exact le_of_eq (by ring)
  have hb0 : ∀ l, 0 ≤ (fun l => 4 * mS d σ l / N) l := fun l => by
    show 0 ≤ 4 * mS d σ l / N
    exact div_nonneg (mul_nonneg (by norm_num) (hm0 l)) hNpos.le
  have hB : ∀ l, 1 ≤ l → l ≤ K → ∀ a i : Fin N,
      |((loopWalk d σ N x) ^ l) a i| ≤ (fun l => 4 * mS d σ l / N) l := by
    intro l hl hlK a i
    show |((loopWalk d σ N x) ^ l) a i| ≤ 4 * mS d σ l / N
    have h1 := hG l hl hlK a i
    have h2 := (he l hl hlK).2
    have hml := hm0 l
    have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    have hp0 : 0 ≤ heatP d σ l (x a - x i) := heatP_nonneg hσ d l _
    have hp1 : heatP d σ l (x a - x i) ≤ mS d σ l := by
      have hc : 0 < 2 * Real.pi ^ 2 * ((l : ℝ) * σ) := mul_pos (by positivity) (mul_pos hl' hσ)
      have hl0 : l ≠ 0 := by omega
      show heatP d σ l (x a - x i) ≤ heatP d σ l 0
      rw [heatP_of_ne d σ hl0, heatP_of_ne d σ hl0]
      exact TorusReduction.heatTorus_le_zero hc d _
    have h3 : e l * mS d σ l ≤ 1 * mS d σ l := mul_le_mul_of_nonneg_right h2 hml
    have h4 := abs_le.mp h1
    have h5 : |(N : ℝ) * ((loopWalk d σ N x) ^ l) a i| ≤ 4 * mS d σ l := by
      rw [abs_le]; constructor <;> linarith [h4.1, h4.2]
    rw [abs_mul, abs_of_pos hNpos] at h5
    rw [le_div_iff₀ hNpos]
    linarith
  have hcmp := pow_compare (κ := 4 * (Mp / N)) (b := fun l => 4 * mS d σ l / N) (K := K)
    (noloopWalk d σ N x) (loopWalk d σ N x) hκ0 hκ hκb hb0 hQ0 hQ1 hE hB
  intro k hk hkK a i
  have h1 := hcmp k hk hkK a i
  have es : ∑ l ∈ Finset.range k, (fun l => 4 * mS d σ l / N) (l + 1)
      = 4 * (∑ l ∈ Finset.range k, mS d σ (l + 1)) / N := by
    show ∑ l ∈ Finset.range k, 4 * mS d σ (l + 1) / N = _
    rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [es, Matrix.sub_apply] at h1
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ l ∈ Finset.range k, mS d σ (l + 1) := ⟨_, rfl⟩
  rw [← hS] at h1 ⊢
  have hfirst : |(N : ℝ) * ((noloopWalk d σ N x) ^ k) a i - (N : ℝ) * ((loopWalk d σ N x) ^ k) a i|
      ≤ 96 * (Mp / N) * S := by
    rw [← mul_sub, abs_mul, abs_of_pos hNpos]
    have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
    refine h2.trans (le_of_eq ?_)
    have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
    first | (field_simp; done) | (field_simp; ring)
  refine ⟨hfirst, ?_⟩
  have h3 := hG k (by omega) hkK a i
  have h4 := abs_sub_le ((N : ℝ) * ((noloopWalk d σ N x) ^ k) a i)
    ((N : ℝ) * ((loopWalk d σ N x) ^ k) a i) (heatP d σ k (x a - x i))
  linarith

/-- **Stage 2: the kernel of the walk without self-loops, for samples.** Hypotheses of
    `kernel_theorem_G28`. Except on an event of probability at most `4/N³`, for all
    `2 ≤ k ≤ K` and all `a, i`:
    `|N P°^k(a,i) - p_k(x_a - x_i)| ≤ kernelC1 d · δ' √k m_k + 96 (M/N) ∑_{l=1}^k m_l`. -/
theorem noloop_kernel_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((noloopWalk d σ N (fun j => X j ω)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ kernelC1 d * δp * Real.sqrt k * mS d σ k
            + 96 * (Mp / N) * ∑ l ∈ Finset.range k, mS d σ (l + 1)}
      ≤ 4 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA := kernel_theorem_G28 hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  obtain ⟨hn8, hB, hM⟩ := norm_event hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have hC0 : 0 ≤ kernelC1 d := by
    unfold kernelC1; exact mul_nonneg (rateCfin3_nonneg d) (by positivity)
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hMp0 : 0 ≤ Mp := by
    rw [hMp]; exact heatTorus_nonneg (by have := Real.pi_pos; positivity) d 0
  have hsub : {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((noloopWalk d σ N (fun j => X j ω)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ kernelC1 d * δp * Real.sqrt k * mS d σ k
            + 96 * (Mp / N) * ∑ l ∈ Finset.range k, mS d σ (l + 1)}
      ⊆ {ω | ¬ ∀ k, 1 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ kernelC1 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
        ∪ {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ normC d * δp} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨hgood, hnorm⟩ := hcon
    apply hω
    intro k hk hkK a i
    have he : ∀ k : ℕ, 1 ≤ k → k ≤ K →
        0 ≤ (fun k : ℕ => kernelC1 d * δp * Real.sqrt k) k
          ∧ (fun k : ℕ => kernelC1 d * δp * Real.sqrt k) k ≤ 1 := by
      intro k _ hkK
      refine ⟨mul_nonneg (mul_nonneg hC0 hδp0) (Real.sqrt_nonneg _), ?_⟩
      have hs : Real.sqrt (k : ℝ) ≤ Real.sqrt (K : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hkK)
      exact (mul_le_mul_of_nonneg_left hs (mul_nonneg hC0 hδp0)).trans hrange
    have hdet := noloop_kernel_det hσ d N K (by omega) (fun j => X j ω) hn8 hnorm
      (by rw [← hMp]; linarith) (e := fun k : ℕ => kernelC1 d * δp * Real.sqrt k) he
      (fun k hk1 hkK a i => by
        have hthis := hgood k hk1 hkK a i
        rw [mS_of_pos d σ hk1]
        exact hthis) k hk hkK a i
    rw [← hMp] at hdet
    exact hdet.2
  have h0 := measureReal_mono hsub (measure_ne_top μ _)
  have h1 := measureReal_union_le (μ := μ)
    {ω | ¬ ∀ k, 1 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ kernelC1 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
    {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ normC d * δp}
  have e4 : (4 : ℝ) / (N : ℝ) ^ 3 = 3 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3 := by ring
  rw [e4]
  linarith

/-- **The trace of the walk without self-loops, for samples.** Same hypotheses and the same
    event; for `2 ≤ k ≤ K` (the case `k = 1`, `Tr P° = 0`, is in `noloop_first_step`, not here):
    `|Tr P°^k - m_k| ≤ kernelC1 d · δ' √k m_k + 96 (M/N) ∑_{l=1}^k m_l`. -/
theorem noloop_trace_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K →
        |((noloopWalk d σ N (fun j => X j ω)) ^ k).trace - mS d σ k|
          ≤ kernelC1 d * δp * Real.sqrt k * mS d σ k
            + 96 * (Mp / N) * ∑ l ∈ Finset.range k, mS d σ (l + 1)}
      ≤ 4 / (N : ℝ) ^ 3 := by
  have h := noloop_kernel_sample hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk hkK
  refine trace_from_diagonal (by omega) _ ?_
  intro a
  have h1 := hgood k hk hkK a a
  rw [sub_self] at h1
  exact h1

/-- **The first step on the diagonal, and `Tr P° = 0`.** The diagonal of the walk without
    self-loops vanishes, so `|N P°(a,a) - p_σ(0)| = p_σ(0) = m_1` and `Tr P° = 0`. This gives only
    `D_1 ≥ m_1`; the bound `4δM` for the off-diagonal entries (which makes `D_1 = m_1` in the
    paper) is NOT part of this statement. -/
theorem noloop_first_step {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 1 ≤ N) (x : ℕ → FlatTorus d)
    {δ : ℝ} (hδ : δ ≤ 1 / 8) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ)
    (hMN : 24 * heatTorus d (2 * Real.pi ^ 2 * σ) 0 ≤ N) :
    (∀ a : Fin N, |(N : ℝ) * ((noloopWalk d σ N x) ^ 1) a a - heatP d σ 1 (x a - x a)|
        = heatTorus d (2 * Real.pi ^ 2 * σ) 0) ∧
    (noloopWalk d σ N x).trace = 0 := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  obtain ⟨-, -, hdiag, -⟩ := noloop_one_step hσ d N hN x hδ hρ hMN
  refine ⟨fun a => ?_, ?_⟩
  · rw [pow_one, hdiag a, sub_self, heatP_one, mul_zero, zero_sub, abs_neg,
      abs_of_nonneg (heatTorus_nonneg hcσ d 0)]
  · rw [Matrix.trace]
    exact Finset.sum_eq_zero fun a _ => by rw [Matrix.diag_apply]; exact hdiag a



/-! ### Stage 3: when the additional term is absorbed -/

theorem absorb {Mp Nr lg δp C k mk : ℝ} (hNr : 0 < Nr) (hlg : 0 < lg) (hMp0 : 0 ≤ Mp)
    (hδ2 : δp ^ 2 = Mp * lg / Nr) (hδ0 : 0 ≤ δp) (hk : 0 ≤ k)
    (hr : C * δp * Real.sqrt k ≤ 1) (hM : Mp ≤ C * lg) (hmk : 1 ≤ mk) :
    Mp / Nr * (k * Mp) ≤ δp * Real.sqrt k * mk := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt k := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hss : s * s = k := by rw [hs]; exact Real.mul_self_sqrt hk
  rw [← hs] at hr ⊢
  have e1 : Mp / Nr = δp ^ 2 / lg := by
    rw [hδ2]; field_simp
  have h1 : Mp / lg ≤ C := by rw [div_le_iff₀ hlg]; exact hM
  have hds : 0 ≤ δp * s := mul_nonneg hδ0 hs0
  have h2 : (δp * s) * (δp * s) * (Mp / lg) ≤ (δp * s) * (δp * s) * C :=
    mul_le_mul_of_nonneg_left h1 (mul_nonneg hds hds)
  have h3 : (δp * s) * (C * δp * s) ≤ (δp * s) * 1 := mul_le_mul_of_nonneg_left hr hds
  have h4 : (δp * s) * 1 ≤ (δp * s) * mk := mul_le_mul_of_nonneg_left hmk hds
  have e2 : Mp / Nr * (k * Mp) = (δp * s) * (δp * s) * (Mp / lg) := by
    rw [e1, ← hss]
    first | (field_simp; done) | (field_simp; ring)
  rw [e2]
  nlinarith

/-- **The kernel of the walk without self-loops in the form of the corollary, under an
    additional condition.** Hypotheses of `kernel_theorem_G28` and `p_σ(0) ≤ kernelC1 d · log N`.
    Except on an event of probability at most `4/N³`, for all `2 ≤ k ≤ K` and all `a, i`:
    `|N P°^k(a,i) - p_k(x_a - x_i)| ≤ (kernelC1 d + 96) δ' √k m_k`. -/
theorem noloop_kernel_sample_small {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1)
    (hsmall : Mp ≤ kernelC1 d * Real.log N) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((noloopWalk d σ N (fun j => X j ω)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ (kernelC1 d + 96) * δp * Real.sqrt k * mS d σ k}
      ≤ 4 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlg : 0 < Real.log N := Real.log_pos (by linarith)
  have hMp0 : 0 ≤ Mp := by rw [hMp]; exact heatTorus_nonneg hcσ d 0
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hδ2 : δp ^ 2 = Mp * Real.log N / N := by
    rw [hδp, Real.sq_sqrt (div_nonneg (mul_nonneg hMp0 hlg.le) hNpos.le)]
  have hC0 : 0 ≤ kernelC1 d := by
    unfold kernelC1; exact mul_nonneg (rateCfin3_nonneg d) (by positivity)
  have h := noloop_kernel_sample hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk hkK a i
  refine (hgood k hk hkK a i).trans ?_
  have hk1 : 1 ≤ k := by omega
  have hkr : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hmk : 1 ≤ mS d σ k := by
    rw [mS_of_pos d σ hk1]
    exact heatTorus_zero_ge_one
      (mul_pos (by positivity) (mul_pos (by exact_mod_cast hk1) hσ)) d
  have hsum : ∑ l ∈ Finset.range k, mS d σ (l + 1) ≤ (k : ℝ) * Mp := by
    have hterm : ∀ l ∈ Finset.range k, mS d σ (l + 1) ≤ Mp := by
      intro l _
      rw [mS_of_pos d σ (show 1 ≤ l + 1 by omega), hMp]
      refine TraceG29.heatTorus_zero_anti hcσ ?_ d
      have h1 : (1 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ l + 1)
      have h2 : σ ≤ ((l + 1 : ℕ) : ℝ) * σ := le_mul_of_one_le_left hσ.le h1
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    calc ∑ l ∈ Finset.range k, mS d σ (l + 1) ≤ ∑ _l ∈ Finset.range k, Mp :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Mp := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hrk : kernelC1 d * δp * Real.sqrt k ≤ 1 := by
    have hs : Real.sqrt (k : ℝ) ≤ Real.sqrt (K : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hkK)
    exact (mul_le_mul_of_nonneg_left hs (mul_nonneg hC0 hδp0)).trans hrange
  have hab := absorb hNpos hlg hMp0 hδ2 hδp0 hkr hrk hsmall hmk
  have h1 : Mp / N * ∑ l ∈ Finset.range k, mS d σ (l + 1) ≤ Mp / N * ((k : ℝ) * Mp) :=
    mul_le_mul_of_nonneg_left hsum (div_nonneg hMp0 hNpos.le)
  linarith


end NoLoops

/-! ## Towards `lem:pibound`: `Π_k` as a sum of degenerate statistics, the degeneracy facts, and the
bounds for the last, the first and the middle summands, and `pi_bound`: `E|Π_k| ≤ piC d (M/N) k m_k` for `M ≤ N`
(the estimate of `lem:pibound` with an explicit constant; the proof is NOT that of `lem:degenerate`). -/

namespace PiBound

open CTG.Reals.TorusReduction H5


/-! ## Stage 1: the statistics `Z⁰`, `Z¹` and the representation of `Π_k` -/

/-- `Z⁰[F]` for `n = 2`, at the level of indices: `N⁻² ∑_{i,j} F(i,j)`. -/
noncomputable def Zs0two (N : ℕ) (F : Fin N → Fin N → ℝ) : ℝ :=
  1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, F i j

/-- `Z⁰[F]` for `n = 3`: `N⁻³ ∑_{i,b,j} F(i,b,j)`. -/
noncomputable def Zs0three (N : ℕ) (F : Fin N → Fin N → Fin N → ℝ) : ℝ :=
  1 / (N : ℝ) ^ 3 * ∑ i, ∑ b, ∑ j, F i b j

/-- `Z¹[F, a = 1]` for `n = 2`: `N⁻³ ∑_{i,j,v} F(i,j) c_{iv}`. -/
noncomputable def Zs1two1 (N : ℕ) (F c : Fin N → Fin N → ℝ) : ℝ :=
  1 / (N : ℝ) ^ 3 * ∑ i, ∑ j, ∑ v, F i j * c i v

/-- `Z¹[F, a = 2]` for `n = 2`: `N⁻³ ∑_{i,j,v} F(i,j) c_{jv}`. -/
noncomputable def Zs1two2 (N : ℕ) (F c : Fin N → Fin N → ℝ) : ℝ :=
  1 / (N : ℝ) ^ 3 * ∑ i, ∑ j, ∑ v, F i j * c j v

/-- `Z¹[F, a = 3]` for `n = 3`: `N⁻⁴ ∑_{i,b,j,v} F(i,b,j) c_{jv}`. -/
noncomputable def Zs1three3 (N : ℕ) (F : Fin N → Fin N → Fin N → ℝ) (c : Fin N → Fin N → ℝ) : ℝ :=
  1 / (N : ℝ) ^ 4 * ∑ i, ∑ b, ∑ j, ∑ v, F i b j * c j v

/-- Algebra of the last term of `Π_k`. -/
theorem absC (N : ℕ) (hN : (N : ℝ) ≠ 0) (K c : Fin N → Fin N → ℝ) (ε : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (hε : ∀ j, ∑ v, c j v = N * ε j) :
    1 / (N : ℝ) * ∑ i, ∑ j, K i j / N * (1 - ε j) * D i j
      = Zs0two N (fun i j => K i j * D i j) - Zs1two2 N (fun i j => K i j * D i j) c := by
  have h1 : ∀ i j, ∑ v, K i j * D i j * c j v = K i j * D i j * (N * ε j) := fun i j => by
    rw [← Finset.mul_sum, hε]
  simp only [Zs0two, Zs1two2, h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- Algebra of the middle terms of `Π_k`. -/
theorem absB (N : ℕ) (hN : (N : ℝ) ≠ 0) (L K c : Fin N → Fin N → ℝ) (ε : Fin N → ℝ)
    (D : Fin N → Fin N → Fin N → ℝ) (hε : ∀ j, ∑ v, c j v = N * ε j) :
    1 / (N : ℝ) ^ 2 * ∑ i, ∑ b, L i b * ∑ j, K b j / N * (1 - ε j) * D i b j
      = Zs0three N (fun i b j => L i b * K b j * D i b j)
        - Zs1three3 N (fun i b j => L i b * K b j * D i b j) c := by
  have h1 : ∀ i b j, ∑ v, L i b * K b j * D i b j * c j v
      = L i b * K b j * D i b j * (N * ε j) := fun i b j => by
    rw [← Finset.mul_sum, hε]
  simp only [Zs0three, Zs1three3, h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- Algebra of the first term of `Π_k`. -/
theorem absA (N : ℕ) (hN : (N : ℝ) ≠ 0) (A K c : Fin N → Fin N → ℝ) (ε : Fin N → ℝ)
    (hε : ∀ j, ∑ v, c j v = N * ε j) :
    1 / (N : ℝ) ^ 2 * ∑ i, ∑ b, A i b * (-ε i - ε b + (∑ j, K b j * ε j) / N)
      = -Zs1two1 N A c - Zs1two2 N A c + Zs1three3 N (fun i b j => A i b * K b j) c := by
  obtain ⟨s, hs⟩ : ∃ s : Fin N → ℝ, ∀ b, ∑ j, K b j * ε j = s b := ⟨_, fun _ => rfl⟩
  have h1 : ∀ i b, ∑ v, A i b * c i v = A i b * (N * ε i) := fun i b => by
    rw [← Finset.mul_sum, hε]
  have h2 : ∀ i b, ∑ v, A i b * c b v = A i b * (N * ε b) := fun i b => by
    rw [← Finset.mul_sum, hε]
  have h3 : ∀ i b j, ∑ v, A i b * K b j * c j v = A i b * K b j * (N * ε j) := fun i b j => by
    rw [← Finset.mul_sum, hε]
  have h4 : ∀ i b, ∑ j, A i b * K b j * (N * ε j) = A i b * (N * s b) := fun i b => by
    rw [← hs b, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Zs1two1, Zs1two2, Zs1three3, h1, h2, h3, h4, hs]
  have e1 : ∑ i, ∑ b, A i b * (N * ε i) = N * ∑ i, ∑ b, A i b * ε i := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∑ i, ∑ b, A i b * (N * ε b) = N * ∑ i, ∑ b, A i b * ε b := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  have e3 : ∑ i, ∑ b, A i b * (N * s b) = N * ∑ i, ∑ b, A i b * s b := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  have e0 : ∑ i, ∑ b, A i b * (-ε i - ε b + s b / N)
      = -(∑ i, ∑ b, A i b * ε i) - (∑ i, ∑ b, A i b * ε b) + (∑ i, ∑ b, A i b * s b) / N := by
    simp only [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e0, e1, e2, e3]
  field_simp

/-- The one-step kernel `p = p_σ` of the walk. -/
noncomputable def pker (d : ℕ) (σ : ℝ) (u : FlatTorus d) : ℝ :=
  heatTorus d (2 * Real.pi ^ 2 * σ) u

/-- `c_{jv} = p(x_j - x_v) - 1` (`lem:degenerate`). -/
noncomputable def cmat (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (j v : Fin N) : ℝ :=
  pker d σ (x j - x v) - 1

/-- `F_A(y₁,y₂) = p_k(u) p(u)`, `u = y₁ - y₂` (proof of `lem:pibound`). -/
noncomputable def FA (d : ℕ) (σ : ℝ) (k : ℕ) (y1 y2 : FlatTorus d) : ℝ :=
  heatP d σ k (y1 - y2) * pker d σ (y1 - y2)

/-- `F_A'(y₁,y₂,y₃) = p_k(u) p(u) p(y₂ - y₃)`. -/
noncomputable def FA' (d : ℕ) (σ : ℝ) (k : ℕ) (y1 y2 y3 : FlatTorus d) : ℝ :=
  heatP d σ k (y1 - y2) * pker d σ (y1 - y2) * pker d σ (y2 - y3)

/-- `ψ_k(u) = p(u) (p_k(u) - m_{k+1})`. -/
noncomputable def psiK (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : ℝ :=
  pker d σ u * (heatP d σ k u - torusM d σ (k + 1))

/-- `Ψ(y₁,y₂) = p(u) (p_k(u) - m_{k+1})`, `u = y₁ - y₂`. -/
noncomputable def Psi (d : ℕ) (σ : ℝ) (k : ℕ) (y1 y2 : FlatTorus d) : ℝ :=
  psiK d σ k (y1 - y2)

/-- `K_m(y₁,y₂,y₃) = p_l(u) p(y₂ - y₃) (p_m(y₃ - y₁) - p_{m+1}(u))`, `l = k - m`. -/
noncomputable def Km (d : ℕ) (σ : ℝ) (l m : ℕ) (y1 y2 y3 : FlatTorus d) : ℝ :=
  heatP d σ l (y1 - y2) * pker d σ (y2 - y3)
    * (heatP d σ m (y3 - y1) - heatP d σ (m + 1) (y1 - y2))

theorem heatP_even (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) :
    heatP d σ k (-u) = heatP d σ k u := by
  unfold heatP
  split_ifs
  · rfl
  · exact heatTorus_even d _ u

/-- `ε_j = (1/N) ∑_v c_{jv}` in multiplied form. -/
theorem eps_eq (d : ℕ) (σ : ℝ) (N : ℕ) (hN : (N : ℝ) ≠ 0) (x : ℕ → FlatTorus d) (j : Fin N) :
    ∑ v : Fin N, (torusK d σ N x j v - 1) = N * (torusRho d σ N x j - 1) := by
  have h1 : ∑ v : Fin N, torusK d σ N x j v
      = ∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l) :=
    Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l)) N
  have h2 : torusRho d σ N x j
      = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l)) / N := rfl
  rw [Finset.sum_sub_distrib, h1, h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

/-- The first term of `Π_k` is `-Z¹[F_A,1] - Z¹[F_A,2] + Z¹[F_A',3]`. -/
theorem first_term (d : ℕ) (σ : ℝ) (N : ℕ) (hN : (N : ℝ) ≠ 0) (x : ℕ → FlatTorus d) (k : ℕ) :
    1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N x k i b * torusQ d σ N x 1 b i * torusTheta1 d σ N x b i
      = -Zs1two1 N (fun i b => FA d σ k (x i) (x b)) (cmat d σ N x)
        - Zs1two2 N (fun i b => FA d σ k (x i) (x b)) (cmat d σ N x)
        + Zs1three3 N (fun i b j => FA' d σ k (x i) (x b) (x j)) (cmat d σ N x) := by
  have hF : (fun i b : Fin N => torusQ d σ N x k i b * torusQ d σ N x 1 b i)
      = fun i b : Fin N => FA d σ k (x i) (x b) := by
    funext i b
    show heatP d σ k (x i - x b) * heatP d σ 1 (x b - x i)
      = heatP d σ k (x i - x b) * heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x b)
    rw [heatP_one, ← neg_sub (x i) (x b), heatTorus_even]
  have hF' : (fun i b j : Fin N =>
        torusQ d σ N x k i b * torusQ d σ N x 1 b i * torusK d σ N x b j)
      = fun i b j : Fin N => FA' d σ k (x i) (x b) (x j) := by
    funext i b j
    show heatP d σ k (x i - x b) * heatP d σ 1 (x b - x i)
        * heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j)
      = heatP d σ k (x i - x b) * heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x b)
        * heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j)
    rw [heatP_one, ← neg_sub (x i) (x b), heatTorus_even]
  have h := absA N hN (fun i b => torusQ d σ N x k i b * torusQ d σ N x 1 b i)
    (torusK d σ N x) (fun j v => torusK d σ N x j v - 1) (fun j => torusRho d σ N x j - 1)
    (eps_eq d σ N hN x)
  rw [← hF, ← hF']
  simp only [torusTheta1_eq]
  exact h

/-- A middle term of `Π_k` is `Z⁰[K_m] - Z¹[K_m,3]`. -/
theorem mid_term (d : ℕ) (σ : ℝ) (N : ℕ) (hN : (N : ℝ) ≠ 0) (x : ℕ → FlatTorus d) (l m : ℕ) :
    1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N x l i b * torusHhat d σ N x m i b
      = Zs0three N (fun i b j => Km d σ l m (x i) (x b) (x j))
        - Zs1three3 N (fun i b j => Km d σ l m (x i) (x b) (x j)) (cmat d σ N x) := by
  have hF : (fun i b j : Fin N => torusQ d σ N x l i b * torusK d σ N x b j
        * (torusQ d σ N x m j i - torusQ d σ N x (m + 1) b i))
      = fun i b j : Fin N => Km d σ l m (x i) (x b) (x j) := by
    funext i b j
    show heatP d σ l (x i - x b) * heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j)
        * (heatP d σ m (x j - x i) - heatP d σ (m + 1) (x b - x i))
      = heatP d σ l (x i - x b) * heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j)
        * (heatP d σ m (x j - x i) - heatP d σ (m + 1) (x i - x b))
    rw [← neg_sub (x i) (x b), heatP_even]
  have h := absB N hN (torusQ d σ N x l) (torusK d σ N x) (fun j v => torusK d σ N x j v - 1)
    (fun j => torusRho d σ N x j - 1)
    (fun i b j => torusQ d σ N x m j i - torusQ d σ N x (m + 1) b i) (eps_eq d σ N hN x)
  rw [← hF]
  exact h

/-- The last term of `Π_k` is `Z⁰[Ψ] - Z¹[Ψ,2]`. -/
theorem last_term (d : ℕ) (σ : ℝ) (N : ℕ) (hN : (N : ℝ) ≠ 0) (x : ℕ → FlatTorus d) (k : ℕ) :
    1 / (N : ℝ) * ∑ i : Fin N, torusHhat d σ N x k i i
      = Zs0two N (fun i j => Psi d σ k (x i) (x j))
        - Zs1two2 N (fun i j => Psi d σ k (x i) (x j)) (cmat d σ N x) := by
  have hF : (fun i j : Fin N => torusK d σ N x i j
        * (torusQ d σ N x k j i - torusQ d σ N x (k + 1) i i))
      = fun i j : Fin N => Psi d σ k (x i) (x j) := by
    funext i j
    show heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j)
        * (heatP d σ k (x j - x i) - heatP d σ (k + 1) (x i - x i))
      = heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j)
        * (heatP d σ k (x i - x j) - torusM d σ (k + 1))
    rw [sub_self, ← neg_sub (x i) (x j), heatP_even,
      heatP_of_ne d σ (by omega : k + 1 ≠ 0)]
    all_goals rfl
  have h := absC N hN (torusK d σ N x) (fun j v => torusK d σ N x j v - 1)
    (fun j => torusRho d σ N x j - 1)
    (fun i j => torusQ d σ N x k j i - torusQ d σ N x (k + 1) i i) (eps_eq d σ N hN x)
  rw [← hF]
  exact h

/-- **Stage 1: `Π_k` as a sum of `2k+3` statistics of the kinds `Z⁰`, `Z¹`** (the first display
    after the definitions in the proof of `lem:pibound`): first term
    `-Z¹[F_A,1] - Z¹[F_A,2] + Z¹[F_A',3]`, the term with `m`: `Z⁰[K_m] - Z¹[K_m,3]`, last term
    `Z⁰[Ψ] - Z¹[Ψ,2]`. -/
theorem torusPi_eq_Z (d : ℕ) (σ : ℝ) (N : ℕ) (hN : (N : ℝ) ≠ 0) (x : ℕ → FlatTorus d) (k : ℕ) :
    torusPi d σ N x k (torusHhat d σ N x)
      = (-Zs1two1 N (fun i b => FA d σ k (x i) (x b)) (cmat d σ N x)
          - Zs1two2 N (fun i b => FA d σ k (x i) (x b)) (cmat d σ N x)
          + Zs1three3 N (fun i b j => FA' d σ k (x i) (x b) (x j)) (cmat d σ N x))
        + ∑ m ∈ Finset.Icc 1 (k - 1),
            (Zs0three N (fun i b j => Km d σ (k - m) m (x i) (x b) (x j))
              - Zs1three3 N (fun i b j => Km d σ (k - m) m (x i) (x b) (x j)) (cmat d σ N x))
        + (Zs0two N (fun i j => Psi d σ k (x i) (x j))
            - Zs1two2 N (fun i j => Psi d σ k (x i) (x j)) (cmat d σ N x)) := by
  unfold torusPi
  rw [first_term d σ N hN x k, last_term d σ N hN x k]
  have hm : ∀ m ∈ Finset.Icc 1 (k - 1),
      1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
          torusQ d σ N x (k - m) i b * torusHhat d σ N x m i b
        = Zs0three N (fun i b j => Km d σ (k - m) m (x i) (x b) (x j))
          - Zs1three3 N (fun i b j => Km d σ (k - m) m (x i) (x b) (x j)) (cmat d σ N x) :=
    fun m _ => mid_term d σ N hN x (k - m) m
  rw [Finset.sum_congr rfl hm]

/-! ## Stage 2: a free index of an independent sample, and the degeneracy facts -/

section Fubini

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Integrating one independent point first.** `U` independent of `Y`, `U` with law `ν`, `G`
    bounded and measurable: `E G(U,Y) = E [ (∫ G(z, ·) dν(z)) (Y) ]`. -/
theorem indep_integral_eq [IsProbabilityMeasure μ] {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] (ν : Measure E) [IsProbabilityMeasure ν] (U : Ω → E) (Y : Ω → F)
    (hU : Measurable U) (hY : Measurable Y) (hind : IndepFun U Y μ) (hlaw : μ.map U = ν)
    (G : E × F → ℝ) (hG : Measurable G) {B : ℝ} (hB : ∀ p, |G p| ≤ B) :
    ∫ ω, G (U ω, Y ω) ∂μ = ∫ y, ∫ z, G (z, y) ∂ν ∂(μ.map Y) := by
  haveI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hY.aemeasurable).mp hind
  have hint : Integrable G (ν.prod (μ.map Y)) :=
    Integrable.of_bound hG.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB p)
  have h1 : ∫ ω, G (U ω, Y ω) ∂μ = ∫ p, G p ∂(μ.map fun ω => (U ω, Y ω)) :=
    (integral_map (hU.prodMk hY).aemeasurable hG.aestronglyMeasurable).symm
  rw [h1, hmap, hlaw]
  exact integral_prod_symm G hint

/-- **A summand with a free index has mean zero** (two-block form): if `∫ G(z,y) dν(z) = 0`
    for every `y`, then `E G(U,Y) = 0`. -/
theorem indep_integral_zero [IsProbabilityMeasure μ] {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] (ν : Measure E) [IsProbabilityMeasure ν] (U : Ω → E) (Y : Ω → F)
    (hU : Measurable U) (hY : Measurable Y) (hind : IndepFun U Y μ) (hlaw : μ.map U = ν)
    (G : E × F → ℝ) (hG : Measurable G) {B : ℝ} (hB : ∀ p, |G p| ≤ B)
    (h0 : ∀ y, ∫ z, G (z, y) ∂ν = 0) :
    ∫ ω, G (U ω, Y ω) ∂μ = 0 := by
  rw [indep_integral_eq ν U Y hU hY hind hlaw G hG hB]
  simp [h0]

/-- The same with an upper bound for the inner integral. -/
theorem indep_integral_le [IsProbabilityMeasure μ] {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] (ν : Measure E) [IsProbabilityMeasure ν] (U : Ω → E) (Y : Ω → F)
    (hU : Measurable U) (hY : Measurable Y) (hind : IndepFun U Y μ) (hlaw : μ.map U = ν)
    (G : E × F → ℝ) (hG : Measurable G) {B V : ℝ} (hB : ∀ p, |G p| ≤ B)
    (hle : ∀ y, ∫ z, G (z, y) ∂ν ≤ V) :
    ∫ ω, G (U ω, Y ω) ∂μ ≤ V := by
  haveI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hint : Integrable G (ν.prod (μ.map Y)) :=
    Integrable.of_bound hG.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB p)
  rw [indep_integral_eq ν U Y hU hY hind hlaw G hG hB]
  calc ∫ y, ∫ z, G (z, y) ∂ν ∂(μ.map Y) ≤ ∫ _y, V ∂(μ.map Y) :=
        integral_mono hint.integral_prod_right (integrable_const V) hle
    _ = V := by simp

/-- **A summand with a free index has mean zero** (sample form, `lem:degenerate`): for
    independent points `X_j` with law `ν`, an index `j` outside the finite set `T` and a bounded
    measurable `G` of the point `x_j` and the points over `T` with `∫ G(z, y) dν(z) = 0` for all
    `y`: `E G(X_j, (X_t)_{t ∈ T}) = 0`. -/
theorem free_index_zero [IsProbabilityMeasure μ] {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (X : ℕ → Ω → E) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (j : ℕ) (T : Finset ℕ)
    (hj : j ∉ T) (G : E × (T → E) → ℝ) (hG : Measurable G) {B : ℝ} (hB : ∀ p, |G p| ≤ B)
    (h0 : ∀ y, ∫ z, G (z, y) ∂ν = 0) :
    ∫ ω, G (X j ω, fun t : T => X t ω) ∂μ = 0 := by
  have hind0 := h_indep.indepFun_finset {j} T (Finset.disjoint_singleton_left.mpr hj) hX
  have hind : IndepFun (X j) (fun ω (t : T) => X t ω) μ :=
    hind0.comp (φ := fun u : (({j} : Finset ℕ) → E) => u ⟨j, Finset.mem_singleton_self j⟩)
      (ψ := id) (measurable_pi_apply _) measurable_id
  exact indep_integral_zero ν (X j) (fun ω (t : T) => X t ω) (hX j)
    (measurable_pi_lambda _ fun t => hX t) hind (hlaw j) G hG hB h0

/-- `E|f| ≤ (E f²)^{1/2}` for a bounded measurable `f` on a probability space. -/
theorem abs_integral_le_sqrt [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    {B W : ℝ} (hb : ∀ ω, |f ω| ≤ B) (hW : ∫ ω, f ω ^ 2 ∂μ ≤ W) :
    ∫ ω, |f ω| ∂μ ≤ Real.sqrt W := by
  have hi1 : Integrable (fun ω => |f ω|) μ :=
    Integrable.of_bound (continuous_abs.measurable.comp hf).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_abs]; exact hb ω)
  have hi2 : Integrable (fun ω => f ω ^ 2) μ :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (B ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ ω, |f ω| ∂μ := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact integral_nonneg fun ω => abs_nonneg _
  have hnn : 0 ≤ ∫ ω, (|f ω| - m) ^ 2 ∂μ := integral_nonneg fun ω => _root_.sq_nonneg _
  have hexp : ∀ ω, (|f ω| - m) ^ 2 = f ω ^ 2 - 2 * m * |f ω| + m ^ 2 := fun ω => by
    rw [sub_sq, sq_abs]; ring
  simp_rw [hexp] at hnn
  have hi3 : Integrable (fun ω => 2 * m * |f ω|) μ := hi1.const_mul _
  have hi4 : Integrable (fun ω => f ω ^ 2 - 2 * m * |f ω|) μ := hi2.sub hi3
  rw [integral_add hi4 (integrable_const _),
    integral_sub hi2 hi3, integral_const_mul, ← hm, integral_const,
    probReal_univ, one_smul] at hnn
  have hmm : m ^ 2 ≤ W := by linarith
  rw [← hm]
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm0).symm
    _ ≤ Real.sqrt W := Real.sqrt_le_sqrt hmm

/-- Integral of a fourfold finite sum. -/
theorem integral_sum4 (s : Finset ℕ) (g : ℕ → ℕ → ℕ → ℕ → Ω → ℝ)
    (hI : ∀ a b c e, Integrable (g a b c e) μ) :
    ∫ ω, ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ e ∈ s, g a b c e ω ∂μ
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ e ∈ s, ∫ ω, g a b c e ω ∂μ := by
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ =>
    integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun e _ => hI a b c e)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finset_sum _ (fun b _ => integrable_finset_sum _ fun c _ =>
    integrable_finset_sum _ fun e _ => hI a b c e)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_finset_sum _ (fun c _ => integrable_finset_sum _ fun e _ => hI a b c e)]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact integral_finset_sum _ (fun e _ => hI a b c e)

end Fubini

/-- Counting the diagonal of a double sum. -/
theorem count1 (N i j : ℕ) (hi : i ∈ Finset.range N) (hj : j ∈ Finset.range N) :
    ∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N, (if i' = i ∧ j' = j then (1 : ℝ) else 0)
      = 1 := by
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hj h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hi h

/-! ## Stage 3: `lem:degenerate`(a) for `n = 2`, with explicit constants -/

/-- The hypotheses of the second-moment argument for a translation-invariant function of two
    points, `F(y₁,y₂) = ψ(y₁ - y₂)`: independent points with law `ν`; `ψ` measurable, bounded by
    `B`, even, with `∫ ψ(x - z) dν(z) = 0` (degenerate) and `∫ ψ(x - z)² dν(z) ≤ V`. -/
structure Deg2 {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) {G : Type*} [AddCommGroup G]
    [MeasurableSpace G] (ν : Measure G) (X : ℕ → Ω → G) (ψ : G → ℝ) (B V : ℝ) : Prop where
  indep : iIndepFun X μ
  meas : ∀ j, Measurable (X j)
  law : ∀ j, μ.map (X j) = ν
  psi_meas : Measurable ψ
  bound : ∀ u, |ψ u| ≤ B
  even : ∀ u, ψ (-u) = ψ u
  mean : ∀ x, ∫ z, ψ (x - z) ∂ν = 0
  var : ∀ x, ∫ z, ψ (x - z) ^ 2 ∂ν ≤ V
  V_nonneg : 0 ≤ V

/-- The off-diagonal summand `ψ(x_i - x_j)` (zero for `i = j`). -/
noncomputable def aT {Ω G : Type*} [AddCommGroup G] (ψ : G → ℝ) (X : ℕ → Ω → G) (i j : ℕ)
    (ω : Ω) : ℝ :=
  if i = j then 0 else ψ (X i ω - X j ω)

/-- The part of `N² Z⁰` from the injective maps. -/
noncomputable def Soff {Ω G : Type*} [AddCommGroup G] (ψ : G → ℝ) (X : ℕ → Ω → G) (N : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, aT ψ X i j ω

namespace Deg2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ : G → ℝ} {B V : ℝ}

omit [MeasurableSub₂ G] in
theorem B_nonneg (H : Deg2 μ ν X ψ B V) : 0 ≤ B := (abs_nonneg (ψ 0)).trans (H.bound 0)

/-- The index `j` occurs only in the first factor: the mean vanishes. -/
theorem cross_right [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    {a b c j : ℕ} (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) :
    ∫ ω, ψ (X a ω - X j ω) * ψ (X b ω - X c ω) ∂μ = 0 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = {a, b, c} := ⟨_, rfl⟩
  have ha : a ∈ T := by rw [hT]; simp
  have hb : b ∈ T := by rw [hT]; simp
  have hc : c ∈ T := by rw [hT]; simp
  have hj : j ∉ T := by rw [hT]; simp [hja, hjb, hjc]
  have hψ := H.psi_meas
  have e1 : Measurable fun p : G × (T → G) => p.2 ⟨a, ha⟩ :=
    (measurable_pi_apply (⟨a, ha⟩ : T)).comp measurable_snd
  have e2 : Measurable fun p : G × (T → G) => p.2 ⟨b, hb⟩ :=
    (measurable_pi_apply (⟨b, hb⟩ : T)).comp measurable_snd
  have e3 : Measurable fun p : G × (T → G) => p.2 ⟨c, hc⟩ :=
    (measurable_pi_apply (⟨c, hc⟩ : T)).comp measurable_snd
  have hmeas : Measurable fun p : G × (T → G) =>
      ψ (p.2 ⟨a, ha⟩ - p.1) * ψ (p.2 ⟨b, hb⟩ - p.2 ⟨c, hc⟩) :=
    (hψ.comp (e1.sub measurable_fst)).mul (hψ.comp (e2.sub e3))
  exact free_index_zero ν X H.indep H.meas H.law j T hj
    (fun p : G × (T → G) => ψ (p.2 ⟨a, ha⟩ - p.1) * ψ (p.2 ⟨b, hb⟩ - p.2 ⟨c, hc⟩)) hmeas
    (B := B * B)
    (fun p => by
      rw [abs_mul]
      exact mul_le_mul (H.bound _) (H.bound _) (abs_nonneg _) H.B_nonneg)
    (fun y => by
      show ∫ z, ψ (y ⟨a, ha⟩ - z) * ψ (y ⟨b, hb⟩ - y ⟨c, hc⟩) ∂ν = 0
      rw [integral_mul_const, H.mean, zero_mul])

/-- The same with the free index in the first slot (`ψ` is even). -/
theorem cross_left [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    {a b c j : ℕ} (hja : j ≠ a) (hjb : j ≠ b) (hjc : j ≠ c) :
    ∫ ω, ψ (X j ω - X a ω) * ψ (X b ω - X c ω) ∂μ = 0 := by
  have e : (fun ω => ψ (X j ω - X a ω) * ψ (X b ω - X c ω))
      = fun ω => ψ (X a ω - X j ω) * ψ (X b ω - X c ω) := by
    funext ω
    have h : ψ (X j ω - X a ω) = ψ (X a ω - X j ω) := by rw [← H.even, neg_sub]
    rw [h]
  rw [e]
  exact H.cross_right hja hjb hjc

/-- `E ψ(X_i - X_j)² ≤ V` for `i ≠ j`. -/
theorem sq_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, ψ (X i ω - X j ω) ^ 2 ∂μ ≤ V :=
  indep_integral_le ν (X j) (X i) (H.meas j) (H.meas i) (H.indep.indepFun hij.symm) (H.law j)
    (fun p : G × G => ψ (p.2 - p.1) ^ 2)
    ((H.psi_meas.comp (measurable_snd.sub measurable_fst)).pow_const 2) (B := B ^ 2)
    (fun p => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (H.bound _) 2)
    (fun y => H.var y)

theorem aT_meas (H : Deg2 μ ν X ψ B V) (i j : ℕ) : Measurable (aT ψ X i j) := by
  unfold aT
  by_cases h : i = j
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact H.psi_meas.comp ((H.meas i).sub (H.meas j))

theorem aT_bound (H : Deg2 μ ν X ψ B V) (i j : ℕ) (ω : Ω) : |aT ψ X i j ω| ≤ B := by
  unfold aT
  split_ifs
  · rw [abs_zero]; exact H.B_nonneg
  · exact H.bound _

theorem aT_prod_integrable [IsFiniteMeasure μ] (H : Deg2 μ ν X ψ B V) (i j i' j' : ℕ) :
    Integrable (fun ω => aT ψ X i j ω * aT ψ X i' j' ω) μ :=
  Integrable.of_bound ((H.aT_meas i j).mul (H.aT_meas i' j')).aestronglyMeasurable (B * B)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (H.aT_bound i j ω) (H.aT_bound i' j' ω) (abs_nonneg _) H.B_nonneg)

/-- **The mean of a product of two off-diagonal summands**: it vanishes unless the two index
    pairs coincide as sets, and is at most `V` then. -/
theorem pair_term_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (i j i' j' : ℕ) :
    ∫ ω, aT ψ X i j ω * aT ψ X i' j' ω ∂μ
      ≤ V * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
          + (if i' = j ∧ j' = i then (1 : ℝ) else 0)) := by
  have hV0 := H.V_nonneg
  have t1 : (0 : ℝ) ≤ (if i' = i ∧ j' = j then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t2 : (0 : ℝ) ≤ (if i' = j ∧ j' = i then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hR : 0 ≤ V * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
      + (if i' = j ∧ j' = i then (1 : ℝ) else 0)) := mul_nonneg hV0 (add_nonneg t1 t2)
  by_cases hij : i = j
  · have hz : (fun ω => aT ψ X i j ω * aT ψ X i' j' ω) = fun _ => (0 : ℝ) := by
      funext ω; simp [aT, hij]
    rw [hz, integral_zero]; exact hR
  by_cases hij' : i' = j'
  · have hz : (fun ω => aT ψ X i j ω * aT ψ X i' j' ω) = fun _ => (0 : ℝ) := by
      funext ω; simp [aT, hij']
    rw [hz, integral_zero]; exact hR
  have hA : (fun ω => aT ψ X i j ω * aT ψ X i' j' ω)
      = fun ω => ψ (X i ω - X j ω) * ψ (X i' ω - X j' ω) := by
    funext ω; simp [aT, hij, hij']
  rw [hA]
  by_cases h1 : j ≠ i' ∧ j ≠ j'
  · rw [H.cross_right (a := i) (b := i') (c := j') (j := j) (Ne.symm hij) h1.1 h1.2]
    exact hR
  by_cases h2 : i ≠ i' ∧ i ≠ j'
  · rw [H.cross_left (a := j) (b := i') (c := j') (j := i) hij h2.1 h2.2]
    exact hR
  have h3 : (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) := by omega
  rcases h3 with h | h
  · have hR1 : V ≤ V * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
        + (if i' = j ∧ j' = i then (1 : ℝ) else 0)) := by
      rw [if_pos h]; linarith [mul_nonneg hV0 t2]
    refine le_trans ?_ hR1
    have he : (fun ω => ψ (X i ω - X j ω) * ψ (X i' ω - X j' ω))
        = fun ω => ψ (X i ω - X j ω) ^ 2 := by
      funext ω; rw [h.1, h.2]; ring
    rw [he]; exact H.sq_le hij
  · have hR2 : V ≤ V * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
        + (if i' = j ∧ j' = i then (1 : ℝ) else 0)) := by
      rw [if_pos h]; linarith [mul_nonneg hV0 t1]
    refine le_trans ?_ hR2
    have he : (fun ω => ψ (X i ω - X j ω) * ψ (X i' ω - X j' ω))
        = fun ω => ψ (X i ω - X j ω) ^ 2 := by
      funext ω
      have hh : ψ (X j ω - X i ω) = ψ (X i ω - X j ω) := by rw [← H.even, neg_sub]
      rw [h.1, h.2, hh]; ring
    rw [he]; exact H.sq_le hij

/-- **Second moment of the injective part**: `E (∑_{i ≠ j} ψ(X_i - X_j))² ≤ 2 N² V`
    (in the paper: `E U² ≤ n⁴ ‖F‖₂² / N²` with `n = 2`; here the constant is `2`). -/
theorem second_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg2 μ ν X ψ B V) (N : ℕ) :
    ∫ ω, Soff ψ X N ω ^ 2 ∂μ ≤ 2 * (N : ℝ) ^ 2 * V := by
  have hS2 : ∀ ω, Soff ψ X N ω ^ 2
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ j' ∈ Finset.range N, aT ψ X i j ω * aT ψ X i' j' ω := by
    intro ω
    unfold Soff
    rw [pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
  have h4 : ∫ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
        ∑ j' ∈ Finset.range N, aT ψ X i j ω * aT ψ X i' j' ω ∂μ
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ j' ∈ Finset.range N, ∫ ω, aT ψ X i j ω * aT ψ X i' j' ω ∂μ :=
    integral_sum4 (Finset.range N) (fun i j i' j' ω => aT ψ X i j ω * aT ψ X i' j' ω)
      (fun i j i' j' => H.aT_prod_integrable i j i' j')
  simp_rw [hS2]
  rw [h4]
  calc ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ j' ∈ Finset.range N, ∫ ω, aT ψ X i j ω * aT ψ X i' j' ω ∂μ
      ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ j' ∈ Finset.range N, V * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
            + (if i' = j ∧ j' = i then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i' _ =>
          Finset.sum_le_sum fun j' _ => H.pair_term_le i j i' j'
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, V * (1 + 1) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        have e : ∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N,
              V * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
                + (if i' = j ∧ j' = i then (1 : ℝ) else 0))
            = V * (∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N,
                  (if i' = i ∧ j' = j then (1 : ℝ) else 0)
                + ∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N,
                  (if i' = j ∧ j' = i then (1 : ℝ) else 0)) := by
          simp only [← Finset.mul_sum, ← Finset.sum_add_distrib]
        rw [e, count1 N i j hi hj, count1 N j i hj hi]
    _ = 2 * (N : ℝ) ^ 2 * V := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **`lem:degenerate`(a) for `n = 2` with explicit constants.** For `F(y₁,y₂) = ψ(y₁ - y₂)`
    degenerate, `Z⁰ = N⁻² ∑_{i,j} ψ(X_i - X_j)` (all pairs, the diagonal included) satisfies
    `E|Z⁰| ≤ (√(2V) + |ψ(0)|)/N`; here `√V` is `‖F‖₂` and `|ψ(0)|` is `ϱ(F)`. -/
theorem Z0_bound [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, |1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)| ∂μ
      ≤ (Real.sqrt (2 * V) + |ψ 0|) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdec : ∀ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
      = Soff ψ X N ω + N * ψ 0 := by
    intro ω
    have h : ∀ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
        = ∑ j ∈ Finset.range N, aT ψ X i j ω + ψ 0 := by
      intro i hi
      have h' : ∀ j ∈ Finset.range N, ψ (X i ω - X j ω)
          = aT ψ X i j ω + (if j = i then ψ 0 else 0) := by
        intro j _
        unfold aT
        by_cases hji : j = i
        · rw [hji]; simp
        · rw [if_neg (fun h'' : i = j => hji h''.symm), if_neg hji, add_zero]
      rw [Finset.sum_congr rfl h', Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hi]
    unfold Soff
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
    simp
  have hSm : Measurable (Soff ψ X N) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => H.aT_meas i j
  have hSb : ∀ ω, |Soff ψ X N ω| ≤ ∑ _i ∈ Finset.range N, ∑ _j ∈ Finset.range N, B := by
    intro ω
    calc |Soff ψ X N ω| ≤ ∑ i ∈ Finset.range N, |∑ j ∈ Finset.range N, aT ψ X i j ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, |aT ψ X i j ω| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range N, ∑ _j ∈ Finset.range N, B :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => H.aT_bound i j ω
  have hSint : Integrable (Soff ψ X N) μ :=
    Integrable.of_bound hSm.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hSb ω)
  have h1 : ∫ ω, |Soff ψ X N ω| ∂μ ≤ N * Real.sqrt (2 * V) := by
    have h := abs_integral_le_sqrt (Soff ψ X N) hSm hSb (H.second_moment N)
    have e : Real.sqrt (2 * (N : ℝ) ^ 2 * V) = N * Real.sqrt (2 * V) := by
      rw [show 2 * (N : ℝ) ^ 2 * V = (N : ℝ) ^ 2 * (2 * V) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hNpos.le]
    rw [e] at h; exact h
  have hpt : ∀ ω, |1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ψ (X i ω - X j ω)|
      ≤ 1 / (N : ℝ) ^ 2 * (|Soff ψ X N ω| + N * |ψ 0|) := by
    intro ω
    rw [hdec ω, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |Soff ψ X N ω + N * ψ 0| ≤ |Soff ψ X N ω| + |(N : ℝ) * ψ 0| := abs_add_le _ _
      _ = |Soff ψ X N ω| + N * |ψ 0| := by rw [abs_mul, abs_of_nonneg hNpos.le]
  have hgi : Integrable (fun ω => 1 / (N : ℝ) ^ 2 * (|Soff ψ X N ω| + N * |ψ 0|)) μ :=
    ((hSint.abs).add (integrable_const _)).const_mul _
  calc ∫ ω, |1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ψ (X i ω - X j ω)| ∂μ
      ≤ ∫ ω, 1 / (N : ℝ) ^ 2 * (|Soff ψ X N ω| + N * |ψ 0|) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _) hgi
          (Filter.Eventually.of_forall hpt)
    _ = 1 / (N : ℝ) ^ 2 * (∫ ω, |Soff ψ X N ω| ∂μ + N * |ψ 0|) := by
        rw [integral_const_mul, integral_add hSint.abs (integrable_const _), integral_const,
          probReal_univ, one_smul]
    _ ≤ 1 / (N : ℝ) ^ 2 * (N * Real.sqrt (2 * V) + N * |ψ 0|) := by gcongr
    _ = (Real.sqrt (2 * V) + |ψ 0|) / N := by field_simp

end Deg2

/-! ## Stages 2 and 3 on the flat torus: degeneracy of `c`, `Ψ`, `K_m`; the bound for `Z⁰[Ψ]` -/

theorem torusM_one (d : ℕ) (σ : ℝ) : torusM d σ 1 = heatTorus d (2 * Real.pi ^ 2 * σ) 0 := by
  unfold torusM; simp

theorem flat_integrable (d : ℕ) (f : FlatTorus d → ℝ) (hf : Continuous f) :
    Integrable f (flatTorusMeasure d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem pker_continuous {σ : ℝ} (hσ : 0 < σ) (d : ℕ) : Continuous (pker d σ) :=
  heatTorus_continuous (by positivity) d

/-- `∫ p(x - z) dz = 1`. -/
theorem pker_mass {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (x : FlatTorus d) :
    ∫ z, pker d σ (x - z) ∂flatTorusMeasure d = 1 := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  rw [integral_sub_left_eq_self (pker d σ) (flatTorusMeasure d) x]
  exact heatTorus_mass (by positivity) d

/-- The semigroup at arbitrary points of the torus:
    `∫ p_σ(x - z) p_s(z - w) dz = p_{σ+s}(x - w)`. -/
theorem semigroup_all {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (x w : FlatTorus d) :
    ∫ z, heatTorus d (2 * Real.pi ^ 2 * σ) (x - z) * heatTorus d (2 * Real.pi ^ 2 * s) (z - w)
        ∂flatTorusMeasure d
      = heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (x - w) := by
  obtain ⟨tx, rfl⟩ := flatTorus_lift d x
  obtain ⟨tw, rfl⟩ := flatTorus_lift d w
  exact torus_first_moment hσ hs d tx tw

/-- **`∫ c = 0`**: `∫ (p(x - z) - 1) dz = 0` for every `x`. -/
theorem c_mean_zero {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (x : FlatTorus d) :
    ∫ z, (pker d σ (x - z) - 1) ∂flatTorusMeasure d = 0 := by
  have hKc : Continuous fun z : FlatTorus d => pker d σ (x - z) :=
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  rw [integral_sub (flat_integrable d _ hKc) (integrable_const _), pker_mass hσ d x,
    integral_const, probReal_univ, one_smul, sub_self]

theorem psiK_facts {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (u : FlatTorus d) :
    0 ≤ pker d σ u ∧ pker d σ u ≤ torusM d σ 1
      ∧ |heatP d σ k u - torusM d σ (k + 1)| ≤ torusM d σ k := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := mul_pos (by positivity) (mul_pos hk' hσ)
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck1 : 0 < 2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) * σ) :=
    mul_pos (by positivity) (mul_pos hk1 hσ)
  refine ⟨heatTorus_nonneg hcσ d u, ?_, ?_⟩
  · rw [torusM_one]; exact heatTorus_le_zero hcσ d u
  · have h1 : 0 ≤ heatP d σ k u := heatP_nonneg hσ d k u
    have h2 : heatP d σ k u ≤ torusM d σ k := by
      rw [heatP_of_ne d σ (by omega : k ≠ 0)]; exact heatTorus_le_zero hck d u
    have h3 : 0 ≤ torusM d σ (k + 1) := heatTorus_nonneg hck1 d 0
    have h4 : torusM d σ (k + 1) ≤ torusM d σ k := torusM_anti hσ d hk (Nat.le_succ k)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem psiK_continuous {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) :
    Continuous (psiK d σ k) := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := mul_pos (by positivity) (mul_pos hk' hσ)
  have hP : heatP d σ k = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) :=
    funext fun u => heatP_of_ne d σ (by omega : k ≠ 0) u
  unfold psiK
  rw [hP]
  exact (pker_continuous hσ d).mul ((heatTorus_continuous hck d).sub continuous_const)

theorem psiK_even (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : psiK d σ k (-u) = psiK d σ k u := by
  unfold psiK pker
  rw [heatTorus_even, heatP_even]

theorem psiK_bound {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (u : FlatTorus d) :
    |psiK d σ k u| ≤ torusM d σ 1 * torusM d σ k := by
  obtain ⟨h0, h1, h2⟩ := psiK_facts hσ d k hk u
  unfold psiK
  rw [abs_mul, abs_of_nonneg h0]
  exact mul_le_mul h1 h2 (abs_nonneg _) (h0.trans h1)

/-- **`Ψ` is degenerate**: `∫ Ψ(y₁, z) dz = ∫ p(u)(p_k(u) - m_{k+1}) = 0` (`∫ p p_k = m_{k+1}`). -/
theorem psi_mean_zero {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    ∫ z, psiK d σ k (x - z) ∂flatTorusMeasure d = 0 := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs : 0 < (k : ℝ) * σ := mul_pos hk' hσ
  have hck : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := mul_pos (by positivity) hs
  have hKc : Continuous fun z : FlatTorus d => pker d σ (x - z) :=
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  have hGc : Continuous fun z : FlatTorus d =>
      heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x) :=
    (heatTorus_continuous hck d).comp (continuous_id.sub continuous_const)
  have hfirst : ∫ z, pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
      ∂flatTorusMeasure d = heatTorus d (2 * Real.pi ^ 2 * (σ + (k : ℝ) * σ)) (x - x) :=
    semigroup_all hσ hs d x x
  have e : ∀ z, psiK d σ k (x - z)
      = pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
        - torusM d σ (k + 1) * pker d σ (x - z) := by
    intro z
    have h1 : heatP d σ k (x - z) = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x) := by
      rw [heatP_of_ne d σ (by omega : k ≠ 0), ← neg_sub z x, heatTorus_even]
    unfold psiK
    rw [h1]; ring
  have i1 : Integrable (fun z : FlatTorus d =>
      pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x))
      (flatTorusMeasure d) := flat_integrable d _ (hKc.mul hGc)
  have i2 : Integrable (fun z : FlatTorus d => torusM d σ (k + 1) * pker d σ (x - z))
      (flatTorusMeasure d) := (flat_integrable d _ hKc).const_mul _
  simp_rw [e]
  rw [integral_sub i1 i2, integral_const_mul, pker_mass hσ d x, hfirst, sub_self]
  have hc : 2 * Real.pi ^ 2 * (σ + (k : ℝ) * σ) = 2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) * σ) := by
    push_cast; ring
  unfold torusM
  rw [hc]; ring

/-- `Ψ` is degenerate in its last argument, in the notation of the paper. -/
theorem Psi_degenerate {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (y1 : FlatTorus d) :
    ∫ z, Psi d σ k y1 z ∂flatTorusMeasure d = 0 :=
  psi_mean_zero hσ d k hk y1

/-- `∫ ψ_k(x - z)² dz ≤ M m_k²` (the entry `‖Ψ‖₂² ≤ M m_k²` of the table of `lem:pibound`). -/
theorem psi_var {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    ∫ z, psiK d σ k (x - z) ^ 2 ∂flatTorusMeasure d ≤ torusM d σ 1 * torusM d σ k ^ 2 := by
  have hKc : Continuous fun z : FlatTorus d => pker d σ (x - z) :=
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  have hψc : Continuous fun z : FlatTorus d => psiK d σ k (x - z) :=
    (psiK_continuous hσ d k hk).comp (continuous_const.sub continuous_id)
  have hpt : ∀ z, psiK d σ k (x - z) ^ 2
      ≤ torusM d σ 1 * torusM d σ k ^ 2 * pker d σ (x - z) := by
    intro z
    obtain ⟨h0, h1, h2⟩ := psiK_facts hσ d k hk (x - z)
    have hq : (heatP d σ k (x - z) - torusM d σ (k + 1)) ^ 2 ≤ torusM d σ k ^ 2 :=
      sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    have hM0 : 0 ≤ torusM d σ 1 := h0.trans h1
    unfold psiK
    calc (pker d σ (x - z) * (heatP d σ k (x - z) - torusM d σ (k + 1))) ^ 2
        = pker d σ (x - z)
          * (pker d σ (x - z) * (heatP d σ k (x - z) - torusM d σ (k + 1)) ^ 2) := by ring
      _ ≤ pker d σ (x - z) * (torusM d σ 1 * torusM d σ k ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hq (_root_.sq_nonneg _) hM0) h0
      _ = torusM d σ 1 * torusM d σ k ^ 2 * pker d σ (x - z) := by ring
  calc ∫ z, psiK d σ k (x - z) ^ 2 ∂flatTorusMeasure d
      ≤ ∫ z, torusM d σ 1 * torusM d σ k ^ 2 * pker d σ (x - z) ∂flatTorusMeasure d :=
        integral_mono (flat_integrable d _ (hψc.pow 2))
          ((flat_integrable d _ hKc).const_mul _) hpt
    _ = torusM d σ 1 * torusM d σ k ^ 2 := by
        rw [integral_const_mul, pker_mass hσ d x, mul_one]

/-- **`K_m` is degenerate in its last argument**:
    `∫ K_m(y₁,y₂,z) dz = 0`, because `∫ p(y₂ - z) p_m(z - y₁) dz = p_{m+1}(y₁ - y₂)`. -/
theorem Km_degenerate {σ : ℝ} (hσ : 0 < σ) (d l m : ℕ) (hm : 1 ≤ m) (y1 y2 : FlatTorus d) :
    ∫ z, Km d σ l m y1 y2 z ∂flatTorusMeasure d = 0 := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs : 0 < (m : ℝ) * σ := mul_pos hm' hσ
  have hcm : 0 < 2 * Real.pi ^ 2 * ((m : ℝ) * σ) := mul_pos (by positivity) hs
  have hKc : Continuous fun z : FlatTorus d => pker d σ (y2 - z) :=
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  have hGc : Continuous fun z : FlatTorus d =>
      heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (z - y1) :=
    (heatTorus_continuous hcm d).comp (continuous_id.sub continuous_const)
  have hfirst : ∫ z, pker d σ (y2 - z) * heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (z - y1)
      ∂flatTorusMeasure d = heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (y2 - y1) :=
    semigroup_all hσ hs d y2 y1
  have e : ∀ z, Km d σ l m y1 y2 z
      = heatP d σ l (y1 - y2)
          * (pker d σ (y2 - z) * heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (z - y1))
        - heatP d σ l (y1 - y2) * heatP d σ (m + 1) (y1 - y2) * pker d σ (y2 - z) := by
    intro z
    unfold Km
    rw [heatP_of_ne d σ (by omega : m ≠ 0)]; ring
  have hev : heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (y2 - y1)
      = heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (y1 - y2) := by
    rw [← neg_sub y1 y2, heatTorus_even]
  have i1 : Integrable (fun z : FlatTorus d => heatP d σ l (y1 - y2)
      * (pker d σ (y2 - z) * heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (z - y1)))
      (flatTorusMeasure d) := (flat_integrable d _ (hKc.mul hGc)).const_mul _
  have i2 : Integrable (fun z : FlatTorus d =>
      heatP d σ l (y1 - y2) * heatP d σ (m + 1) (y1 - y2) * pker d σ (y2 - z))
      (flatTorusMeasure d) := (flat_integrable d _ hKc).const_mul _
  simp_rw [e]
  rw [integral_sub i1 i2, integral_const_mul, integral_const_mul, pker_mass hσ d y2, hfirst,
    hev, heatP_succ]
  ring

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`E c_{jv} = 0` for `j ≠ v`** (independent uniform points). -/
theorem c_offdiag_mean_zero [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {j v : ℕ}
    (hjv : j ≠ v) :
    ∫ ω, (pker d σ (X j ω - X v ω) - 1) ∂μ = 0 :=
  indep_integral_zero (flatTorusMeasure d) (X v) (X j) (hX v) (hX j)
    (h_indep.indepFun hjv.symm) (hlaw v)
    (fun p : FlatTorus d × FlatTorus d => pker d σ (p.2 - p.1) - 1)
    (((pker_continuous hσ d).measurable.comp (measurable_snd.sub measurable_fst)).sub
      measurable_const)
    (B := torusM d σ 1 + 1)
    (fun p => by
      have h0 : 0 ≤ pker d σ (p.2 - p.1) := heatTorus_nonneg (by positivity) d _
      have h1 : pker d σ (p.2 - p.1) ≤ torusM d σ 1 := by
        rw [torusM_one]; exact heatTorus_le_zero (by positivity) d _
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
    (fun y => c_mean_zero hσ d y)

/-- **Stage 3: the mean of `|Z⁰[Ψ]|`**, the first of the two statistics of the last term of
    `Π_k`. For independent uniform points on the flat torus, `k ≥ 1`, `N ≥ 1`:
    `E|Z⁰[Ψ]| ≤ (√(2 M m_k²) + M m_k)/N`, `M = m_1 = p(0)`. -/
theorem Z0_Psi_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, |Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))| ∂μ
      ≤ (Real.sqrt (2 * (torusM d σ 1 * torusM d σ k ^ 2)) + torusM d σ 1 * torusM d σ k) / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : 0 ≤ torusM d σ 1 :=
    (psiK_facts hσ d k hk 0).1.trans (psiK_facts hσ d k hk 0).2.1
  have H : Deg2 μ (flatTorusMeasure d) X (psiK d σ k) (torusM d σ 1 * torusM d σ k)
      (torusM d σ 1 * torusM d σ k ^ 2) :=
    { indep := h_indep
      meas := hX
      law := hlaw
      psi_meas := (psiK_continuous hσ d k hk).measurable
      bound := psiK_bound hσ d k hk
      even := psiK_even d σ k
      mean := psi_mean_zero hσ d k hk
      var := psi_var hσ d k hk
      V_nonneg := mul_nonneg hM0 (_root_.sq_nonneg _) }
  have hconv : ∀ ω, Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
      = 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          psiK d σ k (X i ω - X j ω) := by
    intro ω
    have h1 : ∑ i : Fin N, ∑ j : Fin N, Psi d σ k (X i ω) (X j ω)
        = ∑ i ∈ Finset.range N, ∑ j : Fin N, Psi d σ k (X i ω) (X j ω) :=
      Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, Psi d σ k (X i ω) (X j ω)) N
    have h2 : ∀ i ∈ Finset.range N, ∑ j : Fin N, Psi d σ k (X i ω) (X j ω)
        = ∑ j ∈ Finset.range N, psiK d σ k (X i ω - X j ω) := fun i _ =>
      Fin.sum_univ_eq_sum_range (fun j => psiK d σ k (X i ω - X j ω)) N
    unfold Zs0two
    rw [h1, Finset.sum_congr rfl h2]
  simp_rw [hconv]
  refine (H.Z0_bound N hN).trans ?_
  have hb := psiK_bound hσ d k hk 0
  exact div_le_div_of_nonneg_right (by linarith) hNpos.le

end Sample

/-! ## Stage 3, continued: `Z¹[F, a = 2]` for `n = 2` and a doubly degenerate `F`

`Z¹[F,2] = N⁻³ ∑_{i,j,v} ψ(x_i - x_j) c(x_j - x_v)` is treated as a statistic of three points
which is degenerate in its first and in its last argument (`ψ` and `c` both integrate to zero).
This is NOT the argument of `lem:degenerate`(b) (which does not assume that `F` is degenerate);
it suffices for `Ψ`, not for `F_A`, `F_A'`, `K_m`. -/

section Fubini2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem bdd_integrable [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)

/-- `E G(U,Y) ≤ E g(Y)` if `∫ G(z,y) dν(z) ≤ g(y)` for all `y`. -/
theorem indep_integral_le_fun [IsProbabilityMeasure μ] {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] (ν : Measure E) [IsProbabilityMeasure ν] (U : Ω → E) (Y : Ω → F)
    (hU : Measurable U) (hY : Measurable Y) (hind : IndepFun U Y μ) (hlaw : μ.map U = ν)
    (G : E × F → ℝ) (hG : Measurable G) {B Bg : ℝ} (hB : ∀ p, |G p| ≤ B) (g : F → ℝ)
    (hg : Measurable g) (hgB : ∀ y, |g y| ≤ Bg) (hle : ∀ y, ∫ z, G (z, y) ∂ν ≤ g y) :
    ∫ ω, G (U ω, Y ω) ∂μ ≤ ∫ ω, g (Y ω) ∂μ := by
  haveI : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hint : Integrable G (ν.prod (μ.map Y)) :=
    Integrable.of_bound hG.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB p)
  have hgi : Integrable g (μ.map Y) := bdd_integrable g hg hgB
  have e : ∫ ω, g (Y ω) ∂μ = ∫ y, g y ∂(μ.map Y) :=
    (integral_map hY.aemeasurable hg.aestronglyMeasurable).symm
  rw [indep_integral_eq ν U Y hU hY hind hlaw G hG hB, e]
  exact integral_mono hint.integral_prod_right hgi hle

theorem indep_two {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) {j a b : ℕ} (ha : j ≠ a) (hb : j ≠ b) :
    IndepFun (X j) (fun ω => (X a ω, X b ω)) μ := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = {a, b} := ⟨_, rfl⟩
  have ma : a ∈ T := by rw [hT]; simp
  have mb : b ∈ T := by rw [hT]; simp
  have hj : j ∉ T := by rw [hT]; simp [ha, hb]
  have ea : Measurable fun y : T → E => y ⟨a, ma⟩ := measurable_pi_apply _
  have eb : Measurable fun y : T → E => y ⟨b, mb⟩ := measurable_pi_apply _
  have hind0 := h_indep.indepFun_finset {j} T (Finset.disjoint_singleton_left.mpr hj) hX
  exact hind0.comp (φ := fun u : (({j} : Finset ℕ) → E) => u ⟨j, Finset.mem_singleton_self j⟩)
    (ψ := fun y : T → E => (y ⟨a, ma⟩, y ⟨b, mb⟩)) (measurable_pi_apply _) (ea.prodMk eb)

theorem indep_five {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) {j a b c e f : ℕ} (ha : j ≠ a) (hb : j ≠ b) (hc : j ≠ c)
    (he : j ≠ e) (hf : j ≠ f) :
    IndepFun (X j) (fun ω => (X a ω, X b ω, X c ω, X e ω, X f ω)) μ := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = {a, b, c, e, f} := ⟨_, rfl⟩
  have ma : a ∈ T := by rw [hT]; simp
  have mb : b ∈ T := by rw [hT]; simp
  have mc : c ∈ T := by rw [hT]; simp
  have me : e ∈ T := by rw [hT]; simp
  have mf : f ∈ T := by rw [hT]; simp
  have hj : j ∉ T := by rw [hT]; simp [ha, hb, hc, he, hf]
  have ea : Measurable fun y : T → E => y ⟨a, ma⟩ := measurable_pi_apply _
  have eb : Measurable fun y : T → E => y ⟨b, mb⟩ := measurable_pi_apply _
  have ec : Measurable fun y : T → E => y ⟨c, mc⟩ := measurable_pi_apply _
  have ee : Measurable fun y : T → E => y ⟨e, me⟩ := measurable_pi_apply _
  have ef : Measurable fun y : T → E => y ⟨f, mf⟩ := measurable_pi_apply _
  have hind0 := h_indep.indepFun_finset {j} T (Finset.disjoint_singleton_left.mpr hj) hX
  exact hind0.comp (φ := fun u : (({j} : Finset ℕ) → E) => u ⟨j, Finset.mem_singleton_self j⟩)
    (ψ := fun y : T → E => (y ⟨a, ma⟩, y ⟨b, mb⟩, y ⟨c, mc⟩, y ⟨e, me⟩, y ⟨f, mf⟩))
    (measurable_pi_apply _) (ea.prodMk (eb.prodMk (ec.prodMk (ee.prodMk ef))))

end Fubini2

theorem abs4 {a b c d A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ A) (hd : |d| ≤ B)
    (hA : 0 ≤ A) (hB : 0 ≤ B) : |a * b * (c * d)| ≤ A * B * (A * B) := by
  have h1 : |a * b| ≤ A * B := by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hA
  have h2 : |c * d| ≤ A * B := by rw [abs_mul]; exact mul_le_mul hc hd (abs_nonneg _) hA
  rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hA hB)

/-! ### counting -/

theorem cnt2 (N p q : ℕ) (hp : p ∈ Finset.range N) (hq : q ∈ Finset.range N) :
    ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, (if p = a ∧ q = b then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hq h
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd hp h

theorem c_ab (N p q : ℕ) (hp : p ∈ Finset.range N) (hq : q ∈ Finset.range N) :
    ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ _e ∈ Finset.range N,
      (if p = a ∧ q = b then (1 : ℝ) else 0) = N := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  rw [cnt2 N p q hp hq, mul_one]

theorem c_ae (N p q : ℕ) (hp : p ∈ Finset.range N) (hq : q ∈ Finset.range N) :
    ∑ a ∈ Finset.range N, ∑ _b ∈ Finset.range N, ∑ e ∈ Finset.range N,
      (if p = a ∧ q = e then (1 : ℝ) else 0) = N :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans (c_ab N p q hp hq)

theorem c_ba (N p q : ℕ) (hp : p ∈ Finset.range N) (hq : q ∈ Finset.range N) :
    ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ _e ∈ Finset.range N,
      (if p = b ∧ q = a then (1 : ℝ) else 0) = N :=
  Finset.sum_comm.trans (c_ab N p q hp hq)

theorem c_be (N p q : ℕ) (hp : p ∈ Finset.range N) (hq : q ∈ Finset.range N) :
    ∑ _a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ e ∈ Finset.range N,
      (if p = b ∧ q = e then (1 : ℝ) else 0) = N :=
  Finset.sum_comm.trans (c_ae N p q hp hq)

theorem c_ea (N p q : ℕ) (hp : p ∈ Finset.range N) (hq : q ∈ Finset.range N) :
    ∑ a ∈ Finset.range N, ∑ _b ∈ Finset.range N, ∑ e ∈ Finset.range N,
      (if p = e ∧ q = a then (1 : ℝ) else 0) = N :=
  (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (c_ab N p q hp hq))

theorem c_eb (N p q : ℕ) (hp : p ∈ Finset.range N) (hq : q ∈ Finset.range N) :
    ∑ _a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ e ∈ Finset.range N,
      (if p = e ∧ q = b then (1 : ℝ) else 0) = N :=
  Finset.sum_comm.trans (c_ea N p q hp hq)

theorem sum_R3 (N : ℕ) (f : ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N), f t
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ e ∈ Finset.range N, f (a, b, e) :=
  (Finset.sum_product _ _ _).trans (Finset.sum_congr rfl fun _ _ => Finset.sum_product _ _ _)

/-! ### the three-point statistic -/

/-- `ψ(x_i - x_j) c(x_j - x_v)`. -/
noncomputable def aP {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (i j v : ℕ)
    (ω : Ω) : ℝ :=
  ψ (X i ω - X j ω) * c (X j ω - X v ω)

/-- The summand for an injective triple (zero otherwise). -/
noncomputable def bT {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (i j v : ℕ)
    (ω : Ω) : ℝ :=
  if i = j ∨ j = v ∨ i = v then 0 else aP ψ c X i j v ω

/-- The part of `N³ Z¹` from the injective triples. -/
noncomputable def Toff {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (N : ℕ)
    (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N), bT ψ c X t.1 t.2.1 t.2.2 ω

/-- The summand with `v = i ≠ j`. -/
noncomputable def dT {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (i j : ℕ)
    (ω : Ω) : ℝ :=
  if i = j then 0 else ψ (X i ω - X j ω) * c (X j ω - X i ω)

/-- Two degenerate even kernels `ψ`, `c` for the same independent sample. -/
structure Deg3 {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) {G : Type*} [AddCommGroup G]
    [MeasurableSpace G] (ν : Measure G) (X : ℕ → Ω → G) (ψ c : G → ℝ) (Bψ Bc Vψ Vc : ℝ) :
    Prop where
  hψ : Deg2 μ ν X ψ Bψ Vψ
  hc : Deg2 μ ν X c Bc Vc

/-- The decomposition of the full triple sum into the injective part and the three diagonals. -/
theorem triple_eq {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
        ψ (X i ω - X j ω) * c (X j ω - X v ω)
      = Toff ψ c X N ω
        + ψ 0 * (∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω))
        + c 0 * Soff ψ X N ω
        + ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, dT ψ c X i j ω := by
  have hrow : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N,
      ∑ v ∈ Finset.range N, ψ (X i ω - X j ω) * c (X j ω - X v ω)
        = ∑ v ∈ Finset.range N, bT ψ c X i j v ω
          + (if i = j then ψ 0 * ∑ v ∈ Finset.range N, c (X i ω - X v ω) else 0)
          + c 0 * aT ψ X i j ω + dT ψ c X i j ω := by
    intro i hi j hj
    by_cases hij : i = j
    · have hb : ∀ v ∈ Finset.range N, bT ψ c X i j v ω = 0 := fun v _ => by
        unfold bT; rw [if_pos (Or.inl hij)]
      rw [Finset.sum_congr rfl hb, if_pos hij]
      unfold aT dT
      rw [if_pos hij, if_pos hij]
      subst hij
      simp [Finset.mul_sum]
    · have hv : ∀ v ∈ Finset.range N, ψ (X i ω - X j ω) * c (X j ω - X v ω)
          = bT ψ c X i j v ω + (if v = j then ψ (X i ω - X j ω) * c 0 else 0)
            + (if v = i then ψ (X i ω - X j ω) * c (X j ω - X i ω) else 0) := by
        intro v _
        unfold bT aP
        by_cases hvj : v = j
        · rw [if_pos (Or.inr (Or.inl hvj.symm)), if_pos hvj,
            if_neg (fun q : v = i => hij (q.symm.trans hvj)), hvj, sub_self]
          ring
        · by_cases hvi : v = i
          · rw [if_pos (Or.inr (Or.inr hvi.symm)), if_neg hvj, if_pos hvi, hvi]
            ring
          · have hno : ¬ (i = j ∨ j = v ∨ i = v) := by
              rintro (q | q | q)
              · exact hij q
              · exact hvj q.symm
              · exact hvi q.symm
            rw [if_neg hno, if_neg hvj, if_neg hvi]
            ring
      rw [Finset.sum_congr rfl hv, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos hj, if_pos hi, if_neg hij]
      unfold aT dT
      rw [if_neg hij, if_neg hij]
      ring
  have hite : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (if i = j then ψ 0 * ∑ v ∈ Finset.range N, c (X i ω - X v ω) else 0)
      = ψ 0 * ∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq, if_pos hi]
  have hT : Toff ψ c X N ω
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N, bT ψ c X i j v ω :=
    sum_R3 N (fun t => bT ψ c X t.1 t.2.1 t.2.2 ω)
  rw [hT, Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hrow i hi j hj]
  unfold Soff
  simp only [Finset.sum_add_distrib]
  rw [hite]
  simp only [Finset.mul_sum]

/-- The full double sum is the off-diagonal part plus `N ψ(0)`. -/
theorem full_eq2 {Ω G : Type*} [AddCommGroup G] (ψ : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
      = Soff ψ X N ω + N * ψ 0 := by
  have h : ∀ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
      = ∑ j ∈ Finset.range N, aT ψ X i j ω + ψ 0 := by
    intro i hi
    have h' : ∀ j ∈ Finset.range N, ψ (X i ω - X j ω)
        = aT ψ X i j ω + (if j = i then ψ 0 else 0) := by
      intro j _
      unfold aT
      by_cases hji : j = i
      · rw [hji]; simp
      · rw [if_neg (fun h'' : i = j => hji h''.symm), if_neg hji, add_zero]
    rw [Finset.sum_congr rfl h', Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hi]
  unfold Soff
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  simp

namespace Deg2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ : G → ℝ} {B V : ℝ}

theorem Soff_meas (H : Deg2 μ ν X ψ B V) (N : ℕ) : Measurable (Soff ψ X N) :=
  Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => H.aT_meas i j

theorem Soff_bdd (H : Deg2 μ ν X ψ B V) (N : ℕ) (ω : Ω) :
    |Soff ψ X N ω| ≤ ∑ _i ∈ Finset.range N, ∑ _j ∈ Finset.range N, B :=
  calc |Soff ψ X N ω| ≤ ∑ i ∈ Finset.range N, |∑ j ∈ Finset.range N, aT ψ X i j ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, |aT ψ X i j ω| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range N, ∑ _j ∈ Finset.range N, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => H.aT_bound i j ω

/-- `E|∑_{i ≠ j} ψ(X_i - X_j)| ≤ N √(2V)`. -/
theorem Soff_abs_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (N : ℕ) : ∫ ω, |Soff ψ X N ω| ∂μ ≤ N * Real.sqrt (2 * V) := by
  have h := abs_integral_le_sqrt (Soff ψ X N) (H.Soff_meas N) (H.Soff_bdd N) (H.second_moment N)
  have e : Real.sqrt (2 * (N : ℝ) ^ 2 * V) = N * Real.sqrt (2 * V) := by
    rw [show 2 * (N : ℝ) ^ 2 * V = (N : ℝ) ^ 2 * (2 * V) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg N)]
  rw [e] at h; exact h

/-- Integrability of the full double sum. -/
theorem full_integrable [IsFiniteMeasure μ] (H : Deg2 μ ν X ψ B V) (N : ℕ) :
    Integrable (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) μ :=
  integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    bdd_integrable _ (H.psi_meas.comp ((H.meas i).sub (H.meas j))) (fun ω => H.bound _)

/-- `E|∑_{i,j} ψ(X_i - X_j)| ≤ N √(2V) + N |ψ(0)|` (all pairs). -/
theorem full_abs_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (N : ℕ) :
    ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)| ∂μ
      ≤ N * Real.sqrt (2 * V) + N * |ψ 0| := by
  have iS : Integrable (fun ω => |Soff ψ X N ω|) μ :=
    (bdd_integrable _ (H.Soff_meas N) (H.Soff_bdd N)).abs
  have i2 : Integrable (fun ω => |Soff ψ X N ω| + N * |ψ 0|) μ := iS.add (integrable_const _)
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)|
      ≤ |Soff ψ X N ω| + N * |ψ 0| := by
    intro ω
    rw [full_eq2 ψ X N ω]
    calc |Soff ψ X N ω + N * ψ 0| ≤ |Soff ψ X N ω| + |(N : ℝ) * ψ 0| := abs_add_le _ _
      _ = |Soff ψ X N ω| + N * |ψ 0| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  calc ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)| ∂μ
      ≤ ∫ ω, (|Soff ψ X N ω| + N * |ψ 0|) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _) i2
          (Filter.Eventually.of_forall hpt)
    _ = ∫ ω, |Soff ψ X N ω| ∂μ + N * |ψ 0| := by
        rw [integral_add iS (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ N * Real.sqrt (2 * V) + N * |ψ 0| := by linarith [H.Soff_abs_le N]

end Deg2

namespace Deg3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ c : G → ℝ}
  {Bψ Bc Vψ Vc : ℝ}

theorem aP_meas (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j v : ℕ) : Measurable (aP ψ c X i j v) := by
  unfold aP
  exact (H.hψ.psi_meas.comp ((H.hψ.meas i).sub (H.hψ.meas j))).mul
    (H.hc.psi_meas.comp ((H.hψ.meas j).sub (H.hψ.meas v)))

theorem aP_bound (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j v : ℕ) (ω : Ω) :
    |aP ψ c X i j v ω| ≤ Bψ * Bc := by
  unfold aP
  rw [abs_mul]
  exact mul_le_mul (H.hψ.bound _) (H.hc.bound _) (abs_nonneg _) H.hψ.B_nonneg

theorem bT_meas (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j v : ℕ) : Measurable (bT ψ c X i j v) := by
  unfold bT
  by_cases h : i = j ∨ j = v ∨ i = v
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact H.aP_meas i j v

theorem bT_bound (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j v : ℕ) (ω : Ω) :
    |bT ψ c X i j v ω| ≤ Bψ * Bc := by
  unfold bT
  split_ifs
  · rw [abs_zero]; exact mul_nonneg H.hψ.B_nonneg H.hc.B_nonneg
  · exact H.aP_bound i j v ω

/-- The first index of the first factor is free: the mean vanishes (`ψ` is degenerate). -/
theorem free_i [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {i j v a b e : ℕ} (hj : i ≠ j) (hv : i ≠ v) (ha : i ≠ a)
    (hb : i ≠ b) (he : i ≠ e) :
    ∫ ω, aP ψ c X i j v ω * aP ψ c X a b e ω ∂μ = 0 := by
  have hψm := H.hψ.psi_meas
  have hcm := H.hc.psi_meas
  have q0 : Measurable fun p : G × (G × G × G × G × G) => p.1 := measurable_fst
  have q1 : Measurable fun p : G × (G × G × G × G × G) => p.2.1 := measurable_snd.fst
  have q2 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.1 := measurable_snd.snd.fst
  have q3 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.2.1 :=
    measurable_snd.snd.snd.fst
  have q4 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.2.2.1 :=
    measurable_snd.snd.snd.snd.fst
  have q5 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.2.2.2 :=
    measurable_snd.snd.snd.snd.snd
  exact indep_integral_zero ν (X i) (fun ω => (X j ω, X v ω, X a ω, X b ω, X e ω)) (H.hψ.meas i)
    ((H.hψ.meas j).prodMk ((H.hψ.meas v).prodMk ((H.hψ.meas a).prodMk
      ((H.hψ.meas b).prodMk (H.hψ.meas e)))))
    (indep_five X H.hψ.indep H.hψ.meas hj hv ha hb he) (H.hψ.law i)
    (fun p : G × (G × G × G × G × G) => ψ (p.1 - p.2.1) * c (p.2.1 - p.2.2.1)
      * (ψ (p.2.2.2.1 - p.2.2.2.2.1) * c (p.2.2.2.2.1 - p.2.2.2.2.2)))
    (((hψm.comp (q0.sub q1)).mul (hcm.comp (q1.sub q2))).mul
      ((hψm.comp (q3.sub q4)).mul (hcm.comp (q4.sub q5))))
    (B := Bψ * Bc * (Bψ * Bc))
    (fun p => abs4 (H.hψ.bound _) (H.hc.bound _) (H.hψ.bound _) (H.hc.bound _)
      H.hψ.B_nonneg H.hc.B_nonneg)
    (fun y => by
      show ∫ z, ψ (z - y.1) * c (y.1 - y.2.1)
        * (ψ (y.2.2.1 - y.2.2.2.1) * c (y.2.2.2.1 - y.2.2.2.2)) ∂ν = 0
      have e' : (fun z => ψ (z - y.1) * c (y.1 - y.2.1)
            * (ψ (y.2.2.1 - y.2.2.2.1) * c (y.2.2.2.1 - y.2.2.2.2)))
          = fun z => ψ (y.1 - z) * (c (y.1 - y.2.1)
            * (ψ (y.2.2.1 - y.2.2.2.1) * c (y.2.2.2.1 - y.2.2.2.2))) := by
        funext z
        have h : ψ (z - y.1) = ψ (y.1 - z) := by rw [← H.hψ.even, neg_sub]
        rw [h]; ring
      rw [e', integral_mul_const, H.hψ.mean, zero_mul])

/-- The last index of the first factor is free: the mean vanishes (`c` is degenerate). -/
theorem free_v [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {i j v a b e : ℕ} (hi : v ≠ i) (hj : v ≠ j) (ha : v ≠ a)
    (hb : v ≠ b) (he : v ≠ e) :
    ∫ ω, aP ψ c X i j v ω * aP ψ c X a b e ω ∂μ = 0 := by
  have hψm := H.hψ.psi_meas
  have hcm := H.hc.psi_meas
  have q0 : Measurable fun p : G × (G × G × G × G × G) => p.1 := measurable_fst
  have q1 : Measurable fun p : G × (G × G × G × G × G) => p.2.1 := measurable_snd.fst
  have q2 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.1 := measurable_snd.snd.fst
  have q3 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.2.1 :=
    measurable_snd.snd.snd.fst
  have q4 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.2.2.1 :=
    measurable_snd.snd.snd.snd.fst
  have q5 : Measurable fun p : G × (G × G × G × G × G) => p.2.2.2.2.2 :=
    measurable_snd.snd.snd.snd.snd
  exact indep_integral_zero ν (X v) (fun ω => (X i ω, X j ω, X a ω, X b ω, X e ω)) (H.hψ.meas v)
    ((H.hψ.meas i).prodMk ((H.hψ.meas j).prodMk ((H.hψ.meas a).prodMk
      ((H.hψ.meas b).prodMk (H.hψ.meas e)))))
    (indep_five X H.hψ.indep H.hψ.meas hi hj ha hb he) (H.hψ.law v)
    (fun p : G × (G × G × G × G × G) => ψ (p.2.1 - p.2.2.1) * c (p.2.2.1 - p.1)
      * (ψ (p.2.2.2.1 - p.2.2.2.2.1) * c (p.2.2.2.2.1 - p.2.2.2.2.2)))
    (((hψm.comp (q1.sub q2)).mul (hcm.comp (q2.sub q0))).mul
      ((hψm.comp (q3.sub q4)).mul (hcm.comp (q4.sub q5))))
    (B := Bψ * Bc * (Bψ * Bc))
    (fun p => abs4 (H.hψ.bound _) (H.hc.bound _) (H.hψ.bound _) (H.hc.bound _)
      H.hψ.B_nonneg H.hc.B_nonneg)
    (fun y => by
      show ∫ z, ψ (y.1 - y.2.1) * c (y.2.1 - z)
        * (ψ (y.2.2.1 - y.2.2.2.1) * c (y.2.2.2.1 - y.2.2.2.2)) ∂ν = 0
      have e' : (fun z => ψ (y.1 - y.2.1) * c (y.2.1 - z)
            * (ψ (y.2.2.1 - y.2.2.2.1) * c (y.2.2.2.1 - y.2.2.2.2)))
          = fun z => c (y.2.1 - z) * (ψ (y.1 - y.2.1)
            * (ψ (y.2.2.1 - y.2.2.2.1) * c (y.2.2.2.1 - y.2.2.2.2))) := by
        funext z; ring
      rw [e', integral_mul_const, H.hc.mean, zero_mul])

/-- `E (ψ(X_i - X_j) c(X_j - X_v))² ≤ V_ψ V_c` for an injective triple. -/
theorem aP_sq_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {i j v : ℕ} (hij : i ≠ j) (hjv : j ≠ v) (hiv : i ≠ v) :
    ∫ ω, aP ψ c X i j v ω ^ 2 ∂μ ≤ Vψ * Vc := by
  have hψm := H.hψ.psi_meas
  have hcm := H.hc.psi_meas
  have r0 : Measurable fun p : G × (G × G) => p.1 := measurable_fst
  have r1 : Measurable fun p : G × (G × G) => p.2.1 := measurable_snd.fst
  have r2 : Measurable fun p : G × (G × G) => p.2.2 := measurable_snd.snd
  have h1 : ∫ ω, aP ψ c X i j v ω ^ 2 ∂μ ≤ ∫ ω, Vc * ψ (X i ω - X j ω) ^ 2 ∂μ :=
    indep_integral_le_fun ν (X v) (fun ω => (X i ω, X j ω)) (H.hψ.meas v)
      ((H.hψ.meas i).prodMk (H.hψ.meas j))
      (indep_two X H.hψ.indep H.hψ.meas hiv.symm hjv.symm) (H.hψ.law v)
      (fun p : G × (G × G) => (ψ (p.2.1 - p.2.2) * c (p.2.2 - p.1)) ^ 2)
      (((hψm.comp (r1.sub r2)).mul (hcm.comp (r2.sub r0))).pow_const 2)
      (B := (Bψ * Bc) ^ 2) (Bg := Vc * Bψ ^ 2)
      (fun p => by
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        rw [abs_mul]
        exact mul_le_mul (H.hψ.bound _) (H.hc.bound _) (abs_nonneg _) H.hψ.B_nonneg)
      (fun y : G × G => Vc * ψ (y.1 - y.2) ^ 2)
      (((hψm.comp (measurable_fst.sub measurable_snd)).pow_const 2).const_mul Vc)
      (fun y => by
        rw [abs_mul, abs_of_nonneg H.hc.V_nonneg, abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (H.hψ.bound _) 2)
          H.hc.V_nonneg)
      (fun y => by
        show ∫ z, (ψ (y.1 - y.2) * c (y.2 - z)) ^ 2 ∂ν ≤ Vc * ψ (y.1 - y.2) ^ 2
        have e' : (fun z => (ψ (y.1 - y.2) * c (y.2 - z)) ^ 2)
            = fun z => ψ (y.1 - y.2) ^ 2 * c (y.2 - z) ^ 2 := by funext z; ring
        rw [e', integral_const_mul]
        calc ψ (y.1 - y.2) ^ 2 * ∫ z, c (y.2 - z) ^ 2 ∂ν ≤ ψ (y.1 - y.2) ^ 2 * Vc :=
              mul_le_mul_of_nonneg_left (H.hc.var _) (_root_.sq_nonneg _)
          _ = Vc * ψ (y.1 - y.2) ^ 2 := mul_comm _ _)
  calc ∫ ω, aP ψ c X i j v ω ^ 2 ∂μ ≤ ∫ ω, Vc * ψ (X i ω - X j ω) ^ 2 ∂μ := h1
    _ = Vc * ∫ ω, ψ (X i ω - X j ω) ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ Vc * Vψ := mul_le_mul_of_nonneg_left (H.hψ.sq_le hij) H.hc.V_nonneg
    _ = Vψ * Vc := mul_comm _ _

/-- **The mean of a product of two injective summands** vanishes unless the first and the last
    index of the first triple both occur in the second, and is at most `V_ψ V_c` then. -/
theorem pair3_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j v a b e : ℕ) :
    ∫ ω, bT ψ c X i j v ω * bT ψ c X a b e ω ∂μ
      ≤ Vψ * Vc * ((if i = a ∧ v = b then (1 : ℝ) else 0) + (if i = a ∧ v = e then (1 : ℝ) else 0)
          + (if i = b ∧ v = a then (1 : ℝ) else 0) + (if i = b ∧ v = e then (1 : ℝ) else 0)
          + (if i = e ∧ v = a then (1 : ℝ) else 0) + (if i = e ∧ v = b then (1 : ℝ) else 0)) := by
  have hW0 : 0 ≤ Vψ * Vc := mul_nonneg H.hψ.V_nonneg H.hc.V_nonneg
  have t1 : (0 : ℝ) ≤ (if i = a ∧ v = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t2 : (0 : ℝ) ≤ (if i = a ∧ v = e then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t3 : (0 : ℝ) ≤ (if i = b ∧ v = a then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t4 : (0 : ℝ) ≤ (if i = b ∧ v = e then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t5 : (0 : ℝ) ≤ (if i = e ∧ v = a then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t6 : (0 : ℝ) ≤ (if i = e ∧ v = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hR : 0 ≤ Vψ * Vc * ((if i = a ∧ v = b then (1 : ℝ) else 0)
      + (if i = a ∧ v = e then (1 : ℝ) else 0)
      + (if i = b ∧ v = a then (1 : ℝ) else 0) + (if i = b ∧ v = e then (1 : ℝ) else 0)
      + (if i = e ∧ v = a then (1 : ℝ) else 0) + (if i = e ∧ v = b then (1 : ℝ) else 0)) :=
    mul_nonneg hW0 (by linarith)
  by_cases h : i = j ∨ j = v ∨ i = v
  · have hz : (fun ω => bT ψ c X i j v ω * bT ψ c X a b e ω) = fun _ => (0 : ℝ) := by
      funext ω; unfold bT; rw [if_pos h, zero_mul]
    rw [hz, integral_zero]; exact hR
  by_cases h' : a = b ∨ b = e ∨ a = e
  · have hz : (fun ω => bT ψ c X i j v ω * bT ψ c X a b e ω) = fun _ => (0 : ℝ) := by
      funext ω; unfold bT; rw [if_pos h', mul_zero]
    rw [hz, integral_zero]; exact hR
  have hA : (fun ω => bT ψ c X i j v ω * bT ψ c X a b e ω)
      = fun ω => aP ψ c X i j v ω * aP ψ c X a b e ω := by
    funext ω; unfold bT; rw [if_neg h, if_neg h']
  rw [hA]
  have hij : i ≠ j := fun q => h (Or.inl q)
  have hjv : j ≠ v := fun q => h (Or.inr (Or.inl q))
  have hiv : i ≠ v := fun q => h (Or.inr (Or.inr q))
  have hab : a ≠ b := fun q => h' (Or.inl q)
  have hbe : b ≠ e := fun q => h' (Or.inr (Or.inl q))
  have hae : a ≠ e := fun q => h' (Or.inr (Or.inr q))
  by_cases f1 : i ≠ a ∧ i ≠ b ∧ i ≠ e
  · rw [H.free_i hij hiv f1.1 f1.2.1 f1.2.2]; exact hR
  by_cases f2 : v ≠ a ∧ v ≠ b ∧ v ≠ e
  · rw [H.free_v hiv.symm hjv.symm f2.1 f2.2.1 f2.2.2]; exact hR
  have hi : i = a ∨ i = b ∨ i = e := by omega
  have hv : v = a ∨ v = b ∨ v = e := by omega
  have hsum : 1 ≤ (if i = a ∧ v = b then (1 : ℝ) else 0) + (if i = a ∧ v = e then (1 : ℝ) else 0)
      + (if i = b ∧ v = a then (1 : ℝ) else 0) + (if i = b ∧ v = e then (1 : ℝ) else 0)
      + (if i = e ∧ v = a then (1 : ℝ) else 0) + (if i = e ∧ v = b then (1 : ℝ) else 0) := by
    rcases hi with hi | hi | hi <;> rcases hv with hv | hv | hv <;>
      first
        | exact absurd (hi.trans hv.symm) hiv
        | (rw [if_pos (And.intro hi hv)]; linarith)
  refine le_trans ?_ (le_mul_of_one_le_right hW0 hsum)
  have s1 := H.aP_sq_le hij hjv hiv
  have s2 := H.aP_sq_le hab hbe hae
  have m1 := H.aP_meas i j v
  have m2 := H.aP_meas a b e
  have hBB : 0 ≤ Bψ * Bc := mul_nonneg H.hψ.B_nonneg H.hc.B_nonneg
  have i1 : Integrable (fun ω => aP ψ c X i j v ω ^ 2) μ :=
    bdd_integrable _ (m1.pow_const 2) (B := (Bψ * Bc) ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (H.aP_bound i j v ω) 2)
  have i2 : Integrable (fun ω => aP ψ c X a b e ω ^ 2) μ :=
    bdd_integrable _ (m2.pow_const 2) (B := (Bψ * Bc) ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (H.aP_bound a b e ω) 2)
  have i12 : Integrable (fun ω => aP ψ c X i j v ω * aP ψ c X a b e ω) μ :=
    bdd_integrable _ (m1.mul m2) (B := Bψ * Bc * (Bψ * Bc)) (fun ω => by
      rw [abs_mul]
      exact mul_le_mul (H.aP_bound i j v ω) (H.aP_bound a b e ω) (abs_nonneg _) hBB)
  have i3 : Integrable (fun ω => (aP ψ c X i j v ω ^ 2 + aP ψ c X a b e ω ^ 2) / 2) μ :=
    (i1.add i2).div_const 2
  calc ∫ ω, aP ψ c X i j v ω * aP ψ c X a b e ω ∂μ
      ≤ ∫ ω, (aP ψ c X i j v ω ^ 2 + aP ψ c X a b e ω ^ 2) / 2 ∂μ :=
        integral_mono i12 i3 (fun ω => by
          have := _root_.sq_nonneg (aP ψ c X i j v ω - aP ψ c X a b e ω)
          show aP ψ c X i j v ω * aP ψ c X a b e ω
            ≤ (aP ψ c X i j v ω ^ 2 + aP ψ c X a b e ω ^ 2) / 2
          nlinarith)
    _ = (∫ ω, aP ψ c X i j v ω ^ 2 ∂μ + ∫ ω, aP ψ c X a b e ω ^ 2 ∂μ) / 2 := by
        rw [integral_div, integral_add i1 i2]
    _ ≤ Vψ * Vc := by linarith

theorem Toff_meas (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N : ℕ) : Measurable (Toff ψ c X N) :=
  Finset.measurable_sum _ fun t _ => H.bT_meas t.1 t.2.1 t.2.2

theorem Toff_bdd (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N : ℕ) (ω : Ω) :
    |Toff ψ c X N ω|
      ≤ ∑ _t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N), Bψ * Bc :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun t _ => H.bT_bound t.1 t.2.1 t.2.2 ω)

/-- **Second moment of the injective part**: `E (∑_{i,j,v distinct} ψ c)² ≤ 6 N⁴ V_ψ V_c`. -/
theorem second_moment3 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N : ℕ) :
    ∫ ω, Toff ψ c X N ω ^ 2 ∂μ ≤ 6 * (N : ℝ) ^ 4 * (Vψ * Vc) := by
  have hBB : 0 ≤ Bψ * Bc := mul_nonneg H.hψ.B_nonneg H.hc.B_nonneg
  have hS2 : ∀ ω, Toff ψ c X N ω ^ 2
      = ∑ t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
          ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            bT ψ c X t.1 t.2.1 t.2.2 ω * bT ψ c X t'.1 t'.2.1 t'.2.2 ω := by
    intro ω
    unfold Toff
    rw [pow_two, Finset.sum_mul_sum]
  have hI : ∀ t t' : ℕ × ℕ × ℕ, Integrable
      (fun ω => bT ψ c X t.1 t.2.1 t.2.2 ω * bT ψ c X t'.1 t'.2.1 t'.2.2 ω) μ := fun t t' =>
    bdd_integrable _ ((H.bT_meas _ _ _).mul (H.bT_meas _ _ _)) (B := Bψ * Bc * (Bψ * Bc))
      (fun ω => by
        rw [abs_mul]
        exact mul_le_mul (H.bT_bound _ _ _ ω) (H.bT_bound _ _ _ ω) (abs_nonneg _) hBB)
  have h2 : ∫ ω, ∑ t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
          ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            bT ψ c X t.1 t.2.1 t.2.2 ω * bT ψ c X t'.1 t'.2.1 t'.2.2 ω ∂μ
      = ∑ t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
          ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            ∫ ω, bT ψ c X t.1 t.2.1 t.2.2 ω * bT ψ c X t'.1 t'.2.1 t'.2.2 ω ∂μ := by
    rw [integral_finset_sum _ (fun t _ => integrable_finset_sum _ fun t' _ => hI t t')]
    exact Finset.sum_congr rfl fun t _ => integral_finset_sum _ (fun t' _ => hI t t')
  simp_rw [hS2]
  rw [h2]
  calc ∑ t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
          ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            ∫ ω, bT ψ c X t.1 t.2.1 t.2.2 ω * bT ψ c X t'.1 t'.2.1 t'.2.2 ω ∂μ
      ≤ ∑ t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
          ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            Vψ * Vc * ((if t.1 = t'.1 ∧ t.2.2 = t'.2.1 then (1 : ℝ) else 0)
              + (if t.1 = t'.1 ∧ t.2.2 = t'.2.2 then (1 : ℝ) else 0)
              + (if t.1 = t'.2.1 ∧ t.2.2 = t'.1 then (1 : ℝ) else 0)
              + (if t.1 = t'.2.1 ∧ t.2.2 = t'.2.2 then (1 : ℝ) else 0)
              + (if t.1 = t'.2.2 ∧ t.2.2 = t'.1 then (1 : ℝ) else 0)
              + (if t.1 = t'.2.2 ∧ t.2.2 = t'.2.1 then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun t' _ =>
          H.pair3_le t.1 t.2.1 t.2.2 t'.1 t'.2.1 t'.2.2
    _ = ∑ _t ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
          Vψ * Vc * ((N : ℝ) + N + N + N + N + N) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hp : t.1 ∈ Finset.range N := (Finset.mem_product.mp ht).1
        have hq : t.2.2 ∈ Finset.range N :=
          (Finset.mem_product.mp (Finset.mem_product.mp ht).2).2
        have k1 : ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            (if t.1 = t'.1 ∧ t.2.2 = t'.2.1 then (1 : ℝ) else 0) = N :=
          (sum_R3 N _).trans (c_ab N t.1 t.2.2 hp hq)
        have k2 : ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            (if t.1 = t'.1 ∧ t.2.2 = t'.2.2 then (1 : ℝ) else 0) = N :=
          (sum_R3 N _).trans (c_ae N t.1 t.2.2 hp hq)
        have k3 : ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            (if t.1 = t'.2.1 ∧ t.2.2 = t'.1 then (1 : ℝ) else 0) = N :=
          (sum_R3 N _).trans (c_ba N t.1 t.2.2 hp hq)
        have k4 : ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            (if t.1 = t'.2.1 ∧ t.2.2 = t'.2.2 then (1 : ℝ) else 0) = N :=
          (sum_R3 N _).trans (c_be N t.1 t.2.2 hp hq)
        have k5 : ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            (if t.1 = t'.2.2 ∧ t.2.2 = t'.1 then (1 : ℝ) else 0) = N :=
          (sum_R3 N _).trans (c_ea N t.1 t.2.2 hp hq)
        have k6 : ∑ t' ∈ Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N),
            (if t.1 = t'.2.2 ∧ t.2.2 = t'.2.1 then (1 : ℝ) else 0) = N :=
          (sum_R3 N _).trans (c_eb N t.1 t.2.2 hp hq)
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib]
        rw [k1, k2, k3, k4, k5, k6]
    _ = 6 * (N : ℝ) ^ 4 * (Vψ * Vc) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_product, Finset.card_range,
          nsmul_eq_mul]
        push_cast; ring

/-- `E|∑_{i,j,v distinct} ψ c| ≤ N² √(6 V_ψ V_c)`. -/
theorem Toff_abs_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N : ℕ) :
    ∫ ω, |Toff ψ c X N ω| ∂μ ≤ (N : ℝ) ^ 2 * Real.sqrt (6 * (Vψ * Vc)) := by
  have h := abs_integral_le_sqrt (Toff ψ c X N) (H.Toff_meas N) (H.Toff_bdd N)
    (H.second_moment3 N)
  have e' : Real.sqrt (6 * (N : ℝ) ^ 4 * (Vψ * Vc))
      = (N : ℝ) ^ 2 * Real.sqrt (6 * (Vψ * Vc)) := by
    rw [show 6 * (N : ℝ) ^ 4 * (Vψ * Vc) = ((N : ℝ) ^ 2) ^ 2 * (6 * (Vψ * Vc)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [e'] at h; exact h

theorem dT_meas (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j : ℕ) : Measurable (dT ψ c X i j) := by
  unfold dT
  by_cases h : i = j
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]
    exact (H.hψ.psi_meas.comp ((H.hψ.meas i).sub (H.hψ.meas j))).mul
      (H.hc.psi_meas.comp ((H.hψ.meas j).sub (H.hψ.meas i)))

theorem dT_bound (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j : ℕ) (ω : Ω) :
    |dT ψ c X i j ω| ≤ Bψ * Bc := by
  unfold dT
  split_ifs
  · rw [abs_zero]; exact mul_nonneg H.hψ.B_nonneg H.hc.B_nonneg
  · rw [abs_mul]
    exact mul_le_mul (H.hψ.bound _) (H.hc.bound _) (abs_nonneg _) H.hψ.B_nonneg

/-- `E|ψ(X_i - X_j) c(X_j - X_i)| ≤ B_c ‖ψ‖₁` for `i ≠ j`. -/
theorem dT_mean [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {Lψ : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ Lψ) (i j : ℕ) :
    ∫ ω, |dT ψ c X i j ω| ∂μ ≤ Bc * Lψ := by
  have hψm := H.hψ.psi_meas
  have hcm := H.hc.psi_meas
  have hL0 : 0 ≤ Lψ := le_trans (integral_nonneg fun z => abs_nonneg _) (hL 0)
  by_cases hij : i = j
  · have hz : (fun ω => |dT ψ c X i j ω|) = fun _ => (0 : ℝ) := by
      funext ω; unfold dT; rw [if_pos hij, abs_zero]
    rw [hz, integral_zero]; exact mul_nonneg H.hc.B_nonneg hL0
  have hA : (fun ω => |dT ψ c X i j ω|) = fun ω => |ψ (X i ω - X j ω) * c (X j ω - X i ω)| := by
    funext ω; unfold dT; rw [if_neg hij]
  rw [hA]
  exact indep_integral_le ν (X j) (X i) (H.hψ.meas j) (H.hψ.meas i)
    (H.hψ.indep.indepFun (Ne.symm hij)) (H.hψ.law j)
    (fun p : G × G => |ψ (p.2 - p.1) * c (p.1 - p.2)|)
    (continuous_abs.measurable.comp ((hψm.comp (measurable_snd.sub measurable_fst)).mul
      (hcm.comp (measurable_fst.sub measurable_snd))))
    (B := Bψ * Bc)
    (fun p => by
      rw [abs_abs, abs_mul]
      exact mul_le_mul (H.hψ.bound _) (H.hc.bound _) (abs_nonneg _) H.hψ.B_nonneg)
    (fun y => by
      show ∫ z, |ψ (y - z) * c (z - y)| ∂ν ≤ Bc * Lψ
      have i1 : Integrable (fun z => |ψ (y - z) * c (z - y)|) ν :=
        bdd_integrable _ (continuous_abs.measurable.comp
          ((hψm.comp (measurable_const.sub measurable_id)).mul
            (hcm.comp (measurable_id.sub measurable_const)))) (B := Bψ * Bc) (fun z => by
          rw [abs_abs, abs_mul]
          exact mul_le_mul (H.hψ.bound _) (H.hc.bound _) (abs_nonneg _) H.hψ.B_nonneg)
      have i2 : Integrable (fun z => Bc * |ψ (y - z)|) ν :=
        bdd_integrable _ ((continuous_abs.measurable.comp
          (hψm.comp (measurable_const.sub measurable_id))).const_mul Bc) (B := Bc * Bψ)
          (fun z => by
            rw [abs_mul, abs_abs, abs_of_nonneg H.hc.B_nonneg]
            exact mul_le_mul_of_nonneg_left (H.hψ.bound _) H.hc.B_nonneg)
      calc ∫ z, |ψ (y - z) * c (z - y)| ∂ν ≤ ∫ z, Bc * |ψ (y - z)| ∂ν :=
            integral_mono i1 i2 (fun z => by
              show |ψ (y - z) * c (z - y)| ≤ Bc * |ψ (y - z)|
              have e' : |ψ (y - z) * c (z - y)| = |c (z - y)| * |ψ (y - z)| := by
                rw [abs_mul, mul_comm]
              rw [e']
              exact mul_le_mul_of_nonneg_right (H.hc.bound _) (abs_nonneg _))
        _ = Bc * ∫ z, |ψ (y - z)| ∂ν := integral_const_mul _ _
        _ ≤ Bc * Lψ := mul_le_mul_of_nonneg_left (hL y) H.hc.B_nonneg)

/-- `E|∑_{i ≠ j} ψ(X_i - X_j) c(X_j - X_i)| ≤ N² B_c ‖ψ‖₁`. -/
theorem D_abs_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {Lψ : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ Lψ) (N : ℕ) :
    ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, dT ψ c X i j ω| ∂μ
      ≤ (N : ℝ) ^ 2 * (Bc * Lψ) := by
  have hI : ∀ i j, Integrable (fun ω => |dT ψ c X i j ω|) μ := fun i j =>
    (bdd_integrable _ (H.dT_meas i j) (H.dT_bound i j)).abs
  calc ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, dT ψ c X i j ω| ∂μ
      ≤ ∫ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, |dT ψ c X i j ω| ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
          (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hI i j)
          (Filter.Eventually.of_forall fun ω =>
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∫ ω, |dT ψ c X i j ω| ∂μ := by
        rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hI i j)]
        exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ (fun j _ => hI i j)
    _ ≤ ∑ _i ∈ Finset.range N, ∑ _j ∈ Finset.range N, Bc * Lψ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => H.dT_mean hL i j
    _ = (N : ℝ) ^ 2 * (Bc * Lψ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem triple_integrable [IsFiniteMeasure μ] (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N : ℕ) :
    Integrable (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
      ψ (X i ω - X j ω) * c (X j ω - X v ω)) μ :=
  integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun v _ => bdd_integrable _ (H.aP_meas i j v) (H.aP_bound i j v)

/-- **The mean of `|∑_{i,j,v} ψ(X_i - X_j) c(X_j - X_v)|`** (all triples): injective part by the
    second moment, the three diagonals separately. -/
theorem triple_abs_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {Lψ : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ Lψ) (N : ℕ) :
    ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
        ψ (X i ω - X j ω) * c (X j ω - X v ω)| ∂μ
      ≤ (N : ℝ) ^ 2 * Real.sqrt (6 * (Vψ * Vc))
        + |ψ 0| * (N * Real.sqrt (2 * Vc) + N * |c 0|)
        + |c 0| * (N * Real.sqrt (2 * Vψ)) + (N : ℝ) ^ 2 * (Bc * Lψ) := by
  have iT : Integrable (fun ω => |Toff ψ c X N ω|) μ :=
    (bdd_integrable _ (H.Toff_meas N) (H.Toff_bdd N)).abs
  have iC : Integrable (fun ω => |ψ 0|
      * |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)|) μ :=
    ((H.hc.full_integrable N).abs).const_mul _
  have iS : Integrable (fun ω => |c 0| * |Soff ψ X N ω|) μ :=
    ((bdd_integrable _ (H.hψ.Soff_meas N) (H.hψ.Soff_bdd N)).abs).const_mul _
  have iD : Integrable (fun ω => |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      dT ψ c X i j ω|) μ :=
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      bdd_integrable _ (H.dT_meas i j) (H.dT_bound i j)).abs
  have i12 : Integrable (fun ω => |Toff ψ c X N ω| + |ψ 0|
      * |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)|) μ := iT.add iC
  have i123 : Integrable (fun ω => |Toff ψ c X N ω| + |ψ 0|
      * |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)|
      + |c 0| * |Soff ψ X N ω|) μ := i12.add iS
  have i1234 : Integrable (fun ω => |Toff ψ c X N ω| + |ψ 0|
      * |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)|
      + |c 0| * |Soff ψ X N ω|
      + |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, dT ψ c X i j ω|) μ := i123.add iD
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
        ψ (X i ω - X j ω) * c (X j ω - X v ω)|
      ≤ |Toff ψ c X N ω| + |ψ 0|
          * |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)|
        + |c 0| * |Soff ψ X N ω|
        + |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, dT ψ c X i j ω| := by
    intro ω
    rw [triple_eq ψ c X N ω, ← abs_mul, ← abs_mul]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  have hC : ∫ ω, |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)| ∂μ
      ≤ N * Real.sqrt (2 * Vc) + N * |c 0| := H.hc.full_abs_le N
  have hS := H.hψ.Soff_abs_le N
  have hT := H.Toff_abs_le N
  have hD := H.D_abs_le hL N
  calc ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
          ψ (X i ω - X j ω) * c (X j ω - X v ω)| ∂μ
      ≤ ∫ ω, (|Toff ψ c X N ω| + |ψ 0|
            * |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)|
          + |c 0| * |Soff ψ X N ω|
          + |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, dT ψ c X i j ω|) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _) i1234
          (Filter.Eventually.of_forall hpt)
    _ = ∫ ω, |Toff ψ c X N ω| ∂μ
          + |ψ 0| * ∫ ω, |∑ i ∈ Finset.range N, ∑ v ∈ Finset.range N, c (X i ω - X v ω)| ∂μ
          + |c 0| * ∫ ω, |Soff ψ X N ω| ∂μ
          + ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, dT ψ c X i j ω| ∂μ := by
        rw [integral_add i123 iD, integral_add i12 iS, integral_add iT iC, integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left hC (abs_nonneg (ψ 0))
        have h2 := mul_le_mul_of_nonneg_left hS (abs_nonneg (c 0))
        linarith

end Deg3

/-! ## Stage 3 on the torus: both statistics of the last term of `Π_k` -/

/-- `c(u) = p(u) - 1`. -/
noncomputable def cK (d : ℕ) (σ : ℝ) (u : FlatTorus d) : ℝ := pker d σ u - 1

theorem torusM_one_ge {σ : ℝ} (hσ : 0 < σ) (d : ℕ) : 1 ≤ torusM d σ 1 := by
  rw [torusM_one]; exact heatTorus_zero_ge_one (by positivity) d

theorem cK_even (d : ℕ) (σ : ℝ) (u : FlatTorus d) : cK d σ (-u) = cK d σ u := by
  unfold cK pker
  rw [heatTorus_even]

theorem cK_facts {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (u : FlatTorus d) :
    |cK d σ u| ≤ torusM d σ 1 ∧ cK d σ u ^ 2 ≤ (torusM d σ 1 - 2) * pker d σ u + 1 := by
  have h0 : 0 ≤ pker d σ u := heatTorus_nonneg (by positivity) d u
  have h1 : pker d σ u ≤ torusM d σ 1 := by
    rw [torusM_one]; exact heatTorus_le_zero (by positivity) d u
  have hM := torusM_one_ge hσ d
  have h2 := mul_nonneg h0 (sub_nonneg.mpr h1)
  unfold cK
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  nlinarith

/-- `∫ c(x - z)² dz ≤ M`. -/
theorem cK_var {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (x : FlatTorus d) :
    ∫ z, cK d σ (x - z) ^ 2 ∂flatTorusMeasure d ≤ torusM d σ 1 := by
  have hKc : Continuous fun z : FlatTorus d => pker d σ (x - z) :=
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  have hcc : Continuous fun z : FlatTorus d => cK d σ (x - z) := hKc.sub continuous_const
  have i1 : Integrable (fun z : FlatTorus d => cK d σ (x - z) ^ 2) (flatTorusMeasure d) :=
    flat_integrable d _ (hcc.pow 2)
  have i2 : Integrable (fun z : FlatTorus d => (torusM d σ 1 - 2) * pker d σ (x - z))
      (flatTorusMeasure d) := (flat_integrable d _ hKc).const_mul _
  have i3 : Integrable (fun z : FlatTorus d => (torusM d σ 1 - 2) * pker d σ (x - z) + 1)
      (flatTorusMeasure d) := i2.add (integrable_const _)
  calc ∫ z, cK d σ (x - z) ^ 2 ∂flatTorusMeasure d
      ≤ ∫ z, ((torusM d σ 1 - 2) * pker d σ (x - z) + 1) ∂flatTorusMeasure d :=
        integral_mono i1 i3 (fun z => (cK_facts hσ d (x - z)).2)
    _ = (torusM d σ 1 - 2) * 1 + 1 := by
        rw [integral_add i2 (integrable_const _), integral_const_mul, pker_mass hσ d x,
          integral_const, probReal_univ, one_smul]
    _ ≤ torusM d σ 1 := by linarith

theorem psiK_split (d : ℕ) (σ : ℝ) (k : ℕ) (hk : 1 ≤ k) (x z : FlatTorus d) :
    psiK d σ k (x - z)
      = pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
        - torusM d σ (k + 1) * pker d σ (x - z) := by
  have h1 : heatP d σ k (x - z) = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x) := by
    rw [heatP_of_ne d σ (by omega : k ≠ 0), ← neg_sub z x, heatTorus_even]
  unfold psiK
  rw [h1]; ring

/-- `∫ p p_k = m_{k+1}`. -/
theorem pk_integral {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    ∫ z, pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
      ∂flatTorusMeasure d = torusM d σ (k + 1) := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs : 0 < (k : ℝ) * σ := mul_pos hk' hσ
  refine (semigroup_all hσ hs d x x).trans ?_
  have hc : 2 * Real.pi ^ 2 * (σ + (k : ℝ) * σ) = 2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) * σ) := by
    push_cast; ring
  rw [sub_self, hc]
  rfl

/-- `‖Ψ‖₁ ≤ 2 m_k`. (The entry of the table of `lem:pibound` is the sharper `2 m_{k+1}`; only the
    weaker bound is proved here.) -/
theorem psi_l1 {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    ∫ z, |psiK d σ k (x - z)| ∂flatTorusMeasure d ≤ 2 * torusM d σ k := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := mul_pos (by positivity) (mul_pos hk' hσ)
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck1 : 0 < 2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) * σ) :=
    mul_pos (by positivity) (mul_pos hk1 hσ)
  have hKc : Continuous fun z : FlatTorus d => pker d σ (x - z) :=
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  have hGc : Continuous fun z : FlatTorus d =>
      heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x) :=
    (heatTorus_continuous hck d).comp (continuous_id.sub continuous_const)
  have hψc : Continuous fun z : FlatTorus d => psiK d σ k (x - z) :=
    (psiK_continuous hσ d k hk).comp (continuous_const.sub continuous_id)
  have i0 : Integrable (fun z : FlatTorus d => |psiK d σ k (x - z)|) (flatTorusMeasure d) :=
    flat_integrable d _ hψc.abs
  have i1 : Integrable (fun z : FlatTorus d =>
      pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x))
      (flatTorusMeasure d) := flat_integrable d _ (hKc.mul hGc)
  have i2 : Integrable (fun z : FlatTorus d => torusM d σ (k + 1) * pker d σ (x - z))
      (flatTorusMeasure d) := (flat_integrable d _ hKc).const_mul _
  have i3 : Integrable (fun z : FlatTorus d =>
      pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
        + torusM d σ (k + 1) * pker d σ (x - z)) (flatTorusMeasure d) := i1.add i2
  have hm3 : 0 ≤ torusM d σ (k + 1) := heatTorus_nonneg hck1 d 0
  have hm4 : torusM d σ (k + 1) ≤ torusM d σ k := torusM_anti hσ d hk (Nat.le_succ k)
  have hpt : ∀ z, |psiK d σ k (x - z)|
      ≤ pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
        + torusM d σ (k + 1) * pker d σ (x - z) := by
    intro z
    have p0 : 0 ≤ pker d σ (x - z) := heatTorus_nonneg hcσ d _
    have a1 : 0 ≤ pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x) :=
      mul_nonneg p0 (heatTorus_nonneg hck d _)
    have a2 : 0 ≤ torusM d σ (k + 1) * pker d σ (x - z) := mul_nonneg hm3 p0
    rw [psiK_split d σ k hk x z]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc ∫ z, |psiK d σ k (x - z)| ∂flatTorusMeasure d
      ≤ ∫ z, (pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
          + torusM d σ (k + 1) * pker d σ (x - z)) ∂flatTorusMeasure d :=
        integral_mono i0 i3 hpt
    _ = torusM d σ (k + 1) + torusM d σ (k + 1) * 1 := by
        rw [integral_add i1 i2, integral_const_mul, pker_mass hσ d x, pk_integral hσ d k hk x]
    _ ≤ 2 * torusM d σ k := by linarith

section Sample2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The hypotheses `Deg3` hold for `ψ_k` and `c` on the flat torus. -/
theorem torus_deg3 [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k) :
    Deg3 μ (flatTorusMeasure d) X (psiK d σ k) (cK d σ) (torusM d σ 1 * torusM d σ k)
      (torusM d σ 1) (torusM d σ 1 * torusM d σ k ^ 2) (torusM d σ 1) := by
  have hM1 := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  exact
    { hψ :=
        { indep := h_indep
          meas := hX
          law := hlaw
          psi_meas := (psiK_continuous hσ d k hk).measurable
          bound := psiK_bound hσ d k hk
          even := psiK_even d σ k
          mean := psi_mean_zero hσ d k hk
          var := psi_var hσ d k hk
          V_nonneg := mul_nonneg hM0 (_root_.sq_nonneg _) }
      hc :=
        { indep := h_indep
          meas := hX
          law := hlaw
          psi_meas := ((pker_continuous hσ d).sub continuous_const).measurable
          bound := fun u => (cK_facts hσ d u).1
          even := cK_even d σ
          mean := fun x => c_mean_zero hσ d x
          var := cK_var hσ d
          V_nonneg := hM0 } }

/-- `Z⁰[Ψ]` and `Z¹[Ψ,2]` of a sample as sums over `Finset.range N`. -/
theorem Z0_Psi_conv {d : ℕ} (σ : ℝ) (k N : ℕ) (x : ℕ → FlatTorus d) :
    Zs0two N (fun i j : Fin N => Psi d σ k (x i) (x j))
      = 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          psiK d σ k (x i - x j) :=
  congrArg (fun t => 1 / (N : ℝ) ^ 2 * t)
    ((Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, Psi d σ k (x i) (x j)) N).trans
      (Finset.sum_congr rfl fun i _ =>
        Fin.sum_univ_eq_sum_range (fun j => psiK d σ k (x i - x j)) N))

theorem Z1_Psi_conv {d : ℕ} (σ : ℝ) (k N : ℕ) (x : ℕ → FlatTorus d) :
    Zs1two2 N (fun i j : Fin N => Psi d σ k (x i) (x j)) (cmat d σ N x)
      = 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
          psiK d σ k (x i - x j) * cK d σ (x j - x v) :=
  congrArg (fun t => 1 / (N : ℝ) ^ 3 * t)
    ((Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, ∑ v : Fin N,
        Psi d σ k (x i) (x j) * (pker d σ (x j - x v) - 1)) N).trans
      (Finset.sum_congr rfl fun i _ =>
        (Fin.sum_univ_eq_sum_range (fun j => ∑ v : Fin N,
          Psi d σ k (x i) (x j) * (pker d σ (x j - x v) - 1)) N).trans
        (Finset.sum_congr rfl fun j _ =>
          Fin.sum_univ_eq_sum_range (fun v => psiK d σ k (x i - x j) * cK d σ (x j - x v)) N)))

/-- **Stage 3: the mean of `|Z¹[Ψ, a = 2]|`**, the second statistic of the last term of `Π_k`,
    with explicit constants (`M = m_1 = p(0)`). -/
theorem Z1_Psi_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) :
    ∫ ω, |Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
        (cmat d σ N (fun j => X j ω))| ∂μ
      ≤ 1 / (N : ℝ) ^ 3 * ((N : ℝ) ^ 2
            * Real.sqrt (6 * (torusM d σ 1 * torusM d σ k ^ 2 * torusM d σ 1))
          + |psiK d σ k 0| * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|)
          + |cK d σ 0| * (N * Real.sqrt (2 * (torusM d σ 1 * torusM d σ k ^ 2)))
          + (N : ℝ) ^ 2 * (torusM d σ 1 * (2 * torusM d σ k))) := by
  have H := torus_deg3 X h_indep hX hlaw hσ k hk
  have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 3 := by positivity
  have hfun : (fun ω => |Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
        (cmat d σ N (fun j => X j ω))|)
      = fun ω => 1 / (N : ℝ) ^ 3 * |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ∑ v ∈ Finset.range N, psiK d σ k (X i ω - X j ω) * cK d σ (X j ω - X v ω)| := by
    funext ω
    rw [Z1_Psi_conv σ k N (fun j => X j ω), abs_mul, abs_of_nonneg hpos]
  rw [hfun, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (H.triple_abs_le (psi_l1 hσ d k hk) N) hpos

theorem sqrt_le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y :=
  calc Real.sqrt x ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- Arithmetic of the constants (pure real inequality). -/
theorem last_arith {M m N A Z s1 s2 s3 p0 c0 : ℝ} (hM1 : 1 ≤ M) (hMN : M ≤ N) (hm : 0 ≤ m)
    (hs1 : s1 ≤ 2 * M * m) (hs2 : s2 ≤ 3 * M * m) (hs3 : s3 ≤ 2 * M)
    (hs1' : 0 ≤ s1) (hs3' : 0 ≤ s3)
    (hp0 : 0 ≤ p0) (hp : p0 ≤ M * m) (hc0 : 0 ≤ c0) (hc : c0 ≤ M)
    (hA : A ≤ (s1 + M * m) / N)
    (hZ : Z ≤ 1 / N ^ 3 * (N ^ 2 * s2 + p0 * (N * s3 + N * c0) + c0 * (N * s1)
      + N ^ 2 * (M * (2 * m)))) :
    A + Z ≤ 13 * (M / N) * m := by
  have hN : 0 < N := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hMm : 0 ≤ M * m := mul_nonneg hM0 hm
  have t1 : N ^ 2 * s2 ≤ N ^ 2 * (3 * M * m) := mul_le_mul_of_nonneg_left hs2 (pow_pos hN 2).le
  have t2a : N * s3 + N * c0 ≤ N * (2 * M) + N * M := by
    have := mul_le_mul_of_nonneg_left hs3 hN.le
    have := mul_le_mul_of_nonneg_left hc hN.le
    linarith
  have t2 : p0 * (N * s3 + N * c0) ≤ M * m * (N * (2 * M) + N * M) :=
    mul_le_mul hp t2a (add_nonneg (mul_nonneg hN.le hs3') (mul_nonneg hN.le hc0)) hMm
  have t3a : N * s1 ≤ N * (2 * M * m) := mul_le_mul_of_nonneg_left hs1 hN.le
  have t3 : c0 * (N * s1) ≤ M * (N * (2 * M * m)) :=
    mul_le_mul hc t3a (mul_nonneg hN.le hs1') hM0
  have hZ' : Z ≤ 1 / N ^ 3 * (5 * M * m * N ^ 2 + 5 * M ^ 2 * m * N) := by
    refine hZ.trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one (pow_pos hN 3).le))
    nlinarith
  have hA' : A ≤ 3 * M * m / N := by
    refine hA.trans (div_le_div_of_nonneg_right ?_ hN.le)
    linarith
  have key : 3 * M * m / N + 1 / N ^ 3 * (5 * M * m * N ^ 2 + 5 * M ^ 2 * m * N)
      = 8 * M * m / N + 5 * M ^ 2 * m / N ^ 2 := by
    have hN' : N ≠ 0 := hN.ne'
    first | (field_simp; ring) | field_simp
  have h5 : 5 * M ^ 2 * m / N ^ 2 ≤ 5 * M * m / N := by
    rw [div_le_div_iff₀ (pow_pos hN 2) hN]
    nlinarith [mul_nonneg (mul_nonneg hMm hN.le) (sub_nonneg.mpr hMN)]
  have e13 : 13 * (M / N) * m = 8 * M * m / N + 5 * M * m / N := by
    have hN' : N ≠ 0 := hN.ne'
    first | (field_simp; ring) | field_simp
  linarith

/-- **Stage 3, one summand of `Π_k` completely: the last term.** For independent uniform points
    on the flat torus, `k ≥ 1`, `N ≥ 1` and `M = p(0) ≤ N`:
    `E |(1/N) ∑_i ĥ_k^{(i)}(i)| ≤ 13 (M/N) m_k`. -/
theorem last_term_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |1 / (N : ℝ) * ∑ i : Fin N, torusHhat d σ N (fun j => X j ω) k i i| ∂μ
      ≤ 13 * (torusM d σ 1 / N) * torusM d σ k := by
  have H := torus_deg3 X h_indep hX hlaw hσ k hk
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hM1 := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have hm0 : 0 ≤ torusM d σ k := (abs_nonneg _).trans (psiK_facts hσ d k hk 0).2.2
  have hA := Z0_Psi_bound X h_indep hX hlaw hσ k hk N hN
  have hZ := Z1_Psi_bound X h_indep hX hlaw hσ k hk N
  have f0 : (fun ω => Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω)))
      = fun ω => 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          psiK d σ k (X i ω - X j ω) :=
    funext fun ω => Z0_Psi_conv σ k N (fun j => X j ω)
  have f1 : (fun ω => Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
        (cmat d σ N (fun j => X j ω)))
      = fun ω => 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ∑ v ∈ Finset.range N, psiK d σ k (X i ω - X j ω) * cK d σ (X j ω - X v ω) :=
    funext fun ω => Z1_Psi_conv σ k N (fun j => X j ω)
  have i0 : Integrable (fun ω => Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))) μ := by
    rw [f0]; exact (H.hψ.full_integrable N).const_mul _
  have i1 : Integrable (fun ω => Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
      (cmat d σ N (fun j => X j ω))) μ := by
    rw [f1]; exact (H.triple_integrable N).const_mul _
  have i01 : Integrable (fun ω => |Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))|
      + |Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
          (cmat d σ N (fun j => X j ω))|) μ := i0.abs.add i1.abs
  have hpt : ∀ ω, |1 / (N : ℝ) * ∑ i : Fin N, torusHhat d σ N (fun j => X j ω) k i i|
      ≤ |Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))|
        + |Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
            (cmat d σ N (fun j => X j ω))| := by
    intro ω
    rw [last_term d σ N hN0 (fun j => X j ω) k]
    exact abs_sub _ _
  have hsum : ∫ ω, |1 / (N : ℝ) * ∑ i : Fin N, torusHhat d σ N (fun j => X j ω) k i i| ∂μ
      ≤ ∫ ω, |Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))| ∂μ
        + ∫ ω, |Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
            (cmat d σ N (fun j => X j ω))| ∂μ := by
    rw [← integral_add i0.abs i1.abs]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _) i01
      (Filter.Eventually.of_forall hpt)
  have hp := psiK_bound hσ d k hk 0
  have hc := (cK_facts hσ d 0).1
  have hMm : 0 ≤ torusM d σ 1 * torusM d σ k := mul_nonneg hM0 hm0
  have hs1 : Real.sqrt (2 * (torusM d σ 1 * torusM d σ k ^ 2))
      ≤ 2 * torusM d σ 1 * torusM d σ k :=
    sqrt_le_of_sq (mul_nonneg (mul_nonneg zero_le_two hM0) hm0) (by
      nlinarith [mul_nonneg (mul_nonneg hM0 (_root_.sq_nonneg (torusM d σ k)))
        (by linarith : (0 : ℝ) ≤ 2 * torusM d σ 1 - 1)])
  have hs2 : Real.sqrt (6 * (torusM d σ 1 * torusM d σ k ^ 2 * torusM d σ 1))
      ≤ 3 * torusM d σ 1 * torusM d σ k :=
    sqrt_le_of_sq (mul_nonneg (mul_nonneg (by norm_num) hM0) hm0) (by
      nlinarith [_root_.sq_nonneg (torusM d σ 1 * torusM d σ k)])
  have hs3 : Real.sqrt (2 * torusM d σ 1) ≤ 2 * torusM d σ 1 :=
    sqrt_le_of_sq (mul_nonneg zero_le_two hM0) (by
      nlinarith [mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ 2 * torusM d σ 1 - 1)])
  exact hsum.trans (last_arith hM1 hMN hm0 hs1 hs2 hs3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (abs_nonneg _) hp (abs_nonneg _) hc hA hZ)

end Sample2

/-! # NEW (A24) from here on

## The first summand of `Π_k`: `Z¹[F_A,1]`, `Z¹[F_A,2]` by centring `F_A`

`F_A(y₁,y₂) = φ(u)`, `φ = p_k p`, is not degenerate, but `φ⁰ = φ - m_{k+1}` is (`∫ p p_k = m_{k+1}`),
and `Z¹[F_A,a] = Z¹[φ⁰,a] + m_{k+1} Z⁰[c]`. This is NOT the argument of `lem:degenerate`(b). -/

/-- `φ⁰(u) = p_k(u) p(u) - m_{k+1}`. -/
noncomputable def phi0 (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : ℝ :=
  heatP d σ k u * pker d σ u - torusM d σ (k + 1)

theorem phi0_even (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : phi0 d σ k (-u) = phi0 d σ k u := by
  unfold phi0 pker
  rw [heatTorus_even, heatP_even]

theorem phi0_continuous {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) :
    Continuous (phi0 d σ k) := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := mul_pos (by positivity) (mul_pos hk' hσ)
  have hP : heatP d σ k = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) :=
    funext fun u => heatP_of_ne d σ (by omega : k ≠ 0) u
  unfold phi0
  rw [hP]
  exact ((heatTorus_continuous hck d).mul (pker_continuous hσ d)).sub continuous_const

/-- `0 ≤ φ ≤ M m_k`, `0 ≤ m_{k+1} ≤ m_k`. -/
theorem phi_facts {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (u : FlatTorus d) :
    0 ≤ heatP d σ k u * pker d σ u
      ∧ heatP d σ k u * pker d σ u ≤ torusM d σ 1 * torusM d σ k
      ∧ 0 ≤ torusM d σ (k + 1) ∧ torusM d σ (k + 1) ≤ torusM d σ k := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := mul_pos (by positivity) (mul_pos hk' hσ)
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck1 : 0 < 2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) * σ) :=
    mul_pos (by positivity) (mul_pos hk1 hσ)
  obtain ⟨p0, p1, -⟩ := psiK_facts hσ d k hk u
  have h1 : 0 ≤ heatP d σ k u := heatP_nonneg hσ d k u
  have h2 : heatP d σ k u ≤ torusM d σ k := by
    rw [heatP_of_ne d σ (by omega : k ≠ 0)]; exact heatTorus_le_zero hck d u
  refine ⟨mul_nonneg h1 p0, ?_, heatTorus_nonneg hck1 d 0, torusM_anti hσ d hk (Nat.le_succ k)⟩
  calc heatP d σ k u * pker d σ u ≤ torusM d σ k * torusM d σ 1 :=
        mul_le_mul h2 p1 p0 (h1.trans h2)
    _ = torusM d σ 1 * torusM d σ k := mul_comm _ _

theorem phi0_bound {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (u : FlatTorus d) :
    |phi0 d σ k u| ≤ torusM d σ 1 * torusM d σ k := by
  obtain ⟨f0, f1, f2, f3⟩ := phi_facts hσ d k hk u
  have hM := torusM_one_ge hσ d
  have hm0 : 0 ≤ torusM d σ k := f2.trans f3
  have h := mul_nonneg (by linarith : (0 : ℝ) ≤ torusM d σ 1 - 1) hm0
  unfold phi0
  exact abs_le.mpr ⟨by nlinarith, by linarith⟩

theorem phi0_split (d : ℕ) (σ : ℝ) (k : ℕ) (hk : 1 ≤ k) (x z : FlatTorus d) :
    phi0 d σ k (x - z)
      = pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
        - torusM d σ (k + 1) := by
  have h1 : heatP d σ k (x - z) = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x) := by
    rw [heatP_of_ne d σ (by omega : k ≠ 0), ← neg_sub z x, heatTorus_even]
  unfold phi0
  rw [h1]; ring

theorem phi_integrable {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    Integrable (fun z : FlatTorus d =>
      pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x))
      (flatTorusMeasure d) := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hck : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := mul_pos (by positivity) (mul_pos hk' hσ)
  have hKc : Continuous fun z : FlatTorus d => pker d σ (x - z) :=
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  have hGc : Continuous fun z : FlatTorus d =>
      heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x) :=
    (heatTorus_continuous hck d).comp (continuous_id.sub continuous_const)
  exact flat_integrable d _ (hKc.mul hGc)

/-- `φ⁰` is degenerate. -/
theorem phi0_mean {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    ∫ z, phi0 d σ k (x - z) ∂flatTorusMeasure d = 0 := by
  simp_rw [phi0_split d σ k hk x]
  rw [integral_sub (phi_integrable hσ d k hk x) (integrable_const _), pk_integral hσ d k hk x,
    integral_const, probReal_univ, one_smul, sub_self]

/-- The value `φ(x - z)` in the two forms. -/
theorem phi_value (d : ℕ) (σ : ℝ) (k : ℕ) (hk : 1 ≤ k) (x z : FlatTorus d) :
    pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
      = heatP d σ k (x - z) * pker d σ (x - z) := by
  have e := phi0_split d σ k hk x z
  unfold phi0 at e
  linarith

theorem phi0_var {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    ∫ z, phi0 d σ k (x - z) ^ 2 ∂flatTorusMeasure d ≤ torusM d σ 1 * torusM d σ k ^ 2 := by
  have hc : Continuous fun z : FlatTorus d => phi0 d σ k (x - z) :=
    (phi0_continuous hσ d k hk).comp (continuous_const.sub continuous_id)
  have i1 := phi_integrable hσ d k hk x
  have i2 : Integrable (fun z : FlatTorus d =>
      (torusM d σ 1 * torusM d σ k - 2 * torusM d σ (k + 1))
        * (pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)))
      (flatTorusMeasure d) := i1.const_mul _
  have i3 : Integrable (fun z : FlatTorus d =>
      (torusM d σ 1 * torusM d σ k - 2 * torusM d σ (k + 1))
        * (pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x))
      + torusM d σ (k + 1) ^ 2) (flatTorusMeasure d) := i2.add (integrable_const _)
  obtain ⟨-, -, f2, f3⟩ := phi_facts hσ d k hk 0
  have hM := torusM_one_ge hσ d
  have hpt : ∀ z, phi0 d σ k (x - z) ^ 2
      ≤ (torusM d σ 1 * torusM d σ k - 2 * torusM d σ (k + 1))
          * (pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x))
        + torusM d σ (k + 1) ^ 2 := by
    intro z
    obtain ⟨g0, g1, -, -⟩ := phi_facts hσ d k hk (x - z)
    rw [← phi_value d σ k hk x z] at g0 g1
    have h := mul_nonneg g0 (sub_nonneg.mpr g1)
    rw [phi0_split d σ k hk x z]
    nlinarith
  calc ∫ z, phi0 d σ k (x - z) ^ 2 ∂flatTorusMeasure d
      ≤ ∫ z, ((torusM d σ 1 * torusM d σ k - 2 * torusM d σ (k + 1))
          * (pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x))
        + torusM d σ (k + 1) ^ 2) ∂flatTorusMeasure d :=
        integral_mono (flat_integrable d _ (hc.pow 2)) i3 hpt
    _ = (torusM d σ 1 * torusM d σ k - 2 * torusM d σ (k + 1)) * torusM d σ (k + 1)
          + torusM d σ (k + 1) ^ 2 := by
        rw [integral_add i2 (integrable_const _), integral_const_mul, pk_integral hσ d k hk x,
          integral_const, probReal_univ, one_smul]
    _ ≤ torusM d σ 1 * torusM d σ k ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_left f3
          (mul_nonneg (by linarith : (0 : ℝ) ≤ torusM d σ 1) (f2.trans f3))
        nlinarith [_root_.sq_nonneg (torusM d σ (k + 1))]

theorem phi0_l1 {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (x : FlatTorus d) :
    ∫ z, |phi0 d σ k (x - z)| ∂flatTorusMeasure d ≤ 2 * torusM d σ k := by
  have hc : Continuous fun z : FlatTorus d => phi0 d σ k (x - z) :=
    (phi0_continuous hσ d k hk).comp (continuous_const.sub continuous_id)
  have i1 := phi_integrable hσ d k hk x
  have i3 : Integrable (fun z : FlatTorus d =>
      pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
        + torusM d σ (k + 1)) (flatTorusMeasure d) := i1.add (integrable_const _)
  obtain ⟨-, -, f2, f3⟩ := phi_facts hσ d k hk 0
  have hpt : ∀ z, |phi0 d σ k (x - z)|
      ≤ pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
        + torusM d σ (k + 1) := by
    intro z
    obtain ⟨g0, -, -, -⟩ := phi_facts hσ d k hk (x - z)
    rw [← phi_value d σ k hk x z] at g0
    rw [phi0_split d σ k hk x z]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc ∫ z, |phi0 d σ k (x - z)| ∂flatTorusMeasure d
      ≤ ∫ z, (pker d σ (x - z) * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) (z - x)
          + torusM d σ (k + 1)) ∂flatTorusMeasure d :=
        integral_mono (flat_integrable d _ hc.abs) i3 hpt
    _ = torusM d σ (k + 1) + torusM d σ (k + 1) := by
        rw [integral_add i1 (integrable_const _), pk_integral hσ d k hk x, integral_const,
          probReal_univ, one_smul]
    _ ≤ 2 * torusM d σ k := by linarith

theorem FA_eq (d : ℕ) (σ : ℝ) (k : ℕ) (y1 y2 : FlatTorus d) :
    FA d σ k y1 y2 = phi0 d σ k (y1 - y2) + torusM d σ (k + 1) := by
  unfold FA phi0; ring

theorem FA_symm (d : ℕ) (σ : ℝ) (k : ℕ) (y1 y2 : FlatTorus d) :
    FA d σ k y1 y2 = FA d σ k y2 y1 := by
  rw [FA_eq, FA_eq, ← neg_sub y2 y1, phi0_even]

/-- Pure arithmetic: the bound of `triple_abs_le` with the torus constants is `≤ 10 (M/N) m`. -/
theorem Z_arith {M m N Z s1 s2 s3 p0 c0 : ℝ} (hM1 : 1 ≤ M) (hMN : M ≤ N) (hm : 0 ≤ m)
    (hs1 : s1 ≤ 2 * M * m) (hs2 : s2 ≤ 3 * M * m) (hs3 : s3 ≤ 2 * M)
    (hs1' : 0 ≤ s1) (hs3' : 0 ≤ s3) (hp : p0 ≤ M * m) (hc0 : 0 ≤ c0) (hc : c0 ≤ M)
    (hZ : Z ≤ 1 / N ^ 3 * (N ^ 2 * s2 + p0 * (N * s3 + N * c0) + c0 * (N * s1)
      + N ^ 2 * (M * (2 * m)))) :
    Z ≤ 10 * (M / N) * m := by
  have hN : 0 < N := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hMm : 0 ≤ M * m := mul_nonneg hM0 hm
  have t1 : N ^ 2 * s2 ≤ N ^ 2 * (3 * M * m) := mul_le_mul_of_nonneg_left hs2 (pow_pos hN 2).le
  have t2a : N * s3 + N * c0 ≤ N * (2 * M) + N * M := by
    have := mul_le_mul_of_nonneg_left hs3 hN.le
    have := mul_le_mul_of_nonneg_left hc hN.le
    linarith
  have t2 : p0 * (N * s3 + N * c0) ≤ M * m * (N * (2 * M) + N * M) :=
    mul_le_mul hp t2a (add_nonneg (mul_nonneg hN.le hs3') (mul_nonneg hN.le hc0)) hMm
  have t3a : N * s1 ≤ N * (2 * M * m) := mul_le_mul_of_nonneg_left hs1 hN.le
  have t3 : c0 * (N * s1) ≤ M * (N * (2 * M * m)) :=
    mul_le_mul hc t3a (mul_nonneg hN.le hs1') hM0
  have hZ' : Z ≤ 1 / N ^ 3 * (5 * M * m * N ^ 2 + 5 * M ^ 2 * m * N) := by
    refine hZ.trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one (pow_pos hN 3).le))
    nlinarith
  have key : 1 / N ^ 3 * (5 * M * m * N ^ 2 + 5 * M ^ 2 * m * N)
      = 5 * M * m / N + 5 * M ^ 2 * m / N ^ 2 := by
    have hN' : N ≠ 0 := hN.ne'
    first | (field_simp; ring) | field_simp
  have h5 : 5 * M ^ 2 * m / N ^ 2 ≤ 5 * M * m / N := by
    rw [div_le_div_iff₀ (pow_pos hN 2) hN]
    nlinarith [mul_nonneg (mul_nonneg hMm hN.le) (sub_nonneg.mpr hMN)]
  have e10 : 10 * (M / N) * m = 5 * M * m / N + 5 * M * m / N := by
    have hN' : N ≠ 0 := hN.ne'
    first | (field_simp; ring) | field_simp
  linarith

section SampleFA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The hypotheses `Deg3` hold for `φ⁰` and `c`. -/
theorem torus_deg3F [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k) :
    Deg3 μ (flatTorusMeasure d) X (phi0 d σ k) (cK d σ) (torusM d σ 1 * torusM d σ k)
      (torusM d σ 1) (torusM d σ 1 * torusM d σ k ^ 2) (torusM d σ 1) :=
  { hψ :=
      { indep := h_indep
        meas := hX
        law := hlaw
        psi_meas := (phi0_continuous hσ d k hk).measurable
        bound := phi0_bound hσ d k hk
        even := phi0_even d σ k
        mean := phi0_mean hσ d k hk
        var := phi0_var hσ d k hk
        V_nonneg := (torus_deg3 X h_indep hX hlaw hσ k hk).hψ.V_nonneg }
    hc := (torus_deg3 X h_indep hX hlaw hσ k hk).hc }

/-- `∑_{i,b,v} F_A(x_i,x_b) c(x_b - x_v) = ∑ φ⁰ c + m_{k+1} N ∑_{b,v} c(x_b - x_v)`. -/
theorem FA_sum2 {d : ℕ} (σ : ℝ) (k N : ℕ) (x : ℕ → FlatTorus d) :
    ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (x i) (x b) * cK d σ (x b - x v)
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
          phi0 d σ k (x i - x b) * cK d σ (x b - x v)
        + torusM d σ (k + 1)
          * (N * ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N, cK d σ (x b - x v)) := by
  simp only [FA_eq, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]

/-- The sum for `a = 1` equals the sum for `a = 2` (`F_A` is symmetric). -/
theorem FA_sum1 {d : ℕ} (σ : ℝ) (k N : ℕ) (x : ℕ → FlatTorus d) :
    ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (x i) (x b) * cK d σ (x i - x v)
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
          FA d σ k (x i) (x b) * cK d σ (x b - x v) :=
  Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun v _ => by rw [FA_symm])

/-- `E|∑_{i,b,v} F_A(X_i,X_b) c(X_b - X_v)|`. -/
theorem FA_triple_abs_le [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) :
    ∫ ω, |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)| ∂μ
      ≤ ((N : ℝ) ^ 2 * Real.sqrt (6 * (torusM d σ 1 * torusM d σ k ^ 2 * torusM d σ 1))
          + |phi0 d σ k 0| * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|)
          + |cK d σ 0| * (N * Real.sqrt (2 * (torusM d σ 1 * torusM d σ k ^ 2)))
          + (N : ℝ) ^ 2 * (torusM d σ 1 * (2 * torusM d σ k)))
        + torusM d σ (k + 1)
          * (N * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|)) := by
  have H := torus_deg3F X h_indep hX hlaw hσ k hk
  obtain ⟨-, -, f2, -⟩ := phi_facts hσ d k hk 0
  have hT := H.triple_abs_le (phi0_l1 hσ d k hk) N
  have hC := H.hc.full_abs_le N
  have iT : Integrable (fun ω => |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
      ∑ v ∈ Finset.range N, phi0 d σ k (X i ω - X b ω) * cK d σ (X b ω - X v ω)|) μ :=
    (H.triple_integrable N).abs
  have iC : Integrable (fun ω => torusM d σ (k + 1) * (N * |∑ b ∈ Finset.range N,
      ∑ v ∈ Finset.range N, cK d σ (X b ω - X v ω)|)) μ :=
    (((H.hc.full_integrable N).abs).const_mul _).const_mul _
  have iTC : Integrable (fun ω => |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
      ∑ v ∈ Finset.range N, phi0 d σ k (X i ω - X b ω) * cK d σ (X b ω - X v ω)|
      + torusM d σ (k + 1) * (N * |∑ b ∈ Finset.range N,
        ∑ v ∈ Finset.range N, cK d σ (X b ω - X v ω)|)) μ := iT.add iC
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)|
      ≤ |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ∑ v ∈ Finset.range N, phi0 d σ k (X i ω - X b ω) * cK d σ (X b ω - X v ω)|
        + torusM d σ (k + 1) * (N * |∑ b ∈ Finset.range N,
          ∑ v ∈ Finset.range N, cK d σ (X b ω - X v ω)|) := by
    intro ω
    rw [FA_sum2 σ k N (fun j => X j ω)]
    refine (abs_add_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
    rw [abs_mul, abs_mul, abs_of_nonneg f2, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  calc ∫ ω, |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)| ∂μ
      ≤ ∫ ω, (|∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, phi0 d σ k (X i ω - X b ω) * cK d σ (X b ω - X v ω)|
          + torusM d σ (k + 1) * (N * |∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, cK d σ (X b ω - X v ω)|)) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _) iTC
          (Filter.Eventually.of_forall hpt)
    _ = ∫ ω, |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, phi0 d σ k (X i ω - X b ω) * cK d σ (X b ω - X v ω)| ∂μ
          + torusM d σ (k + 1) * (N * ∫ ω, |∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, cK d σ (X b ω - X v ω)| ∂μ) := by
        rw [integral_add iT iC, integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))) f2
        linarith

theorem Z1_FA2_conv {d : ℕ} (σ : ℝ) (k N : ℕ) (x : ℕ → FlatTorus d) :
    Zs1two2 N (fun i b : Fin N => FA d σ k (x i) (x b)) (cmat d σ N x)
      = 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
          FA d σ k (x i) (x b) * cK d σ (x b - x v) :=
  congrArg (fun t => 1 / (N : ℝ) ^ 3 * t)
    ((Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, ∑ v : Fin N,
        FA d σ k (x i) (x j) * (pker d σ (x j - x v) - 1)) N).trans
      (Finset.sum_congr rfl fun i _ =>
        (Fin.sum_univ_eq_sum_range (fun j => ∑ v : Fin N,
          FA d σ k (x i) (x j) * (pker d σ (x j - x v) - 1)) N).trans
        (Finset.sum_congr rfl fun j _ =>
          Fin.sum_univ_eq_sum_range (fun v => FA d σ k (x i) (x j) * cK d σ (x j - x v)) N)))

theorem Z1_FA1_conv {d : ℕ} (σ : ℝ) (k N : ℕ) (x : ℕ → FlatTorus d) :
    Zs1two1 N (fun i b : Fin N => FA d σ k (x i) (x b)) (cmat d σ N x)
      = 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
          FA d σ k (x i) (x b) * cK d σ (x i - x v) :=
  congrArg (fun t => 1 / (N : ℝ) ^ 3 * t)
    ((Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, ∑ v : Fin N,
        FA d σ k (x i) (x j) * (pker d σ (x i - x v) - 1)) N).trans
      (Finset.sum_congr rfl fun i _ =>
        (Fin.sum_univ_eq_sum_range (fun j => ∑ v : Fin N,
          FA d σ k (x i) (x j) * (pker d σ (x i - x v) - 1)) N).trans
        (Finset.sum_congr rfl fun j _ =>
          Fin.sum_univ_eq_sum_range (fun v => FA d σ k (x i) (x j) * cK d σ (x i - x v)) N)))

/-- **`E|Z¹[F_A, a = 2]| ≤ 13 (M/N) m_k`** for `M ≤ N`. -/
theorem Z1_FA2_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
        (cmat d σ N (fun j => X j ω))| ∂μ
      ≤ 13 * (torusM d σ 1 / N) * torusM d σ k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 3 := by positivity
  have hM1 := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  obtain ⟨-, -, f2, f3⟩ := phi_facts hσ d k hk 0
  have hm0 : 0 ≤ torusM d σ k := f2.trans f3
  have hMm : 0 ≤ torusM d σ 1 * torusM d σ k := mul_nonneg hM0 hm0
  have hfun : (fun ω => |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
        (cmat d σ N (fun j => X j ω))|)
      = fun ω => 1 / (N : ℝ) ^ 3 * |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ∑ v ∈ Finset.range N, FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)| := by
    funext ω
    rw [Z1_FA2_conv σ k N (fun j => X j ω), abs_mul, abs_of_nonneg hpos]
  have hB := FA_triple_abs_le X h_indep hX hlaw hσ k hk N
  have hp := phi0_bound hσ d k hk 0
  have hc := (cK_facts hσ d 0).1
  have hs1 : Real.sqrt (2 * (torusM d σ 1 * torusM d σ k ^ 2))
      ≤ 2 * torusM d σ 1 * torusM d σ k :=
    sqrt_le_of_sq (mul_nonneg (mul_nonneg zero_le_two hM0) hm0) (by
      nlinarith [mul_nonneg (mul_nonneg hM0 (_root_.sq_nonneg (torusM d σ k)))
        (by linarith : (0 : ℝ) ≤ 2 * torusM d σ 1 - 1)])
  have hs2 : Real.sqrt (6 * (torusM d σ 1 * torusM d σ k ^ 2 * torusM d σ 1))
      ≤ 3 * torusM d σ 1 * torusM d σ k :=
    sqrt_le_of_sq (mul_nonneg (mul_nonneg (by norm_num) hM0) hm0) (by
      nlinarith [_root_.sq_nonneg (torusM d σ 1 * torusM d σ k)])
  have hs3 : Real.sqrt (2 * torusM d σ 1) ≤ 2 * torusM d σ 1 :=
    sqrt_le_of_sq (mul_nonneg zero_le_two hM0) (by
      nlinarith [mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ 2 * torusM d σ 1 - 1)])
  have hZ := Z_arith hM1 hMN hm0 hs1 hs2 hs3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hp
    (abs_nonneg (cK d σ 0)) hc (le_refl (1 / (N : ℝ) ^ 3 * ((N : ℝ) ^ 2
      * Real.sqrt (6 * (torusM d σ 1 * torusM d σ k ^ 2 * torusM d σ 1))
      + |phi0 d σ k 0| * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|)
      + |cK d σ 0| * (N * Real.sqrt (2 * (torusM d σ 1 * torusM d σ k ^ 2)))
      + (N : ℝ) ^ 2 * (torusM d σ 1 * (2 * torusM d σ k)))))
  -- the extra term `m_{k+1} (√(2M) + |c(0)|)/N ≤ 3 (M/N) m_k`
  have hE : 1 / (N : ℝ) ^ 3 * (torusM d σ (k + 1)
        * (N * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|)))
      ≤ 3 * (torusM d σ 1 / N) * torusM d σ k := by
    have e1 : 1 / (N : ℝ) ^ 3 * (torusM d σ (k + 1)
          * (N * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|)))
        = torusM d σ (k + 1) * (Real.sqrt (2 * torusM d σ 1) + |cK d σ 0|) / N := by
      have hN' : (N : ℝ) ≠ 0 := hNpos.ne'
      first | (field_simp; ring) | field_simp
    have e2 : 3 * (torusM d σ 1 / N) * torusM d σ k
        = torusM d σ k * (3 * torusM d σ 1) / N := by ring
    rw [e1, e2]
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    exact mul_le_mul f3 (by linarith) (add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hm0
  rw [hfun, integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left hB hpos
  rw [mul_add] at h1
  linarith

/-- **`E|Z¹[F_A, a = 1]| ≤ 13 (M/N) m_k`** for `M ≤ N` (it equals `Z¹[F_A, 2]`). -/
theorem Z1_FA1_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
        (cmat d σ N (fun j => X j ω))| ∂μ
      ≤ 13 * (torusM d σ 1 / N) * torusM d σ k := by
  have e : (fun ω => |Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
        (cmat d σ N (fun j => X j ω))|)
      = fun ω => |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
        (cmat d σ N (fun j => X j ω))| := by
    funext ω
    rw [Z1_FA1_conv σ k N (fun j => X j ω), Z1_FA2_conv σ k N (fun j => X j ω),
      FA_sum1 σ k N (fun j => X j ω)]
  rw [e]
  exact Z1_FA2_bound X h_indep hX hlaw hσ k hk N hN hMN

end SampleFA


/-! # NEW (A26) from here on

## The third statistic of the first summand of `Π_k`: `Z¹[F_A', a = 3]`

`N⁴ Z¹[F_A',3] = ∑_{i,b,q,v} F_A(x_i,x_b) p(x_b - x_q) c(x_q - x_v)
             = ∑_q (∑_{i,b} F_A(x_i,x_b) p(x_b - x_q)) · H_q`, `H_q = ∑_v c(x_q - x_v) = N ε_q`.
With `F_A = φ⁰ + m_{k+1}` and `p = c + 1` the inner sum is
`A_q + Φ + m_{k+1} N H_q + m_{k+1} N²`, `A_q = ∑_{i,b} φ⁰(x_i - x_b) c(x_b - x_q)`,
`Φ = ∑_{i,b} φ⁰(x_i - x_b)`.  The term `m_{k+1} N² ∑_q H_q` is a full double sum of `c`
(`Deg2.full_abs_le`); every other term is treated FOR EACH `q` SEPARATELY by the Cauchy–Schwarz
inequality, `E|Y H_q| ≤ (E Y²)^{1/2} (E H_q²)^{1/2}`, with second moments of sums over at most
two free indices.  This is NOT the argument of `lem:degenerate`(b) (no second moment of the
whole four-index sum is taken, the cancellation between different `q` is not used). -/

/-! ### bounded measurable functions -/

/-- A bounded measurable real function (so that integrability never has to be argued). -/
structure BM {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ) : Prop where
  meas : Measurable f
  bdd : ∃ B, ∀ ω, |f ω| ≤ B

section BMsec

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f g : Ω → ℝ}

theorem BM.const (c : ℝ) : BM (fun _ : Ω => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem BM.add (hf : BM f) (hg : BM g) : BM (fun ω => f ω + g ω) := by
  obtain ⟨Bf, hBf⟩ := hf.bdd
  obtain ⟨Bg, hBg⟩ := hg.bdd
  exact ⟨hf.meas.add hg.meas, Bf + Bg, fun ω =>
    (abs_add_le _ _).trans (add_le_add (hBf ω) (hBg ω))⟩

theorem BM.mul (hf : BM f) (hg : BM g) : BM (fun ω => f ω * g ω) := by
  obtain ⟨Bf, hBf⟩ := hf.bdd
  obtain ⟨Bg, hBg⟩ := hg.bdd
  refine ⟨hf.meas.mul hg.meas, Bf * Bg, fun ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hBf ω) (hBg ω) (abs_nonneg _) ((abs_nonneg _).trans (hBf ω))

theorem BM.absv (hf : BM f) : BM (fun ω => |f ω|) := by
  obtain ⟨Bf, hBf⟩ := hf.bdd
  exact ⟨continuous_abs.measurable.comp hf.meas, Bf, fun ω => by rw [abs_abs]; exact hBf ω⟩

theorem BM.sqr (hf : BM f) : BM (fun ω => f ω ^ 2) := by
  have h := hf.mul hf
  have e : (fun ω => f ω ^ 2) = fun ω => f ω * f ω := by funext ω; ring
  rw [e]; exact h

theorem BM.const_mul (c : ℝ) (hf : BM f) : BM (fun ω => c * f ω) := (BM.const c).mul hf

theorem BM.sum {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ) (h : ∀ i ∈ s, BM (F i)) :
    BM (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun ω : Ω => ∑ i ∈ (∅ : Finset ι), F i ω) = fun _ => (0 : ℝ) := by
      funext ω; simp
    rw [e]; exact BM.const 0
  · intro a s ha ih h
    have e : (fun ω => ∑ i ∈ insert a s, F i ω) = fun ω => F a ω + ∑ i ∈ s, F i ω := by
      funext ω; rw [Finset.sum_insert ha]
    rw [e]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem BM.integrable {μ : Measure Ω} [IsFiniteMeasure μ] (hf : BM f) : Integrable f μ := by
  obtain ⟨B, hB⟩ := hf.bdd
  exact bdd_integrable f hf.meas hB

/-- `∫ (f + g)² ≤ 2 ∫ f² + 2 ∫ g²`. -/
theorem sq2_int {μ : Measure Ω} [IsFiniteMeasure μ] (hf : BM f) (hg : BM g) {P Q : ℝ}
    (hP : ∫ ω, f ω ^ 2 ∂μ ≤ P) (hQ : ∫ ω, g ω ^ 2 ∂μ ≤ Q) :
    ∫ ω, (f ω + g ω) ^ 2 ∂μ ≤ 2 * P + 2 * Q := by
  have iF : Integrable (fun ω => f ω ^ 2) μ := hf.sqr.integrable
  have iG : Integrable (fun ω => g ω ^ 2) μ := hg.sqr.integrable
  have iS : Integrable (fun ω => (f ω + g ω) ^ 2) μ := (hf.add hg).sqr.integrable
  have hpt : ∀ ω, (f ω + g ω) ^ 2 ≤ 2 * f ω ^ 2 + 2 * g ω ^ 2 := fun ω => by
    nlinarith [_root_.sq_nonneg (f ω - g ω)]
  calc ∫ ω, (f ω + g ω) ^ 2 ∂μ ≤ ∫ ω, (2 * f ω ^ 2 + 2 * g ω ^ 2) ∂μ :=
        integral_mono iS ((iF.const_mul 2).add (iG.const_mul 2)) hpt
    _ = 2 * ∫ ω, f ω ^ 2 ∂μ + 2 * ∫ ω, g ω ^ 2 ∂μ := by
        rw [integral_add (iF.const_mul 2) (iG.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * P + 2 * Q := by linarith

/-- **Cauchy–Schwarz**, in the form used below: `∫ f² ≤ P`, `∫ g² ≤ Q`, `P Q ≤ W²` give
    `∫ |f g| ≤ W`. -/
theorem cs_abs {μ : Measure Ω} [IsFiniteMeasure μ] (hf : BM f) (hg : BM g) {P Q W : ℝ}
    (hP : ∫ ω, f ω ^ 2 ∂μ ≤ P) (hQ : ∫ ω, g ω ^ 2 ∂μ ≤ Q) (hQ0 : 0 < Q) (hW0 : 0 ≤ W)
    (hPQ : P * Q ≤ W ^ 2) : ∫ ω, |f ω * g ω| ∂μ ≤ W := by
  have iF : Integrable (fun ω => f ω ^ 2) μ := hf.sqr.integrable
  have iG : Integrable (fun ω => g ω ^ 2) μ := hg.sqr.integrable
  have iR : Integrable (fun ω => |f ω * g ω|) μ := (hf.mul hg).absv.integrable
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ∫ ω, |f ω * g ω| ∂μ := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; exact integral_nonneg fun ω => abs_nonneg _
  have key : ∀ t : ℝ, 0 < t → 2 * t * R ≤ P + t ^ 2 * Q := by
    intro t ht
    have hpt : ∀ ω, 2 * t * |f ω * g ω| ≤ f ω ^ 2 + t ^ 2 * g ω ^ 2 := by
      intro ω
      have h := _root_.sq_nonneg (|f ω| - t * |g ω|)
      have e : (|f ω| - t * |g ω|) ^ 2
          = f ω ^ 2 - 2 * t * (|f ω| * |g ω|) + t ^ 2 * g ω ^ 2 := by
        rw [sub_sq, mul_pow, sq_abs, sq_abs]; ring
      rw [abs_mul]
      linarith
    have h1 : ∫ ω, 2 * t * |f ω * g ω| ∂μ ≤ ∫ ω, (f ω ^ 2 + t ^ 2 * g ω ^ 2) ∂μ :=
      integral_mono (iR.const_mul _) (iF.add (iG.const_mul _)) hpt
    rw [integral_const_mul, integral_add iF (iG.const_mul _), integral_const_mul, ← hR] at h1
    have h2 : t ^ 2 * ∫ ω, g ω ^ 2 ∂μ ≤ t ^ 2 * Q :=
      mul_le_mul_of_nonneg_left hQ (_root_.sq_nonneg t)
    linarith
  rw [← hR]
  by_contra hcon
  have hcon' : W < R := not_le.mp hcon
  have hRpos : 0 < R := lt_of_le_of_lt hW0 hcon'
  have h := key (R / Q) (div_pos hRpos hQ0)
  have hQ' : Q ≠ 0 := hQ0.ne'
  have e : 2 * (R / Q) * R - (R / Q) ^ 2 * Q = R ^ 2 / Q := by
    first | (field_simp; ring) | field_simp
  have h3 : R ^ 2 / Q ≤ P := by linarith
  have h4 : R ^ 2 ≤ P * Q := by rwa [div_le_iff₀ hQ0] at h3
  have h5 := mul_pos (sub_pos.mpr hcon') (by linarith : (0 : ℝ) < R + W)
  nlinarith

end BMsec

theorem amgm4 (a b x y : ℝ) :
    a * x * (b * y) ≤ (|a| * |b| * x ^ 2 + |b| * |a| * y ^ 2) / 2 := by
  have h1 : a * x * (b * y) ≤ |a * x * (b * y)| := le_abs_self _
  rw [abs_mul, abs_mul, abs_mul] at h1
  have hxy : |x| * |y| ≤ (x ^ 2 + y ^ 2) / 2 := by
    nlinarith [_root_.sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  have hab : 0 ≤ |a| * |b| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hxy hab
  linarith

theorem abs3 (a b c : ℝ) : |-a - b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le (-a - b) c
  have h2 := abs_sub (-a) b
  rw [abs_neg] at h2
  linarith

theorem cnt_first (N i : ℕ) (hi : i ∈ Finset.range N) :
    ∑ i' ∈ Finset.range N, ∑ _b' ∈ Finset.range N, (if i' = i then (1 : ℝ) else 0) = N := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hi h

section Fubini3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem indep_three {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) {j a b c : ℕ} (ha : j ≠ a) (hb : j ≠ b) (hc : j ≠ c) :
    IndepFun (X j) (fun ω => (X a ω, X b ω, X c ω)) μ := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = {a, b, c} := ⟨_, rfl⟩
  have ma : a ∈ T := by rw [hT]; simp
  have mb : b ∈ T := by rw [hT]; simp
  have mc : c ∈ T := by rw [hT]; simp
  have hj : j ∉ T := by rw [hT]; simp [ha, hb, hc]
  have ea : Measurable fun y : T → E => y ⟨a, ma⟩ := measurable_pi_apply _
  have eb : Measurable fun y : T → E => y ⟨b, mb⟩ := measurable_pi_apply _
  have ec : Measurable fun y : T → E => y ⟨c, mc⟩ := measurable_pi_apply _
  have hind0 := h_indep.indepFun_finset {j} T (Finset.disjoint_singleton_left.mpr hj) hX
  exact hind0.comp (φ := fun u : (({j} : Finset ℕ) → E) => u ⟨j, Finset.mem_singleton_self j⟩)
    (ψ := fun y : T → E => (y ⟨a, ma⟩, y ⟨b, mb⟩, y ⟨c, mc⟩))
    (measurable_pi_apply _) (ea.prodMk (eb.prodMk ec))

end Fubini3

/-! ### row sums of a degenerate kernel -/

/-- The row sum `∑_v ψ(x_q - x_v)` over all `v < N` (for `ψ = c` this is `N ε_q`). -/
noncomputable def Hrow {Ω G : Type*} [AddCommGroup G] (ψ : G → ℝ) (X : ℕ → Ω → G) (N q : ℕ)
    (ω : Ω) : ℝ :=
  ∑ v ∈ Finset.range N, ψ (X q ω - X v ω)

/-- The same without the diagonal term. -/
noncomputable def Hoff {Ω G : Type*} [AddCommGroup G] (ψ : G → ℝ) (X : ℕ → Ω → G) (N q : ℕ)
    (ω : Ω) : ℝ :=
  ∑ v ∈ Finset.range N, aT ψ X q v ω

theorem Hrow_eq {Ω G : Type*} [AddCommGroup G] (ψ : G → ℝ) (X : ℕ → Ω → G) (N q : ℕ)
    (hq : q ∈ Finset.range N) (ω : Ω) : Hrow ψ X N q ω = Hoff ψ X N q ω + ψ 0 := by
  have h' : ∀ v ∈ Finset.range N, ψ (X q ω - X v ω)
      = aT ψ X q v ω + (if v = q then ψ 0 else 0) := by
    intro v _
    unfold aT
    by_cases hvq : v = q
    · rw [hvq]; simp
    · rw [if_neg (fun h'' : q = v => hvq h''.symm), if_neg hvq, add_zero]
  unfold Hrow Hoff
  rw [Finset.sum_congr rfl h', Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hq]

namespace Deg2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ : G → ℝ} {B V : ℝ}

theorem BM_psi (H : Deg2 μ ν X ψ B V) (i j : ℕ) : BM (fun ω => ψ (X i ω - X j ω)) :=
  ⟨H.psi_meas.comp ((H.meas i).sub (H.meas j)), B, fun ω => H.bound _⟩

theorem BM_aT (H : Deg2 μ ν X ψ B V) (i j : ℕ) : BM (aT ψ X i j) :=
  ⟨H.aT_meas i j, B, H.aT_bound i j⟩

theorem BM_Hoff (H : Deg2 μ ν X ψ B V) (N q : ℕ) : BM (Hoff ψ X N q) := by
  show BM (fun ω => ∑ v ∈ Finset.range N, aT ψ X q v ω)
  exact BM.sum (Finset.range N) (fun v => aT ψ X q v) fun v _ => H.BM_aT q v

theorem BM_Hrow (H : Deg2 μ ν X ψ B V) (N q : ℕ) : BM (Hrow ψ X N q) := by
  show BM (fun ω => ∑ v ∈ Finset.range N, ψ (X q ω - X v ω))
  exact BM.sum (Finset.range N) (fun v ω => ψ (X q ω - X v ω)) fun v _ => H.BM_psi q v

theorem BM_full (H : Deg2 μ ν X ψ B V) (N : ℕ) :
    BM (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) :=
  BM.sum (Finset.range N) (fun i ω => ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) fun i _ =>
    BM.sum (Finset.range N) (fun j ω => ψ (X i ω - X j ω)) fun j _ => H.BM_psi i j

/-- `E (∑_{v ≠ q} ψ(X_q - X_v))² ≤ 2 N V`. -/
theorem Hoff_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (N q : ℕ) : ∫ ω, Hoff ψ X N q ω ^ 2 ∂μ ≤ 2 * (N : ℝ) * V := by
  have hS2 : ∀ ω, Hoff ψ X N q ω ^ 2
      = ∑ v ∈ Finset.range N, ∑ v' ∈ Finset.range N, aT ψ X q v ω * aT ψ X q v' ω := by
    intro ω
    unfold Hoff
    rw [pow_two, Finset.sum_mul_sum]
  have hI : ∀ v v', Integrable (fun ω => aT ψ X q v ω * aT ψ X q v' ω) μ := fun v v' =>
    H.aT_prod_integrable q v q v'
  have hV0 := H.V_nonneg
  simp_rw [hS2]
  rw [integral_finset_sum _ (fun v _ => integrable_finset_sum _ fun v' _ => hI v v')]
  calc ∑ v ∈ Finset.range N, ∫ ω, ∑ v' ∈ Finset.range N, aT ψ X q v ω * aT ψ X q v' ω ∂μ
      = ∑ v ∈ Finset.range N, ∑ v' ∈ Finset.range N,
          ∫ ω, aT ψ X q v ω * aT ψ X q v' ω ∂μ :=
        Finset.sum_congr rfl fun v _ => integral_finset_sum _ (fun v' _ => hI v v')
    _ ≤ ∑ v ∈ Finset.range N, ∑ v' ∈ Finset.range N, (if v' = v then 2 * V else 0) :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun v' _ => by
          refine (H.pair_term_le q v q v').trans ?_
          by_cases h : v' = v
          · rw [if_pos h]
            have t1 : (if q = q ∧ v' = v then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
            have t2 : (if q = v ∧ v' = q then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
            have h3 := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hV0
            linarith
          · rw [if_neg h, if_neg (fun hh : q = q ∧ v' = v => h hh.2),
              if_neg (fun hh : q = v ∧ v' = q => h (hh.2.trans hh.1))]
            simp
    _ = 2 * (N : ℝ) * V := by
        have e : ∀ v ∈ Finset.range N,
            ∑ v' ∈ Finset.range N, (if v' = v then 2 * V else 0) = 2 * V := fun v hv => by
          rw [Finset.sum_ite_eq', if_pos hv]
        rw [Finset.sum_congr rfl e]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `E (∑_v ψ(X_q - X_v))² ≤ 4 N V + 2 ψ(0)²` for `q < N`. -/
theorem Hrow_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (N q : ℕ) (hq : q ∈ Finset.range N) :
    ∫ ω, Hrow ψ X N q ω ^ 2 ∂μ ≤ 4 * (N : ℝ) * V + 2 * ψ 0 ^ 2 := by
  have hpt : ∀ ω, Hrow ψ X N q ω ^ 2 ≤ 2 * Hoff ψ X N q ω ^ 2 + 2 * ψ 0 ^ 2 := by
    intro ω
    rw [Hrow_eq ψ X N q hq ω]
    nlinarith [_root_.sq_nonneg (Hoff ψ X N q ω - ψ 0)]
  have i1 : Integrable (fun ω => Hrow ψ X N q ω ^ 2) μ := (H.BM_Hrow N q).sqr.integrable
  have i2 : Integrable (fun ω => Hoff ψ X N q ω ^ 2) μ := (H.BM_Hoff N q).sqr.integrable
  calc ∫ ω, Hrow ψ X N q ω ^ 2 ∂μ ≤ ∫ ω, (2 * Hoff ψ X N q ω ^ 2 + 2 * ψ 0 ^ 2) ∂μ :=
        integral_mono i1 ((i2.const_mul 2).add (integrable_const _)) hpt
    _ = 2 * ∫ ω, Hoff ψ X N q ω ^ 2 ∂μ + 2 * ψ 0 ^ 2 := by
        rw [integral_add (i2.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 4 * (N : ℝ) * V + 2 * ψ 0 ^ 2 := by linarith [H.Hoff_sq N q]

/-- `E (∑_{i,j} ψ(X_i - X_j))² ≤ 4 N² V + 2 (N ψ(0))²` (all pairs). -/
theorem full_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (N : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) ^ 2 ∂μ
      ≤ 4 * (N : ℝ) ^ 2 * V + 2 * ((N : ℝ) * ψ 0) ^ 2 := by
  have bS : BM (Soff ψ X N) := ⟨H.Soff_meas N, _, H.Soff_bdd N⟩
  have hpt : ∀ ω, (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) ^ 2
      ≤ 2 * Soff ψ X N ω ^ 2 + 2 * ((N : ℝ) * ψ 0) ^ 2 := by
    intro ω
    rw [full_eq2 ψ X N ω]
    nlinarith [_root_.sq_nonneg (Soff ψ X N ω - (N : ℝ) * ψ 0)]
  have i1 : Integrable (fun ω =>
      (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) ^ 2) μ :=
    (H.BM_full N).sqr.integrable
  have i2 : Integrable (fun ω => Soff ψ X N ω ^ 2) μ := bS.sqr.integrable
  calc ∫ ω, (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) ^ 2 ∂μ
      ≤ ∫ ω, (2 * Soff ψ X N ω ^ 2 + 2 * ((N : ℝ) * ψ 0) ^ 2) ∂μ :=
        integral_mono i1 ((i2.const_mul 2).add (integrable_const _)) hpt
    _ = 2 * ∫ ω, Soff ψ X N ω ^ 2 ∂μ + 2 * ((N : ℝ) * ψ 0) ^ 2 := by
        rw [integral_add (i2.const_mul 2) (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ 4 * (N : ℝ) ^ 2 * V + 2 * ((N : ℝ) * ψ 0) ^ 2 := by linarith [H.second_moment N]

/-- `E|ψ(X_i - X_b)| ≤ ‖ψ‖₁` for `i ≠ b`. -/
theorem abs_mean [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) {i b : ℕ} (hib : i ≠ b) :
    ∫ ω, |ψ (X i ω - X b ω)| ∂μ ≤ L :=
  indep_integral_le ν (X b) (X i) (H.meas b) (H.meas i) (H.indep.indepFun hib.symm) (H.law b)
    (fun p : G × G => |ψ (p.2 - p.1)|)
    (continuous_abs.measurable.comp (H.psi_meas.comp (measurable_snd.sub measurable_fst)))
    (B := B)
    (fun p => by rw [abs_abs]; exact H.bound _)
    (fun y => hL y)

/-- `E|ψ(X_q - X_b)| |ψ(X_q - X_{b'})| ≤ ‖ψ‖₁²` for three distinct indices. -/
theorem abs_pair_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) {q b b' : ℕ} (hqb : q ≠ b) (hqb' : q ≠ b')
    (hbb' : b ≠ b') :
    ∫ ω, |ψ (X q ω - X b ω)| * |ψ (X q ω - X b' ω)| ∂μ ≤ L ^ 2 := by
  have hL0 : 0 ≤ L := le_trans (integral_nonneg fun z => abs_nonneg _) (hL 0)
  have hψm := H.psi_meas
  have r0 : Measurable fun p : G × (G × G) => p.1 := measurable_fst
  have r1 : Measurable fun p : G × (G × G) => p.2.1 := measurable_snd.fst
  have r2 : Measurable fun p : G × (G × G) => p.2.2 := measurable_snd.snd
  have s1 : ∫ ω, |ψ (X q ω - X b ω)| * |ψ (X q ω - X b' ω)| ∂μ
      ≤ ∫ ω, L * |ψ (X q ω - X b ω)| ∂μ :=
    indep_integral_le_fun ν (X b') (fun ω => (X q ω, X b ω)) (H.meas b')
      ((H.meas q).prodMk (H.meas b)) (indep_two X H.indep H.meas hqb'.symm hbb'.symm) (H.law b')
      (fun p : G × (G × G) => |ψ (p.2.1 - p.2.2)| * |ψ (p.2.1 - p.1)|)
      ((continuous_abs.measurable.comp (hψm.comp (r1.sub r2))).mul
        (continuous_abs.measurable.comp (hψm.comp (r1.sub r0))))
      (B := B * B) (Bg := L * B)
      (fun p => by
        rw [abs_mul, abs_abs, abs_abs]
        exact mul_le_mul (H.bound _) (H.bound _) (abs_nonneg _) H.B_nonneg)
      (fun y : G × G => L * |ψ (y.1 - y.2)|)
      ((continuous_abs.measurable.comp
        (hψm.comp (measurable_fst.sub measurable_snd))).const_mul L)
      (fun y => by
        rw [abs_mul, abs_abs, abs_of_nonneg hL0]
        exact mul_le_mul_of_nonneg_left (H.bound _) hL0)
      (fun y => by
        show ∫ z, |ψ (y.1 - y.2)| * |ψ (y.1 - z)| ∂ν ≤ L * |ψ (y.1 - y.2)|
        rw [integral_const_mul]
        calc |ψ (y.1 - y.2)| * ∫ z, |ψ (y.1 - z)| ∂ν ≤ |ψ (y.1 - y.2)| * L :=
              mul_le_mul_of_nonneg_left (hL _) (abs_nonneg _)
          _ = L * |ψ (y.1 - y.2)| := mul_comm _ _)
  calc ∫ ω, |ψ (X q ω - X b ω)| * |ψ (X q ω - X b' ω)| ∂μ
      ≤ ∫ ω, L * |ψ (X q ω - X b ω)| ∂μ := s1
    _ = L * ∫ ω, |ψ (X q ω - X b ω)| ∂μ := integral_const_mul _ _
    _ ≤ L * L := mul_le_mul_of_nonneg_left (H.abs_mean hL hqb) hL0
    _ = L ^ 2 := by ring

/-- The mean of `|a_{qb}| |a_{qb'}|` for the off-diagonal summands of one row. -/
theorem aT_abs_pair [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) (q b b' : ℕ) :
    ∫ ω, |aT ψ X q b ω| * |aT ψ X q b' ω| ∂μ
      ≤ L ^ 2 + V * (if b' = b then (1 : ℝ) else 0) := by
  have hV0 := H.V_nonneg
  have t : (0 : ℝ) ≤ (if b' = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hR : 0 ≤ L ^ 2 + V * (if b' = b then (1 : ℝ) else 0) :=
    add_nonneg (_root_.sq_nonneg L) (mul_nonneg hV0 t)
  by_cases hqb : q = b
  · have hz : (fun ω => |aT ψ X q b ω| * |aT ψ X q b' ω|) = fun _ => (0 : ℝ) := by
      funext ω; simp [aT, hqb]
    rw [hz, integral_zero]; exact hR
  by_cases hqb' : q = b'
  · have hz : (fun ω => |aT ψ X q b ω| * |aT ψ X q b' ω|) = fun _ => (0 : ℝ) := by
      funext ω; simp [aT, hqb']
    rw [hz, integral_zero]; exact hR
  have hA : (fun ω => |aT ψ X q b ω| * |aT ψ X q b' ω|)
      = fun ω => |ψ (X q ω - X b ω)| * |ψ (X q ω - X b' ω)| := by
    funext ω; simp [aT, hqb, hqb']
  rw [hA]
  by_cases hbb : b' = b
  · rw [if_pos hbb, mul_one, hbb]
    have e : (fun ω => |ψ (X q ω - X b ω)| * |ψ (X q ω - X b ω)|)
        = fun ω => ψ (X q ω - X b ω) ^ 2 := by
      funext ω; rw [abs_mul_abs_self]; ring
    rw [e]
    linarith [H.sq_le hqb, _root_.sq_nonneg L]
  · rw [if_neg hbb, mul_zero, add_zero]
    exact H.abs_pair_le hL hqb hqb' (Ne.symm hbb)

/-- `E (∑_b |a_{qb}|)² ≤ N² ‖ψ‖₁² + N V`. -/
theorem Sabs_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) (N q : ℕ) :
    ∫ ω, (∑ b ∈ Finset.range N, |aT ψ X q b ω|) ^ 2 ∂μ
      ≤ (N : ℝ) ^ 2 * L ^ 2 + (N : ℝ) * V := by
  have hS2 : ∀ ω, (∑ b ∈ Finset.range N, |aT ψ X q b ω|) ^ 2
      = ∑ b ∈ Finset.range N, ∑ b' ∈ Finset.range N,
          |aT ψ X q b ω| * |aT ψ X q b' ω| := by
    intro ω
    rw [pow_two, Finset.sum_mul_sum]
  have hI : ∀ b b', Integrable (fun ω => |aT ψ X q b ω| * |aT ψ X q b' ω|) μ := fun b b' =>
    BM.integrable ((H.BM_aT q b).absv.mul (H.BM_aT q b').absv)
  simp_rw [hS2]
  rw [integral_finset_sum _ (fun b _ => integrable_finset_sum _ fun b' _ => hI b b')]
  calc ∑ b ∈ Finset.range N,
        ∫ ω, ∑ b' ∈ Finset.range N, |aT ψ X q b ω| * |aT ψ X q b' ω| ∂μ
      = ∑ b ∈ Finset.range N, ∑ b' ∈ Finset.range N,
          ∫ ω, |aT ψ X q b ω| * |aT ψ X q b' ω| ∂μ :=
        Finset.sum_congr rfl fun b _ => integral_finset_sum _ (fun b' _ => hI b b')
    _ ≤ ∑ b ∈ Finset.range N, ∑ b' ∈ Finset.range N,
          (L ^ 2 + V * (if b' = b then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => H.aT_abs_pair hL q b b'
    _ = (N : ℝ) ^ 2 * L ^ 2 + (N : ℝ) * V := by
        have e : ∀ b ∈ Finset.range N, ∑ b' ∈ Finset.range N,
            (L ^ 2 + V * (if b' = b then (1 : ℝ) else 0)) = N * L ^ 2 + V := by
          intro b hb
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', if_pos hb]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        rw [Finset.sum_congr rfl e]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Deg2

/-! ### the three-point sums with a fixed last index `q` -/

/-- `A_q = ∑_{i,b} ψ(x_i - x_b) c(x_b - x_q)` (all `i, b < N`). -/
noncomputable def Aq {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (N q : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ψ (X i ω - X b ω) * c (X b ω - X q ω)

/-- The part of `A_q` with `i, b, q` distinct. -/
noncomputable def Iq {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (N q : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, bT ψ c X i b q ω

/-- The part of `A_q` with `i = q ≠ b`. -/
noncomputable def Dq {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (N q : ℕ)
    (ω : Ω) : ℝ :=
  ∑ b ∈ Finset.range N, dT ψ c X q b ω

/-- Everything that multiplies `H_q` and is treated by one Cauchy–Schwarz step:
    `I_q + c(0) ∑_{i ≠ q} ψ(x_q - x_i) + D_q + ∑_{i,j} ψ(x_i - x_j)`. -/
noncomputable def Apr {Ω G : Type*} [AddCommGroup G] (ψ c : G → ℝ) (X : ℕ → Ω → G) (N q : ℕ)
    (ω : Ω) : ℝ :=
  (Iq ψ c X N q ω + c 0 * Hoff ψ X N q ω)
    + (Dq ψ c X N q ω + ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω))

namespace Deg3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ c : G → ℝ}
  {Bψ Bc Vψ Vc : ℝ}

/-- The decomposition of `A_q` into the injective part and the three diagonals (`q < N`). -/
theorem Aq_eq (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N q : ℕ) (hq : q ∈ Finset.range N) (ω : Ω) :
    Aq ψ c X N q ω
      = Iq ψ c X N q ω + ψ 0 * Hrow c X N q ω + c 0 * Hoff ψ X N q ω + Dq ψ c X N q ω := by
  have hterm : ∀ i b : ℕ, ψ (X i ω - X b ω) * c (X b ω - X q ω)
      = bT ψ c X i b q ω + (if i = b then ψ 0 * c (X q ω - X b ω) else 0)
        + (if b = q then c 0 * aT ψ X q i ω else 0)
        + (if i = q then dT ψ c X q b ω else 0) := by
    intro i b
    by_cases hib : i = b
    · have hce : c (X b ω - X q ω) = c (X q ω - X b ω) := by rw [← H.hc.even, neg_sub]
      have hb0 : bT ψ c X i b q ω = 0 := by unfold bT; rw [if_pos (Or.inl hib)]
      have hψ0 : ψ (X i ω - X b ω) = ψ 0 := by rw [hib, sub_self]
      rw [hb0, if_pos hib, hψ0, hce]
      by_cases hbq : b = q
      · have hiq : i = q := hib.trans hbq
        have ha : aT ψ X q i ω = 0 := by unfold aT; rw [if_pos hiq.symm]
        have hd : dT ψ c X q b ω = 0 := by unfold dT; rw [if_pos hbq.symm]
        rw [if_pos hbq, if_pos hiq, ha, hd]; ring
      · have hiq : ¬ i = q := fun h => hbq (hib.symm.trans h)
        rw [if_neg hbq, if_neg hiq]; ring
    · rw [if_neg hib]
      by_cases hbq : b = q
      · have hb0 : bT ψ c X i b q ω = 0 := by
          unfold bT; rw [if_pos (Or.inr (Or.inl hbq))]
        have hiq : ¬ i = q := fun h => hib (h.trans hbq.symm)
        have ha : aT ψ X q i ω = ψ (X i ω - X b ω) := by
          unfold aT
          rw [if_neg (fun h : q = i => hiq h.symm), ← H.hψ.even, neg_sub, hbq]
        have hc0 : c (X b ω - X q ω) = c 0 := by rw [hbq, sub_self]
        rw [hb0, if_pos hbq, if_neg hiq, ha, hc0]; ring
      · rw [if_neg hbq]
        by_cases hiq : i = q
        · have hb0 : bT ψ c X i b q ω = 0 := by
            unfold bT; rw [if_pos (Or.inr (Or.inr hiq))]
          have hd : dT ψ c X q b ω = ψ (X i ω - X b ω) * c (X b ω - X q ω) := by
            unfold dT
            rw [if_neg (fun h : q = b => hbq h.symm), hiq]
          rw [hb0, if_pos hiq, hd]; ring
        · have hno : ¬ (i = b ∨ b = q ∨ i = q) := by
            rintro (h | h | h)
            · exact hib h
            · exact hbq h
            · exact hiq h
          have hb : bT ψ c X i b q ω = ψ (X i ω - X b ω) * c (X b ω - X q ω) := by
            unfold bT aP; rw [if_neg hno]
          rw [hb, if_neg hiq]; ring
  have e2 : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (if i = b then ψ 0 * c (X q ω - X b ω) else 0)
      = ψ 0 * ∑ v ∈ Finset.range N, c (X q ω - X v ω) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq, if_pos hi]
  have e3 : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (if b = q then c 0 * aT ψ X q i ω else 0)
      = c 0 * ∑ v ∈ Finset.range N, aT ψ X q v ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq', if_pos hq]
  have e4 : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (if i = q then dT ψ c X q b ω else 0)
      = ∑ b ∈ Finset.range N, dT ψ c X q b ω := by
    have h : ∀ i ∈ Finset.range N,
        ∑ b ∈ Finset.range N, (if i = q then dT ψ c X q b ω else 0)
          = if i = q then ∑ b ∈ Finset.range N, dT ψ c X q b ω else 0 := fun i _ => by
      by_cases hiq : i = q
      · simp only [if_pos hiq]
      · simp only [if_neg hiq, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_eq', if_pos hq]
  unfold Aq Iq Dq Hrow Hoff
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => hterm i b]
  simp only [Finset.sum_add_distrib]
  rw [e2, e3, e4]

theorem BM_bT (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j v : ℕ) : BM (bT ψ c X i j v) :=
  ⟨H.bT_meas i j v, _, H.bT_bound i j v⟩

theorem BM_dT (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j : ℕ) : BM (dT ψ c X i j) :=
  ⟨H.dT_meas i j, _, H.dT_bound i j⟩

theorem BM_aP (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (i j v : ℕ) : BM (aP ψ c X i j v) :=
  ⟨H.aP_meas i j v, _, H.aP_bound i j v⟩

theorem BM_Iq (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N q : ℕ) : BM (Iq ψ c X N q) := by
  show BM (fun ω => ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, bT ψ c X i b q ω)
  exact BM.sum (Finset.range N) (fun i ω => ∑ b ∈ Finset.range N, bT ψ c X i b q ω) fun i _ =>
    BM.sum (Finset.range N) (fun b => bT ψ c X i b q) fun b _ => H.BM_bT i b q

theorem BM_Dq (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N q : ℕ) : BM (Dq ψ c X N q) := by
  show BM (fun ω => ∑ b ∈ Finset.range N, dT ψ c X q b ω)
  exact BM.sum (Finset.range N) (fun b => dT ψ c X q b) fun b _ => H.BM_dT q b

theorem BM_Apr (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N q : ℕ) : BM (Apr ψ c X N q) := by
  show BM (fun ω => (Iq ψ c X N q ω + c 0 * Hoff ψ X N q ω)
    + (Dq ψ c X N q ω + ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)))
  exact ((H.BM_Iq N q).add (BM.const_mul (c 0) (H.hψ.BM_Hoff N q))).add
    ((H.BM_Dq N q).add (H.hψ.BM_full N))

/-- The mean of a product of two summands over injective triples is at most `V_ψ V_c`
    (AM–GM and `aP_sq_le`). -/
theorem aP_prod_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {i j v a b e : ℕ} (hij : i ≠ j) (hjv : j ≠ v)
    (hiv : i ≠ v) (hab : a ≠ b) (hbe : b ≠ e) (hae : a ≠ e) :
    ∫ ω, aP ψ c X i j v ω * aP ψ c X a b e ω ∂μ ≤ Vψ * Vc := by
  have s1 := H.aP_sq_le hij hjv hiv
  have s2 := H.aP_sq_le hab hbe hae
  have m1 := H.BM_aP i j v
  have m2 := H.BM_aP a b e
  have i1 : Integrable (fun ω => aP ψ c X i j v ω ^ 2) μ := m1.sqr.integrable
  have i2 : Integrable (fun ω => aP ψ c X a b e ω ^ 2) μ := m2.sqr.integrable
  have i12 : Integrable (fun ω => aP ψ c X i j v ω * aP ψ c X a b e ω) μ :=
    (m1.mul m2).integrable
  have i3 : Integrable (fun ω => (aP ψ c X i j v ω ^ 2 + aP ψ c X a b e ω ^ 2) / 2) μ :=
    (i1.add i2).div_const 2
  calc ∫ ω, aP ψ c X i j v ω * aP ψ c X a b e ω ∂μ
      ≤ ∫ ω, (aP ψ c X i j v ω ^ 2 + aP ψ c X a b e ω ^ 2) / 2 ∂μ :=
        integral_mono i12 i3 (fun ω => by
          have := _root_.sq_nonneg (aP ψ c X i j v ω - aP ψ c X a b e ω)
          show aP ψ c X i j v ω * aP ψ c X a b e ω
            ≤ (aP ψ c X i j v ω ^ 2 + aP ψ c X a b e ω ^ 2) / 2
          nlinarith)
    _ = (∫ ω, aP ψ c X i j v ω ^ 2 ∂μ + ∫ ω, aP ψ c X a b e ω ^ 2 ∂μ) / 2 := by
        rw [integral_div, integral_add i1 i2]
    _ ≤ Vψ * Vc := by linarith

/-- `E |ψ(X_i - X_b)| c(X_b - X_q)² ≤ V_c ‖ψ‖₁` for three distinct indices. -/
theorem abs_csq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) {i b q : ℕ}
    (hib : i ≠ b) (hiq : i ≠ q) (hbq : b ≠ q) :
    ∫ ω, |ψ (X i ω - X b ω)| * c (X b ω - X q ω) ^ 2 ∂μ ≤ Vc * L := by
  have hψm := H.hψ.psi_meas
  have hcm := H.hc.psi_meas
  have hVc := H.hc.V_nonneg
  have r0 : Measurable fun p : G × (G × G) => p.1 := measurable_fst
  have r1 : Measurable fun p : G × (G × G) => p.2.1 := measurable_snd.fst
  have r2 : Measurable fun p : G × (G × G) => p.2.2 := measurable_snd.snd
  have s1 : ∫ ω, |ψ (X i ω - X b ω)| * c (X b ω - X q ω) ^ 2 ∂μ
      ≤ ∫ ω, Vc * |ψ (X i ω - X b ω)| ∂μ :=
    indep_integral_le_fun ν (X q) (fun ω => (X i ω, X b ω)) (H.hψ.meas q)
      ((H.hψ.meas i).prodMk (H.hψ.meas b))
      (indep_two X H.hψ.indep H.hψ.meas hiq.symm hbq.symm) (H.hψ.law q)
      (fun p : G × (G × G) => |ψ (p.2.1 - p.2.2)| * c (p.2.2 - p.1) ^ 2)
      ((continuous_abs.measurable.comp (hψm.comp (r1.sub r2))).mul
        ((hcm.comp (r2.sub r0)).pow_const 2))
      (B := Bψ * Bc ^ 2) (Bg := Vc * Bψ)
      (fun p => by
        rw [abs_mul, abs_abs, abs_pow]
        exact mul_le_mul (H.hψ.bound _) (pow_le_pow_left₀ (abs_nonneg _) (H.hc.bound _) 2)
          (pow_nonneg (abs_nonneg _) 2) H.hψ.B_nonneg)
      (fun y : G × G => Vc * |ψ (y.1 - y.2)|)
      ((continuous_abs.measurable.comp
        (hψm.comp (measurable_fst.sub measurable_snd))).const_mul Vc)
      (fun y => by
        rw [abs_mul, abs_abs, abs_of_nonneg hVc]
        exact mul_le_mul_of_nonneg_left (H.hψ.bound _) hVc)
      (fun y => by
        show ∫ z, |ψ (y.1 - y.2)| * c (y.2 - z) ^ 2 ∂ν ≤ Vc * |ψ (y.1 - y.2)|
        rw [integral_const_mul]
        calc |ψ (y.1 - y.2)| * ∫ z, c (y.2 - z) ^ 2 ∂ν ≤ |ψ (y.1 - y.2)| * Vc :=
              mul_le_mul_of_nonneg_left (H.hc.var _) (abs_nonneg _)
          _ = Vc * |ψ (y.1 - y.2)| := mul_comm _ _)
  calc ∫ ω, |ψ (X i ω - X b ω)| * c (X b ω - X q ω) ^ 2 ∂μ
      ≤ ∫ ω, Vc * |ψ (X i ω - X b ω)| ∂μ := s1
    _ = Vc * ∫ ω, |ψ (X i ω - X b ω)| ∂μ := integral_const_mul _ _
    _ ≤ Vc * L := mul_le_mul_of_nonneg_left (H.hψ.abs_mean hL hib) hVc

/-- `E |ψ(X_i - X_b)| |ψ(X_i - X_{b'})| c(X_b - X_q)² ≤ ‖ψ‖₁² V_c` for four distinct indices
    (integrate `x_{b'}`, then `x_q`, then `x_b`). -/
theorem chain1 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L)
    {i b b' q : ℕ} (hib : i ≠ b) (hib' : i ≠ b') (hbb' : b ≠ b') (hiq : i ≠ q) (hbq : b ≠ q)
    (hb'q : b' ≠ q) :
    ∫ ω, |ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2 ∂μ
      ≤ L ^ 2 * Vc := by
  have hψm := H.hψ.psi_meas
  have hcm := H.hc.psi_meas
  have hL0 : 0 ≤ L := le_trans (integral_nonneg fun z => abs_nonneg _) (hL 0)
  have hBψ := H.hψ.B_nonneg
  have q0 : Measurable fun p : G × (G × G × G) => p.1 := measurable_fst
  have q1 : Measurable fun p : G × (G × G × G) => p.2.1 := measurable_snd.fst
  have q2 : Measurable fun p : G × (G × G × G) => p.2.2.1 := measurable_snd.snd.fst
  have q3 : Measurable fun p : G × (G × G × G) => p.2.2.2 := measurable_snd.snd.snd
  have g1 : Measurable fun y : G × G × G => y.1 := measurable_fst
  have g2 : Measurable fun y : G × G × G => y.2.1 := measurable_snd.fst
  have g3 : Measurable fun y : G × G × G => y.2.2 := measurable_snd.snd
  have s1 : ∫ ω, |ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2 ∂μ
      ≤ ∫ ω, L * (|ψ (X i ω - X b ω)| * c (X b ω - X q ω) ^ 2) ∂μ :=
    indep_integral_le_fun ν (X b') (fun ω => (X i ω, X b ω, X q ω)) (H.hψ.meas b')
      ((H.hψ.meas i).prodMk ((H.hψ.meas b).prodMk (H.hψ.meas q)))
      (indep_three X H.hψ.indep H.hψ.meas hib'.symm hbb'.symm hb'q) (H.hψ.law b')
      (fun p : G × (G × G × G) =>
        |ψ (p.2.1 - p.2.2.1)| * |ψ (p.2.1 - p.1)| * c (p.2.2.1 - p.2.2.2) ^ 2)
      (((continuous_abs.measurable.comp (hψm.comp (q1.sub q2))).mul
        (continuous_abs.measurable.comp (hψm.comp (q1.sub q0)))).mul
        ((hcm.comp (q2.sub q3)).pow_const 2))
      (B := Bψ * Bψ * Bc ^ 2) (Bg := L * (Bψ * Bc ^ 2))
      (fun p => by
        rw [abs_mul, abs_mul, abs_abs, abs_abs, abs_pow]
        exact mul_le_mul (mul_le_mul (H.hψ.bound _) (H.hψ.bound _) (abs_nonneg _) hBψ)
          (pow_le_pow_left₀ (abs_nonneg _) (H.hc.bound _) 2) (pow_nonneg (abs_nonneg _) 2)
          (mul_nonneg hBψ hBψ))
      (fun y : G × G × G => L * (|ψ (y.1 - y.2.1)| * c (y.2.1 - y.2.2) ^ 2))
      (((continuous_abs.measurable.comp (hψm.comp (g1.sub g2))).mul
        ((hcm.comp (g2.sub g3)).pow_const 2)).const_mul L)
      (fun y => by
        rw [abs_mul, abs_of_nonneg hL0, abs_mul, abs_abs, abs_pow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (H.hψ.bound _) (pow_le_pow_left₀ (abs_nonneg _) (H.hc.bound _) 2)
            (pow_nonneg (abs_nonneg _) 2) hBψ) hL0)
      (fun y => by
        show ∫ z, |ψ (y.1 - y.2.1)| * |ψ (y.1 - z)| * c (y.2.1 - y.2.2) ^ 2 ∂ν
          ≤ L * (|ψ (y.1 - y.2.1)| * c (y.2.1 - y.2.2) ^ 2)
        have e' : (fun z => |ψ (y.1 - y.2.1)| * |ψ (y.1 - z)| * c (y.2.1 - y.2.2) ^ 2)
            = fun z => (|ψ (y.1 - y.2.1)| * c (y.2.1 - y.2.2) ^ 2) * |ψ (y.1 - z)| := by
          funext z; ring
        rw [e', integral_const_mul]
        calc (|ψ (y.1 - y.2.1)| * c (y.2.1 - y.2.2) ^ 2) * ∫ z, |ψ (y.1 - z)| ∂ν
            ≤ (|ψ (y.1 - y.2.1)| * c (y.2.1 - y.2.2) ^ 2) * L :=
              mul_le_mul_of_nonneg_left (hL _)
                (mul_nonneg (abs_nonneg _) (_root_.sq_nonneg _))
          _ = L * (|ψ (y.1 - y.2.1)| * c (y.2.1 - y.2.2) ^ 2) := mul_comm _ _)
  calc ∫ ω, |ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2 ∂μ
      ≤ ∫ ω, L * (|ψ (X i ω - X b ω)| * c (X b ω - X q ω) ^ 2) ∂μ := s1
    _ = L * ∫ ω, |ψ (X i ω - X b ω)| * c (X b ω - X q ω) ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ L * (Vc * L) := mul_le_mul_of_nonneg_left (H.abs_csq hL hib hiq hbq) hL0
    _ = L ^ 2 * Vc := by ring

/-- **The pairs with a common first index only**: for `i, b, b', q` distinct,
    `E[ψ_{ib} c_{bq} ψ_{ib'} c_{b'q}] ≤ ‖ψ‖₁² V_c` (this is the Young inequality
    `‖ψ * c‖₂ ≤ ‖ψ‖₁ ‖c‖₂`, written with absolute values and AM–GM). -/
theorem chain_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L)
    {i b b' q : ℕ} (hib : i ≠ b) (hib' : i ≠ b') (hbb' : b ≠ b') (hiq : i ≠ q) (hbq : b ≠ q)
    (hb'q : b' ≠ q) :
    ∫ ω, aP ψ c X i b q ω * aP ψ c X i b' q ω ∂μ ≤ L ^ 2 * Vc := by
  have h1 := H.chain1 hL hib hib' hbb' hiq hbq hb'q
  have h2 := H.chain1 hL hib' hib hbb'.symm hiq hb'q hbq
  have b1 : BM (fun ω => |ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2) :=
    ((H.hψ.BM_psi i b).absv.mul (H.hψ.BM_psi i b').absv).mul (H.hc.BM_psi b q).sqr
  have b2 : BM (fun ω =>
      |ψ (X i ω - X b' ω)| * |ψ (X i ω - X b ω)| * c (X b' ω - X q ω) ^ 2) :=
    ((H.hψ.BM_psi i b').absv.mul (H.hψ.BM_psi i b).absv).mul (H.hc.BM_psi b' q).sqr
  have i1 : Integrable (fun ω =>
      |ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2) μ := b1.integrable
  have i2 : Integrable (fun ω =>
      |ψ (X i ω - X b' ω)| * |ψ (X i ω - X b ω)| * c (X b' ω - X q ω) ^ 2) μ := b2.integrable
  have i12 : Integrable (fun ω => aP ψ c X i b q ω * aP ψ c X i b' q ω) μ :=
    ((H.BM_aP i b q).mul (H.BM_aP i b' q)).integrable
  have i3 : Integrable (fun ω =>
      (|ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2
        + |ψ (X i ω - X b' ω)| * |ψ (X i ω - X b ω)| * c (X b' ω - X q ω) ^ 2) / 2) μ :=
    (i1.add i2).div_const 2
  calc ∫ ω, aP ψ c X i b q ω * aP ψ c X i b' q ω ∂μ
      ≤ ∫ ω, (|ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2
          + |ψ (X i ω - X b' ω)| * |ψ (X i ω - X b ω)| * c (X b' ω - X q ω) ^ 2) / 2 ∂μ :=
        integral_mono i12 i3 (fun ω => by
          show aP ψ c X i b q ω * aP ψ c X i b' q ω
            ≤ (|ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2
              + |ψ (X i ω - X b' ω)| * |ψ (X i ω - X b ω)| * c (X b' ω - X q ω) ^ 2) / 2
          unfold aP
          exact amgm4 _ _ _ _)
    _ = (∫ ω, |ψ (X i ω - X b ω)| * |ψ (X i ω - X b' ω)| * c (X b ω - X q ω) ^ 2 ∂μ
          + ∫ ω, |ψ (X i ω - X b' ω)| * |ψ (X i ω - X b ω)| * c (X b' ω - X q ω) ^ 2 ∂μ) / 2 := by
        rw [integral_div, integral_add i1 i2]
    _ ≤ L ^ 2 * Vc := by linarith

/-- **The mean of a product of two summands of `I_q`**: it vanishes unless the first index of
    each pair occurs in the other pair; a common first index costs `‖ψ‖₁² V_c`, the two pairs
    with equal index sets cost `V_ψ V_c`. -/
theorem pairI_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L)
    (q i b i' b' : ℕ) :
    ∫ ω, bT ψ c X i b q ω * bT ψ c X i' b' q ω ∂μ
      ≤ L ^ 2 * Vc * (if i' = i then (1 : ℝ) else 0)
        + Vψ * Vc * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
          + (if i' = b ∧ b' = i then (1 : ℝ) else 0)) := by
  have hA0 : 0 ≤ L ^ 2 * Vc := mul_nonneg (_root_.sq_nonneg L) H.hc.V_nonneg
  have hW0 : 0 ≤ Vψ * Vc := mul_nonneg H.hψ.V_nonneg H.hc.V_nonneg
  have t0 : (0 : ℝ) ≤ (if i' = i then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t1 : (0 : ℝ) ≤ (if i' = i ∧ b' = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t2 : (0 : ℝ) ≤ (if i' = b ∧ b' = i then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hR : 0 ≤ L ^ 2 * Vc * (if i' = i then (1 : ℝ) else 0)
      + Vψ * Vc * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
        + (if i' = b ∧ b' = i then (1 : ℝ) else 0)) :=
    add_nonneg (mul_nonneg hA0 t0) (mul_nonneg hW0 (add_nonneg t1 t2))
  by_cases h : i = b ∨ b = q ∨ i = q
  · have hz : (fun ω => bT ψ c X i b q ω * bT ψ c X i' b' q ω) = fun _ => (0 : ℝ) := by
      funext ω; unfold bT; rw [if_pos h, zero_mul]
    rw [hz, integral_zero]; exact hR
  by_cases h' : i' = b' ∨ b' = q ∨ i' = q
  · have hz : (fun ω => bT ψ c X i b q ω * bT ψ c X i' b' q ω) = fun _ => (0 : ℝ) := by
      funext ω; unfold bT; rw [if_pos h', mul_zero]
    rw [hz, integral_zero]; exact hR
  have hA : (fun ω => bT ψ c X i b q ω * bT ψ c X i' b' q ω)
      = fun ω => aP ψ c X i b q ω * aP ψ c X i' b' q ω := by
    funext ω; unfold bT; rw [if_neg h, if_neg h']
  rw [hA]
  have hib : i ≠ b := fun e => h (Or.inl e)
  have hbq : b ≠ q := fun e => h (Or.inr (Or.inl e))
  have hiq : i ≠ q := fun e => h (Or.inr (Or.inr e))
  have hi'b' : i' ≠ b' := fun e => h' (Or.inl e)
  have hb'q : b' ≠ q := fun e => h' (Or.inr (Or.inl e))
  have hi'q : i' ≠ q := fun e => h' (Or.inr (Or.inr e))
  by_cases f1 : i ≠ i' ∧ i ≠ b'
  · rw [H.free_i hib hiq f1.1 f1.2 hiq]; exact hR
  by_cases f2 : i' ≠ i ∧ i' ≠ b
  · have e : (fun ω => aP ψ c X i b q ω * aP ψ c X i' b' q ω)
        = fun ω => aP ψ c X i' b' q ω * aP ψ c X i b q ω := by
      funext ω; ring
    rw [e, H.free_i hi'b' hi'q f2.1 f2.2 hi'q]; exact hR
  by_cases hii : i' = i
  · by_cases hbb : b' = b
    · have key := H.aP_prod_le hib hbq hiq hi'b' hb'q hi'q
      rw [if_pos (And.intro hii hbb)]
      have u0 := mul_nonneg hA0 t0
      have u2 := mul_nonneg hW0 t2
      linarith
    · have hib2 : i ≠ b' := fun e => hi'b' (hii.trans e)
      have key := H.chain_le hL hib hib2 (Ne.symm hbb) hiq hbq hb'q
      have u1 : (0 : ℝ) ≤ (if i = i ∧ b' = b then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      have u2 : (0 : ℝ) ≤ (if i = b ∧ b' = i then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      have u3 := mul_nonneg hW0 (add_nonneg u1 u2)
      have e0 : (if i = i then (1 : ℝ) else 0) = 1 := if_pos rfl
      rw [hii, e0]
      linarith
  · have k1 : i = b' := by omega
    have k2 : i' = b := by omega
    have key := H.aP_prod_le hib hbq hiq hi'b' hb'q hi'q
    rw [if_pos (And.intro k2 k1.symm)]
    have u0 := mul_nonneg hA0 t0
    have u1 := mul_nonneg hW0 t1
    linarith

/-- **Second moment of `I_q`**: `E I_q² ≤ N³ ‖ψ‖₁² V_c + 2 N² V_ψ V_c`. -/
theorem Iq_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) (N q : ℕ) :
    ∫ ω, Iq ψ c X N q ω ^ 2 ∂μ
      ≤ (N : ℝ) ^ 3 * (L ^ 2 * Vc) + 2 * (N : ℝ) ^ 2 * (Vψ * Vc) := by
  have hS2 : ∀ ω, Iq ψ c X N q ω ^ 2
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, bT ψ c X i b q ω * bT ψ c X i' b' q ω := by
    intro ω
    unfold Iq
    rw [pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
  have h4 : ∫ ω, ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
        ∑ b' ∈ Finset.range N, bT ψ c X i b q ω * bT ψ c X i' b' q ω ∂μ
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, ∫ ω, bT ψ c X i b q ω * bT ψ c X i' b' q ω ∂μ :=
    integral_sum4 (Finset.range N) (fun i b i' b' ω => bT ψ c X i b q ω * bT ψ c X i' b' q ω)
      (fun i b i' b' => ((H.BM_bT i b q).mul (H.BM_bT i' b' q)).integrable)
  simp_rw [hS2]
  rw [h4]
  calc ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, ∫ ω, bT ψ c X i b q ω * bT ψ c X i' b' q ω ∂μ
      ≤ ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, (L ^ 2 * Vc * (if i' = i then (1 : ℝ) else 0)
            + Vψ * Vc * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
              + (if i' = b ∧ b' = i then (1 : ℝ) else 0))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i' _ =>
          Finset.sum_le_sum fun b' _ => H.pairI_le hL q i b i' b'
    _ = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
          (L ^ 2 * Vc * N + Vψ * Vc * (1 + 1)) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun b hb => ?_
        have e : ∑ i' ∈ Finset.range N, ∑ b' ∈ Finset.range N,
              (L ^ 2 * Vc * (if i' = i then (1 : ℝ) else 0)
                + Vψ * Vc * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
                  + (if i' = b ∧ b' = i then (1 : ℝ) else 0)))
            = L ^ 2 * Vc * (∑ i' ∈ Finset.range N, ∑ _b' ∈ Finset.range N,
                  (if i' = i then (1 : ℝ) else 0))
              + Vψ * Vc * (∑ i' ∈ Finset.range N, ∑ b' ∈ Finset.range N,
                  (if i' = i ∧ b' = b then (1 : ℝ) else 0)
                + ∑ i' ∈ Finset.range N, ∑ b' ∈ Finset.range N,
                  (if i' = b ∧ b' = i then (1 : ℝ) else 0)) := by
          simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
        rw [e, cnt_first N i hi, count1 N i b hi hb, count1 N b i hb hi]
    _ = (N : ℝ) ^ 3 * (L ^ 2 * Vc) + 2 * (N : ℝ) ^ 2 * (Vψ * Vc) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem dT_le_aT (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (q b : ℕ) (ω : Ω) :
    |dT ψ c X q b ω| ≤ Bc * |aT ψ X q b ω| := by
  unfold dT aT
  by_cases h : q = b
  · simp only [if_pos h, abs_zero, mul_zero, le_refl]
  · rw [if_neg h, if_neg h, abs_mul]
    calc |ψ (X q ω - X b ω)| * |c (X b ω - X q ω)| ≤ |ψ (X q ω - X b ω)| * Bc :=
          mul_le_mul_of_nonneg_left (H.hc.bound _) (abs_nonneg _)
      _ = Bc * |ψ (X q ω - X b ω)| := mul_comm _ _

/-- **Second moment of `D_q`**: `E D_q² ≤ B_c² (N² ‖ψ‖₁² + N V_ψ)`. -/
theorem Dq_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) (N q : ℕ) :
    ∫ ω, Dq ψ c X N q ω ^ 2 ∂μ ≤ Bc ^ 2 * ((N : ℝ) ^ 2 * L ^ 2 + (N : ℝ) * Vψ) := by
  have hpt : ∀ ω, Dq ψ c X N q ω ^ 2
      ≤ Bc ^ 2 * (∑ b ∈ Finset.range N, |aT ψ X q b ω|) ^ 2 := by
    intro ω
    have h1 : |Dq ψ c X N q ω| ≤ Bc * ∑ b ∈ Finset.range N, |aT ψ X q b ω| := by
      unfold Dq
      rw [Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun b _ => H.dT_le_aT q b ω)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow] at h2
    exact h2
  have b1 : BM (fun ω => ∑ b ∈ Finset.range N, |aT ψ X q b ω|) :=
    BM.sum (Finset.range N) (fun b ω => |aT ψ X q b ω|) fun b _ => (H.hψ.BM_aT q b).absv
  have i1 : Integrable (fun ω => Dq ψ c X N q ω ^ 2) μ := (H.BM_Dq N q).sqr.integrable
  have i2 : Integrable (fun ω => Bc ^ 2 * (∑ b ∈ Finset.range N, |aT ψ X q b ω|) ^ 2) μ :=
    (BM.const_mul (Bc ^ 2) b1.sqr).integrable
  calc ∫ ω, Dq ψ c X N q ω ^ 2 ∂μ
      ≤ ∫ ω, Bc ^ 2 * (∑ b ∈ Finset.range N, |aT ψ X q b ω|) ^ 2 ∂μ :=
        integral_mono i1 i2 hpt
    _ = Bc ^ 2 * ∫ ω, (∑ b ∈ Finset.range N, |aT ψ X q b ω|) ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ Bc ^ 2 * ((N : ℝ) ^ 2 * L ^ 2 + (N : ℝ) * Vψ) :=
        mul_le_mul_of_nonneg_left (H.hψ.Sabs_sq hL N q) (_root_.sq_nonneg Bc)

/-- **Second moment of the factor of `H_q`**. -/
theorem Apr_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) {L : ℝ} (hL : ∀ x, ∫ z, |ψ (x - z)| ∂ν ≤ L) (N q : ℕ) :
    ∫ ω, Apr ψ c X N q ω ^ 2 ∂μ
      ≤ 2 * (2 * ((N : ℝ) ^ 3 * (L ^ 2 * Vc) + 2 * (N : ℝ) ^ 2 * (Vψ * Vc))
            + 2 * (c 0 ^ 2 * (2 * (N : ℝ) * Vψ)))
        + 2 * (2 * (Bc ^ 2 * ((N : ℝ) ^ 2 * L ^ 2 + (N : ℝ) * Vψ))
            + 2 * (4 * (N : ℝ) ^ 2 * Vψ + 2 * ((N : ℝ) * ψ 0) ^ 2)) := by
  have h1 := H.Iq_sq hL N q
  have h2 : ∫ ω, (c 0 * Hoff ψ X N q ω) ^ 2 ∂μ ≤ c 0 ^ 2 * (2 * (N : ℝ) * Vψ) := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (H.hψ.Hoff_sq N q) (_root_.sq_nonneg _)
  have h3 := H.Dq_sq hL N q
  have h4 := H.hψ.full_sq N
  have b1 := H.BM_Iq N q
  have b2 : BM (fun ω => c 0 * Hoff ψ X N q ω) := BM.const_mul (c 0) (H.hψ.BM_Hoff N q)
  have b3 := H.BM_Dq N q
  have b4 := H.hψ.BM_full N
  have h12 := sq2_int (μ := μ) b1 b2 h1 h2
  have h34 := sq2_int (μ := μ) b3 b4 h3 h4
  have h := sq2_int (μ := μ) (b1.add b2) (b3.add b4) h12 h34
  exact h

end Deg3
/-! ### `Z¹[F_A', a = 3]` on the torus -/

/-- Pure arithmetic: the bound of `Deg3.Apr_sq` with the torus constants is `≤ 76 N³ M m²`. -/
theorem PA_arith {M m N c0 p0 PA : ℝ} (hM1 : 1 ≤ M) (hMN : M ≤ N) (hm : 0 ≤ m)
    (hc : c0 ^ 2 ≤ M ^ 2) (hp : p0 ^ 2 ≤ (M * m) ^ 2)
    (h : PA ≤ 2 * (2 * (N ^ 3 * ((2 * m) ^ 2 * M) + 2 * N ^ 2 * (M * m ^ 2 * M))
            + 2 * (c0 ^ 2 * (2 * N * (M * m ^ 2))))
        + 2 * (2 * (M ^ 2 * (N ^ 2 * (2 * m) ^ 2 + N * (M * m ^ 2)))
            + 2 * (4 * N ^ 2 * (M * m ^ 2) + 2 * (N * p0) ^ 2))) :
    PA ≤ 76 * N ^ 3 * M * m ^ 2 := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hMm2 : 0 ≤ M * m ^ 2 := mul_nonneg hM0 (_root_.sq_nonneg m)
  have u1 : c0 ^ 2 * (2 * N * (M * m ^ 2)) ≤ M ^ 2 * (2 * N * (M * m ^ 2)) :=
    mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg zero_le_two hN0) hMm2)
  have u2 : N ^ 2 * p0 ^ 2 ≤ N ^ 2 * (M * m) ^ 2 :=
    mul_le_mul_of_nonneg_left hp (_root_.sq_nonneg N)
  have u3 : 0 ≤ N ^ 2 * (M * m ^ 2) * (N - M) :=
    mul_nonneg (mul_nonneg (_root_.sq_nonneg N) hMm2) (sub_nonneg.mpr hMN)
  have u4a : 0 ≤ N ^ 2 - M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hMN) (add_nonneg hN0 hM0)]
  have u4 : 0 ≤ N * (M * m ^ 2) * (N ^ 2 - M ^ 2) := mul_nonneg (mul_nonneg hN0 hMm2) u4a
  have u5 : 0 ≤ N ^ 2 * (M * m ^ 2) * (N - 1) :=
    mul_nonneg (mul_nonneg (_root_.sq_nonneg N) hMm2) (sub_nonneg.mpr hN1)
  nlinarith [u1, u2, u3, u4, u5]

/-- Pure arithmetic for the final bound of `Z¹[F_A',3]`. -/
theorem FA3_arith {M m m' N p0 c0 s Z : ℝ} (hM1 : 1 ≤ M) (hMN : M ≤ N) (hm : 0 ≤ m)
    (hm0 : 0 ≤ m') (hm' : m' ≤ m) (hp0 : 0 ≤ p0) (hp : p0 ≤ M * m) (hc0 : 0 ≤ c0)
    (hc : c0 ≤ M) (hs0 : 0 ≤ s) (hs : s ≤ 2 * M)
    (hZ : Z ≤ 1 / N ^ 4 * (N * (22 * N ^ 2 * M * m + (p0 + m' * N) * (6 * N * M))
      + m' * N ^ 2 * (N * s + N * c0))) :
    Z ≤ 37 * (M / N) * m := by
  have hN : 0 < N := by linarith
  have hM0 : 0 ≤ M := by linarith
  have t1 : m' * N ≤ m * N := mul_le_mul_of_nonneg_right hm' hN.le
  have t2 : (p0 + m' * N) * (6 * N * M) ≤ (M * m + m * N) * (6 * N * M) :=
    mul_le_mul_of_nonneg_right (by linarith)
      (mul_nonneg (mul_nonneg (by norm_num) hN.le) hM0)
  have t3 : N * ((p0 + m' * N) * (6 * N * M)) ≤ N * ((M * m + m * N) * (6 * N * M)) :=
    mul_le_mul_of_nonneg_left t2 hN.le
  have t4 : N * s + N * c0 ≤ N * (2 * M) + N * M := by
    have := mul_le_mul_of_nonneg_left hs hN.le
    have := mul_le_mul_of_nonneg_left hc hN.le
    linarith
  have t5 : m' * N ^ 2 * (N * s + N * c0) ≤ m * N ^ 2 * (N * (2 * M) + N * M) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hm' (_root_.sq_nonneg N)) t4
      (add_nonneg (mul_nonneg hN.le hs0) (mul_nonneg hN.le hc0))
      (mul_nonneg hm (_root_.sq_nonneg N))
  have t6 : 0 ≤ N ^ 2 * M * m * (N - M) :=
    mul_nonneg (mul_nonneg (mul_nonneg (_root_.sq_nonneg N) hM0) hm) (sub_nonneg.mpr hMN)
  have hin : N * (22 * N ^ 2 * M * m + (p0 + m' * N) * (6 * N * M))
      + m' * N ^ 2 * (N * s + N * c0) ≤ 37 * N ^ 3 * M * m := by
    nlinarith [t3, t5, t6]
  have h1 := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ 1 / N ^ 4)
  have e : 1 / N ^ 4 * (37 * N ^ 3 * M * m) = 37 * (M / N) * m := by
    have hN' : N ≠ 0 := hN.ne'
    first | (field_simp; ring) | field_simp
  linarith

/-- The four-index sum, with the sum over `v` collected in the row sum `H_q` of `c`, and
    `F_A = φ⁰ + m_{k+1}`, `p = c + 1` inserted. -/
theorem T4_eq {Ω : Type*} {d : ℕ} (σ : ℝ) (k N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω)
      = ∑ q ∈ Finset.range N,
          (Aq (phi0 d σ k) (cK d σ) X N q ω
            + (∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, phi0 d σ k (X i ω - X b ω))
            + torusM d σ (k + 1) * (N * Hrow (cK d σ) X N q ω)
            + torusM d σ (k + 1) * (N : ℝ) ^ 2) * Hrow (cK d σ) X N q ω := by
  have hq : ∀ q : ℕ, ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω)
      = Aq (phi0 d σ k) (cK d σ) X N q ω
        + (∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, phi0 d σ k (X i ω - X b ω))
        + torusM d σ (k + 1) * (N * Hrow (cK d σ) X N q ω)
        + torusM d σ (k + 1) * (N : ℝ) ^ 2 := by
    intro q
    have hterm : ∀ i b : ℕ, FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω)
        = phi0 d σ k (X i ω - X b ω) * cK d σ (X b ω - X q ω) + phi0 d σ k (X i ω - X b ω)
          + torusM d σ (k + 1) * cK d σ (X q ω - X b ω) + torusM d σ (k + 1) := by
      intro i b
      have e1 : cK d σ (X q ω - X b ω) = cK d σ (X b ω - X q ω) := by
        rw [← cK_even, neg_sub]
      rw [FA_eq, e1]
      unfold cK
      ring
    unfold Aq Hrow
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => hterm i b]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  calc ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ∑ v ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω)
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * Hrow (cK d σ) X N q ω := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun q _ => ?_
        unfold Hrow
        rw [Finset.mul_sum]
    _ = ∑ q ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * Hrow (cK d σ) X N q ω :=
        (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ q ∈ Finset.range N, (∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω)) * Hrow (cK d σ) X N q ω := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ = _ := Finset.sum_congr rfl fun q _ => by rw [hq q]

/-- `Z¹[F_A', a = 3]` of a sample as a sum over `Finset.range N`. -/
theorem Z1_FA3_conv {d : ℕ} (σ : ℝ) (k N : ℕ) (x : ℕ → FlatTorus d) :
    Zs1three3 N (fun i b j : Fin N => FA' d σ k (x i) (x b) (x j)) (cmat d σ N x)
      = 1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
          ∑ v ∈ Finset.range N,
            FA d σ k (x i) (x b) * pker d σ (x b - x q) * cK d σ (x q - x v) :=
  congrArg (fun t => 1 / (N : ℝ) ^ 4 * t)
    ((Fin.sum_univ_eq_sum_range (fun i => ∑ b : Fin N, ∑ j : Fin N, ∑ v : Fin N,
        FA' d σ k (x i) (x b) (x j) * (pker d σ (x j - x v) - 1)) N).trans
      (Finset.sum_congr rfl fun i _ =>
        (Fin.sum_univ_eq_sum_range (fun b => ∑ j : Fin N, ∑ v : Fin N,
          FA' d σ k (x i) (x b) (x j) * (pker d σ (x j - x v) - 1)) N).trans
        (Finset.sum_congr rfl fun b _ =>
          (Fin.sum_univ_eq_sum_range (fun j => ∑ v : Fin N,
            FA' d σ k (x i) (x b) (x j) * (pker d σ (x j - x v) - 1)) N).trans
          (Finset.sum_congr rfl fun j _ =>
            Fin.sum_univ_eq_sum_range (fun v =>
              FA d σ k (x i) (x b) * pker d σ (x b - x j) * cK d σ (x j - x v)) N))))

section SampleFA3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem BM_FA {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k) (i b : ℕ) :
    BM (fun ω => FA d σ k (X i ω) (X b ω)) := by
  have hφ : BM (fun ω => phi0 d σ k (X i ω - X b ω)) :=
    ⟨(phi0_continuous hσ d k hk).measurable.comp ((hX i).sub (hX b)), _,
      fun ω => phi0_bound hσ d k hk _⟩
  have h : BM (fun ω => phi0 d σ k (X i ω - X b ω) + torusM d σ (k + 1)) :=
    hφ.add (BM.const (torusM d σ (k + 1)))
  have e : (fun ω => FA d σ k (X i ω) (X b ω))
      = fun ω => phi0 d σ k (X i ω - X b ω) + torusM d σ (k + 1) := by
    funext ω; rw [FA_eq]
  rw [e]; exact h

theorem BM_pker {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) (a b : ℕ) : BM (fun ω => pker d σ (X a ω - X b ω)) :=
  ⟨(pker_continuous hσ d).measurable.comp ((hX a).sub (hX b)), torusM d σ 1, fun ω => by
    rw [abs_of_nonneg (psiK_facts hσ d 1 le_rfl _).1]
    exact (psiK_facts hσ d 1 le_rfl _).2.1⟩

theorem BM_cK {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) (a b : ℕ) : BM (fun ω => cK d σ (X a ω - X b ω)) :=
  ⟨((pker_continuous hσ d).sub continuous_const).measurable.comp ((hX a).sub (hX b)), _,
    fun ω => (cK_facts hσ d _).1⟩

/-- **`E|Z¹[F_A', a = 3]| ≤ 37 (M/N) m_k`** for `M ≤ N`: the third statistic of the first
    summand of `Π_k`. -/
theorem Z1_FA3_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
        (cmat d σ N (fun j => X j ω))| ∂μ
      ≤ 37 * (torusM d σ 1 / N) * torusM d σ k := by
  have H := torus_deg3F X h_indep hX hlaw hσ k hk
  have hL := phi0_l1 hσ d k hk
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 4 := by positivity
  have hM1 := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  obtain ⟨-, -, f2, f3⟩ := phi_facts hσ d k hk 0
  have hm0 : 0 ≤ torusM d σ k := f2.trans f3
  have hp := phi0_bound hσ d k hk 0
  have hc := (cK_facts hσ d 0).1
  have hc2 : cK d σ 0 ^ 2 ≤ torusM d σ 1 ^ 2 := sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2
  have hp2 : phi0 d σ k 0 ^ 2 ≤ (torusM d σ 1 * torusM d σ k) ^ 2 :=
    sq_le_sq' (abs_le.mp hp).1 (abs_le.mp hp).2
  have hs3 : Real.sqrt (2 * torusM d σ 1) ≤ 2 * torusM d σ 1 :=
    sqrt_le_of_sq (mul_nonneg zero_le_two hM0) (by
      nlinarith [mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ 2 * torusM d σ 1 - 1)])
  -- second moments for a fixed `q`
  have hQ : ∀ q ∈ Finset.range N,
      ∫ ω, Hrow (cK d σ) X N q ω ^ 2 ∂μ ≤ 6 * (N : ℝ) * torusM d σ 1 := by
    intro q hq
    refine (H.hc.Hrow_sq N q hq).trans ?_
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hMN)]
  have hPA : ∀ q : ℕ, ∫ ω, Apr (phi0 d σ k) (cK d σ) X N q ω ^ 2 ∂μ
      ≤ 76 * (N : ℝ) ^ 3 * torusM d σ 1 * torusM d σ k ^ 2 := fun q =>
    PA_arith hM1 hMN hm0 hc2 hp2 (H.Apr_sq hL N q)
  have bA : ∀ q, BM (Apr (phi0 d σ k) (cK d σ) X N q) := fun q => H.BM_Apr N q
  have bH : ∀ q, BM (Hrow (cK d σ) X N q) := fun q => H.hc.BM_Hrow N q
  have hCS : ∀ q ∈ Finset.range N,
      ∫ ω, |Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω| ∂μ
        ≤ 22 * (N : ℝ) ^ 2 * torusM d σ 1 * torusM d σ k := fun q hq =>
    cs_abs (bA q) (bH q) (hPA q) (hQ q hq)
      (mul_pos (mul_pos (by norm_num) hNpos) (by linarith))
      (mul_nonneg (mul_nonneg (by positivity) hM0) hm0)
      (by nlinarith [_root_.sq_nonneg ((N : ℝ) ^ 2 * torusM d σ 1 * torusM d σ k)])
  -- the integrand for a fixed `q`
  have iAH : ∀ q, Integrable (fun ω =>
      |Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|) μ := fun q =>
    ((bA q).mul (bH q)).absv.integrable
  have iH2 : ∀ q, Integrable (fun ω => (|phi0 d σ k 0| + torusM d σ (k + 1) * N)
      * Hrow (cK d σ) X N q ω ^ 2) μ := fun q =>
    (BM.const_mul _ (bH q).sqr).integrable
  have iR : ∀ q, Integrable (fun ω =>
      |Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|
        + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * Hrow (cK d σ) X N q ω ^ 2) μ :=
    fun q => (iAH q).add (iH2 q)
  have hRq : ∀ q ∈ Finset.range N, ∫ ω,
      (|Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|
        + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * Hrow (cK d σ) X N q ω ^ 2) ∂μ
      ≤ 22 * (N : ℝ) ^ 2 * torusM d σ 1 * torusM d σ k
        + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * (6 * (N : ℝ) * torusM d σ 1) := by
    intro q hq
    rw [integral_add (iAH q) (iH2 q), integral_const_mul]
    have h2 := mul_le_mul_of_nonneg_left (hQ q hq)
      (add_nonneg (abs_nonneg (phi0 d σ k 0)) (mul_nonneg f2 hNpos.le))
    linarith [hCS q hq]
  have iC : Integrable (fun ω => torusM d σ (k + 1) * (N : ℝ) ^ 2
      * |∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N, cK d σ (X q ω - X v ω)|) μ :=
    ((H.hc.full_integrable N).abs).const_mul _
  have iSum : Integrable (fun ω => ∑ q ∈ Finset.range N,
      (|Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|
        + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * Hrow (cK d σ) X N q ω ^ 2)) μ :=
    integrable_finset_sum _ fun q _ => iR q
  -- pointwise bound
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ∑ v ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω)|
      ≤ ∑ q ∈ Finset.range N,
          (|Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|
            + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * Hrow (cK d σ) X N q ω ^ 2)
        + torusM d σ (k + 1) * (N : ℝ) ^ 2
          * |∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N, cK d σ (X q ω - X v ω)| := by
    intro ω
    have e : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
          ∑ v ∈ Finset.range N,
            FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω)
        = ∑ q ∈ Finset.range N,
            (Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω
              + (phi0 d σ k 0 + torusM d σ (k + 1) * N) * Hrow (cK d σ) X N q ω ^ 2)
          + torusM d σ (k + 1) * (N : ℝ) ^ 2
            * ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N, cK d σ (X q ω - X v ω) := by
      rw [T4_eq σ k N X ω, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [H.Aq_eq N q hq ω]
      unfold Apr Hrow
      ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_nonneg (_root_.sq_nonneg (Hrow (cK d σ) X N q ω))]
      refine mul_le_mul_of_nonneg_right ?_ (_root_.sq_nonneg _)
      refine (abs_add_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
      exact abs_of_nonneg (mul_nonneg f2 hNpos.le)
    · rw [abs_mul, abs_of_nonneg (mul_nonneg f2 (_root_.sq_nonneg (N : ℝ)))]
  have hT : ∫ ω, |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ∑ v ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω)| ∂μ
      ≤ N * (22 * (N : ℝ) ^ 2 * torusM d σ 1 * torusM d σ k
          + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * (6 * (N : ℝ) * torusM d σ 1))
        + torusM d σ (k + 1) * (N : ℝ) ^ 2
          * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|) :=
    calc ∫ ω, |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
          ∑ v ∈ Finset.range N,
            FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω)| ∂μ
        ≤ ∫ ω, (∑ q ∈ Finset.range N,
            (|Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|
              + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * Hrow (cK d σ) X N q ω ^ 2)
          + torusM d σ (k + 1) * (N : ℝ) ^ 2
            * |∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N, cK d σ (X q ω - X v ω)|) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
            (iSum.add iC) (Filter.Eventually.of_forall hpt)
      _ = ∑ q ∈ Finset.range N, ∫ ω,
            (|Apr (phi0 d σ k) (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|
              + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * Hrow (cK d σ) X N q ω ^ 2) ∂μ
          + torusM d σ (k + 1) * (N : ℝ) ^ 2
            * ∫ ω, |∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
                cK d σ (X q ω - X v ω)| ∂μ := by
          rw [integral_add iSum iC, integral_finset_sum _ (fun q _ => iR q),
            integral_const_mul]
      _ ≤ ∑ _q ∈ Finset.range N, (22 * (N : ℝ) ^ 2 * torusM d σ 1 * torusM d σ k
            + (|phi0 d σ k 0| + torusM d σ (k + 1) * N) * (6 * (N : ℝ) * torusM d σ 1))
          + torusM d σ (k + 1) * (N : ℝ) ^ 2
            * (N * Real.sqrt (2 * torusM d σ 1) + N * |cK d σ 0|) :=
          add_le_add (Finset.sum_le_sum hRq)
            (mul_le_mul_of_nonneg_left (H.hc.full_abs_le N)
              (mul_nonneg f2 (_root_.sq_nonneg (N : ℝ))))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfun : (fun ω => |Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
        (cmat d σ N (fun j => X j ω))|)
      = fun ω => 1 / (N : ℝ) ^ 4 * |∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
            FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω)| := by
    funext ω
    rw [Z1_FA3_conv σ k N (fun j => X j ω), abs_mul, abs_of_nonneg hpos]
  rw [hfun, integral_const_mul]
  exact FA3_arith hM1 hMN hm0 f2 f3 (abs_nonneg _) hp (abs_nonneg _) hc (Real.sqrt_nonneg _) hs3
    (mul_le_mul_of_nonneg_left hT hpos)

/-- **Stage 3, one summand of `Π_k` completely: the first term.** For independent uniform
    points on the flat torus, `k ≥ 1`, `N ≥ 1` and `M = p(0) ≤ N`:
    `E |N⁻² ∑_{i,b} p_k(x_i - x_b) p(x_b - x_i) θ¹_{bi}| ≤ 63 (M/N) m_k`. -/
theorem first_term_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) k i b * torusQ d σ N (fun j => X j ω) 1 b i
          * torusTheta1 d σ N (fun j => X j ω) b i| ∂μ
      ≤ 63 * (torusM d σ 1 / N) * torusM d σ k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have h1 := Z1_FA1_bound X h_indep hX hlaw hσ k hk N hN hMN
  have h2 := Z1_FA2_bound X h_indep hX hlaw hσ k hk N hN hMN
  have h3 := Z1_FA3_bound X h_indep hX hlaw hσ k hk N hN hMN
  have bF := BM_FA X hX hσ k hk
  have bp := BM_pker X hX hσ
  have bc := BM_cK X hX hσ
  have i1 : Integrable (fun ω => Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
      (cmat d σ N (fun j => X j ω))) μ := by
    have e : (fun ω => Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
          (cmat d σ N (fun j => X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω) :=
      funext fun ω => Z1_FA1_conv σ k N (fun j => X j ω)
    rw [e]
    exact BM.integrable (BM.const_mul _ (BM.sum (Finset.range N)
      (fun i ω => ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω)) fun i _ =>
      BM.sum (Finset.range N) (fun b ω => ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω)) fun b _ =>
      BM.sum (Finset.range N) (fun v ω => FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω))
        fun v _ => (bF i b).mul (bc i v)))
  have i2 : Integrable (fun ω => Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
      (cmat d σ N (fun j => X j ω))) μ := by
    have e : (fun ω => Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
          (cmat d σ N (fun j => X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω) :=
      funext fun ω => Z1_FA2_conv σ k N (fun j => X j ω)
    rw [e]
    exact BM.integrable (BM.const_mul _ (BM.sum (Finset.range N)
      (fun i ω => ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)) fun i _ =>
      BM.sum (Finset.range N) (fun b ω => ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)) fun b _ =>
      BM.sum (Finset.range N) (fun v ω => FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω))
        fun v _ => (bF i b).mul (bc b v)))
  have i3 : Integrable (fun ω => Zs1three3 N
      (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
      (cmat d σ N (fun j => X j ω))) μ := by
    have e : (fun ω => Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
          (cmat d σ N (fun j => X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
              FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω) :=
      funext fun ω => Z1_FA3_conv σ k N (fun j => X j ω)
    rw [e]
    exact BM.integrable (BM.const_mul _ (BM.sum (Finset.range N)
      (fun i ω => ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
      fun i _ => BM.sum (Finset.range N)
        (fun b ω => ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
        fun b _ => BM.sum (Finset.range N)
          (fun q ω => ∑ v ∈ Finset.range N,
            FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
          fun q _ => BM.sum (Finset.range N)
            (fun v ω =>
              FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
            fun v _ => ((bF i b).mul (bp b q)).mul (bc q v)))
  have i12 : Integrable (fun ω =>
      |Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω)) (cmat d σ N (fun j => X j ω))|
      + |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
          (cmat d σ N (fun j => X j ω))|) μ := i1.abs.add i2.abs
  have i123 : Integrable (fun ω =>
      |Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω)) (cmat d σ N (fun j => X j ω))|
      + |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
          (cmat d σ N (fun j => X j ω))|
      + |Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
          (cmat d σ N (fun j => X j ω))|) μ := i12.add i3.abs
  have hpt : ∀ ω, |1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) k i b * torusQ d σ N (fun j => X j ω) 1 b i
          * torusTheta1 d σ N (fun j => X j ω) b i|
      ≤ |Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
            (cmat d σ N (fun j => X j ω))|
        + |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
            (cmat d σ N (fun j => X j ω))|
        + |Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
            (cmat d σ N (fun j => X j ω))| := by
    intro ω
    rw [first_term d σ N hN0 (fun j => X j ω) k]
    exact abs3 _ _ _
  calc ∫ ω, |1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
          torusQ d σ N (fun j => X j ω) k i b * torusQ d σ N (fun j => X j ω) 1 b i
            * torusTheta1 d σ N (fun j => X j ω) b i| ∂μ
      ≤ ∫ ω, (|Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
              (cmat d σ N (fun j => X j ω))|
          + |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
              (cmat d σ N (fun j => X j ω))|
          + |Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
              (cmat d σ N (fun j => X j ω))|) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _) i123
          (Filter.Eventually.of_forall hpt)
    _ = ∫ ω, |Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
              (cmat d σ N (fun j => X j ω))| ∂μ
          + ∫ ω, |Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
              (cmat d σ N (fun j => X j ω))| ∂μ
          + ∫ ω, |Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
              (cmat d σ N (fun j => X j ω))| ∂μ := by
        rw [integral_add i12 i3.abs, integral_add i1.abs i2.abs]
    _ ≤ 63 * (torusM d σ 1 / N) * torusM d σ k := by linarith

end SampleFA3



/-! # NEW (A27) from here on

## The middle summands of `Π_k`: `Z⁰[K_m]`, `Z¹[K_m, a = 3]`, and the bound for `Π_k`

For `l, m ≥ 1` (`l = k - m`), with `u = y₁ - y₂`, `w = y₂ - y₃`, `v = y₁ - y₃` and
`φ_{a,b}(x) = p_a(x) p_b(x) - m_{a+b}` (degenerate, `∫ p_a p_b = m_{a+b}`):

`K_m = T + φ_{l+1,m}(v) + φ_{1,l+m}(w) - m_{k+1} c(w) - φ_{l,m+1}(u) c(w)`,

where `T = p_l(u) p(w) p_m(v) - p_l p_{m+1}(u) - p_{l+1} p_m(v) - p p_{l+m}(w) + 2 m_{k+1}` is the
completely degenerate part of the triangle `p_l(u) p(w) p_m(v)` (it integrates to zero in each of
its three arguments).  For a FIXED last index `q` the sum `∑_{i,b} T(x_i,x_b,x_q)` over distinct
indices has second moment `≤ 2 N² ‖T‖₂²` (only the two pairings `{i,b} = {i',b'}` survive); the
three diagonals of `T` are again combinations of the `φ_{a,b}`.  All other pieces are sums of the
kinds already treated (`Deg2`, `Deg3`).  As in A26 the argument is NOT the one of `lem:degenerate`:
no second moment of a whole three- or four-index sum is taken; everything is done for each `q`
separately (Cauchy–Schwarz against the row sum `H_q = N ε_q` for `Z¹`). -/

/-! ### more on bounded measurable functions -/

section BMmore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f g h k : Ω → ℝ}

theorem BM.sub (hf : BM f) (hg : BM g) : BM (fun ω => f ω - g ω) := by
  have h' := hf.add (BM.const_mul (-1) hg)
  have e : (fun ω => f ω - g ω) = fun ω => f ω + -1 * g ω := by funext ω; ring
  rw [e]; exact h'

theorem BM.div_const (hf : BM f) (c : ℝ) : BM (fun ω => f ω / c) := by
  have h' := BM.const_mul c⁻¹ hf
  have e : (fun ω => f ω / c) = fun ω => c⁻¹ * f ω := by funext ω; rw [div_eq_inv_mul]
  rw [e]; exact h'

/-- `∫ (f + g + h)² ≤ 3 (∫ f² + ∫ g² + ∫ h²)`. -/
theorem sq3_int {μ : Measure Ω} [IsFiniteMeasure μ] (hf : BM f) (hg : BM g) (hh : BM h)
    {P Q R : ℝ} (hP : ∫ ω, f ω ^ 2 ∂μ ≤ P) (hQ : ∫ ω, g ω ^ 2 ∂μ ≤ Q)
    (hR : ∫ ω, h ω ^ 2 ∂μ ≤ R) :
    ∫ ω, (f ω + g ω + h ω) ^ 2 ∂μ ≤ 3 * (P + Q + R) := by
  have iF : Integrable (fun ω => f ω ^ 2) μ := hf.sqr.integrable
  have iG : Integrable (fun ω => g ω ^ 2) μ := hg.sqr.integrable
  have iH : Integrable (fun ω => h ω ^ 2) μ := hh.sqr.integrable
  have iS : Integrable (fun ω => (f ω + g ω + h ω) ^ 2) μ :=
    ((hf.add hg).add hh).sqr.integrable
  have j1 : Integrable (fun ω => 3 * f ω ^ 2) μ := iF.const_mul 3
  have j2 : Integrable (fun ω => 3 * g ω ^ 2) μ := iG.const_mul 3
  have j3 : Integrable (fun ω => 3 * h ω ^ 2) μ := iH.const_mul 3
  have j12 : Integrable (fun ω => 3 * f ω ^ 2 + 3 * g ω ^ 2) μ := j1.add j2
  have hpt : ∀ ω, (f ω + g ω + h ω) ^ 2 ≤ 3 * f ω ^ 2 + 3 * g ω ^ 2 + 3 * h ω ^ 2 := fun ω => by
    nlinarith [_root_.sq_nonneg (f ω - g ω), _root_.sq_nonneg (f ω - h ω),
      _root_.sq_nonneg (g ω - h ω)]
  calc ∫ ω, (f ω + g ω + h ω) ^ 2 ∂μ
      ≤ ∫ ω, (3 * f ω ^ 2 + 3 * g ω ^ 2 + 3 * h ω ^ 2) ∂μ := integral_mono iS (j12.add j3) hpt
    _ = 3 * ∫ ω, f ω ^ 2 ∂μ + 3 * ∫ ω, g ω ^ 2 ∂μ + 3 * ∫ ω, h ω ^ 2 ∂μ := by
        rw [integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
          integral_const_mul]
    _ ≤ 3 * (P + Q + R) := by linarith

/-- `∫ (f + g + h + k)² ≤ 4 (∫ f² + ∫ g² + ∫ h² + ∫ k²)`. -/
theorem sq4_int {μ : Measure Ω} [IsFiniteMeasure μ] (hf : BM f) (hg : BM g) (hh : BM h)
    (hk : BM k) {P Q R S : ℝ} (hP : ∫ ω, f ω ^ 2 ∂μ ≤ P) (hQ : ∫ ω, g ω ^ 2 ∂μ ≤ Q)
    (hR : ∫ ω, h ω ^ 2 ∂μ ≤ R) (hS : ∫ ω, k ω ^ 2 ∂μ ≤ S) :
    ∫ ω, (f ω + g ω + h ω + k ω) ^ 2 ∂μ ≤ 4 * (P + Q + R + S) := by
  have iF : Integrable (fun ω => f ω ^ 2) μ := hf.sqr.integrable
  have iG : Integrable (fun ω => g ω ^ 2) μ := hg.sqr.integrable
  have iH : Integrable (fun ω => h ω ^ 2) μ := hh.sqr.integrable
  have iK : Integrable (fun ω => k ω ^ 2) μ := hk.sqr.integrable
  have iS : Integrable (fun ω => (f ω + g ω + h ω + k ω) ^ 2) μ :=
    (((hf.add hg).add hh).add hk).sqr.integrable
  have j1 : Integrable (fun ω => 4 * f ω ^ 2) μ := iF.const_mul 4
  have j2 : Integrable (fun ω => 4 * g ω ^ 2) μ := iG.const_mul 4
  have j3 : Integrable (fun ω => 4 * h ω ^ 2) μ := iH.const_mul 4
  have j4 : Integrable (fun ω => 4 * k ω ^ 2) μ := iK.const_mul 4
  have j12 : Integrable (fun ω => 4 * f ω ^ 2 + 4 * g ω ^ 2) μ := j1.add j2
  have j123 : Integrable (fun ω => 4 * f ω ^ 2 + 4 * g ω ^ 2 + 4 * h ω ^ 2) μ := j12.add j3
  have hpt : ∀ ω, (f ω + g ω + h ω + k ω) ^ 2
      ≤ 4 * f ω ^ 2 + 4 * g ω ^ 2 + 4 * h ω ^ 2 + 4 * k ω ^ 2 := fun ω => by
    nlinarith [_root_.sq_nonneg (f ω - g ω), _root_.sq_nonneg (f ω - h ω),
      _root_.sq_nonneg (f ω - k ω), _root_.sq_nonneg (g ω - h ω), _root_.sq_nonneg (g ω - k ω),
      _root_.sq_nonneg (h ω - k ω)]
  calc ∫ ω, (f ω + g ω + h ω + k ω) ^ 2 ∂μ
      ≤ ∫ ω, (4 * f ω ^ 2 + 4 * g ω ^ 2 + 4 * h ω ^ 2 + 4 * k ω ^ 2) ∂μ :=
        integral_mono iS (j123.add j4) hpt
    _ = 4 * ∫ ω, f ω ^ 2 ∂μ + 4 * ∫ ω, g ω ^ 2 ∂μ + 4 * ∫ ω, h ω ^ 2 ∂μ
          + 4 * ∫ ω, k ω ^ 2 ∂μ := by
        rw [integral_add j123 j4, integral_add j12 j3, integral_add j1 j2, integral_const_mul,
          integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ 4 * (P + Q + R + S) := by linarith

/-- `∫ |f + g| ≤ ∫ |f| + ∫ |g|`, with bounds. -/
theorem abs_int_add {μ : Measure Ω} [IsFiniteMeasure μ] (hf : BM f) (hg : BM g) {A B : ℝ}
    (hA : ∫ ω, |f ω| ∂μ ≤ A) (hB : ∫ ω, |g ω| ∂μ ≤ B) : ∫ ω, |f ω + g ω| ∂μ ≤ A + B := by
  have iF : Integrable (fun ω => |f ω|) μ := hf.absv.integrable
  have iG : Integrable (fun ω => |g ω|) μ := hg.absv.integrable
  have iS : Integrable (fun ω => |f ω + g ω|) μ := (hf.add hg).absv.integrable
  calc ∫ ω, |f ω + g ω| ∂μ ≤ ∫ ω, (|f ω| + |g ω|) ∂μ :=
        integral_mono iS (iF.add iG) (fun ω => abs_add_le _ _)
    _ = ∫ ω, |f ω| ∂μ + ∫ ω, |g ω| ∂μ := integral_add iF iG
    _ ≤ A + B := add_le_add hA hB

/-- `∫ |c f| ≤ |c| L` if `∫ |f| ≤ L`. -/
theorem int_abs_cmul {μ : Measure Ω} (c : ℝ) {L : ℝ} (hL : ∫ ω, |f ω| ∂μ ≤ L) :
    ∫ ω, |c * f ω| ∂μ ≤ |c| * L := by
  simp_rw [abs_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hL (abs_nonneg c)

/-- `∫ (c f)² ≤ c² P` if `∫ f² ≤ P`. -/
theorem sq_cmul_int {μ : Measure Ω} (c : ℝ) {P : ℝ} (hP : ∫ ω, f ω ^ 2 ∂μ ≤ P) :
    ∫ ω, (c * f ω) ^ 2 ∂μ ≤ c ^ 2 * P := by
  simp_rw [mul_pow]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hP (_root_.sq_nonneg c)

/-- `∫ |f| ≤ √W` if `∫ f² ≤ W` (bounded measurable `f`, probability measure). -/
theorem BM.abs_le_sqrt {μ : Measure Ω} [IsProbabilityMeasure μ] (hf : BM f) {W : ℝ}
    (hW : ∫ ω, f ω ^ 2 ∂μ ≤ W) : ∫ ω, |f ω| ∂μ ≤ Real.sqrt W := by
  obtain ⟨B, hB⟩ := hf.bdd
  exact abs_integral_le_sqrt f hf.meas hB hW

end BMmore

/-! ### a function of three points that is degenerate in its first two arguments -/

/-- Hypotheses for the second moment of `∑_{i,b} F(x_i, x_b, x_q)` with a FIXED third index:
    `F` jointly measurable and bounded, `∫ F(z,b,c) dν(z) = 0`, `∫ F(a,z,c) dν(z) = 0`, and
    `E F(X_i,X_b,X_q)² ≤ V` for distinct indices. -/
structure Tri3 {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) {G : Type*}
    [MeasurableSpace G] (ν : Measure G) (X : ℕ → Ω → G) (F : G → G → G → ℝ) (B V : ℝ) :
    Prop where
  indep : iIndepFun X μ
  meas : ∀ j, Measurable (X j)
  law : ∀ j, μ.map (X j) = ν
  F_meas : Measurable (fun p : G × G × G => F p.1 p.2.1 p.2.2)
  bound : ∀ a b c, |F a b c| ≤ B
  mean1 : ∀ b c, ∫ z, F z b c ∂ν = 0
  mean2 : ∀ a c, ∫ z, F a z c ∂ν = 0
  var : ∀ i b q : ℕ, i ≠ b → i ≠ q → b ≠ q → ∫ ω, F (X i ω) (X b ω) (X q ω) ^ 2 ∂μ ≤ V
  V_nonneg : 0 ≤ V

/-- The summand for distinct `i, b, q` (zero otherwise). -/
noncomputable def aF {Ω G : Type*} (F : G → G → G → ℝ) (X : ℕ → Ω → G) (i b q : ℕ) (ω : Ω) : ℝ :=
  if i = b ∨ b = q ∨ i = q then 0 else F (X i ω) (X b ω) (X q ω)

/-- `∑_{i,b} F(x_i,x_b,x_q)` over the pairs with `i, b, q` distinct. -/
noncomputable def Roff {Ω G : Type*} (F : G → G → G → ℝ) (X : ℕ → Ω → G) (N q : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, aF F X i b q ω

namespace Tri3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [MeasurableSpace G]
  {ν : Measure G} {X : ℕ → Ω → G} {F : G → G → G → ℝ} {B V : ℝ}

theorem BM_F (H : Tri3 μ ν X F B V) (i b q : ℕ) :
    BM (fun ω => F (X i ω) (X b ω) (X q ω)) :=
  ⟨H.F_meas.comp ((H.meas i).prodMk ((H.meas b).prodMk (H.meas q))), B,
    fun ω => H.bound _ _ _⟩

theorem BM_aF (H : Tri3 μ ν X F B V) (i b q : ℕ) : BM (aF F X i b q) := by
  unfold aF
  by_cases h : i = b ∨ b = q ∨ i = q
  · simp only [if_pos h]; exact BM.const 0
  · simp only [if_neg h]; exact H.BM_F i b q

theorem BM_Roff (H : Tri3 μ ν X F B V) (N q : ℕ) : BM (Roff F X N q) := by
  show BM (fun ω => ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, aF F X i b q ω)
  exact BM.sum (Finset.range N) (fun i ω => ∑ b ∈ Finset.range N, aF F X i b q ω) fun i _ =>
    BM.sum (Finset.range N) (fun b => aF F X i b q) fun b _ => H.BM_aF i b q

/-- The index `i` occurs only in the first slot of the first factor: the mean vanishes. -/
theorem free1 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Tri3 μ ν X F B V)
    {i b q i' b' : ℕ} (hib : i ≠ b) (hiq : i ≠ q) (hii' : i ≠ i') (hib' : i ≠ b') :
    ∫ ω, F (X i ω) (X b ω) (X q ω) * F (X i' ω) (X b' ω) (X q ω) ∂μ = 0 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = {b, q, i', b'} := ⟨_, rfl⟩
  have mb : b ∈ T := by rw [hT]; simp
  have mq : q ∈ T := by rw [hT]; simp
  have mi' : i' ∈ T := by rw [hT]; simp
  have mb' : b' ∈ T := by rw [hT]; simp
  have hi : i ∉ T := by rw [hT]; simp [hib, hiq, hii', hib']
  have eb : Measurable fun p : G × (T → G) => p.2 ⟨b, mb⟩ :=
    (measurable_pi_apply (⟨b, mb⟩ : T)).comp measurable_snd
  have eq' : Measurable fun p : G × (T → G) => p.2 ⟨q, mq⟩ :=
    (measurable_pi_apply (⟨q, mq⟩ : T)).comp measurable_snd
  have ei' : Measurable fun p : G × (T → G) => p.2 ⟨i', mi'⟩ :=
    (measurable_pi_apply (⟨i', mi'⟩ : T)).comp measurable_snd
  have eb' : Measurable fun p : G × (T → G) => p.2 ⟨b', mb'⟩ :=
    (measurable_pi_apply (⟨b', mb'⟩ : T)).comp measurable_snd
  have hmeas : Measurable fun p : G × (T → G) =>
      F p.1 (p.2 ⟨b, mb⟩) (p.2 ⟨q, mq⟩) * F (p.2 ⟨i', mi'⟩) (p.2 ⟨b', mb'⟩) (p.2 ⟨q, mq⟩) :=
    (H.F_meas.comp (measurable_fst.prodMk (eb.prodMk eq'))).mul
      (H.F_meas.comp (ei'.prodMk (eb'.prodMk eq')))
  exact free_index_zero ν X H.indep H.meas H.law i T hi
    (fun p : G × (T → G) =>
      F p.1 (p.2 ⟨b, mb⟩) (p.2 ⟨q, mq⟩) * F (p.2 ⟨i', mi'⟩) (p.2 ⟨b', mb'⟩) (p.2 ⟨q, mq⟩))
    hmeas (B := B * B)
    (fun p => by
      rw [abs_mul]
      exact mul_le_mul (H.bound _ _ _) (H.bound _ _ _) (abs_nonneg _)
        ((abs_nonneg (F p.1 p.1 p.1)).trans (H.bound p.1 p.1 p.1)))
    (fun y => by
      show ∫ z, F z (y ⟨b, mb⟩) (y ⟨q, mq⟩)
        * F (y ⟨i', mi'⟩) (y ⟨b', mb'⟩) (y ⟨q, mq⟩) ∂ν = 0
      rw [integral_mul_const, H.mean1, zero_mul])

/-- The index `b` occurs only in the second slot of the first factor: the mean vanishes. -/
theorem free2 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Tri3 μ ν X F B V)
    {i b q i' b' : ℕ} (hbi : b ≠ i) (hbq : b ≠ q) (hbi' : b ≠ i') (hbb' : b ≠ b') :
    ∫ ω, F (X i ω) (X b ω) (X q ω) * F (X i' ω) (X b' ω) (X q ω) ∂μ = 0 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = {i, q, i', b'} := ⟨_, rfl⟩
  have mi : i ∈ T := by rw [hT]; simp
  have mq : q ∈ T := by rw [hT]; simp
  have mi' : i' ∈ T := by rw [hT]; simp
  have mb' : b' ∈ T := by rw [hT]; simp
  have hb : b ∉ T := by rw [hT]; simp [hbi, hbq, hbi', hbb']
  have ei : Measurable fun p : G × (T → G) => p.2 ⟨i, mi⟩ :=
    (measurable_pi_apply (⟨i, mi⟩ : T)).comp measurable_snd
  have eq' : Measurable fun p : G × (T → G) => p.2 ⟨q, mq⟩ :=
    (measurable_pi_apply (⟨q, mq⟩ : T)).comp measurable_snd
  have ei' : Measurable fun p : G × (T → G) => p.2 ⟨i', mi'⟩ :=
    (measurable_pi_apply (⟨i', mi'⟩ : T)).comp measurable_snd
  have eb' : Measurable fun p : G × (T → G) => p.2 ⟨b', mb'⟩ :=
    (measurable_pi_apply (⟨b', mb'⟩ : T)).comp measurable_snd
  have hmeas : Measurable fun p : G × (T → G) =>
      F (p.2 ⟨i, mi⟩) p.1 (p.2 ⟨q, mq⟩) * F (p.2 ⟨i', mi'⟩) (p.2 ⟨b', mb'⟩) (p.2 ⟨q, mq⟩) :=
    (H.F_meas.comp (ei.prodMk (measurable_fst.prodMk eq'))).mul
      (H.F_meas.comp (ei'.prodMk (eb'.prodMk eq')))
  exact free_index_zero ν X H.indep H.meas H.law b T hb
    (fun p : G × (T → G) =>
      F (p.2 ⟨i, mi⟩) p.1 (p.2 ⟨q, mq⟩) * F (p.2 ⟨i', mi'⟩) (p.2 ⟨b', mb'⟩) (p.2 ⟨q, mq⟩))
    hmeas (B := B * B)
    (fun p => by
      rw [abs_mul]
      exact mul_le_mul (H.bound _ _ _) (H.bound _ _ _) (abs_nonneg _)
        ((abs_nonneg (F p.1 p.1 p.1)).trans (H.bound p.1 p.1 p.1)))
    (fun y => by
      show ∫ z, F (y ⟨i, mi⟩) z (y ⟨q, mq⟩)
        * F (y ⟨i', mi'⟩) (y ⟨b', mb'⟩) (y ⟨q, mq⟩) ∂ν = 0
      rw [integral_mul_const, H.mean2, zero_mul])

/-- **The mean of a product of two summands with the same third index**: it vanishes unless
    `{i,b} = {i',b'}`, and is at most `V` then. -/
theorem pair_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Tri3 μ ν X F B V)
    (q i b i' b' : ℕ) :
    ∫ ω, aF F X i b q ω * aF F X i' b' q ω ∂μ
      ≤ V * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
          + (if i' = b ∧ b' = i then (1 : ℝ) else 0)) := by
  have hV0 := H.V_nonneg
  have t1 : (0 : ℝ) ≤ (if i' = i ∧ b' = b then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t2 : (0 : ℝ) ≤ (if i' = b ∧ b' = i then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hR : 0 ≤ V * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
      + (if i' = b ∧ b' = i then (1 : ℝ) else 0)) := mul_nonneg hV0 (add_nonneg t1 t2)
  by_cases h1 : i = b ∨ b = q ∨ i = q
  · have hz : (fun ω => aF F X i b q ω * aF F X i' b' q ω) = fun _ => (0 : ℝ) := by
      funext ω
      have : aF F X i b q ω = 0 := by unfold aF; rw [if_pos h1]
      rw [this, zero_mul]
    rw [hz, integral_zero]; exact hR
  by_cases h2 : i' = b' ∨ b' = q ∨ i' = q
  · have hz : (fun ω => aF F X i b q ω * aF F X i' b' q ω) = fun _ => (0 : ℝ) := by
      funext ω
      have : aF F X i' b' q ω = 0 := by unfold aF; rw [if_pos h2]
      rw [this, mul_zero]
    rw [hz, integral_zero]; exact hR
  have hib : i ≠ b := fun h => h1 (Or.inl h)
  have hbq : b ≠ q := fun h => h1 (Or.inr (Or.inl h))
  have hiq : i ≠ q := fun h => h1 (Or.inr (Or.inr h))
  have hib' : i' ≠ b' := fun h => h2 (Or.inl h)
  have hA : (fun ω => aF F X i b q ω * aF F X i' b' q ω)
      = fun ω => F (X i ω) (X b ω) (X q ω) * F (X i' ω) (X b' ω) (X q ω) := by
    funext ω
    have e1 : aF F X i b q ω = F (X i ω) (X b ω) (X q ω) := by unfold aF; rw [if_neg h1]
    have e2 : aF F X i' b' q ω = F (X i' ω) (X b' ω) (X q ω) := by unfold aF; rw [if_neg h2]
    rw [e1, e2]
  rw [hA]
  by_cases c1 : i ≠ i' ∧ i ≠ b'
  · rw [H.free1 hib hiq c1.1 c1.2]; exact hR
  by_cases c2 : b ≠ i' ∧ b ≠ b'
  · rw [H.free2 (Ne.symm hib) hbq c2.1 c2.2]; exact hR
  have h3 : (i' = i ∧ b' = b) ∨ (i' = b ∧ b' = i) := by omega
  rcases h3 with h | h
  · have hR1 : V ≤ V * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
        + (if i' = b ∧ b' = i then (1 : ℝ) else 0)) := by
      rw [if_pos h]; linarith [mul_nonneg hV0 t2]
    refine le_trans ?_ hR1
    have he : (fun ω => F (X i ω) (X b ω) (X q ω) * F (X i' ω) (X b' ω) (X q ω))
        = fun ω => F (X i ω) (X b ω) (X q ω) ^ 2 := by
      funext ω; rw [h.1, h.2]; ring
    rw [he]; exact H.var i b q hib hiq hbq
  · have hR2 : V ≤ V * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
        + (if i' = b ∧ b' = i then (1 : ℝ) else 0)) := by
      rw [if_pos h]; linarith [mul_nonneg hV0 t1]
    refine le_trans ?_ hR2
    have he : (fun ω => F (X i ω) (X b ω) (X q ω) * F (X i' ω) (X b' ω) (X q ω))
        = fun ω => F (X i ω) (X b ω) (X q ω) * F (X b ω) (X i ω) (X q ω) := by
      funext ω; rw [h.1, h.2]
    rw [he]
    have b1 := H.BM_F i b q
    have b2 := H.BM_F b i q
    have i1 : Integrable (fun ω => F (X i ω) (X b ω) (X q ω) ^ 2) μ := b1.sqr.integrable
    have i2 : Integrable (fun ω => F (X b ω) (X i ω) (X q ω) ^ 2) μ := b2.sqr.integrable
    have i3 : Integrable (fun ω => F (X i ω) (X b ω) (X q ω) * F (X b ω) (X i ω) (X q ω)) μ :=
      (b1.mul b2).integrable
    have j1 : Integrable (fun ω => 1 / 2 * F (X i ω) (X b ω) (X q ω) ^ 2) μ := i1.const_mul _
    have j2 : Integrable (fun ω => 1 / 2 * F (X b ω) (X i ω) (X q ω) ^ 2) μ := i2.const_mul _
    have v1 := H.var i b q hib hiq hbq
    have v2 := H.var b i q (Ne.symm hib) hbq hiq
    calc ∫ ω, F (X i ω) (X b ω) (X q ω) * F (X b ω) (X i ω) (X q ω) ∂μ
        ≤ ∫ ω, (1 / 2 * F (X i ω) (X b ω) (X q ω) ^ 2
            + 1 / 2 * F (X b ω) (X i ω) (X q ω) ^ 2) ∂μ :=
          integral_mono i3 (j1.add j2) (fun ω => by
            nlinarith [_root_.sq_nonneg (F (X i ω) (X b ω) (X q ω) - F (X b ω) (X i ω) (X q ω))])
      _ = 1 / 2 * ∫ ω, F (X i ω) (X b ω) (X q ω) ^ 2 ∂μ
            + 1 / 2 * ∫ ω, F (X b ω) (X i ω) (X q ω) ^ 2 ∂μ := by
          rw [integral_add j1 j2, integral_const_mul, integral_const_mul]
      _ ≤ V := by linarith

/-- **Second moment for a fixed third index**: `E (∑_{i,b distinct from each other and from q}
    F(X_i,X_b,X_q))² ≤ 2 N² V`. -/
theorem Roff_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Tri3 μ ν X F B V)
    (N q : ℕ) : ∫ ω, Roff F X N q ω ^ 2 ∂μ ≤ 2 * (N : ℝ) ^ 2 * V := by
  have hS2 : ∀ ω, Roff F X N q ω ^ 2
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, aF F X i b q ω * aF F X i' b' q ω := by
    intro ω
    unfold Roff
    rw [pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
  have h4 : ∫ ω, ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
        ∑ b' ∈ Finset.range N, aF F X i b q ω * aF F X i' b' q ω ∂μ
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, ∫ ω, aF F X i b q ω * aF F X i' b' q ω ∂μ :=
    integral_sum4 (Finset.range N) (fun i b i' b' ω => aF F X i b q ω * aF F X i' b' q ω)
      (fun i b i' b' => ((H.BM_aF i b q).mul (H.BM_aF i' b' q)).integrable)
  simp_rw [hS2]
  rw [h4]
  calc ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, ∫ ω, aF F X i b q ω * aF F X i' b' q ω ∂μ
      ≤ ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ b' ∈ Finset.range N, V * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
            + (if i' = b ∧ b' = i then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun i' _ =>
          Finset.sum_le_sum fun b' _ => H.pair_le q i b i' b'
    _ = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, V * (1 + 1) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun b hb => ?_
        have e : ∑ i' ∈ Finset.range N, ∑ b' ∈ Finset.range N,
              V * ((if i' = i ∧ b' = b then (1 : ℝ) else 0)
                + (if i' = b ∧ b' = i then (1 : ℝ) else 0))
            = V * (∑ i' ∈ Finset.range N, ∑ b' ∈ Finset.range N,
                  (if i' = i ∧ b' = b then (1 : ℝ) else 0)
                + ∑ i' ∈ Finset.range N, ∑ b' ∈ Finset.range N,
                  (if i' = b ∧ b' = i then (1 : ℝ) else 0)) := by
          simp only [← Finset.mul_sum, ← Finset.sum_add_distrib]
        rw [e, count1 N i b hi hb, count1 N b i hb hi]
    _ = 2 * (N : ℝ) ^ 2 * V := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Tri3

/-! ### the kernels `p_a` (`a ≥ 1` steps) and the degenerate products `φ_{a,b}` -/

theorem heatP_eq (d : ℕ) (σ : ℝ) {a : ℕ} (ha : 1 ≤ a) :
    heatP d σ a = heatTorus d (2 * Real.pi ^ 2 * ((a : ℝ) * σ)) :=
  funext fun u => heatP_of_ne d σ (by omega) u

theorem tpos {σ : ℝ} (hσ : 0 < σ) {a : ℕ} (ha : 1 ≤ a) : 0 < (a : ℝ) * σ :=
  mul_pos (Nat.cast_pos.mpr (by omega)) hσ

theorem cpos {σ : ℝ} (hσ : 0 < σ) {a : ℕ} (ha : 1 ≤ a) :
    0 < 2 * Real.pi ^ 2 * ((a : ℝ) * σ) := mul_pos (by positivity) (tpos hσ ha)

theorem heatP_le {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a : ℕ} (ha : 1 ≤ a) (u : FlatTorus d) :
    heatP d σ a u ≤ torusM d σ a := by
  rw [heatP_eq d σ ha]; exact heatTorus_le_zero (cpos hσ ha) d u

theorem heatP_zero (d : ℕ) (σ : ℝ) {a : ℕ} (ha : 1 ≤ a) : heatP d σ a 0 = torusM d σ a := by
  rw [heatP_eq d σ ha]; rfl

theorem heatP_cont {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    Continuous (heatP d σ a) := by
  rw [heatP_eq d σ ha]; exact heatTorus_continuous (cpos hσ ha) d

theorem torusM_ge_one {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a : ℕ} (ha : 1 ≤ a) : 1 ≤ torusM d σ a :=
  heatTorus_zero_ge_one (cpos hσ ha) d

theorem heatP_flip (d : ℕ) (σ : ℝ) (a : ℕ) (x z : FlatTorus d) :
    heatP d σ a (x - z) = heatP d σ a (z - x) := by
  rw [← neg_sub z x, heatP_even]

/-- `∫ p_a(x - z) dz = 1`. -/
theorem heatP_mass {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a : ℕ} (ha : 1 ≤ a) (x : FlatTorus d) :
    ∫ z, heatP d σ a (x - z) ∂flatTorusMeasure d = 1 := by
  rw [heatP_eq d σ ha]
  exact pker_mass (tpos hσ ha) d x

/-- The semigroup: `∫ p_a(x - z) p_b(z - w) dz = p_{a+b}(x - w)`. -/
theorem heatP_semi {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (x w : FlatTorus d) :
    ∫ z, heatP d σ a (x - z) * heatP d σ b (z - w) ∂flatTorusMeasure d
      = heatP d σ (a + b) (x - w) := by
  have h := semigroup_all (tpos hσ ha) (tpos hσ hb) d x w
  have hc : 2 * Real.pi ^ 2 * ((a : ℝ) * σ + (b : ℝ) * σ)
      = 2 * Real.pi ^ 2 * (((a + b : ℕ) : ℝ) * σ) := by push_cast; ring
  rw [hc] at h
  have e1 : ∀ u, heatP d σ a u = heatTorus d (2 * Real.pi ^ 2 * ((a : ℝ) * σ)) u :=
    fun u => heatP_of_ne d σ (by omega) u
  have e2 : ∀ u, heatP d σ b u = heatTorus d (2 * Real.pi ^ 2 * ((b : ℝ) * σ)) u :=
    fun u => heatP_of_ne d σ (by omega) u
  have e3 : heatP d σ (a + b) (x - w)
      = heatTorus d (2 * Real.pi ^ 2 * (((a + b : ℕ) : ℝ) * σ)) (x - w) :=
    heatP_of_ne d σ (by omega) _
  simp_rw [e1, e2]
  rw [e3]
  exact h

/-- `φ_{a,b}(u) = p_a(u) p_b(u) - m_{a+b}`. -/
noncomputable def phiN (d : ℕ) (σ : ℝ) (a b : ℕ) (u : FlatTorus d) : ℝ :=
  heatP d σ a u * heatP d σ b u - torusM d σ (a + b)

theorem phiN_even (d : ℕ) (σ : ℝ) (a b : ℕ) (u : FlatTorus d) :
    phiN d σ a b (-u) = phiN d σ a b u := by
  unfold phiN
  rw [heatP_even, heatP_even]

theorem phiN_cont {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Continuous (phiN d σ a b) := by
  unfold phiN
  exact ((heatP_cont hσ d ha).mul (heatP_cont hσ d hb)).sub continuous_const

/-- `0 ≤ p_a p_b ≤ m_a m_b`, `1 ≤ m_{a+b} ≤ m_a`, `1 ≤ m_b`. -/
theorem phiN_facts {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (u : FlatTorus d) :
    0 ≤ heatP d σ a u * heatP d σ b u
      ∧ heatP d σ a u * heatP d σ b u ≤ torusM d σ a * torusM d σ b
      ∧ 1 ≤ torusM d σ (a + b) ∧ torusM d σ (a + b) ≤ torusM d σ a ∧ 1 ≤ torusM d σ b := by
  have h1 := heatP_nonneg hσ d a u
  have h2 := heatP_nonneg hσ d b u
  have h3 := heatP_le hσ d ha u
  have h4 := heatP_le hσ d hb u
  exact ⟨mul_nonneg h1 h2, mul_le_mul h3 h4 h2 (h1.trans h3),
    torusM_ge_one hσ d (by omega), torusM_anti hσ d ha (by omega), torusM_ge_one hσ d hb⟩

theorem phiN_bound {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (u : FlatTorus d) : |phiN d σ a b u| ≤ torusM d σ a * torusM d σ b := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := phiN_facts hσ d ha hb u
  have h := mul_nonneg (by linarith : (0 : ℝ) ≤ torusM d σ a) (by linarith : (0 : ℝ) ≤ torusM d σ b - 1)
  unfold phiN
  exact abs_le.mpr ⟨by nlinarith, by linarith⟩

theorem phiN_split (d : ℕ) (σ : ℝ) (a b : ℕ) (x z : FlatTorus d) :
    phiN d σ a b (x - z)
      = heatP d σ a (x - z) * heatP d σ b (z - x) - torusM d σ (a + b) := by
  have h1 := heatP_flip d σ b x z
  unfold phiN
  rw [h1]

theorem pp_integrable {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (x : FlatTorus d) :
    Integrable (fun z : FlatTorus d => heatP d σ a (x - z) * heatP d σ b (z - x))
      (flatTorusMeasure d) :=
  flat_integrable d _ (((heatP_cont hσ d ha).comp (continuous_const.sub continuous_id)).mul
    ((heatP_cont hσ d hb).comp (continuous_id.sub continuous_const)))

/-- `∫ p_a p_b = m_{a+b}`. -/
theorem pp_integral {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (x : FlatTorus d) :
    ∫ z, heatP d σ a (x - z) * heatP d σ b (z - x) ∂flatTorusMeasure d = torusM d σ (a + b) := by
  rw [heatP_semi hσ d ha hb x x, sub_self]
  exact heatP_zero d σ (by omega)

/-- `φ_{a,b}` is degenerate. -/
theorem phiN_mean {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (x : FlatTorus d) : ∫ z, phiN d σ a b (x - z) ∂flatTorusMeasure d = 0 := by
  simp_rw [phiN_split d σ a b x]
  rw [integral_sub (pp_integrable hσ d ha hb x) (integrable_const _), pp_integral hσ d ha hb x,
    integral_const, probReal_univ, one_smul, sub_self]

theorem phiN_var {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (x : FlatTorus d) :
    ∫ z, phiN d σ a b (x - z) ^ 2 ∂flatTorusMeasure d
      ≤ torusM d σ a * torusM d σ b * torusM d σ (a + b) := by
  have hc : Continuous fun z : FlatTorus d => phiN d σ a b (x - z) :=
    (phiN_cont hσ d ha hb).comp (continuous_const.sub continuous_id)
  have i1 := pp_integrable hσ d ha hb x
  have i2 : Integrable (fun z : FlatTorus d =>
      (torusM d σ a * torusM d σ b - 2 * torusM d σ (a + b))
        * (heatP d σ a (x - z) * heatP d σ b (z - x))) (flatTorusMeasure d) := i1.const_mul _
  have i3 : Integrable (fun z : FlatTorus d =>
      (torusM d σ a * torusM d σ b - 2 * torusM d σ (a + b))
        * (heatP d σ a (x - z) * heatP d σ b (z - x))
      + torusM d σ (a + b) ^ 2) (flatTorusMeasure d) := i2.add (integrable_const _)
  obtain ⟨-, -, f2, f3, f4⟩ := phiN_facts hσ d ha hb 0
  have hpt : ∀ z, phiN d σ a b (x - z) ^ 2
      ≤ (torusM d σ a * torusM d σ b - 2 * torusM d σ (a + b))
          * (heatP d σ a (x - z) * heatP d σ b (z - x))
        + torusM d σ (a + b) ^ 2 := by
    intro z
    obtain ⟨g0, g1, -, -, -⟩ := phiN_facts hσ d ha hb (x - z)
    rw [heatP_flip d σ b x z] at g0 g1
    have h := mul_nonneg g0 (sub_nonneg.mpr g1)
    rw [phiN_split d σ a b x z]
    nlinarith
  calc ∫ z, phiN d σ a b (x - z) ^ 2 ∂flatTorusMeasure d
      ≤ ∫ z, ((torusM d σ a * torusM d σ b - 2 * torusM d σ (a + b))
          * (heatP d σ a (x - z) * heatP d σ b (z - x))
        + torusM d σ (a + b) ^ 2) ∂flatTorusMeasure d :=
        integral_mono (flat_integrable d _ (hc.pow 2)) i3 hpt
    _ = (torusM d σ a * torusM d σ b - 2 * torusM d σ (a + b)) * torusM d σ (a + b)
          + torusM d σ (a + b) ^ 2 := by
        rw [integral_add i2 (integrable_const _), integral_const_mul, pp_integral hσ d ha hb x,
          integral_const, probReal_univ, one_smul]
    _ ≤ torusM d σ a * torusM d σ b * torusM d σ (a + b) := by
        nlinarith [_root_.sq_nonneg (torusM d σ (a + b))]

theorem phiN_l1 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (x : FlatTorus d) :
    ∫ z, |phiN d σ a b (x - z)| ∂flatTorusMeasure d ≤ 2 * torusM d σ (a + b) := by
  have hc : Continuous fun z : FlatTorus d => phiN d σ a b (x - z) :=
    (phiN_cont hσ d ha hb).comp (continuous_const.sub continuous_id)
  have i1 := pp_integrable hσ d ha hb x
  have i3 : Integrable (fun z : FlatTorus d =>
      heatP d σ a (x - z) * heatP d σ b (z - x) + torusM d σ (a + b)) (flatTorusMeasure d) :=
    i1.add (integrable_const _)
  obtain ⟨-, -, f2, -, -⟩ := phiN_facts hσ d ha hb 0
  have hpt : ∀ z, |phiN d σ a b (x - z)|
      ≤ heatP d σ a (x - z) * heatP d σ b (z - x) + torusM d σ (a + b) := by
    intro z
    obtain ⟨g0, -, -, -, -⟩ := phiN_facts hσ d ha hb (x - z)
    rw [heatP_flip d σ b x z] at g0
    rw [phiN_split d σ a b x z]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc ∫ z, |phiN d σ a b (x - z)| ∂flatTorusMeasure d
      ≤ ∫ z, (heatP d σ a (x - z) * heatP d σ b (z - x) + torusM d σ (a + b))
          ∂flatTorusMeasure d := integral_mono (flat_integrable d _ hc.abs) i3 hpt
    _ = torusM d σ (a + b) + torusM d σ (a + b) := by
        rw [integral_add i1 (integrable_const _), pp_integral hσ d ha hb x, integral_const,
          probReal_univ, one_smul]
    _ = 2 * torusM d σ (a + b) := by ring

/-- `m_l m_m ≤ (√2)^d M m_{l+m}` for `l, m ≥ 1` (the larger index is at least `(l+m)/2`). -/
theorem m_prod {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    torusM d σ l * torusM d σ m ≤ Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ (l + m) := by
  have hA : (0 : ℝ) ≤ Real.sqrt 2 ^ d := pow_nonneg (Real.sqrt_nonneg 2) d
  have hl1 := torusM_anti hσ d (le_refl 1) hl
  have hm1 := torusM_anti hσ d (le_refl 1) hm
  have hl0 : 0 ≤ torusM d σ l := by linarith [torusM_ge_one hσ d hl]
  have hm0 : 0 ≤ torusM d σ m := by linarith [torusM_ge_one hσ d hm]
  have hk0 : 0 ≤ torusM d σ (l + m) := by
    linarith [torusM_ge_one hσ d (by omega : 1 ≤ l + m)]
  by_cases h : l ≤ m
  · have h2 := torusM_ratio hσ d hm (by omega : m ≤ l + m) (by omega : l + m ≤ 2 * m)
    calc torusM d σ l * torusM d σ m
        ≤ torusM d σ 1 * (Real.sqrt 2 ^ d * torusM d σ (l + m)) :=
          mul_le_mul hl1 h2 hm0 (hl0.trans hl1)
      _ = Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ (l + m) := by ring
  · have h2 := torusM_ratio hσ d hl (by omega : l ≤ l + m) (by omega : l + m ≤ 2 * l)
    calc torusM d σ l * torusM d σ m
        ≤ (Real.sqrt 2 ^ d * torusM d σ (l + m)) * torusM d σ 1 :=
          mul_le_mul h2 hm1 hm0 (mul_nonneg hA hk0)
      _ = Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ (l + m) := by ring

theorem sqrt2_pow_ge_one (d : ℕ) : (1 : ℝ) ≤ Real.sqrt 2 ^ d :=
  one_le_pow₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num))

section SamplePhi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The hypotheses `Deg2` for `φ_{a,b}`. -/
theorem phiN_deg2 [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    Deg2 μ (flatTorusMeasure d) X (phiN d σ a b) (torusM d σ a * torusM d σ b)
      (torusM d σ a * torusM d σ b * torusM d σ (a + b)) := by
  obtain ⟨-, -, f2, f3, f4⟩ := phiN_facts hσ d ha hb 0
  exact
    { indep := h_indep
      meas := hX
      law := hlaw
      psi_meas := (phiN_cont hσ d ha hb).measurable
      bound := phiN_bound hσ d ha hb
      even := phiN_even d σ a b
      mean := phiN_mean hσ d ha hb
      var := phiN_var hσ d ha hb
      V_nonneg := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith) }

/-- The hypotheses `Deg2` for `c = p - 1`. -/
theorem cK_deg2 [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) :
    Deg2 μ (flatTorusMeasure d) X (cK d σ) (torusM d σ 1) (torusM d σ 1) :=
  (torus_deg3 X h_indep hX hlaw hσ 1 le_rfl).hc

/-- The hypotheses `Deg3` for `φ_{a,b}` and `c`. -/
theorem phiN_deg3 [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    Deg3 μ (flatTorusMeasure d) X (phiN d σ a b) (cK d σ) (torusM d σ a * torusM d σ b)
      (torusM d σ 1) (torusM d σ a * torusM d σ b * torusM d σ (a + b)) (torusM d σ 1) :=
  { hψ := phiN_deg2 X h_indep hX hlaw hσ ha hb
    hc := cK_deg2 X h_indep hX hlaw hσ }

theorem BM_heatP {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) {a : ℕ} (ha : 1 ≤ a) (i b : ℕ) :
    BM (fun ω => heatP d σ a (X i ω - X b ω)) :=
  ⟨(heatP_cont hσ d ha).measurable.comp ((hX i).sub (hX b)), torusM d σ a, fun ω => by
    rw [abs_of_nonneg (heatP_nonneg hσ d a _)]
    exact heatP_le hσ d ha _⟩

end SamplePhi

/-! ### the completely degenerate part `T` of the triangle `p_l(u) p(w) p_m(v)` -/

/-- `T(y₁,y₂,y₃) = p_l(u) p(w) p_m(v) - p_l(u) p_{m+1}(u) - p_{l+1}(v) p_m(v) - p(w) p_{l+m}(w)
    + 2 m_{l+m+1}`, `u = y₁ - y₂`, `w = y₂ - y₃`, `v = y₁ - y₃`. -/
noncomputable def Tdeg (d : ℕ) (σ : ℝ) (l m : ℕ) (y1 y2 y3 : FlatTorus d) : ℝ :=
  heatP d σ l (y1 - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (y1 - y3)
    - heatP d σ l (y1 - y2) * heatP d σ (m + 1) (y1 - y2)
    - heatP d σ (l + 1) (y1 - y3) * heatP d σ m (y1 - y3)
    - heatP d σ 1 (y2 - y3) * heatP d σ (l + m) (y2 - y3)
    + 2 * torusM d σ (l + m + 1)

/-- **The decomposition of `K_m`**:
    `K_m = T + φ_{l+1,m}(v) + φ_{1,l+m}(w) - m_{l+m+1} c(w) - φ_{l,m+1}(u) c(w)`. -/
theorem Km_decomp (d : ℕ) (σ : ℝ) (l m : ℕ) (y1 y2 y3 : FlatTorus d) :
    Km d σ l m y1 y2 y3
      = Tdeg d σ l m y1 y2 y3 + phiN d σ (l + 1) m (y1 - y3) + phiN d σ 1 (l + m) (y2 - y3)
        - torusM d σ (l + m + 1) * cK d σ (y2 - y3)
        - phiN d σ l (m + 1) (y1 - y2) * cK d σ (y2 - y3) := by
  have e1 : heatP d σ m (y3 - y1) = heatP d σ m (y1 - y3) := heatP_flip d σ m y3 y1
  have j1 : l + 1 + m = l + m + 1 := by omega
  have j2 : 1 + (l + m) = l + m + 1 := by omega
  have j3 : l + (m + 1) = l + m + 1 := rfl
  have e2 : pker d σ (y2 - y3) = heatP d σ 1 (y2 - y3) := (heatP_one d σ _).symm
  unfold Km Tdeg phiN cK
  rw [e1, e2, j1, j2, j3]
  ring

/-- Linearity of the integral for `f₁ - f₂ - f₃ - c` on a probability space. -/
theorem int4 {G : Type*} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    {f1 f2 f3 : G → ℝ} (h1 : Integrable f1 ν) (h2 : Integrable f2 ν) (h3 : Integrable f3 ν)
    (c : ℝ) :
    ∫ z, (f1 z - f2 z - f3 z - c) ∂ν = ∫ z, f1 z ∂ν - ∫ z, f2 z ∂ν - ∫ z, f3 z ∂ν - c := by
  have h12 : Integrable (fun z => f1 z - f2 z) ν := h1.sub h2
  have h123 : Integrable (fun z => f1 z - f2 z - f3 z) ν := h12.sub h3
  rw [integral_sub h123 (integrable_const c), integral_sub h12 h3, integral_sub h1 h2,
    integral_const, probReal_univ, one_smul]

/-- **`T` is degenerate in its first argument.** -/
theorem Tdeg_mean1 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (y2 y3 : FlatTorus d) : ∫ z, Tdeg d σ l m z y2 y3 ∂flatTorusMeasure d = 0 := by
  have cl : Continuous fun z : FlatTorus d => heatP d σ l (z - y2) :=
    (heatP_cont hσ d hl).comp (continuous_id.sub continuous_const)
  have cm : Continuous fun z : FlatTorus d => heatP d σ m (z - y3) :=
    (heatP_cont hσ d hm).comp (continuous_id.sub continuous_const)
  have cm1 : Continuous fun z : FlatTorus d => heatP d σ (m + 1) (z - y2) :=
    (heatP_cont hσ d (by omega : 1 ≤ m + 1)).comp (continuous_id.sub continuous_const)
  have cl1 : Continuous fun z : FlatTorus d => heatP d σ (l + 1) (z - y3) :=
    (heatP_cont hσ d (by omega : 1 ≤ l + 1)).comp (continuous_id.sub continuous_const)
  have i1 : Integrable (fun z : FlatTorus d =>
      heatP d σ l (z - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (z - y3))
      (flatTorusMeasure d) := flat_integrable d _ ((cl.mul continuous_const).mul cm)
  have i2 : Integrable (fun z : FlatTorus d =>
      heatP d σ l (z - y2) * heatP d σ (m + 1) (z - y2)) (flatTorusMeasure d) :=
    flat_integrable d _ (cl.mul cm1)
  have i3 : Integrable (fun z : FlatTorus d =>
      heatP d σ (l + 1) (z - y3) * heatP d σ m (z - y3)) (flatTorusMeasure d) :=
    flat_integrable d _ (cl1.mul cm)
  have I1 : ∫ z, heatP d σ l (z - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (z - y3)
      ∂flatTorusMeasure d = heatP d σ 1 (y2 - y3) * heatP d σ (m + l) (y3 - y2) := by
    have e : ∀ z : FlatTorus d,
        heatP d σ l (z - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (z - y3)
          = heatP d σ 1 (y2 - y3) * (heatP d σ m (y3 - z) * heatP d σ l (z - y2)) := fun z => by
      rw [heatP_flip d σ m z y3]; ring
    simp_rw [e]
    rw [integral_const_mul, heatP_semi hσ d hm hl y3 y2]
  have I2 : ∫ z, heatP d σ l (z - y2) * heatP d σ (m + 1) (z - y2) ∂flatTorusMeasure d
      = torusM d σ (l + (m + 1)) := by
    have e : ∀ z : FlatTorus d, heatP d σ l (z - y2) * heatP d σ (m + 1) (z - y2)
        = heatP d σ l (y2 - z) * heatP d σ (m + 1) (z - y2) := fun z => by
      rw [heatP_flip d σ l z y2]
    simp_rw [e]
    exact pp_integral hσ d hl (by omega) y2
  have I3 : ∫ z, heatP d σ (l + 1) (z - y3) * heatP d σ m (z - y3) ∂flatTorusMeasure d
      = torusM d σ (l + 1 + m) := by
    have e : ∀ z : FlatTorus d, heatP d σ (l + 1) (z - y3) * heatP d σ m (z - y3)
        = heatP d σ (l + 1) (y3 - z) * heatP d σ m (z - y3) := fun z => by
      rw [heatP_flip d σ (l + 1) z y3]
    simp_rw [e]
    exact pp_integral hσ d (by omega) hm y3
  have hsum : ∫ z, Tdeg d σ l m z y2 y3 ∂flatTorusMeasure d
      = ∫ z, heatP d σ l (z - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (z - y3)
            ∂flatTorusMeasure d
        - ∫ z, heatP d σ l (z - y2) * heatP d σ (m + 1) (z - y2) ∂flatTorusMeasure d
        - ∫ z, heatP d σ (l + 1) (z - y3) * heatP d σ m (z - y3) ∂flatTorusMeasure d
        - (heatP d σ 1 (y2 - y3) * heatP d σ (l + m) (y2 - y3)
            - 2 * torusM d σ (l + m + 1)) := by
    have e : ∀ z : FlatTorus d, Tdeg d σ l m z y2 y3
        = heatP d σ l (z - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (z - y3)
          - heatP d σ l (z - y2) * heatP d σ (m + 1) (z - y2)
          - heatP d σ (l + 1) (z - y3) * heatP d σ m (z - y3)
          - (heatP d σ 1 (y2 - y3) * heatP d σ (l + m) (y2 - y3)
              - 2 * torusM d σ (l + m + 1)) := fun z => by
      unfold Tdeg; ring
    simp_rw [e]
    exact int4 (flatTorusMeasure d) i1 i2 i3 _
  have e2 : heatP d σ (m + l) (y3 - y2) = heatP d σ (l + m) (y2 - y3) := by
    rw [Nat.add_comm m l]; exact heatP_flip d σ (l + m) y3 y2
  have j1 : l + (m + 1) = l + m + 1 := rfl
  have j2 : l + 1 + m = l + m + 1 := by omega
  rw [hsum, I1, I2, I3, e2, j1, j2]
  ring

/-- **`T` is degenerate in its second argument.** -/
theorem Tdeg_mean2 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (y1 y3 : FlatTorus d) : ∫ z, Tdeg d σ l m y1 z y3 ∂flatTorusMeasure d = 0 := by
  have cl : Continuous fun z : FlatTorus d => heatP d σ l (y1 - z) :=
    (heatP_cont hσ d hl).comp (continuous_const.sub continuous_id)
  have c1 : Continuous fun z : FlatTorus d => heatP d σ 1 (z - y3) :=
    (heatP_cont hσ d le_rfl).comp (continuous_id.sub continuous_const)
  have cm1 : Continuous fun z : FlatTorus d => heatP d σ (m + 1) (y1 - z) :=
    (heatP_cont hσ d (by omega : 1 ≤ m + 1)).comp (continuous_const.sub continuous_id)
  have clm : Continuous fun z : FlatTorus d => heatP d σ (l + m) (z - y3) :=
    (heatP_cont hσ d (by omega : 1 ≤ l + m)).comp (continuous_id.sub continuous_const)
  have i1 : Integrable (fun z : FlatTorus d =>
      heatP d σ l (y1 - z) * heatP d σ 1 (z - y3) * heatP d σ m (y1 - y3))
      (flatTorusMeasure d) := flat_integrable d _ ((cl.mul c1).mul continuous_const)
  have i2 : Integrable (fun z : FlatTorus d =>
      heatP d σ l (y1 - z) * heatP d σ (m + 1) (y1 - z)) (flatTorusMeasure d) :=
    flat_integrable d _ (cl.mul cm1)
  have i3 : Integrable (fun z : FlatTorus d =>
      heatP d σ 1 (z - y3) * heatP d σ (l + m) (z - y3)) (flatTorusMeasure d) :=
    flat_integrable d _ (c1.mul clm)
  have I1 : ∫ z, heatP d σ l (y1 - z) * heatP d σ 1 (z - y3) * heatP d σ m (y1 - y3)
      ∂flatTorusMeasure d = heatP d σ (l + 1) (y1 - y3) * heatP d σ m (y1 - y3) := by
    rw [integral_mul_const, heatP_semi hσ d hl le_rfl y1 y3]
  have I2 : ∫ z, heatP d σ l (y1 - z) * heatP d σ (m + 1) (y1 - z) ∂flatTorusMeasure d
      = torusM d σ (l + (m + 1)) := by
    have e : ∀ z : FlatTorus d, heatP d σ l (y1 - z) * heatP d σ (m + 1) (y1 - z)
        = heatP d σ l (y1 - z) * heatP d σ (m + 1) (z - y1) := fun z => by
      rw [heatP_flip d σ (m + 1) y1 z]
    simp_rw [e]
    exact pp_integral hσ d hl (by omega) y1
  have I3 : ∫ z, heatP d σ 1 (z - y3) * heatP d σ (l + m) (z - y3) ∂flatTorusMeasure d
      = torusM d σ (1 + (l + m)) := by
    have e : ∀ z : FlatTorus d, heatP d σ 1 (z - y3) * heatP d σ (l + m) (z - y3)
        = heatP d σ 1 (y3 - z) * heatP d σ (l + m) (z - y3) := fun z => by
      rw [heatP_flip d σ 1 z y3]
    simp_rw [e]
    exact pp_integral hσ d le_rfl (by omega) y3
  have hsum : ∫ z, Tdeg d σ l m y1 z y3 ∂flatTorusMeasure d
      = ∫ z, heatP d σ l (y1 - z) * heatP d σ 1 (z - y3) * heatP d σ m (y1 - y3)
            ∂flatTorusMeasure d
        - ∫ z, heatP d σ l (y1 - z) * heatP d σ (m + 1) (y1 - z) ∂flatTorusMeasure d
        - ∫ z, heatP d σ 1 (z - y3) * heatP d σ (l + m) (z - y3) ∂flatTorusMeasure d
        - (heatP d σ (l + 1) (y1 - y3) * heatP d σ m (y1 - y3)
            - 2 * torusM d σ (l + m + 1)) := by
    have e : ∀ z : FlatTorus d, Tdeg d σ l m y1 z y3
        = heatP d σ l (y1 - z) * heatP d σ 1 (z - y3) * heatP d σ m (y1 - y3)
          - heatP d σ l (y1 - z) * heatP d σ (m + 1) (y1 - z)
          - heatP d σ 1 (z - y3) * heatP d σ (l + m) (z - y3)
          - (heatP d σ (l + 1) (y1 - y3) * heatP d σ m (y1 - y3)
              - 2 * torusM d σ (l + m + 1)) := fun z => by
      unfold Tdeg; ring
    simp_rw [e]
    exact int4 (flatTorusMeasure d) i1 i2 i3 _
  have j1 : l + (m + 1) = l + m + 1 := rfl
  have j2 : 1 + (l + m) = l + m + 1 := by omega
  rw [hsum, I1, I2, I3, j1, j2]
  ring

/-- The sup bound used for `T` (only needed for integrability). -/
noncomputable def TdegB (d : ℕ) (σ : ℝ) (l m : ℕ) : ℝ :=
  torusM d σ l * torusM d σ 1 * torusM d σ m + torusM d σ l * torusM d σ (m + 1)
    + torusM d σ (l + 1) * torusM d σ m + torusM d σ 1 * torusM d σ (l + m)
    + 2 * torusM d σ (l + m + 1)

theorem Tdeg_bound {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (y1 y2 y3 : FlatTorus d) : |Tdeg d σ l m y1 y2 y3| ≤ TdegB d σ l m := by
  have a0 := heatP_nonneg hσ d l (y1 - y2)
  have a1 := heatP_le hσ d hl (y1 - y2)
  have b0 := heatP_nonneg hσ d 1 (y2 - y3)
  have b1 := heatP_le hσ d (le_refl 1) (y2 - y3)
  have c0 := heatP_nonneg hσ d m (y1 - y3)
  have c1 := heatP_le hσ d hm (y1 - y3)
  have t0 : 0 ≤ heatP d σ l (y1 - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (y1 - y3) :=
    mul_nonneg (mul_nonneg a0 b0) c0
  have t1 : heatP d σ l (y1 - y2) * heatP d σ 1 (y2 - y3) * heatP d σ m (y1 - y3)
      ≤ torusM d σ l * torusM d σ 1 * torusM d σ m :=
    mul_le_mul (mul_le_mul a1 b1 b0 (a0.trans a1)) c1 c0
      (mul_nonneg (a0.trans a1) (b0.trans b1))
  obtain ⟨u0, u1, -, -, -⟩ := phiN_facts hσ d hl (by omega : 1 ≤ m + 1) (y1 - y2)
  obtain ⟨v0, v1, -, -, -⟩ := phiN_facts hσ d (by omega : 1 ≤ l + 1) hm (y1 - y3)
  obtain ⟨w0, w1, -, -, -⟩ := phiN_facts hσ d (le_refl 1) (by omega : 1 ≤ l + m) (y2 - y3)
  have k0 : 0 ≤ torusM d σ (l + m + 1) := by
    linarith [torusM_ge_one hσ d (by omega : 1 ≤ l + m + 1)]
  unfold Tdeg TdegB
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem Tdeg_meas {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
      Tdeg d σ l m p.1 p.2.1 p.2.2) := by
  have hP : ∀ a : ℕ, 1 ≤ a → Measurable (heatP d σ a) := fun a ha =>
    (heatP_cont hσ d ha).measurable
  have mu : Measurable fun p : FlatTorus d × FlatTorus d × FlatTorus d => p.1 - p.2.1 :=
    measurable_fst.sub measurable_snd.fst
  have mw : Measurable fun p : FlatTorus d × FlatTorus d × FlatTorus d => p.2.1 - p.2.2 :=
    measurable_snd.fst.sub measurable_snd.snd
  have mv : Measurable fun p : FlatTorus d × FlatTorus d × FlatTorus d => p.1 - p.2.2 :=
    measurable_fst.sub measurable_snd.snd
  have pl := (hP l hl).comp mu
  have pm1 := (hP (m + 1) (by omega)).comp mu
  have p1 := (hP 1 le_rfl).comp mw
  have plm := (hP (l + m) (by omega)).comp mw
  have pm := (hP m hm).comp mv
  have pl1 := (hP (l + 1) (by omega)).comp mv
  show Measurable fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
    heatP d σ l (p.1 - p.2.1) * heatP d σ 1 (p.2.1 - p.2.2) * heatP d σ m (p.1 - p.2.2)
      - heatP d σ l (p.1 - p.2.1) * heatP d σ (m + 1) (p.1 - p.2.1)
      - heatP d σ (l + 1) (p.1 - p.2.2) * heatP d σ m (p.1 - p.2.2)
      - heatP d σ 1 (p.2.1 - p.2.2) * heatP d σ (l + m) (p.2.1 - p.2.2)
      + 2 * torusM d σ (l + m + 1)
  exact (((((pl.mul p1).mul pm).sub (pl.mul pm1)).sub (pl1.mul pm)).sub (p1.mul plm)).add
    measurable_const

/-- Second moment by one more elementary inequality:
    `t² ≤ 4 (B f + K + a² + b² + c²)` pointwise gives `∫ t² ≤ 4 (B F₀ + K + V_a + V_b + V_c)`. -/
theorem sq_tri_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {t f a b c : Ω → ℝ} (ht : BM t) (hf : BM f) (ha : BM a) (hb : BM b) (hc : BM c) {B K : ℝ}
    (hpt : ∀ ω, t ω ^ 2 ≤ 4 * (B * f ω + K + a ω ^ 2 + b ω ^ 2 + c ω ^ 2)) {F0 Va Vb Vc : ℝ}
    (hB : 0 ≤ B) (hF : ∫ ω, f ω ∂μ ≤ F0) (hA : ∫ ω, a ω ^ 2 ∂μ ≤ Va)
    (hBb : ∫ ω, b ω ^ 2 ∂μ ≤ Vb) (hC : ∫ ω, c ω ^ 2 ∂μ ≤ Vc) :
    ∫ ω, t ω ^ 2 ∂μ ≤ 4 * (B * F0 + K + Va + Vb + Vc) := by
  have iT : Integrable (fun ω => t ω ^ 2) μ := ht.sqr.integrable
  have iA : Integrable (fun ω => a ω ^ 2) μ := ha.sqr.integrable
  have iB : Integrable (fun ω => b ω ^ 2) μ := hb.sqr.integrable
  have iC : Integrable (fun ω => c ω ^ 2) μ := hc.sqr.integrable
  have j1 : Integrable (fun ω => B * f ω) μ := hf.integrable.const_mul B
  have j2 : Integrable (fun ω => B * f ω + K) μ := j1.add (integrable_const K)
  have j3 : Integrable (fun ω => B * f ω + K + a ω ^ 2) μ := j2.add iA
  have j4 : Integrable (fun ω => B * f ω + K + a ω ^ 2 + b ω ^ 2) μ := j3.add iB
  have j5 : Integrable (fun ω => B * f ω + K + a ω ^ 2 + b ω ^ 2 + c ω ^ 2) μ := j4.add iC
  have j6 : Integrable (fun ω => 4 * (B * f ω + K + a ω ^ 2 + b ω ^ 2 + c ω ^ 2)) μ :=
    j5.const_mul 4
  calc ∫ ω, t ω ^ 2 ∂μ
      ≤ ∫ ω, 4 * (B * f ω + K + a ω ^ 2 + b ω ^ 2 + c ω ^ 2) ∂μ := integral_mono iT j6 hpt
    _ = 4 * (B * ∫ ω, f ω ∂μ + K + ∫ ω, a ω ^ 2 ∂μ + ∫ ω, b ω ^ 2 ∂μ + ∫ ω, c ω ^ 2 ∂μ) := by
        rw [integral_const_mul, integral_add j4 iC, integral_add j3 iB, integral_add j2 iA,
          integral_add j1 (integrable_const K), integral_const_mul, integral_const,
          probReal_univ, one_smul]
    _ ≤ 4 * (B * F0 + K + Va + Vb + Vc) := by
        have h1 := mul_le_mul_of_nonneg_left hF hB
        linarith

/-- The bound for the second moment of `T` at three distinct sample points. -/
noncomputable def TdegV (d : ℕ) (σ : ℝ) (l m : ℕ) : ℝ :=
  4 * (torusM d σ l * torusM d σ 1 * torusM d σ m * torusM d σ (l + (1 + m))
    + torusM d σ (l + m + 1) ^ 2
    + torusM d σ l * torusM d σ (m + 1) * torusM d σ (l + (m + 1))
    + torusM d σ (l + 1) * torusM d σ m * torusM d σ (l + 1 + m)
    + torusM d σ 1 * torusM d σ (l + m) * torusM d σ (1 + (l + m)))

section SampleT

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `E p_l(X_i - X_b) p(X_b - X_q) p_m(X_i - X_q) ≤ m_{l+m+1}` for distinct indices (it is an
    equality; only the bound is needed). -/
theorem tri_mean [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) {i b q : ℕ} (hib : i ≠ b) (hiq : i ≠ q) (hbq : b ≠ q) :
    ∫ ω, heatP d σ l (X i ω - X b ω) * heatP d σ 1 (X b ω - X q ω)
        * heatP d σ m (X i ω - X q ω) ∂μ ≤ torusM d σ (l + (1 + m)) := by
  have hP : ∀ a : ℕ, 1 ≤ a → Measurable (heatP d σ a) := fun a ha =>
    (heatP_cont hσ d ha).measurable
  have hl0 : 0 ≤ torusM d σ l := by linarith [torusM_ge_one hσ d hl]
  have h10 : 0 ≤ torusM d σ 1 := by linarith [torusM_ge_one hσ d (le_refl 1)]
  have r0 : Measurable fun p : FlatTorus d × (FlatTorus d × FlatTorus d) => p.1 := measurable_fst
  have r1 : Measurable fun p : FlatTorus d × (FlatTorus d × FlatTorus d) => p.2.1 :=
    measurable_snd.fst
  have r2 : Measurable fun p : FlatTorus d × (FlatTorus d × FlatTorus d) => p.2.2 :=
    measurable_snd.snd
  have s1 : ∫ ω, heatP d σ l (X i ω - X b ω) * heatP d σ 1 (X b ω - X q ω)
        * heatP d σ m (X i ω - X q ω) ∂μ
      ≤ ∫ ω, heatP d σ l (X i ω - X b ω) * heatP d σ (1 + m) (X b ω - X i ω) ∂μ :=
    indep_integral_le_fun (flatTorusMeasure d) (X q) (fun ω => (X i ω, X b ω)) (hX q)
      ((hX i).prodMk (hX b)) (indep_two X h_indep hX (Ne.symm hiq) (Ne.symm hbq)) (hlaw q)
      (fun p : FlatTorus d × (FlatTorus d × FlatTorus d) =>
        heatP d σ l (p.2.1 - p.2.2) * heatP d σ 1 (p.2.2 - p.1) * heatP d σ m (p.2.1 - p.1))
      ((((hP l hl).comp (r1.sub r2)).mul ((hP 1 le_rfl).comp (r2.sub r0))).mul
        ((hP m hm).comp (r1.sub r0)))
      (B := torusM d σ l * torusM d σ 1 * torusM d σ m)
      (Bg := torusM d σ l * torusM d σ (1 + m))
      (fun p => by
        have a0 := heatP_nonneg hσ d l (p.2.1 - p.2.2)
        have a1 := heatP_le hσ d hl (p.2.1 - p.2.2)
        have b0 := heatP_nonneg hσ d 1 (p.2.2 - p.1)
        have b1 := heatP_le hσ d (le_refl 1) (p.2.2 - p.1)
        have c0 := heatP_nonneg hσ d m (p.2.1 - p.1)
        have c1 := heatP_le hσ d hm (p.2.1 - p.1)
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg a0 b0) c0)]
        exact mul_le_mul (mul_le_mul a1 b1 b0 hl0) c1 c0 (mul_nonneg hl0 h10))
      (fun y : FlatTorus d × FlatTorus d =>
        heatP d σ l (y.1 - y.2) * heatP d σ (1 + m) (y.2 - y.1))
      (((hP l hl).comp (measurable_fst.sub measurable_snd)).mul
        ((hP (1 + m) (by omega)).comp (measurable_snd.sub measurable_fst)))
      (fun y => by
        have a0 := heatP_nonneg hσ d l (y.1 - y.2)
        have a1 := heatP_le hσ d hl (y.1 - y.2)
        have b0 := heatP_nonneg hσ d (1 + m) (y.2 - y.1)
        have b1 := heatP_le hσ d (by omega : 1 ≤ 1 + m) (y.2 - y.1)
        rw [abs_of_nonneg (mul_nonneg a0 b0)]
        exact mul_le_mul a1 b1 b0 hl0)
      (fun y => by
        show ∫ z, heatP d σ l (y.1 - y.2) * heatP d σ 1 (y.2 - z) * heatP d σ m (y.1 - z)
            ∂flatTorusMeasure d ≤ heatP d σ l (y.1 - y.2) * heatP d σ (1 + m) (y.2 - y.1)
        have e : ∀ z : FlatTorus d,
            heatP d σ l (y.1 - y.2) * heatP d σ 1 (y.2 - z) * heatP d σ m (y.1 - z)
              = heatP d σ l (y.1 - y.2) * (heatP d σ 1 (y.2 - z) * heatP d σ m (z - y.1)) :=
          fun z => by rw [heatP_flip d σ m y.1 z]; ring
        simp_rw [e]
        rw [integral_const_mul, heatP_semi hσ d le_rfl hm y.2 y.1])
  have s2 : ∫ ω, heatP d σ l (X i ω - X b ω) * heatP d σ (1 + m) (X b ω - X i ω) ∂μ
      ≤ torusM d σ (l + (1 + m)) :=
    indep_integral_le (flatTorusMeasure d) (X b) (X i) (hX b) (hX i)
      (h_indep.indepFun (Ne.symm hib)) (hlaw b)
      (fun p : FlatTorus d × FlatTorus d =>
        heatP d σ l (p.2 - p.1) * heatP d σ (1 + m) (p.1 - p.2))
      (((hP l hl).comp (measurable_snd.sub measurable_fst)).mul
        ((hP (1 + m) (by omega)).comp (measurable_fst.sub measurable_snd)))
      (B := torusM d σ l * torusM d σ (1 + m))
      (fun p => by
        have a0 := heatP_nonneg hσ d l (p.2 - p.1)
        have a1 := heatP_le hσ d hl (p.2 - p.1)
        have b0 := heatP_nonneg hσ d (1 + m) (p.1 - p.2)
        have b1 := heatP_le hσ d (by omega : 1 ≤ 1 + m) (p.1 - p.2)
        rw [abs_of_nonneg (mul_nonneg a0 b0)]
        exact mul_le_mul a1 b1 b0 hl0)
      (fun y => le_of_eq (pp_integral hσ d hl (by omega) y))
  exact s1.trans s2

/-- The pointwise inequality behind the second moment of `T`. -/
theorem tri_sq_pt {x K a b c B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (hK : 0 ≤ K) :
    (x - K - a - b - c) ^ 2 ≤ 4 * (B * x + K ^ 2 + a ^ 2 + b ^ 2 + c ^ 2) := by
  have hxx : x * x ≤ B * x := mul_le_mul_of_nonneg_right hxB hx0
  have hkx : 0 ≤ K * x := mul_nonneg hK hx0
  have e : 4 * (B * x + K ^ 2 + a ^ 2 + b ^ 2 + c ^ 2) - (x - K - a - b - c) ^ 2
      = (x - K + a) ^ 2 + (x - K + b) ^ 2 + (x - K + c) ^ 2 + (a - b) ^ 2 + (a - c) ^ 2
        + (b - c) ^ 2 + 4 * (B * x - x * x) + 8 * (K * x) := by ring
  have h1 := _root_.sq_nonneg (x - K + a)
  have h2 := _root_.sq_nonneg (x - K + b)
  have h3 := _root_.sq_nonneg (x - K + c)
  have h4 := _root_.sq_nonneg (a - b)
  have h5 := _root_.sq_nonneg (a - c)
  have h6 := _root_.sq_nonneg (b - c)
  linarith

/-- `E T(X_i,X_b,X_q)² ≤ TdegV` for distinct indices. -/
theorem tdeg_var [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) {i b q : ℕ} (hib : i ≠ b) (hiq : i ≠ q) (hbq : b ≠ q) :
    ∫ ω, Tdeg d σ l m (X i ω) (X b ω) (X q ω) ^ 2 ∂μ ≤ TdegV d σ l m := by
  have hl0 : 0 ≤ torusM d σ l := by linarith [torusM_ge_one hσ d hl]
  have hm0 : 0 ≤ torusM d σ m := by linarith [torusM_ge_one hσ d hm]
  have h10 : 0 ≤ torusM d σ 1 := by linarith [torusM_ge_one hσ d (le_refl 1)]
  have hK0 : 0 ≤ torusM d σ (l + m + 1) := by
    linarith [torusM_ge_one hσ d (by omega : 1 ≤ l + m + 1)]
  have hB0 : 0 ≤ torusM d σ l * torusM d σ 1 * torusM d σ m :=
    mul_nonneg (mul_nonneg hl0 h10) hm0
  have Hu := phiN_deg2 X h_indep hX hlaw hσ hl (by omega : 1 ≤ m + 1)
  have Hv := phiN_deg2 X h_indep hX hlaw hσ (by omega : 1 ≤ l + 1) hm
  have Hw := phiN_deg2 X h_indep hX hlaw hσ (le_refl 1) (by omega : 1 ≤ l + m)
  have hmT := (Tdeg_meas hσ d hl hm).comp ((hX i).prodMk ((hX b).prodMk (hX q)))
  have bT : BM (fun ω => Tdeg d σ l m (X i ω) (X b ω) (X q ω)) :=
    ⟨hmT, TdegB d σ l m, fun ω => Tdeg_bound hσ d hl hm (X i ω) (X b ω) (X q ω)⟩
  have bTri : BM (fun ω => heatP d σ l (X i ω - X b ω) * heatP d σ 1 (X b ω - X q ω)
      * heatP d σ m (X i ω - X q ω)) :=
    ((BM_heatP X hX hσ hl i b).mul (BM_heatP X hX hσ (le_refl 1) b q)).mul
      (BM_heatP X hX hσ hm i q)
  have hpt : ∀ ω, Tdeg d σ l m (X i ω) (X b ω) (X q ω) ^ 2
      ≤ 4 * (torusM d σ l * torusM d σ 1 * torusM d σ m
            * (heatP d σ l (X i ω - X b ω) * heatP d σ 1 (X b ω - X q ω)
              * heatP d σ m (X i ω - X q ω))
          + torusM d σ (l + m + 1) ^ 2
          + phiN d σ l (m + 1) (X i ω - X b ω) ^ 2
          + phiN d σ (l + 1) m (X i ω - X q ω) ^ 2
          + phiN d σ 1 (l + m) (X b ω - X q ω) ^ 2) := by
    intro ω
    have a0 := heatP_nonneg hσ d l (X i ω - X b ω)
    have a1 := heatP_le hσ d hl (X i ω - X b ω)
    have b0 := heatP_nonneg hσ d 1 (X b ω - X q ω)
    have b1 := heatP_le hσ d (le_refl 1) (X b ω - X q ω)
    have c0 := heatP_nonneg hσ d m (X i ω - X q ω)
    have c1 := heatP_le hσ d hm (X i ω - X q ω)
    have x0 : 0 ≤ heatP d σ l (X i ω - X b ω) * heatP d σ 1 (X b ω - X q ω)
        * heatP d σ m (X i ω - X q ω) := mul_nonneg (mul_nonneg a0 b0) c0
    have x1 : heatP d σ l (X i ω - X b ω) * heatP d σ 1 (X b ω - X q ω)
        * heatP d σ m (X i ω - X q ω) ≤ torusM d σ l * torusM d σ 1 * torusM d σ m :=
      mul_le_mul (mul_le_mul a1 b1 b0 hl0) c1 c0 (mul_nonneg hl0 h10)
    have j1 : l + (m + 1) = l + m + 1 := rfl
    have j2 : l + 1 + m = l + m + 1 := by omega
    have j3 : 1 + (l + m) = l + m + 1 := by omega
    have hT : Tdeg d σ l m (X i ω) (X b ω) (X q ω)
        = heatP d σ l (X i ω - X b ω) * heatP d σ 1 (X b ω - X q ω)
            * heatP d σ m (X i ω - X q ω)
          - torusM d σ (l + m + 1) - phiN d σ l (m + 1) (X i ω - X b ω)
          - phiN d σ (l + 1) m (X i ω - X q ω) - phiN d σ 1 (l + m) (X b ω - X q ω) := by
      unfold Tdeg phiN
      rw [j1, j2, j3]
      ring
    rw [hT]
    exact tri_sq_pt x0 x1 hK0
  exact sq_tri_bound bT bTri (Hu.BM_psi i b) (Hv.BM_psi i q) (Hw.BM_psi b q) hpt hB0
    (tri_mean X h_indep hX hlaw hσ hl hm hib hiq hbq) (Hu.sq_le hib) (Hv.sq_le hiq)
    (Hw.sq_le hbq)

/-- **The hypotheses `Tri3` hold for `T`.** -/
theorem tdeg_tri3 [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) :
    Tri3 μ (flatTorusMeasure d) X (Tdeg d σ l m) (TdegB d σ l m) (TdegV d σ l m) := by
  have hl0 : 0 ≤ torusM d σ l := by linarith [torusM_ge_one hσ d hl]
  have hm0 : 0 ≤ torusM d σ m := by linarith [torusM_ge_one hσ d hm]
  have h10 : 0 ≤ torusM d σ 1 := by linarith [torusM_ge_one hσ d (le_refl 1)]
  have hB0 : 0 ≤ torusM d σ l * torusM d σ 1 * torusM d σ m :=
    mul_nonneg (mul_nonneg hl0 h10) hm0
  have Hu := phiN_deg2 X h_indep hX hlaw hσ hl (by omega : 1 ≤ m + 1)
  have Hv := phiN_deg2 X h_indep hX hlaw hσ (by omega : 1 ≤ l + 1) hm
  have Hw := phiN_deg2 X h_indep hX hlaw hσ (le_refl 1) (by omega : 1 ≤ l + m)
  have hV0 : 0 ≤ TdegV d σ l m := by
    have ha : 0 ≤ torusM d σ (l + (1 + m)) := by
      linarith [torusM_ge_one hσ d (by omega : 1 ≤ l + (1 + m))]
    have h1 := mul_nonneg hB0 ha
    have h2 := _root_.sq_nonneg (torusM d σ (l + m + 1))
    have h3 := Hu.V_nonneg
    have h4 := Hv.V_nonneg
    have h5 := Hw.V_nonneg
    unfold TdegV
    linarith
  exact
    { indep := h_indep
      meas := hX
      law := hlaw
      F_meas := Tdeg_meas hσ d hl hm
      bound := Tdeg_bound hσ d hl hm
      mean1 := Tdeg_mean1 hσ d hl hm
      mean2 := Tdeg_mean2 hσ d hl hm
      var := fun i b q hib hiq hbq => tdeg_var X h_indep hX hlaw hσ hl hm hib hiq hbq
      V_nonneg := hV0 }

end SampleT

/-! ### the diagonals of `T`, and the sum `R_q = ∑_{i,b} K_m(x_i,x_b,x_q)` for a fixed `q` -/

/-- `T(y,y,z)` as a function of `y - z`. -/
noncomputable def gD1 (d : ℕ) (σ : ℝ) (l m : ℕ) (e : FlatTorus d) : ℝ :=
  torusM d σ l * phiN d σ 1 m e - phiN d σ (l + 1) m e - phiN d σ 1 (l + m) e

/-- `T(z,y,z)` as a function of `y - z`. -/
noncomputable def gD2 (d : ℕ) (σ : ℝ) (l m : ℕ) (e : FlatTorus d) : ℝ :=
  torusM d σ m * phiN d σ l 1 e - phiN d σ l (m + 1) e - phiN d σ 1 (l + m) e

/-- `T(y,z,z)` as a function of `y - z`. -/
noncomputable def gD3 (d : ℕ) (σ : ℝ) (l m : ℕ) (e : FlatTorus d) : ℝ :=
  torusM d σ 1 * phiN d σ l m e - phiN d σ l (m + 1) e - phiN d σ (l + 1) m e

theorem Tdeg_diag1 (d : ℕ) (σ : ℝ) {l m : ℕ} (hl : 1 ≤ l) (y z : FlatTorus d) :
    Tdeg d σ l m y y z = gD1 d σ l m (y - z) := by
  have j1 : 1 + m = m + 1 := by omega
  have j2 : l + 1 + m = l + m + 1 := by omega
  have j3 : 1 + (l + m) = l + m + 1 := by omega
  unfold Tdeg gD1 phiN
  rw [sub_self, heatP_zero d σ hl, heatP_zero d σ (by omega : 1 ≤ m + 1), j1, j2, j3]
  ring

theorem Tdeg_diag2 (d : ℕ) (σ : ℝ) {l m : ℕ} (hm : 1 ≤ m) (y z : FlatTorus d) :
    Tdeg d σ l m z y z = gD2 d σ l m (y - z) := by
  have j1 : l + (m + 1) = l + m + 1 := rfl
  have j3 : 1 + (l + m) = l + m + 1 := by omega
  unfold Tdeg gD2 phiN
  rw [sub_self, heatP_zero d σ hm, heatP_zero d σ (by omega : 1 ≤ l + 1),
    heatP_flip d σ l z y, heatP_flip d σ (m + 1) z y, j1, j3]
  ring

theorem Tdeg_diag3 (d : ℕ) (σ : ℝ) {l m : ℕ} (hl : 1 ≤ l) (y z : FlatTorus d) :
    Tdeg d σ l m y z z = gD3 d σ l m (y - z) := by
  have j1 : l + (m + 1) = l + m + 1 := rfl
  have j2 : l + 1 + m = l + m + 1 := by omega
  unfold Tdeg gD3 phiN
  rw [sub_self, heatP_zero d σ (le_refl 1), heatP_zero d σ (by omega : 1 ≤ l + m), j1, j2]
  ring

theorem sum_off (N q : ℕ) (hq : q ∈ Finset.range N) (f : ℕ → ℝ) :
    ∑ v ∈ Finset.range N, (if v = q then 0 else f v) = ∑ v ∈ Finset.range N, f v - f q := by
  have h : ∀ v ∈ Finset.range N,
      (if v = q then 0 else f v) = f v - (if v = q then f v else 0) := by
    intro v _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos hq]

theorem Hrow_flip {Ω G : Type*} [AddCommGroup G] {ψ : G → ℝ} (hev : ∀ u, ψ (-u) = ψ u)
    (X : ℕ → Ω → G) (N q : ℕ) (ω : Ω) :
    ∑ v ∈ Finset.range N, ψ (X v ω - X q ω) = Hrow ψ X N q ω := by
  unfold Hrow
  exact Finset.sum_congr rfl fun v _ => by rw [← hev, neg_sub]

/-- The full sum of `T` over `i, b` for a fixed `q < N`: the part with distinct indices and the
    three diagonals. -/
theorem RT_eq {Ω : Type*} {d : ℕ} (σ : ℝ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (X : ℕ → Ω → FlatTorus d) (N q : ℕ) (hq : q ∈ Finset.range N) (ω : Ω) :
    ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, Tdeg d σ l m (X i ω) (X b ω) (X q ω)
      = Roff (Tdeg d σ l m) X N q ω
        + ∑ v ∈ Finset.range N, gD1 d σ l m (X v ω - X q ω)
        + (∑ v ∈ Finset.range N, gD2 d σ l m (X v ω - X q ω) - gD2 d σ l m 0)
        + (∑ v ∈ Finset.range N, gD3 d σ l m (X v ω - X q ω) - gD3 d σ l m 0) := by
  have hterm : ∀ i b : ℕ, Tdeg d σ l m (X i ω) (X b ω) (X q ω)
      = aF (Tdeg d σ l m) X i b q ω
        + (if i = b then gD1 d σ l m (X i ω - X q ω) else 0)
        + (if i = q then (if b = q then 0 else gD2 d σ l m (X b ω - X q ω)) else 0)
        + (if b = q then (if i = q then 0 else gD3 d σ l m (X i ω - X q ω)) else 0) := by
    intro i b
    by_cases hib : i = b
    · have ha : aF (Tdeg d σ l m) X i b q ω = 0 := by unfold aF; rw [if_pos (Or.inl hib)]
      have hT : Tdeg d σ l m (X i ω) (X b ω) (X q ω) = gD1 d σ l m (X i ω - X q ω) := by
        rw [← hib]; exact Tdeg_diag1 d σ hl _ _
      rw [hT, ha]
      by_cases hiq : i = q
      · have hbq : b = q := hib.symm.trans hiq
        simp only [if_pos hib, if_pos hiq, if_pos hbq]
        ring
      · have hbq : ¬ b = q := fun h => hiq (hib.trans h)
        simp only [if_pos hib, if_neg hiq, if_neg hbq]
        ring
    · by_cases hiq : i = q
      · have hbq : ¬ b = q := fun h => hib (hiq.trans h.symm)
        have ha : aF (Tdeg d σ l m) X i b q ω = 0 := by
          unfold aF; rw [if_pos (Or.inr (Or.inr hiq))]
        have hT : Tdeg d σ l m (X i ω) (X b ω) (X q ω) = gD2 d σ l m (X b ω - X q ω) := by
          rw [hiq]; exact Tdeg_diag2 d σ hm _ _
        rw [hT, ha]
        simp only [if_neg hib, if_pos hiq, if_neg hbq]
        ring
      · by_cases hbq : b = q
        · have ha : aF (Tdeg d σ l m) X i b q ω = 0 := by
            unfold aF; rw [if_pos (Or.inr (Or.inl hbq))]
          have hT : Tdeg d σ l m (X i ω) (X b ω) (X q ω) = gD3 d σ l m (X i ω - X q ω) := by
            rw [hbq]; exact Tdeg_diag3 d σ hl _ _
          rw [hT, ha]
          simp only [if_neg hib, if_neg hiq, if_pos hbq]
          ring
        · have hno : ¬ (i = b ∨ b = q ∨ i = q) := by
            rintro (h | h | h)
            · exact hib h
            · exact hbq h
            · exact hiq h
          have ha : aF (Tdeg d σ l m) X i b q ω = Tdeg d σ l m (X i ω) (X b ω) (X q ω) := by
            unfold aF; rw [if_neg hno]
          rw [ha]
          simp only [if_neg hib, if_neg hiq, if_neg hbq]
          ring
  have e1 : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (if i = b then gD1 d σ l m (X i ω - X q ω) else 0)
      = ∑ v ∈ Finset.range N, gD1 d σ l m (X v ω - X q ω) :=
    Finset.sum_congr rfl fun i hi => by rw [Finset.sum_ite_eq, if_pos hi]
  have e2 : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (if i = q then (if b = q then 0 else gD2 d σ l m (X b ω - X q ω)) else 0)
      = ∑ b ∈ Finset.range N, (if b = q then 0 else gD2 d σ l m (X b ω - X q ω)) := by
    have h : ∀ i ∈ Finset.range N,
        ∑ b ∈ Finset.range N,
            (if i = q then (if b = q then 0 else gD2 d σ l m (X b ω - X q ω)) else 0)
          = if i = q then
              ∑ b ∈ Finset.range N, (if b = q then 0 else gD2 d σ l m (X b ω - X q ω))
            else 0 := fun i _ => by
      by_cases hiq : i = q
      · simp only [if_pos hiq]
      · simp only [if_neg hiq, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_eq', if_pos hq]
  have e3 : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (if b = q then (if i = q then 0 else gD3 d σ l m (X i ω - X q ω)) else 0)
      = ∑ i ∈ Finset.range N, (if i = q then 0 else gD3 d σ l m (X i ω - X q ω)) :=
    Finset.sum_congr rfl fun i _ => by rw [Finset.sum_ite_eq', if_pos hq]
  have o2 : ∑ b ∈ Finset.range N, (if b = q then 0 else gD2 d σ l m (X b ω - X q ω))
      = ∑ v ∈ Finset.range N, gD2 d σ l m (X v ω - X q ω) - gD2 d σ l m 0 := by
    have h : ∑ b ∈ Finset.range N, (if b = q then 0 else gD2 d σ l m (X b ω - X q ω))
        = ∑ v ∈ Finset.range N, gD2 d σ l m (X v ω - X q ω)
          - gD2 d σ l m (X q ω - X q ω) :=
      sum_off N q hq (fun v => gD2 d σ l m (X v ω - X q ω))
    rw [sub_self] at h
    exact h
  have o3 : ∑ i ∈ Finset.range N, (if i = q then 0 else gD3 d σ l m (X i ω - X q ω))
      = ∑ v ∈ Finset.range N, gD3 d σ l m (X v ω - X q ω) - gD3 d σ l m 0 := by
    have h : ∑ i ∈ Finset.range N, (if i = q then 0 else gD3 d σ l m (X i ω - X q ω))
        = ∑ v ∈ Finset.range N, gD3 d σ l m (X v ω - X q ω)
          - gD3 d σ l m (X q ω - X q ω) :=
      sum_off N q hq (fun v => gD3 d σ l m (X v ω - X q ω))
    rw [sub_self] at h
    exact h
  have hsum : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, Tdeg d σ l m (X i ω) (X b ω) (X q ω)
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, aF (Tdeg d σ l m) X i b q ω
        + ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            (if i = b then gD1 d σ l m (X i ω - X q ω) else 0)
        + ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            (if i = q then (if b = q then 0 else gD2 d σ l m (X b ω - X q ω)) else 0)
        + ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            (if b = q then (if i = q then 0 else gD3 d σ l m (X i ω - X q ω)) else 0) := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => hterm i b]
    simp only [Finset.sum_add_distrib]
  rw [hsum, e1, e2, e3, o2, o3]
  rfl

/-- `R_q = ∑_{i,b} K_m(x_i,x_b,x_q)` (all `i, b < N`). -/
noncomputable def Rq {Ω : Type*} {d : ℕ} (σ : ℝ) (l m : ℕ) (X : ℕ → Ω → FlatTorus d) (N q : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, Km d σ l m (X i ω) (X b ω) (X q ω)

/-- The constant from the two diagonals `i = q`, `b = q` of `T`. -/
noncomputable def t2N (d : ℕ) (σ : ℝ) (l m : ℕ) : ℝ := gD2 d σ l m 0 + gD3 d σ l m 0

/-- **`R_q` in pieces**: the degenerate triangle over distinct indices, row sums of the
    `φ_{a,b}`, a constant, the row sum of `c`, and the chain `A_q`. -/
theorem Rq_eq {Ω : Type*} {d : ℕ} (σ : ℝ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (X : ℕ → Ω → FlatTorus d) (N q : ℕ) (hq : q ∈ Finset.range N) (ω : Ω) :
    Rq σ l m X N q ω
      = (Roff (Tdeg d σ l m) X N q ω + -t2N d σ l m)
        + (torusM d σ l * Hrow (phiN d σ 1 m) X N q ω
            + torusM d σ m * Hrow (phiN d σ l 1) X N q ω
            + torusM d σ 1 * Hrow (phiN d σ l m) X N q ω)
        + ((-2) * Hrow (phiN d σ l (m + 1)) X N q ω
            + ((N : ℝ) - 2) * Hrow (phiN d σ (l + 1) m) X N q ω
            + ((N : ℝ) - 2) * Hrow (phiN d σ 1 (l + m)) X N q ω)
        - torusM d σ (l + m + 1) * ((N : ℝ) * Hrow (cK d σ) X N q ω)
        - Aq (phiN d σ l (m + 1)) (cK d σ) X N q ω := by
  have f : ∀ a b : ℕ, ∑ v ∈ Finset.range N, phiN d σ a b (X v ω - X q ω)
      = Hrow (phiN d σ a b) X N q ω := fun a b => Hrow_flip (phiN_even d σ a b) X N q ω
  have fc : ∑ v ∈ Finset.range N, cK d σ (X v ω - X q ω) = Hrow (cK d σ) X N q ω :=
    Hrow_flip (cK_even d σ) X N q ω
  have hK : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, Km d σ l m (X i ω) (X b ω) (X q ω)
      = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, Tdeg d σ l m (X i ω) (X b ω) (X q ω)
        + (N : ℝ) * ∑ v ∈ Finset.range N, phiN d σ (l + 1) m (X v ω - X q ω)
        + (N : ℝ) * ∑ v ∈ Finset.range N, phiN d σ 1 (l + m) (X v ω - X q ω)
        - torusM d σ (l + m + 1) * ((N : ℝ) * ∑ v ∈ Finset.range N, cK d σ (X v ω - X q ω))
        - ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            phiN d σ l (m + 1) (X i ω - X b ω) * cK d σ (X b ω - X q ω) := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
      Km_decomp d σ l m (X i ω) (X b ω) (X q ω)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    try ring
  have g1 : ∑ v ∈ Finset.range N, gD1 d σ l m (X v ω - X q ω)
      = torusM d σ l * Hrow (phiN d σ 1 m) X N q ω - Hrow (phiN d σ (l + 1) m) X N q ω
        - Hrow (phiN d σ 1 (l + m)) X N q ω := by
    rw [← f 1 m, ← f (l + 1) m, ← f 1 (l + m)]
    unfold gD1
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  have g2 : ∑ v ∈ Finset.range N, gD2 d σ l m (X v ω - X q ω)
      = torusM d σ m * Hrow (phiN d σ l 1) X N q ω - Hrow (phiN d σ l (m + 1)) X N q ω
        - Hrow (phiN d σ 1 (l + m)) X N q ω := by
    rw [← f l 1, ← f l (m + 1), ← f 1 (l + m)]
    unfold gD2
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  have g3 : ∑ v ∈ Finset.range N, gD3 d σ l m (X v ω - X q ω)
      = torusM d σ 1 * Hrow (phiN d σ l m) X N q ω - Hrow (phiN d σ l (m + 1)) X N q ω
        - Hrow (phiN d σ (l + 1) m) X N q ω := by
    rw [← f l m, ← f l (m + 1), ← f (l + 1) m]
    unfold gD3
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  have hA : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
        phiN d σ l (m + 1) (X i ω - X b ω) * cK d σ (X b ω - X q ω)
      = Aq (phiN d σ l (m + 1)) (cK d σ) X N q ω := rfl
  unfold Rq
  rw [hK, RT_eq σ hl hm X N q hq ω, g1, g2, g3, f (l + 1) m, f 1 (l + m), fc, hA]
  unfold t2N
  ring

/-- `Z⁰[K_m]` of a sample through the `R_q`. -/
theorem Z0_Km_conv {Ω : Type*} {d : ℕ} (σ : ℝ) (l m N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    Zs0three N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
      = 1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N, Rq σ l m X N q ω :=
  congrArg (fun t => 1 / (N : ℝ) ^ 3 * t)
    (((Fin.sum_univ_eq_sum_range (fun i => ∑ b : Fin N, ∑ j : Fin N,
        Km d σ l m (X i ω) (X b ω) (X j ω)) N).trans
      (Finset.sum_congr rfl fun i _ =>
        (Fin.sum_univ_eq_sum_range (fun b => ∑ j : Fin N,
          Km d σ l m (X i ω) (X b ω) (X j ω)) N).trans
        (Finset.sum_congr rfl fun b _ =>
          Fin.sum_univ_eq_sum_range (fun j => Km d σ l m (X i ω) (X b ω) (X j ω)) N))).trans
      ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm))

/-- `Z¹[K_m, a = 3]` of a sample through the `R_q` and the row sums `H_q` of `c`. -/
theorem Z1_Km_conv {Ω : Type*} {d : ℕ} (σ : ℝ) (l m N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    Zs1three3 N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
        (cmat d σ N (fun j => X j ω))
      = 1 / (N : ℝ) ^ 4
        * ∑ q ∈ Finset.range N, Rq σ l m X N q ω * Hrow (cK d σ) X N q ω := by
  have hA : Zs1three3 N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
        (cmat d σ N (fun j => X j ω))
      = 1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
          ∑ v ∈ Finset.range N,
            Km d σ l m (X i ω) (X b ω) (X q ω) * cK d σ (X q ω - X v ω) :=
    congrArg (fun t => 1 / (N : ℝ) ^ 4 * t)
      ((Fin.sum_univ_eq_sum_range (fun i => ∑ b : Fin N, ∑ j : Fin N, ∑ v : Fin N,
          Km d σ l m (X i ω) (X b ω) (X j ω) * (pker d σ (X j ω - X v ω) - 1)) N).trans
        (Finset.sum_congr rfl fun i _ =>
          (Fin.sum_univ_eq_sum_range (fun b => ∑ j : Fin N, ∑ v : Fin N,
            Km d σ l m (X i ω) (X b ω) (X j ω) * (pker d σ (X j ω - X v ω) - 1)) N).trans
          (Finset.sum_congr rfl fun b _ =>
            (Fin.sum_univ_eq_sum_range (fun j => ∑ v : Fin N,
              Km d σ l m (X i ω) (X b ω) (X j ω) * (pker d σ (X j ω - X v ω) - 1)) N).trans
            (Finset.sum_congr rfl fun j _ =>
              Fin.sum_univ_eq_sum_range (fun v =>
                Km d σ l m (X i ω) (X b ω) (X j ω) * cK d σ (X j ω - X v ω)) N))))
  have hB : ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
        ∑ v ∈ Finset.range N, Km d σ l m (X i ω) (X b ω) (X q ω) * cK d σ (X q ω - X v ω)
      = ∑ q ∈ Finset.range N, Rq σ l m X N q ω * Hrow (cK d σ) X N q ω :=
    calc ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
          ∑ v ∈ Finset.range N, Km d σ l m (X i ω) (X b ω) (X q ω) * cK d σ (X q ω - X v ω)
        = ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N,
            Km d σ l m (X i ω) (X b ω) (X q ω) * Hrow (cK d σ) X N q ω := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun q _ => ?_
          unfold Hrow
          rw [Finset.mul_sum]
      _ = ∑ q ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            Km d σ l m (X i ω) (X b ω) (X q ω) * Hrow (cK d σ) X N q ω :=
          (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
      _ = ∑ q ∈ Finset.range N, Rq σ l m X N q ω * Hrow (cK d σ) X N q ω := by
          refine Finset.sum_congr rfl fun q _ => ?_
          unfold Rq
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  rw [hA, hB]

/-! ### pure arithmetic for the constants

`M = p(0)`, `k = m_{l+m}`, `w = (√2)^d M k`, so that `M k ≤ w` and `m_l m_m ≤ w`.  Second
moments `P` of the pieces of the factor of `H_q` are bounded in the form `M P ≤ c N³ w²`; with
`E H_q² ≤ 6 N M` this gives `E|X H_q| ≤ c' N² w` by the Cauchy–Schwarz inequality. -/

theorem ar_clsI {c ψ0 V M w N P : ℝ} (hM : 0 ≤ M) (hMN : M ≤ N) (hcB : |c * ψ0| ≤ M * w)
    (hcV : c ^ 2 * V ≤ M * w ^ 2) (hP : P ≤ c ^ 2 * (4 * N * V + 2 * ψ0 ^ 2)) :
    M * P ≤ 6 * (N ^ 3 * w ^ 2) := by
  have hN : 0 ≤ N := hM.trans hMN
  have h1 : (c * ψ0) ^ 2 ≤ (M * w) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (c * ψ0)) hcB 2
    rwa [sq_abs] at this
  have h2 : N * M ^ 2 ≤ N ^ 3 := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM hMN 2) hN
    calc N * M ^ 2 ≤ N * N ^ 2 := this
      _ = N ^ 3 := by ring
  have h3 : M ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ hM hMN 3
  have h4 : c ^ 2 * (4 * N * V + 2 * ψ0 ^ 2) ≤ 4 * N * (M * w ^ 2) + 2 * (M * w) ^ 2 := by
    have e : c ^ 2 * (4 * N * V + 2 * ψ0 ^ 2) = 4 * N * (c ^ 2 * V) + 2 * (c * ψ0) ^ 2 := by
      ring
    have := mul_le_mul_of_nonneg_left hcV (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hN)
    rw [e]; linarith
  have h5 : M * P ≤ M * (4 * N * (M * w ^ 2) + 2 * (M * w) ^ 2) :=
    mul_le_mul_of_nonneg_left (hP.trans h4) hM
  have e2 : M * (4 * N * (M * w ^ 2) + 2 * (M * w) ^ 2)
      = (4 * (N * M ^ 2) + 2 * M ^ 3) * w ^ 2 := by ring
  have h6 : (4 * (N * M ^ 2) + 2 * M ^ 3) * w ^ 2 ≤ (6 * N ^ 3) * w ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (_root_.sq_nonneg w)
  calc M * P ≤ M * (4 * N * (M * w ^ 2) + 2 * (M * w) ^ 2) := h5
    _ = (4 * (N * M ^ 2) + 2 * M ^ 3) * w ^ 2 := e2
    _ ≤ (6 * N ^ 3) * w ^ 2 := h6
    _ = 6 * (N ^ 3 * w ^ 2) := by ring

theorem ar_clsII {κ ψ0 V M w k N P : ℝ} (h1M : 1 ≤ M) (hMN : M ≤ N) (hMk : M * k ≤ w)
    (hκ : κ ^ 2 ≤ 4 * N ^ 2) (hψ : |ψ0| ≤ w) (hV0 : 0 ≤ V) (hV : V ≤ w * k)
    (hP : P ≤ κ ^ 2 * (4 * N * V + 2 * ψ0 ^ 2)) : M * P ≤ 24 * (N ^ 3 * w ^ 2) := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hw0 : 0 ≤ w := (abs_nonneg ψ0).trans hψ
  have hψ2 : ψ0 ^ 2 ≤ w ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg ψ0) hψ 2
    rwa [sq_abs] at this
  have hin0 : 0 ≤ 4 * N * V + 2 * ψ0 ^ 2 := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hN0) hV0
    linarith [_root_.sq_nonneg ψ0]
  have hin : 4 * N * V + 2 * ψ0 ^ 2 ≤ 4 * N * (w * k) + 2 * w ^ 2 := by
    have := mul_le_mul_of_nonneg_left hV (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hN0)
    linarith
  have hN2 : (0 : ℝ) ≤ 4 * N ^ 2 := mul_nonneg (by norm_num) (_root_.sq_nonneg N)
  have hP2 : P ≤ 4 * N ^ 2 * (4 * N * (w * k) + 2 * w ^ 2) :=
    hP.trans (mul_le_mul hκ hin hin0 hN2)
  have h5 : M * P ≤ M * (4 * N ^ 2 * (4 * N * (w * k) + 2 * w ^ 2)) :=
    mul_le_mul_of_nonneg_left hP2 hM0
  have a1 : N ^ 3 * (w * (M * k)) ≤ N ^ 3 * (w * w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMk hw0) (pow_nonneg hN0 3)
  have a2 : N ^ 2 * (M * w ^ 2) ≤ N ^ 2 * (N * w ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMN (_root_.sq_nonneg w))
      (_root_.sq_nonneg N)
  have e : M * (4 * N ^ 2 * (4 * N * (w * k) + 2 * w ^ 2))
      = 16 * (N ^ 3 * (w * (M * k))) + 8 * (N ^ 2 * (M * w ^ 2)) := by ring
  have e' : 16 * (N ^ 3 * (w * w)) + 8 * (N ^ 2 * (N * w ^ 2)) = 24 * (N ^ 3 * w ^ 2) := by ring
  linarith

theorem ar_VT {a b K1 K Vu Vv Vw M w k : ℝ} (h1M : 1 ≤ M) (hMk : M * k ≤ w) (hk : 0 ≤ k)
    (hab0 : 0 ≤ a * b) (hab : a * b ≤ w) (hK10 : 0 ≤ K1) (hK1 : K1 ≤ k) (hK0 : 0 ≤ K)
    (hK : K ≤ k) (hVu : Vu ≤ w * k) (hVv : Vv ≤ w * k) (hVw : Vw ≤ w * k) :
    4 * (a * M * b * K1 + K ^ 2 + Vu + Vv + Vw) ≤ 20 * M * w * k := by
  have hM0 : 0 ≤ M := by linarith
  have hw0 : 0 ≤ w := hab0.trans hab
  have hkM : k ≤ M * k := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ M - 1) hk
    linarith [show (M - 1) * k = M * k - k by ring]
  have hkw : k ≤ w := hkM.trans hMk
  have p1 : a * M * b * K1 ≤ M * w * k := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hab hM0) hK1 hK10 (mul_nonneg hM0 hw0)
    calc a * M * b * K1 = M * (a * b) * K1 := by ring
      _ ≤ M * w * k := this
  have p2 : K ^ 2 ≤ w * k := by
    have h1 : K ^ 2 ≤ k ^ 2 := pow_le_pow_left₀ hK0 hK 2
    have h2 : k * k ≤ w * k := mul_le_mul_of_nonneg_right hkw hk
    linarith [show k ^ 2 = k * k by ring]
  have p3 : w * k ≤ M * w * k := by
    have := mul_nonneg (mul_nonneg hw0 hk) (by linarith : (0 : ℝ) ≤ M - 1)
    linarith [show w * k * (M - 1) = M * w * k - w * k by ring]
  linarith

theorem ar_roff {VT M w k N : ℝ} (h1M : 1 ≤ M) (hMN : M ≤ N) (hMk : M * k ≤ w) (hk : 0 ≤ k)
    (hw0 : 0 ≤ w) (hVT : VT ≤ 20 * M * w * k) :
    M * (2 * N ^ 2 * VT) ≤ 40 * (N ^ 3 * w ^ 2) := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hN2 : (0 : ℝ) ≤ 2 * N ^ 2 := mul_nonneg (by norm_num) (_root_.sq_nonneg N)
  have h1 : M * (2 * N ^ 2 * VT) ≤ M * (2 * N ^ 2 * (20 * M * w * k)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVT hN2) hM0
  have h2 : N ^ 2 * (M * (w * (M * k))) ≤ N ^ 2 * (N * (w * w)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hMN (mul_le_mul_of_nonneg_left hMk hw0)
        (mul_nonneg hw0 (mul_nonneg hM0 hk)) hN0)
      (_root_.sq_nonneg N)
  have e : M * (2 * N ^ 2 * (20 * M * w * k)) = 40 * (N ^ 2 * (M * (w * (M * k)))) := by ring
  have e' : 40 * (N ^ 2 * (N * (w * w))) = 40 * (N ^ 3 * w ^ 2) := by ring
  linarith

theorem ar_const {t M w N : ℝ} (hM0 : 0 ≤ M) (hMN : M ≤ N) (ht : |t| ≤ 6 * M * w) :
    M * (-t) ^ 2 ≤ 36 * (N ^ 3 * w ^ 2) := by
  have h1 : t ^ 2 ≤ (6 * M * w) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg t) ht 2
    rwa [sq_abs] at this
  have h3 : M ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ hM0 hMN 3
  have h4 : M * (-t) ^ 2 ≤ M * (6 * M * w) ^ 2 := by
    rw [neg_sq]; exact mul_le_mul_of_nonneg_left h1 hM0
  have h5 : M ^ 3 * w ^ 2 ≤ N ^ 3 * w ^ 2 := mul_le_mul_of_nonneg_right h3 (_root_.sq_nonneg w)
  have e : M * (6 * M * w) ^ 2 = 36 * (M ^ 3 * w ^ 2) := by ring
  linarith

theorem ar_E4 {L Vψ c0 M w k N P : ℝ} (h1M : 1 ≤ M) (hMN : M ≤ N) (hMk : M * k ≤ w)
    (hw0 : 0 ≤ w) (hL0 : 0 ≤ L) (hL : L ≤ 2 * k) (hV0 : 0 ≤ Vψ) (hV : Vψ ≤ w * k)
    (hc : c0 ^ 2 ≤ M ^ 2)
    (hP : P ≤ 3 * ((N ^ 3 * (L ^ 2 * M) + 2 * N ^ 2 * (Vψ * M)) + c0 ^ 2 * (2 * N * Vψ)
      + M ^ 2 * (N ^ 2 * L ^ 2 + N * Vψ))) : M * P ≤ 39 * (N ^ 3 * w ^ 2) := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = M * L := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = M * Vψ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hM0 hL0
  have hr1 : r ≤ 2 * w := by
    rw [hr]
    have := mul_le_mul_of_nonneg_left hL hM0
    linarith [show M * (2 * k) = 2 * (M * k) by ring]
  have hr2 : r ^ 2 ≤ 4 * w ^ 2 := by
    have := pow_le_pow_left₀ hr0 hr1 2
    linarith [show (2 * w) ^ 2 = 4 * w ^ 2 by ring]
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg hM0 hV0
  have ht1 : t ≤ w ^ 2 := by
    rw [ht]
    have h1 := mul_le_mul_of_nonneg_left hV hM0
    have h2 := mul_le_mul_of_nonneg_left hMk hw0
    linarith [show M * (w * k) = w * (M * k) by ring, show w * w = w ^ 2 by ring]
  have hM2 : M ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hM0 hMN 2
  have hc2 : c0 ^ 2 ≤ N ^ 2 := hc.trans hM2
  have c1 : M * t ≤ N * w ^ 2 := mul_le_mul hMN ht1 ht0 hN0
  have c2 : c0 ^ 2 * t ≤ N ^ 2 * w ^ 2 := mul_le_mul hc2 ht1 ht0 (_root_.sq_nonneg N)
  have c3 : M ^ 2 * t ≤ N ^ 2 * w ^ 2 := mul_le_mul hM2 ht1 ht0 (_root_.sq_nonneg N)
  have c4 : M * r ^ 2 ≤ N * (4 * w ^ 2) := mul_le_mul hMN hr2 (_root_.sq_nonneg r) hN0
  have d1 : N ^ 3 * r ^ 2 ≤ N ^ 3 * (4 * w ^ 2) :=
    mul_le_mul_of_nonneg_left hr2 (pow_nonneg hN0 3)
  have d2 : N ^ 2 * (M * t) ≤ N ^ 2 * (N * w ^ 2) :=
    mul_le_mul_of_nonneg_left c1 (_root_.sq_nonneg N)
  have d3 : N * (c0 ^ 2 * t) ≤ N * (N ^ 2 * w ^ 2) := mul_le_mul_of_nonneg_left c2 hN0
  have d4 : N ^ 2 * (M * r ^ 2) ≤ N ^ 2 * (N * (4 * w ^ 2)) :=
    mul_le_mul_of_nonneg_left c4 (_root_.sq_nonneg N)
  have d5 : N * (M ^ 2 * t) ≤ N * (N ^ 2 * w ^ 2) := mul_le_mul_of_nonneg_left c3 hN0
  have h5 : M * P ≤ M * (3 * ((N ^ 3 * (L ^ 2 * M) + 2 * N ^ 2 * (Vψ * M))
      + c0 ^ 2 * (2 * N * Vψ) + M ^ 2 * (N ^ 2 * L ^ 2 + N * Vψ))) :=
    mul_le_mul_of_nonneg_left hP hM0
  have e : M * (3 * ((N ^ 3 * (L ^ 2 * M) + 2 * N ^ 2 * (Vψ * M)) + c0 ^ 2 * (2 * N * Vψ)
      + M ^ 2 * (N ^ 2 * L ^ 2 + N * Vψ)))
      = 3 * (N ^ 3 * r ^ 2 + 2 * (N ^ 2 * (M * t)) + 2 * (N * (c0 ^ 2 * t))
        + N ^ 2 * (M * r ^ 2) + N * (M ^ 2 * t)) := by rw [hr, ht]; ring
  have e' : 3 * (N ^ 3 * (4 * w ^ 2) + 2 * (N ^ 2 * (N * w ^ 2)) + 2 * (N * (N ^ 2 * w ^ 2))
      + N ^ 2 * (N * (4 * w ^ 2)) + N * (N ^ 2 * w ^ 2)) = 39 * (N ^ 3 * w ^ 2) := by ring
  linarith

theorem comb2 {M a b c1 c2 T : ℝ} (m1 : M * a ≤ c1 * T) (m2 : M * b ≤ c2 * T) :
    M * (2 * a + 2 * b) ≤ (2 * (c1 + c2)) * T := by
  have e : M * (2 * a + 2 * b) = 2 * (M * a) + 2 * (M * b) := by ring
  have e' : (2 * (c1 + c2)) * T = 2 * (c1 * T) + 2 * (c2 * T) := by ring
  linarith

theorem comb3 {M a b c c1 c2 c3 T : ℝ} (m1 : M * a ≤ c1 * T) (m2 : M * b ≤ c2 * T)
    (m3 : M * c ≤ c3 * T) : M * (3 * (a + b + c)) ≤ (3 * (c1 + c2 + c3)) * T := by
  have e : M * (3 * (a + b + c)) = 3 * (M * a) + 3 * (M * b) + 3 * (M * c) := by ring
  have e' : (3 * (c1 + c2 + c3)) * T = 3 * (c1 * T) + 3 * (c2 * T) + 3 * (c3 * T) := by ring
  linarith

theorem comb4 {M P1 P2 P3 P4 c1 c2 c3 c4 I T : ℝ} (hM : 0 ≤ M)
    (hI : I ≤ 4 * (P1 + P2 + P3 + P4)) (m1 : M * P1 ≤ c1 * T) (m2 : M * P2 ≤ c2 * T)
    (m3 : M * P3 ≤ c3 * T) (m4 : M * P4 ≤ c4 * T) :
    M * I ≤ (4 * (c1 + c2 + c3 + c4)) * T := by
  have h := mul_le_mul_of_nonneg_left hI hM
  have e : M * (4 * (P1 + P2 + P3 + P4))
      = 4 * (M * P1) + 4 * (M * P2) + 4 * (M * P3) + 4 * (M * P4) := by ring
  have e' : (4 * (c1 + c2 + c3 + c4)) * T
      = 4 * (c1 * T) + 4 * (c2 * T) + 4 * (c3 * T) + 4 * (c4 * T) := by ring
  linarith

/-- The Cauchy–Schwarz product: from `M I ≤ 1844 N³ w²` to `I (6 N M) ≤ (106 N² w)²`. -/
theorem ar_cs {I M N w : ℝ} (hN0 : 0 ≤ N)
    (h : M * I ≤ (4 * (2 * (40 + 36) + 3 * (6 + 6 + 6) + 3 * (24 + 24 + 24) + 39))
      * (N ^ 3 * w ^ 2)) : I * (6 * N * M) ≤ (106 * N ^ 2 * w) ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_left h (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hN0)
  have h2 : 0 ≤ N ^ 4 * w ^ 2 := mul_nonneg (pow_nonneg hN0 4) (_root_.sq_nonneg w)
  have e1 : 6 * N * (M * I) = I * (6 * N * M) := by ring
  have e2 : 6 * N * ((4 * (2 * (40 + 36) + 3 * (6 + 6 + 6) + 3 * (24 + 24 + 24) + 39))
      * (N ^ 3 * w ^ 2)) = 11064 * (N ^ 4 * w ^ 2) := by ring
  have e3 : (106 * N ^ 2 * w) ^ 2 = 11236 * (N ^ 4 * w ^ 2) := by ring
  linarith

theorem ar_Z1 {N M w k K φ0 Z : ℝ} (hN : 1 ≤ N) (h1M : 1 ≤ M) (hMN : M ≤ N)
    (hMk : M * k ≤ w) (hK0 : 0 ≤ K) (hK : K ≤ k) (hφ0 : 0 ≤ φ0) (hφ : φ0 ≤ w)
    (hZ : Z ≤ 1 / N ^ 4 * (N * (106 * N ^ 2 * w + (K * N + φ0) * (6 * N * M)))) :
    Z ≤ 118 * (w / N) := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hw0 : 0 ≤ w := hφ0.trans hφ
  have hKM : K * M ≤ w :=
    calc K * M ≤ k * M := mul_le_mul_of_nonneg_right hK hM0
      _ = M * k := mul_comm _ _
      _ ≤ w := hMk
  have g1 : N ^ 3 * (K * M) ≤ N ^ 3 * w := mul_le_mul_of_nonneg_left hKM (pow_nonneg hN0.le 3)
  have hφM : φ0 * M ≤ w * N := mul_le_mul hφ hMN hM0 hw0
  have g2 : N ^ 2 * (φ0 * M) ≤ N ^ 2 * (w * N) :=
    mul_le_mul_of_nonneg_left hφM (_root_.sq_nonneg N)
  have hin : N * (106 * N ^ 2 * w + (K * N + φ0) * (6 * N * M)) ≤ 118 * N ^ 3 * w := by
    have e : N * (106 * N ^ 2 * w + (K * N + φ0) * (6 * N * M))
        = 106 * (N ^ 3 * w) + 6 * (N ^ 3 * (K * M)) + 6 * (N ^ 2 * (φ0 * M)) := by ring
    have e' : N ^ 2 * (w * N) = N ^ 3 * w := by ring
    rw [e]; linarith
  have h1 := mul_le_mul_of_nonneg_left hin (by positivity : (0 : ℝ) ≤ 1 / N ^ 4)
  have e : 1 / N ^ 4 * (118 * N ^ 3 * w) = 118 * (w / N) := by
    have hN' : N ≠ 0 := hN0.ne'
    first | (field_simp; ring) | field_simp
  linarith

theorem ar_Z0 {N w Z S : ℝ} (hN : 0 < N) (hS : S ≤ 53 * N ^ 2 * w) (hZ : Z ≤ 1 / N ^ 3 * S) :
    Z ≤ 53 * (w / N) := by
  have h1 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 1 / N ^ 3)
  have e : 1 / N ^ 3 * (53 * N ^ 2 * w) = 53 * (w / N) := by
    have hN' : N ≠ 0 := hN.ne'
    first | (field_simp; ring) | field_simp
  linarith

theorem z_roff {VT M w k N : ℝ} (hMk : M * k ≤ w) (hw0 : 0 ≤ w) (hN0 : 0 ≤ N)
    (hVT : VT ≤ 20 * M * w * k) : N * Real.sqrt (2 * N ^ 2 * VT) ≤ 7 * N ^ 2 * w := by
  have h1 : 2 * N ^ 2 * VT ≤ (7 * N * w) ^ 2 := by
    have a : N ^ 2 * VT ≤ N ^ 2 * (20 * M * w * k) :=
      mul_le_mul_of_nonneg_left hVT (_root_.sq_nonneg N)
    have b : N ^ 2 * (w * (M * k)) ≤ N ^ 2 * (w * w) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMk hw0) (_root_.sq_nonneg N)
    have c : 0 ≤ N ^ 2 * (w * w) := mul_nonneg (_root_.sq_nonneg N) (mul_nonneg hw0 hw0)
    have e1 : N ^ 2 * (20 * M * w * k) = 20 * (N ^ 2 * (w * (M * k))) := by ring
    have e2 : (7 * N * w) ^ 2 = 49 * (N ^ 2 * (w * w)) := by ring
    linarith
  have h2 := sqrt_le_of_sq (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) hN0) hw0) h1
  calc N * Real.sqrt (2 * N ^ 2 * VT) ≤ N * (7 * N * w) := mul_le_mul_of_nonneg_left h2 hN0
    _ = 7 * N ^ 2 * w := by ring

theorem z_const {t M w N : ℝ} (hM0 : 0 ≤ M) (hMN : M ≤ N) (hw0 : 0 ≤ w)
    (ht : |t| ≤ 6 * M * w) : |N * -t| ≤ 6 * N ^ 2 * w := by
  have hN0 : 0 ≤ N := hM0.trans hMN
  rw [abs_mul, abs_neg, abs_of_nonneg hN0]
  have a := mul_le_mul_of_nonneg_left ht hN0
  have b : N * (M * w) ≤ N * (N * w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMN hw0) hN0
  linarith [show N * (6 * M * w) = 6 * (N * (M * w)) by ring,
    show 6 * (N * (N * w)) = 6 * N ^ 2 * w by ring]

theorem z_clsI {c ψ0 V M w N : ℝ} (h1M : 1 ≤ M) (hMN : M ≤ N) (hw0 : 0 ≤ w) (hV0 : 0 ≤ V)
    (hcB : |c * ψ0| ≤ M * w) (hcV : c ^ 2 * V ≤ M * w ^ 2) :
    |c| * (N * Real.sqrt (2 * V) + N * |ψ0|) ≤ 3 * N ^ 2 * w := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hx0 : 0 ≤ |c| * Real.sqrt (2 * V) := mul_nonneg (abs_nonneg c) (Real.sqrt_nonneg _)
  have hy0 : 0 ≤ 2 * M * w := mul_nonneg (mul_nonneg (by norm_num) hM0) hw0
  have hsq : (|c| * Real.sqrt (2 * V)) ^ 2 ≤ (2 * M * w) ^ 2 := by
    have e1 : (|c| * Real.sqrt (2 * V)) ^ 2 = 2 * (c ^ 2 * V) := by
      rw [mul_pow, sq_abs, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * V)]; ring
    have hMM : M ≤ M ^ 2 := by
      have := mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ M - 1)
      linarith [show M * (M - 1) = M ^ 2 - M by ring]
    have a : M * w ^ 2 ≤ M ^ 2 * w ^ 2 := mul_le_mul_of_nonneg_right hMM (_root_.sq_nonneg w)
    have b : 0 ≤ M ^ 2 * w ^ 2 := mul_nonneg (_root_.sq_nonneg M) (_root_.sq_nonneg w)
    rw [e1]
    linarith [show (2 * M * w) ^ 2 = 4 * (M ^ 2 * w ^ 2) by ring]
  have hx : |c| * Real.sqrt (2 * V) ≤ 2 * M * w := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hx0, Real.sqrt_sq hy0] at this
  have e : |c| * (N * Real.sqrt (2 * V) + N * |ψ0|)
      = N * (|c| * Real.sqrt (2 * V)) + N * |c * ψ0| := by rw [abs_mul]; ring
  have a1 := mul_le_mul_of_nonneg_left hx hN0
  have a2 := mul_le_mul_of_nonneg_left hcB hN0
  have a3 : N * (M * w) ≤ N * (N * w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMN hw0) hN0
  rw [e]
  linarith [show N * (2 * M * w) = 2 * (N * (M * w)) by ring,
    show 3 * (N * (N * w)) = 3 * N ^ 2 * w by ring]

theorem z_clsII {κ ψ0 V M w k N : ℝ} (h1M : 1 ≤ M) (hMk : M * k ≤ w) (hk : 0 ≤ k)
    (hN0 : 0 ≤ N) (hκ : |κ| ≤ 2 * N) (hψ : |ψ0| ≤ w) (hV : V ≤ w * k) :
    |κ| * (N * Real.sqrt (2 * V) + N * |ψ0|) ≤ 6 * N ^ 2 * w := by
  have hw0 : 0 ≤ w := (abs_nonneg ψ0).trans hψ
  have hkM : k ≤ M * k := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ M - 1) hk
    linarith [show (M - 1) * k = M * k - k by ring]
  have hkw : k ≤ w := hkM.trans hMk
  have hs : Real.sqrt (2 * V) ≤ 2 * w := by
    refine sqrt_le_of_sq (by linarith) ?_
    have a := mul_le_mul_of_nonneg_left hkw hw0
    have b : 0 ≤ w * w := mul_nonneg hw0 hw0
    linarith [show (2 * w) ^ 2 = 4 * (w * w) by ring]
  have hin : N * Real.sqrt (2 * V) + N * |ψ0| ≤ 3 * N * w := by
    have a1 := mul_le_mul_of_nonneg_left hs hN0
    have a2 := mul_le_mul_of_nonneg_left hψ hN0
    linarith
  have hin0 : 0 ≤ N * Real.sqrt (2 * V) + N * |ψ0| :=
    add_nonneg (mul_nonneg hN0 (Real.sqrt_nonneg _)) (mul_nonneg hN0 (abs_nonneg _))
  calc |κ| * (N * Real.sqrt (2 * V) + N * |ψ0|) ≤ (2 * N) * (3 * N * w) :=
        mul_le_mul hκ hin hin0 (by linarith)
    _ = 6 * N ^ 2 * w := by ring

theorem z_hc {K c0 M w k N : ℝ} (h1M : 1 ≤ M) (hMk : M * k ≤ w) (hK0 : 0 ≤ K) (hK : K ≤ k)
    (hN0 : 0 ≤ N) (hc : |c0| ≤ M) :
    |-(K * N)| * (N * Real.sqrt (2 * M) + N * |c0|) ≤ 3 * N ^ 2 * w := by
  have hM0 : 0 ≤ M := by linarith
  rw [abs_neg, abs_of_nonneg (mul_nonneg hK0 hN0)]
  have hs : Real.sqrt (2 * M) ≤ 2 * M := by
    refine sqrt_le_of_sq (by linarith) ?_
    have := mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ M - 1)
    linarith [show (2 * M) ^ 2 = 4 * (M * (M - 1)) + 4 * M by ring]
  have hin : N * Real.sqrt (2 * M) + N * |c0| ≤ 3 * N * M := by
    have a1 := mul_le_mul_of_nonneg_left hs hN0
    have a2 := mul_le_mul_of_nonneg_left hc hN0
    linarith
  have hKM : K * M ≤ w :=
    calc K * M ≤ k * M := mul_le_mul_of_nonneg_right hK hM0
      _ = M * k := mul_comm _ _
      _ ≤ w := hMk
  have hN2 : (0 : ℝ) ≤ 3 * N ^ 2 := mul_nonneg (by norm_num) (_root_.sq_nonneg N)
  calc K * N * (N * Real.sqrt (2 * M) + N * |c0|) ≤ K * N * (3 * N * M) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hK0 hN0)
    _ = 3 * N ^ 2 * (K * M) := by ring
    _ ≤ 3 * N ^ 2 * w := mul_le_mul_of_nonneg_left hKM hN2

theorem z_trip {Vψ ψ0 c0 L M w k N : ℝ} (h1M : 1 ≤ M) (hMN : M ≤ N) (hMk : M * k ≤ w)
    (hk : 0 ≤ k) (hψ : |ψ0| ≤ w) (hc : |c0| ≤ M) (hV0 : 0 ≤ Vψ) (hV : Vψ ≤ w * k)
    (hL : L ≤ 2 * k) :
    N ^ 2 * Real.sqrt (6 * (Vψ * M)) + |ψ0| * (N * Real.sqrt (2 * M) + N * |c0|)
        + |c0| * (N * Real.sqrt (2 * Vψ)) + N ^ 2 * (M * L) ≤ 10 * N ^ 2 * w := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hw0 : 0 ≤ w := (abs_nonneg ψ0).trans hψ
  have hkM : k ≤ M * k := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ M - 1) hk
    linarith [show (M - 1) * k = M * k - k by ring]
  have hkw : k ≤ w := hkM.trans hMk
  have hww : 0 ≤ w * w := mul_nonneg hw0 hw0
  have s1 : Real.sqrt (6 * (Vψ * M)) ≤ 3 * w := by
    refine sqrt_le_of_sq (by linarith) ?_
    have a := mul_le_mul_of_nonneg_right hV hM0
    have b := mul_le_mul_of_nonneg_left hMk hw0
    linarith [show w * k * M = w * (M * k) by ring, show (3 * w) ^ 2 = 9 * (w * w) by ring]
  have s2 : Real.sqrt (2 * M) ≤ 2 * M := by
    refine sqrt_le_of_sq (by linarith) ?_
    have := mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ M - 1)
    linarith [show (2 * M) ^ 2 = 4 * (M * (M - 1)) + 4 * M by ring]
  have s3 : Real.sqrt (2 * Vψ) ≤ 2 * w := by
    refine sqrt_le_of_sq (by linarith) ?_
    have a := mul_le_mul_of_nonneg_left hkw hw0
    linarith [show (2 * w) ^ 2 = 4 * (w * w) by ring]
  have hNMw : N * (M * w) ≤ N * (N * w) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMN hw0) hN0
  have t1 : N ^ 2 * Real.sqrt (6 * (Vψ * M)) ≤ N ^ 2 * (3 * w) :=
    mul_le_mul_of_nonneg_left s1 (_root_.sq_nonneg N)
  have hin : N * Real.sqrt (2 * M) + N * |c0| ≤ 3 * N * M := by
    have a1 := mul_le_mul_of_nonneg_left s2 hN0
    have a2 := mul_le_mul_of_nonneg_left hc hN0
    linarith
  have hin0 : 0 ≤ N * Real.sqrt (2 * M) + N * |c0| :=
    add_nonneg (mul_nonneg hN0 (Real.sqrt_nonneg _)) (mul_nonneg hN0 (abs_nonneg _))
  have t2 : |ψ0| * (N * Real.sqrt (2 * M) + N * |c0|) ≤ w * (3 * N * M) :=
    mul_le_mul hψ hin hin0 hw0
  have t3 : |c0| * (N * Real.sqrt (2 * Vψ)) ≤ M * (N * (2 * w)) :=
    mul_le_mul hc (mul_le_mul_of_nonneg_left s3 hN0)
      (mul_nonneg hN0 (Real.sqrt_nonneg _)) hM0
  have t4 : N ^ 2 * (M * L) ≤ N ^ 2 * (2 * w) := by
    refine mul_le_mul_of_nonneg_left ?_ (_root_.sq_nonneg N)
    have := mul_le_mul_of_nonneg_left hL hM0
    linarith [show M * (2 * k) = 2 * (M * k) by ring]
  linarith [show w * (3 * N * M) = 3 * (N * (M * w)) by ring,
    show M * (N * (2 * w)) = 2 * (N * (M * w)) by ring,
    show N * (N * w) = N ^ 2 * w by ring]

/-! ### the two statistics of a middle summand on the torus -/

/-- `w = (√2)^d M m_{l+m}`: the unit of all bounds for the middle summand `(l, m)`. -/
noncomputable def wN (d : ℕ) (σ : ℝ) (l m : ℕ) : ℝ :=
  Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ (l + m)

theorem tM0 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {a : ℕ} (ha : 1 ≤ a) : 0 ≤ torusM d σ a := by
  linarith [torusM_ge_one hσ d ha]

theorem wN_Mk {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) :
    torusM d σ 1 * torusM d σ (l + m) ≤ wN d σ l m := by
  have h := mul_nonneg (by linarith [sqrt2_pow_ge_one d] : (0 : ℝ) ≤ Real.sqrt 2 ^ d - 1)
    (mul_nonneg (tM0 hσ d (le_refl 1)) (tM0 hσ d (by omega : 1 ≤ l + m)))
  unfold wN
  linarith [show (Real.sqrt 2 ^ d - 1) * (torusM d σ 1 * torusM d σ (l + m))
    = Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ (l + m)
      - torusM d σ 1 * torusM d σ (l + m) by ring]

theorem wN_ab {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    torusM d σ l * torusM d σ m ≤ wN d σ l m := m_prod hσ d hl hm

theorem wN_nonneg {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) : 0 ≤ wN d σ l m :=
  (mul_nonneg (tM0 hσ d (le_refl 1)) (tM0 hσ d (by omega : 1 ≤ l + m))).trans (wN_Mk hσ d hl)

theorem prod_le_w {x y a b w : ℝ} (hx : x ≤ a) (hy : y ≤ b) (hy0 : 0 ≤ y) (ha0 : 0 ≤ a)
    (hab : a * b ≤ w) : x * y ≤ w := (mul_le_mul hx hy hy0 ha0).trans hab

/-- class I, first piece: coefficient `m_l`, kernel `φ_{1,m}`. -/
theorem clsI_1 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    |torusM d σ l * phiN d σ 1 m 0| ≤ torusM d σ 1 * wN d σ l m
      ∧ torusM d σ l ^ 2 * (torusM d σ 1 * torusM d σ m * torusM d σ (1 + m))
          ≤ torusM d σ 1 * wN d σ l m ^ 2 := by
  have hl0 := tM0 hσ d hl
  have hm0 := tM0 hσ d hm
  have h10 := tM0 hσ d (le_refl 1)
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hab := wN_ab hσ d hl hm
  have hm1 : torusM d σ (1 + m) ≤ torusM d σ m := torusM_anti hσ d hm (by omega)
  have hm10 := tM0 hσ d (by omega : 1 ≤ 1 + m)
  constructor
  · rw [abs_mul, abs_of_nonneg hl0]
    calc torusM d σ l * |phiN d σ 1 m 0| ≤ torusM d σ l * (torusM d σ 1 * torusM d σ m) :=
          mul_le_mul_of_nonneg_left (phiN_bound hσ d (le_refl 1) hm 0) hl0
      _ = torusM d σ 1 * (torusM d σ l * torusM d σ m) := by ring
      _ ≤ torusM d σ 1 * wN d σ l m := mul_le_mul_of_nonneg_left hab h10
  · have h2 : torusM d σ l * torusM d σ (1 + m) ≤ wN d σ l m :=
      prod_le_w le_rfl hm1 hm10 hl0 hab
    calc torusM d σ l ^ 2 * (torusM d σ 1 * torusM d σ m * torusM d σ (1 + m))
        = torusM d σ 1 * ((torusM d σ l * torusM d σ m)
            * (torusM d σ l * torusM d σ (1 + m))) := by ring
      _ ≤ torusM d σ 1 * (wN d σ l m * wN d σ l m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hab h2 (mul_nonneg hl0 hm10) hw0) h10
      _ = torusM d σ 1 * wN d σ l m ^ 2 := by ring

/-- class I, second piece: coefficient `m_m`, kernel `φ_{l,1}`. -/
theorem clsI_2 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    |torusM d σ m * phiN d σ l 1 0| ≤ torusM d σ 1 * wN d σ l m
      ∧ torusM d σ m ^ 2 * (torusM d σ l * torusM d σ 1 * torusM d σ (l + 1))
          ≤ torusM d σ 1 * wN d σ l m ^ 2 := by
  have hl0 := tM0 hσ d hl
  have hm0 := tM0 hσ d hm
  have h10 := tM0 hσ d (le_refl 1)
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hab := wN_ab hσ d hl hm
  have hl1 : torusM d σ (l + 1) ≤ torusM d σ l := torusM_anti hσ d hl (by omega)
  have hl10 := tM0 hσ d (by omega : 1 ≤ l + 1)
  constructor
  · rw [abs_mul, abs_of_nonneg hm0]
    calc torusM d σ m * |phiN d σ l 1 0| ≤ torusM d σ m * (torusM d σ l * torusM d σ 1) :=
          mul_le_mul_of_nonneg_left (phiN_bound hσ d hl (le_refl 1) 0) hm0
      _ = torusM d σ 1 * (torusM d σ l * torusM d σ m) := by ring
      _ ≤ torusM d σ 1 * wN d σ l m := mul_le_mul_of_nonneg_left hab h10
  · have h2 : torusM d σ (l + 1) * torusM d σ m ≤ wN d σ l m :=
      prod_le_w hl1 le_rfl hm0 hl0 hab
    calc torusM d σ m ^ 2 * (torusM d σ l * torusM d σ 1 * torusM d σ (l + 1))
        = torusM d σ 1 * ((torusM d σ l * torusM d σ m)
            * (torusM d σ (l + 1) * torusM d σ m)) := by ring
      _ ≤ torusM d σ 1 * (wN d σ l m * wN d σ l m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hab h2 (mul_nonneg hl10 hm0) hw0) h10
      _ = torusM d σ 1 * wN d σ l m ^ 2 := by ring

/-- class I, third piece: coefficient `M`, kernel `φ_{l,m}`. -/
theorem clsI_3 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    |torusM d σ 1 * phiN d σ l m 0| ≤ torusM d σ 1 * wN d σ l m
      ∧ torusM d σ 1 ^ 2 * (torusM d σ l * torusM d σ m * torusM d σ (l + m))
          ≤ torusM d σ 1 * wN d σ l m ^ 2 := by
  have hl0 := tM0 hσ d hl
  have hm0 := tM0 hσ d hm
  have h10 := tM0 hσ d (le_refl 1)
  have hk0 := tM0 hσ d (by omega : 1 ≤ l + m)
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hab := wN_ab hσ d hl hm
  have hMk := wN_Mk (m := m) hσ d hl
  constructor
  · rw [abs_mul, abs_of_nonneg h10]
    exact mul_le_mul_of_nonneg_left ((phiN_bound hσ d hl hm 0).trans hab) h10
  · calc torusM d σ 1 ^ 2 * (torusM d σ l * torusM d σ m * torusM d σ (l + m))
        = torusM d σ 1 * ((torusM d σ l * torusM d σ m)
            * (torusM d σ 1 * torusM d σ (l + m))) := by ring
      _ ≤ torusM d σ 1 * (wN d σ l m * wN d σ l m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hab hMk (mul_nonneg h10 hk0) hw0) h10
      _ = torusM d σ 1 * wN d σ l m ^ 2 := by ring

/-- class II: the kernels `φ_{l,m+1}`, `φ_{l+1,m}`, `φ_{1,l+m}`. -/
theorem clsII_1 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    |phiN d σ l (m + 1) 0| ≤ wN d σ l m
      ∧ torusM d σ l * torusM d σ (m + 1) * torusM d σ (l + (m + 1))
          ≤ wN d σ l m * torusM d σ (l + m) := by
  have hl0 := tM0 hσ d hl
  have hm10 := tM0 hσ d (by omega : 1 ≤ m + 1)
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hab := wN_ab hσ d hl hm
  have hm1 : torusM d σ (m + 1) ≤ torusM d σ m := torusM_anti hσ d hm (by omega)
  have h2 : torusM d σ l * torusM d σ (m + 1) ≤ wN d σ l m := prod_le_w le_rfl hm1 hm10 hl0 hab
  have hK : torusM d σ (l + (m + 1)) ≤ torusM d σ (l + m) :=
    torusM_anti hσ d (by omega) (by omega)
  exact ⟨(phiN_bound hσ d hl (by omega) 0).trans h2,
    mul_le_mul h2 hK (tM0 hσ d (by omega)) hw0⟩

theorem clsII_2 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    |phiN d σ (l + 1) m 0| ≤ wN d σ l m
      ∧ torusM d σ (l + 1) * torusM d σ m * torusM d σ (l + 1 + m)
          ≤ wN d σ l m * torusM d σ (l + m) := by
  have hl0 := tM0 hσ d hl
  have hm0 := tM0 hσ d hm
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hab := wN_ab hσ d hl hm
  have hl1 : torusM d σ (l + 1) ≤ torusM d σ l := torusM_anti hσ d hl (by omega)
  have h2 : torusM d σ (l + 1) * torusM d σ m ≤ wN d σ l m := prod_le_w hl1 le_rfl hm0 hl0 hab
  have hK : torusM d σ (l + 1 + m) ≤ torusM d σ (l + m) :=
    torusM_anti hσ d (by omega) (by omega)
  exact ⟨(phiN_bound hσ d (by omega) hm 0).trans h2,
    mul_le_mul h2 hK (tM0 hσ d (by omega)) hw0⟩

theorem clsII_3 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) :
    |phiN d σ 1 (l + m) 0| ≤ wN d σ l m
      ∧ torusM d σ 1 * torusM d σ (l + m) * torusM d σ (1 + (l + m))
          ≤ wN d σ l m * torusM d σ (l + m) := by
  have hw0 := wN_nonneg (m := m) hσ d hl
  have h2 := wN_Mk (m := m) hσ d hl
  have hK : torusM d σ (1 + (l + m)) ≤ torusM d σ (l + m) :=
    torusM_anti hσ d (by omega) (by omega)
  exact ⟨(phiN_bound hσ d (le_refl 1) (by omega) 0).trans h2,
    mul_le_mul h2 hK (tM0 hσ d (by omega)) hw0⟩

/-- The constant from the diagonals: `|t₂| ≤ 6 M w`. -/
theorem t2N_bound {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    |t2N d σ l m| ≤ 6 * torusM d σ 1 * wN d σ l m := by
  have hM1 := torusM_one_ge hσ d
  have hw0 := wN_nonneg (m := m) hσ d hl
  have a1 := abs_le.mp (clsI_2 hσ d hl hm).1
  have a2 := abs_le.mp (clsI_3 hσ d hl hm).1
  have b1 := abs_le.mp (clsII_1 hσ d hl hm).1
  have b2 := abs_le.mp (clsII_2 hσ d hl hm).1
  have b3 := abs_le.mp (clsII_3 (m := m) hσ d hl).1
  have hwM : wN d σ l m ≤ torusM d σ 1 * wN d σ l m := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ torusM d σ 1 - 1) hw0
    linarith [show (torusM d σ 1 - 1) * wN d σ l m
      = torusM d σ 1 * wN d σ l m - wN d σ l m by ring]
  unfold t2N gD2 gD3
  exact abs_le.mpr ⟨by linarith [a1.1, a2.1, b1.2, b2.2, b3.2], by
    linarith [a1.2, a2.2, b1.1, b2.1, b3.1]⟩

/-- `‖T‖₂² ≤ 20 M w m_{l+m}`. -/
theorem TdegV_le {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    TdegV d σ l m ≤ 20 * torusM d σ 1 * wN d σ l m * torusM d σ (l + m) :=
  ar_VT (torusM_one_ge hσ d) (wN_Mk hσ d hl) (tM0 hσ d (by omega))
    (mul_nonneg (tM0 hσ d hl) (tM0 hσ d hm)) (wN_ab hσ d hl hm)
    (tM0 hσ d (by omega : 1 ≤ l + (1 + m)))
    (torusM_anti hσ d (by omega : 1 ≤ l + m) (by omega : l + m ≤ l + (1 + m)))
    (tM0 hσ d (by omega : 1 ≤ l + m + 1))
    (torusM_anti hσ d (by omega : 1 ≤ l + m) (by omega : l + m ≤ l + m + 1))
    (clsII_1 hσ d hl hm).2 (clsII_2 hσ d hl hm).2 (clsII_3 hσ d hl).2

/-- The factor of `H_q` in `Z¹[K_m,3]` that is treated by one Cauchy–Schwarz step. -/
noncomputable def Xq {Ω : Type*} {d : ℕ} (σ : ℝ) (l m : ℕ) (X : ℕ → Ω → FlatTorus d) (N q : ℕ)
    (ω : Ω) : ℝ :=
  (Roff (Tdeg d σ l m) X N q ω + -t2N d σ l m)
    + (torusM d σ l * Hrow (phiN d σ 1 m) X N q ω
        + torusM d σ m * Hrow (phiN d σ l 1) X N q ω
        + torusM d σ 1 * Hrow (phiN d σ l m) X N q ω)
    + ((-2) * Hrow (phiN d σ l (m + 1)) X N q ω
        + ((N : ℝ) - 2) * Hrow (phiN d σ (l + 1) m) X N q ω
        + ((N : ℝ) - 2) * Hrow (phiN d σ 1 (l + m)) X N q ω)
    + (-1) * (Iq (phiN d σ l (m + 1)) (cK d σ) X N q ω
        + cK d σ 0 * Hoff (phiN d σ l (m + 1)) X N q ω
        + Dq (phiN d σ l (m + 1)) (cK d σ) X N q ω)

theorem Deg3.BM_Aq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*}
    [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G}
    {ψ c : G → ℝ} {Bψ Bc Vψ Vc : ℝ} (H : Deg3 μ ν X ψ c Bψ Bc Vψ Vc) (N q : ℕ) :
    BM (Aq ψ c X N q) := by
  show BM (fun ω => ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N, aP ψ c X i b q ω)
  exact BM.sum (Finset.range N) (fun i ω => ∑ b ∈ Finset.range N, aP ψ c X i b q ω) fun i _ =>
    BM.sum (Finset.range N) (fun b => aP ψ c X i b q) fun b _ => H.BM_aP i b q

theorem abs_int_sum {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (s : Finset ℕ) (F : ℕ → Ω → ℝ) (hF : ∀ i ∈ s, BM (F i)) {A : ℝ}
    (hA : ∀ i ∈ s, ∫ ω, |F i ω| ∂μ ≤ A) : ∫ ω, |∑ i ∈ s, F i ω| ∂μ ≤ s.card * A := by
  have iS : Integrable (fun ω => |∑ i ∈ s, F i ω|) μ := (BM.sum s F hF).absv.integrable
  have iT : Integrable (fun ω => ∑ i ∈ s, |F i ω|) μ :=
    integrable_finset_sum _ fun i hi => (hF i hi).absv.integrable
  calc ∫ ω, |∑ i ∈ s, F i ω| ∂μ ≤ ∫ ω, ∑ i ∈ s, |F i ω| ∂μ :=
        integral_mono iS iT (fun ω => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i ∈ s, ∫ ω, |F i ω| ∂μ :=
        integral_finset_sum _ fun i hi => (hF i hi).absv.integrable
    _ ≤ ∑ _i ∈ s, A := Finset.sum_le_sum hA
    _ = s.card * A := by rw [Finset.sum_const, nsmul_eq_mul]

section SampleMid

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem BM_Km {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) (i b q : ℕ) :
    BM (fun ω => Km d σ l m (X i ω) (X b ω) (X q ω)) :=
  ((BM_heatP X hX hσ hl i b).mul (BM_pker X hX hσ b q)).mul
    ((BM_heatP X hX hσ hm q i).sub (BM_heatP X hX hσ (by omega : 1 ≤ m + 1) i b))

theorem BM_Rq {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) (N q : ℕ) : BM (Rq σ l m X N q) := by
  show BM (fun ω => ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
    Km d σ l m (X i ω) (X b ω) (X q ω))
  exact BM.sum (Finset.range N) (fun i ω => ∑ b ∈ Finset.range N,
      Km d σ l m (X i ω) (X b ω) (X q ω)) fun i _ =>
    BM.sum (Finset.range N) (fun b ω => Km d σ l m (X i ω) (X b ω) (X q ω)) fun b _ =>
      BM_Km X hX hσ hl hm i b q

/-- `R_q = X_q - (m_{l+m+1} N + φ_{l,m+1}(0)) H_q` for `q < N`. -/
theorem Rq_split [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) (N q : ℕ) (hq : q ∈ Finset.range N) (ω : Ω) :
    Rq σ l m X N q ω
      = Xq σ l m X N q ω
        - (torusM d σ (l + m + 1) * (N : ℝ) + phiN d σ l (m + 1) 0)
          * Hrow (cK d σ) X N q ω := by
  have H := phiN_deg3 X h_indep hX hlaw hσ hl (by omega : 1 ≤ m + 1)
  unfold Xq
  rw [Rq_eq σ hl hm X N q hq ω, H.Aq_eq N q hq ω]
  ring

/-- **Second moment of `X_q`**, in the form `M E X_q² ≤ 1844 N³ w²`. -/
theorem Xq_sq [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) (q : ℕ)
    (hq : q ∈ Finset.range N) :
    BM (Xq σ l m X N q) ∧
    torusM d σ 1 * ∫ ω, Xq σ l m X N q ω ^ 2 ∂μ
      ≤ (4 * (2 * (40 + 36) + 3 * (6 + 6 + 6) + 3 * (24 + 24 + 24) + 39))
        * ((N : ℝ) ^ 3 * wN d σ l m ^ 2) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h1M := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hMk := wN_Mk (m := m) hσ d hl
  have hk0 := tM0 hσ d (by omega : 1 ≤ l + m)
  have HT := tdeg_tri3 X h_indep hX hlaw hσ hl hm
  have H1 := phiN_deg2 X h_indep hX hlaw hσ (le_refl 1) hm
  have H2 := phiN_deg2 X h_indep hX hlaw hσ hl (le_refl 1)
  have H3 := phiN_deg2 X h_indep hX hlaw hσ hl hm
  have H4 := phiN_deg2 X h_indep hX hlaw hσ hl (by omega : 1 ≤ m + 1)
  have H5 := phiN_deg2 X h_indep hX hlaw hσ (by omega : 1 ≤ l + 1) hm
  have H6 := phiN_deg2 X h_indep hX hlaw hσ (le_refl 1) (by omega : 1 ≤ l + m)
  have H := phiN_deg3 X h_indep hX hlaw hσ hl (by omega : 1 ≤ m + 1)
  have hL := phiN_l1 hσ d hl (by omega : 1 ≤ m + 1)
  -- the four groups
  have b1 : BM (fun ω => Roff (Tdeg d σ l m) X N q ω + -t2N d σ l m) :=
    (HT.BM_Roff N q).add (BM.const (-t2N d σ l m))
  have b2 : BM (fun ω => torusM d σ l * Hrow (phiN d σ 1 m) X N q ω
      + torusM d σ m * Hrow (phiN d σ l 1) X N q ω
      + torusM d σ 1 * Hrow (phiN d σ l m) X N q ω) :=
    ((BM.const_mul _ (H1.BM_Hrow N q)).add (BM.const_mul _ (H2.BM_Hrow N q))).add
      (BM.const_mul _ (H3.BM_Hrow N q))
  have b3 : BM (fun ω => (-2) * Hrow (phiN d σ l (m + 1)) X N q ω
      + ((N : ℝ) - 2) * Hrow (phiN d σ (l + 1) m) X N q ω
      + ((N : ℝ) - 2) * Hrow (phiN d σ 1 (l + m)) X N q ω) :=
    ((BM.const_mul _ (H4.BM_Hrow N q)).add (BM.const_mul _ (H5.BM_Hrow N q))).add
      (BM.const_mul _ (H6.BM_Hrow N q))
  have b4i : BM (fun ω => Iq (phiN d σ l (m + 1)) (cK d σ) X N q ω
      + cK d σ 0 * Hoff (phiN d σ l (m + 1)) X N q ω
      + Dq (phiN d σ l (m + 1)) (cK d σ) X N q ω) :=
    ((H.BM_Iq N q).add (BM.const_mul _ (H.hψ.BM_Hoff N q))).add (H.BM_Dq N q)
  have b4 : BM (fun ω => (-1) * (Iq (phiN d σ l (m + 1)) (cK d σ) X N q ω
      + cK d σ 0 * Hoff (phiN d σ l (m + 1)) X N q ω
      + Dq (phiN d σ l (m + 1)) (cK d σ) X N q ω)) := BM.const_mul (-1) b4i
  have bX : BM (Xq σ l m X N q) := ((b1.add b2).add b3).add b4
  refine ⟨bX, ?_⟩
  have hc2 : ∫ _ω : Ω, (-t2N d σ l m) ^ 2 ∂μ ≤ (-t2N d σ l m) ^ 2 :=
    le_of_eq (by rw [integral_const, probReal_univ, one_smul])
  have h1 : ∫ ω, (Roff (Tdeg d σ l m) X N q ω + -t2N d σ l m) ^ 2 ∂μ
      ≤ 2 * (2 * (N : ℝ) ^ 2 * TdegV d σ l m) + 2 * (-t2N d σ l m) ^ 2 :=
    sq2_int (HT.BM_Roff N q) (BM.const (-t2N d σ l m)) (HT.Roff_sq N q) hc2
  have h2 : ∫ ω, (torusM d σ l * Hrow (phiN d σ 1 m) X N q ω
        + torusM d σ m * Hrow (phiN d σ l 1) X N q ω
        + torusM d σ 1 * Hrow (phiN d σ l m) X N q ω) ^ 2 ∂μ
      ≤ 3 * (torusM d σ l ^ 2 * (4 * (N : ℝ) * (torusM d σ 1 * torusM d σ m
              * torusM d σ (1 + m)) + 2 * phiN d σ 1 m 0 ^ 2)
          + torusM d σ m ^ 2 * (4 * (N : ℝ) * (torusM d σ l * torusM d σ 1
              * torusM d σ (l + 1)) + 2 * phiN d σ l 1 0 ^ 2)
          + torusM d σ 1 ^ 2 * (4 * (N : ℝ) * (torusM d σ l * torusM d σ m
              * torusM d σ (l + m)) + 2 * phiN d σ l m 0 ^ 2)) :=
    sq3_int (BM.const_mul _ (H1.BM_Hrow N q)) (BM.const_mul _ (H2.BM_Hrow N q))
      (BM.const_mul _ (H3.BM_Hrow N q)) (sq_cmul_int _ (H1.Hrow_sq N q hq))
      (sq_cmul_int _ (H2.Hrow_sq N q hq)) (sq_cmul_int _ (H3.Hrow_sq N q hq))
  have h3 : ∫ ω, ((-2) * Hrow (phiN d σ l (m + 1)) X N q ω
        + ((N : ℝ) - 2) * Hrow (phiN d σ (l + 1) m) X N q ω
        + ((N : ℝ) - 2) * Hrow (phiN d σ 1 (l + m)) X N q ω) ^ 2 ∂μ
      ≤ 3 * ((-2 : ℝ) ^ 2 * (4 * (N : ℝ) * (torusM d σ l * torusM d σ (m + 1)
              * torusM d σ (l + (m + 1))) + 2 * phiN d σ l (m + 1) 0 ^ 2)
          + ((N : ℝ) - 2) ^ 2 * (4 * (N : ℝ) * (torusM d σ (l + 1) * torusM d σ m
              * torusM d σ (l + 1 + m)) + 2 * phiN d σ (l + 1) m 0 ^ 2)
          + ((N : ℝ) - 2) ^ 2 * (4 * (N : ℝ) * (torusM d σ 1 * torusM d σ (l + m)
              * torusM d σ (1 + (l + m))) + 2 * phiN d σ 1 (l + m) 0 ^ 2)) :=
    sq3_int (BM.const_mul _ (H4.BM_Hrow N q)) (BM.const_mul _ (H5.BM_Hrow N q))
      (BM.const_mul _ (H6.BM_Hrow N q)) (sq_cmul_int _ (H4.Hrow_sq N q hq))
      (sq_cmul_int _ (H5.Hrow_sq N q hq)) (sq_cmul_int _ (H6.Hrow_sq N q hq))
  have h4i : ∫ ω, (Iq (phiN d σ l (m + 1)) (cK d σ) X N q ω
        + cK d σ 0 * Hoff (phiN d σ l (m + 1)) X N q ω
        + Dq (phiN d σ l (m + 1)) (cK d σ) X N q ω) ^ 2 ∂μ
      ≤ 3 * (((N : ℝ) ^ 3 * ((2 * torusM d σ (l + (m + 1))) ^ 2 * torusM d σ 1)
            + 2 * (N : ℝ) ^ 2 * (torusM d σ l * torusM d σ (m + 1) * torusM d σ (l + (m + 1))
              * torusM d σ 1))
          + cK d σ 0 ^ 2 * (2 * (N : ℝ) * (torusM d σ l * torusM d σ (m + 1)
              * torusM d σ (l + (m + 1))))
          + torusM d σ 1 ^ 2 * ((N : ℝ) ^ 2 * (2 * torusM d σ (l + (m + 1))) ^ 2
              + (N : ℝ) * (torusM d σ l * torusM d σ (m + 1) * torusM d σ (l + (m + 1))))) :=
    sq3_int (H.BM_Iq N q) (BM.const_mul _ (H.hψ.BM_Hoff N q)) (H.BM_Dq N q) (H.Iq_sq hL N q)
      (sq_cmul_int _ (H.hψ.Hoff_sq N q)) (H.Dq_sq hL N q)
  have h4 : ∫ ω, ((-1) * (Iq (phiN d σ l (m + 1)) (cK d σ) X N q ω
        + cK d σ 0 * Hoff (phiN d σ l (m + 1)) X N q ω
        + Dq (phiN d σ l (m + 1)) (cK d σ) X N q ω)) ^ 2 ∂μ
      ≤ (-1 : ℝ) ^ 2 * (3 * (((N : ℝ) ^ 3 * ((2 * torusM d σ (l + (m + 1))) ^ 2 * torusM d σ 1)
            + 2 * (N : ℝ) ^ 2 * (torusM d σ l * torusM d σ (m + 1) * torusM d σ (l + (m + 1))
              * torusM d σ 1))
          + cK d σ 0 ^ 2 * (2 * (N : ℝ) * (torusM d σ l * torusM d σ (m + 1)
              * torusM d σ (l + (m + 1))))
          + torusM d σ 1 ^ 2 * ((N : ℝ) ^ 2 * (2 * torusM d σ (l + (m + 1))) ^ 2
              + (N : ℝ) * (torusM d σ l * torusM d σ (m + 1)
                * torusM d σ (l + (m + 1)))))) :=
    sq_cmul_int (-1) h4i
  have hXI := sq4_int b1 b2 b3 b4 h1 h2 h3 h4
  -- the numerical bounds
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
  have hκ1 : (-2 : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    linarith [show (-2 : ℝ) ^ 2 = 4 by norm_num]
  have hκ2 : ((N : ℝ) - 2) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    linarith [show ((N : ℝ) - 2) ^ 2 = (N : ℝ) ^ 2 - 4 * (N : ℝ) + 4 by ring]
  have m1 := comb2 (ar_roff h1M hMN hMk hk0 hw0 (TdegV_le hσ d hl hm))
    (ar_const (N := (N : ℝ)) hM0 hMN (t2N_bound hσ d hl hm))
  have m2 := comb3
    (ar_clsI hM0 hMN (clsI_1 hσ d hl hm).1 (clsI_1 hσ d hl hm).2 (le_refl _))
    (ar_clsI hM0 hMN (clsI_2 hσ d hl hm).1 (clsI_2 hσ d hl hm).2 (le_refl _))
    (ar_clsI hM0 hMN (clsI_3 hσ d hl hm).1 (clsI_3 hσ d hl hm).2 (le_refl _))
  have m3 := comb3
    (ar_clsII h1M hMN hMk hκ1 (clsII_1 hσ d hl hm).1 H4.V_nonneg (clsII_1 hσ d hl hm).2
      (le_refl _))
    (ar_clsII h1M hMN hMk hκ2 (clsII_2 hσ d hl hm).1 H5.V_nonneg (clsII_2 hσ d hl hm).2
      (le_refl _))
    (ar_clsII h1M hMN hMk hκ2 (clsII_3 (m := m) hσ d hl).1 H6.V_nonneg
      (clsII_3 (m := m) hσ d hl).2 (le_refl _))
  have hc := (cK_facts hσ d 0).1
  have hcc : cK d σ 0 ^ 2 ≤ torusM d σ 1 ^ 2 := sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2
  have hKK : torusM d σ (l + (m + 1)) ≤ torusM d σ (l + m) :=
    torusM_anti hσ d (by omega) (by omega)
  have hKK0 := tM0 hσ d (by omega : 1 ≤ l + (m + 1))
  have m4 : torusM d σ 1 * ((-1 : ℝ) ^ 2 * (3 * (((N : ℝ) ^ 3
            * ((2 * torusM d σ (l + (m + 1))) ^ 2 * torusM d σ 1)
            + 2 * (N : ℝ) ^ 2 * (torusM d σ l * torusM d σ (m + 1) * torusM d σ (l + (m + 1))
              * torusM d σ 1))
          + cK d σ 0 ^ 2 * (2 * (N : ℝ) * (torusM d σ l * torusM d σ (m + 1)
              * torusM d σ (l + (m + 1))))
          + torusM d σ 1 ^ 2 * ((N : ℝ) ^ 2 * (2 * torusM d σ (l + (m + 1))) ^ 2
              + (N : ℝ) * (torusM d σ l * torusM d σ (m + 1)
                * torusM d σ (l + (m + 1)))))))
      ≤ 39 * ((N : ℝ) ^ 3 * wN d σ l m ^ 2) :=
    ar_E4 (L := 2 * torusM d σ (l + (m + 1))) h1M hMN hMk hw0 (by linarith) (by linarith)
      H4.V_nonneg (clsII_1 hσ d hl hm).2 hcc (le_of_eq (by ring))
  exact comb4 hM0 hXI m1 m2 m3 m4

end SampleMid

section SampleMid2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **For a fixed `q`: `E|R_q H_q| ≤ 106 N² w + (m_{l+m+1} N + |φ_{l,m+1}(0)|) 6 N M`.** -/
theorem RH_abs [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) (q : ℕ)
    (hq : q ∈ Finset.range N) :
    ∫ ω, |Rq σ l m X N q ω * Hrow (cK d σ) X N q ω| ∂μ
      ≤ 106 * (N : ℝ) ^ 2 * wN d σ l m
        + (torusM d σ (l + m + 1) * (N : ℝ) + |phiN d σ l (m + 1) 0|)
          * (6 * (N : ℝ) * torusM d σ 1) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h1M := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hK0 := tM0 hσ d (by omega : 1 ≤ l + m + 1)
  have Hc := cK_deg2 X h_indep hX hlaw hσ
  obtain ⟨bX, hXsq⟩ := Xq_sq X h_indep hX hlaw hσ hl hm N hN hMN q hq
  have bH : BM (Hrow (cK d σ) X N q) := Hc.BM_Hrow N q
  have hc := (cK_facts hσ d 0).1
  have hcc : cK d σ 0 ^ 2 ≤ torusM d σ 1 ^ 2 := sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2
  have hQ : ∫ ω, Hrow (cK d σ) X N q ω ^ 2 ∂μ ≤ 6 * (N : ℝ) * torusM d σ 1 := by
    refine (Hc.Hrow_sq N q hq).trans ?_
    have := mul_nonneg hM0 (sub_nonneg.mpr hMN)
    linarith [show torusM d σ 1 * ((N : ℝ) - torusM d σ 1)
      = (N : ℝ) * torusM d σ 1 - torusM d σ 1 ^ 2 by ring]
  have hQpos : 0 < 6 * (N : ℝ) * torusM d σ 1 :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hCS : ∫ ω, |Xq σ l m X N q ω * Hrow (cK d σ) X N q ω| ∂μ
      ≤ 106 * (N : ℝ) ^ 2 * wN d σ l m :=
    cs_abs bX bH (le_refl _) hQ hQpos
      (mul_nonneg (mul_nonneg (by norm_num) (_root_.sq_nonneg _)) hw0) (ar_cs hN0 hXsq)
  have hH2 : ∫ ω, |Hrow (cK d σ) X N q ω ^ 2| ∂μ ≤ 6 * (N : ℝ) * torusM d σ 1 := by
    have e : (fun ω => |Hrow (cK d σ) X N q ω ^ 2|) = fun ω => Hrow (cK d σ) X N q ω ^ 2 :=
      funext fun ω => abs_of_nonneg (_root_.sq_nonneg _)
    rw [e]; exact hQ
  have hsplit : (fun ω => |Rq σ l m X N q ω * Hrow (cK d σ) X N q ω|)
      = fun ω => |Xq σ l m X N q ω * Hrow (cK d σ) X N q ω
          + (-(torusM d σ (l + m + 1) * (N : ℝ) + phiN d σ l (m + 1) 0))
            * Hrow (cK d σ) X N q ω ^ 2| := by
    funext ω
    rw [Rq_split X h_indep hX hlaw hσ hl hm N q hq ω]
    congr 1
    ring
  rw [hsplit]
  have h := abs_int_add (bX.mul bH)
    (BM.const_mul (-(torusM d σ (l + m + 1) * (N : ℝ) + phiN d σ l (m + 1) 0)) bH.sqr) hCS
    (int_abs_cmul (-(torusM d σ (l + m + 1) * (N : ℝ) + phiN d σ l (m + 1) 0)) hH2)
  refine h.trans ?_
  have hk : |-(torusM d σ (l + m + 1) * (N : ℝ) + phiN d σ l (m + 1) 0)|
      ≤ torusM d σ (l + m + 1) * (N : ℝ) + |phiN d σ l (m + 1) 0| := by
    rw [abs_neg]
    exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_of_nonneg (mul_nonneg hK0 hN0)]))
  have := mul_le_mul_of_nonneg_right hk hQpos.le
  linarith

/-- **`E|Z¹[K_m, a = 3]| ≤ 118 w/N`**, `w = (√2)^d M m_{l+m}`, for `M ≤ N`. -/
theorem Z1_Km_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |Zs1three3 N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
        (cmat d σ N (fun j => X j ω))| ∂μ ≤ 118 * (wN d σ l m / N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 4 := by positivity
  have Hc := cK_deg2 X h_indep hX hlaw hσ
  have hfun : (fun ω => |Zs1three3 N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
        (cmat d σ N (fun j => X j ω))|)
      = fun ω => 1 / (N : ℝ) ^ 4
          * |∑ q ∈ Finset.range N, Rq σ l m X N q ω * Hrow (cK d σ) X N q ω| := by
    funext ω
    rw [Z1_Km_conv σ l m N X ω, abs_mul, abs_of_nonneg hpos]
  have hsum : ∫ ω, |∑ q ∈ Finset.range N, Rq σ l m X N q ω * Hrow (cK d σ) X N q ω| ∂μ
      ≤ (N : ℝ) * (106 * (N : ℝ) ^ 2 * wN d σ l m
        + (torusM d σ (l + m + 1) * (N : ℝ) + |phiN d σ l (m + 1) 0|)
          * (6 * (N : ℝ) * torusM d σ 1)) := by
    have h := abs_int_sum (μ := μ) (Finset.range N)
      (fun q ω => Rq σ l m X N q ω * Hrow (cK d σ) X N q ω)
      (fun q _ => (BM_Rq X hX hσ hl hm N q).mul (Hc.BM_Hrow N q))
      (fun q hq => RH_abs X h_indep hX hlaw hσ hl hm N hN hMN q hq)
    rw [Finset.card_range] at h
    exact h
  rw [hfun, integral_const_mul]
  exact ar_Z1 hN1 (torusM_one_ge hσ d) hMN (wN_Mk hσ d hl)
    (tM0 hσ d (by omega : 1 ≤ l + m + 1))
    (torusM_anti hσ d (by omega : 1 ≤ l + m) (by omega : l + m ≤ l + m + 1)) (abs_nonneg _)
    (clsII_1 hσ d hl hm).1 (mul_le_mul_of_nonneg_left hsum hpos)

/-- **`E|Z⁰[K_m]| ≤ 53 w/N`**, `w = (√2)^d M m_{l+m}`, for `M ≤ N`. -/
theorem Z0_Km_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |Zs0three N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))| ∂μ
      ≤ 53 * (wN d σ l m / N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hpos : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 3 := by positivity
  have h1M := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have hw0 := wN_nonneg (m := m) hσ d hl
  have hMk := wN_Mk (m := m) hσ d hl
  have hk0 := tM0 hσ d (by omega : 1 ≤ l + m)
  have hK0 := tM0 hσ d (by omega : 1 ≤ l + m + 1)
  have hK : torusM d σ (l + m + 1) ≤ torusM d σ (l + m) :=
    torusM_anti hσ d (by omega) (by omega)
  have hKK : torusM d σ (l + (m + 1)) ≤ torusM d σ (l + m) :=
    torusM_anti hσ d (by omega) (by omega)
  have hc := (cK_facts hσ d 0).1
  have HT := tdeg_tri3 X h_indep hX hlaw hσ hl hm
  have H1 := phiN_deg2 X h_indep hX hlaw hσ (le_refl 1) hm
  have H2 := phiN_deg2 X h_indep hX hlaw hσ hl (le_refl 1)
  have H3 := phiN_deg2 X h_indep hX hlaw hσ hl hm
  have H4 := phiN_deg2 X h_indep hX hlaw hσ hl (by omega : 1 ≤ m + 1)
  have H5 := phiN_deg2 X h_indep hX hlaw hσ (by omega : 1 ≤ l + 1) hm
  have H6 := phiN_deg2 X h_indep hX hlaw hσ (le_refl 1) (by omega : 1 ≤ l + m)
  have H := phiN_deg3 X h_indep hX hlaw hσ hl (by omega : 1 ≤ m + 1)
  have Hc := cK_deg2 X h_indep hX hlaw hσ
  have hL := phiN_l1 hσ d hl (by omega : 1 ≤ m + 1)
  have hκa : |(-2 : ℝ)| ≤ 2 * (N : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hκb : |(N : ℝ) - 2| ≤ 2 * (N : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  -- the pieces, each with its bound `c N² w`
  have bS0 : BM (fun ω => ∑ q ∈ Finset.range N, Roff (Tdeg d σ l m) X N q ω) :=
    BM.sum (Finset.range N) (fun q => Roff (Tdeg d σ l m) X N q) fun q _ => HT.BM_Roff N q
  have hS0 : ∫ ω, |∑ q ∈ Finset.range N, Roff (Tdeg d σ l m) X N q ω| ∂μ
      ≤ 7 * (N : ℝ) ^ 2 * wN d σ l m := by
    have h := abs_int_sum (μ := μ) (Finset.range N) (fun q => Roff (Tdeg d σ l m) X N q)
      (fun q _ => HT.BM_Roff N q)
      (fun q _ => (HT.BM_Roff N q).abs_le_sqrt (HT.Roff_sq N q))
    rw [Finset.card_range] at h
    exact h.trans (z_roff hMk hw0 hN0 (TdegV_le hσ d hl hm))
  have c7 : BM (fun _ω : Ω => (N : ℝ) * -t2N d σ l m) := BM.const _
  have hC7 : ∫ _ω : Ω, |(N : ℝ) * -t2N d σ l m| ∂μ ≤ 6 * (N : ℝ) ^ 2 * wN d σ l m := by
    rw [integral_const, probReal_univ, one_smul]
    exact z_const hM0 hMN hw0 (t2N_bound hσ d hl hm)
  have bF : ∀ (ψ : FlatTorus d → ℝ) (B V : ℝ), Deg2 μ (flatTorusMeasure d) X ψ B V →
      BM (fun ω => ∑ q ∈ Finset.range N, Hrow ψ X N q ω) := fun ψ _ _ Hd =>
    BM.sum (Finset.range N) (fun q => Hrow ψ X N q) fun q _ => Hd.BM_Hrow N q
  have hF : ∀ (ψ : FlatTorus d → ℝ) (B V : ℝ), Deg2 μ (flatTorusMeasure d) X ψ B V →
      ∫ ω, |∑ q ∈ Finset.range N, Hrow ψ X N q ω| ∂μ
        ≤ (N : ℝ) * Real.sqrt (2 * V) + (N : ℝ) * |ψ 0| := fun _ _ _ Hd => Hd.full_abs_le N
  have b1 := BM.const_mul (torusM d σ l) (bF _ _ _ H1)
  have b2 := BM.const_mul (torusM d σ m) (bF _ _ _ H2)
  have b3 := BM.const_mul (torusM d σ 1) (bF _ _ _ H3)
  have b4 := BM.const_mul (-2 : ℝ) (bF _ _ _ H4)
  have b5 := BM.const_mul ((N : ℝ) - 2) (bF _ _ _ H5)
  have b6 := BM.const_mul ((N : ℝ) - 2) (bF _ _ _ H6)
  have b8 := BM.const_mul (-(torusM d σ (l + m + 1) * (N : ℝ))) (bF _ _ _ Hc)
  have a1 := (int_abs_cmul (torusM d σ l) (hF _ _ _ H1)).trans
    (z_clsI h1M hMN hw0 H1.V_nonneg (clsI_1 hσ d hl hm).1 (clsI_1 hσ d hl hm).2)
  have a2 := (int_abs_cmul (torusM d σ m) (hF _ _ _ H2)).trans
    (z_clsI h1M hMN hw0 H2.V_nonneg (clsI_2 hσ d hl hm).1 (clsI_2 hσ d hl hm).2)
  have a3 := (int_abs_cmul (torusM d σ 1) (hF _ _ _ H3)).trans
    (z_clsI h1M hMN hw0 H3.V_nonneg (clsI_3 hσ d hl hm).1 (clsI_3 hσ d hl hm).2)
  have a4 := (int_abs_cmul (-2 : ℝ) (hF _ _ _ H4)).trans
    (z_clsII h1M hMk hk0 hN0 hκa (clsII_1 hσ d hl hm).1 (clsII_1 hσ d hl hm).2)
  have a5 := (int_abs_cmul ((N : ℝ) - 2) (hF _ _ _ H5)).trans
    (z_clsII h1M hMk hk0 hN0 hκb (clsII_2 hσ d hl hm).1 (clsII_2 hσ d hl hm).2)
  have a6 := (int_abs_cmul ((N : ℝ) - 2) (hF _ _ _ H6)).trans
    (z_clsII h1M hMk hk0 hN0 hκb (clsII_3 (m := m) hσ d hl).1 (clsII_3 (m := m) hσ d hl).2)
  have a8 := (int_abs_cmul (-(torusM d σ (l + m + 1) * (N : ℝ))) (hF _ _ _ Hc)).trans
    (z_hc h1M hMk hK0 hK hN0 hc)
  have eAs : ∀ ω, ∑ q ∈ Finset.range N, Aq (phiN d σ l (m + 1)) (cK d σ) X N q ω
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
          phiN d σ l (m + 1) (X i ω - X j ω) * cK d σ (X j ω - X v ω) := by
    intro ω
    unfold Aq
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  have bAs : BM (fun ω => ∑ q ∈ Finset.range N, Aq (phiN d σ l (m + 1)) (cK d σ) X N q ω) :=
    BM.sum (Finset.range N) (fun q => Aq (phiN d σ l (m + 1)) (cK d σ) X N q) fun q _ =>
      H.BM_Aq N q
  have hAs : ∫ ω, |∑ q ∈ Finset.range N, Aq (phiN d σ l (m + 1)) (cK d σ) X N q ω| ∂μ
      ≤ 10 * (N : ℝ) ^ 2 * wN d σ l m := by
    simp_rw [eAs]
    exact (H.triple_abs_le hL N).trans
      (z_trip h1M hMN hMk hk0 (clsII_1 hσ d hl hm).1 hc H4.V_nonneg (clsII_1 hσ d hl hm).2
        (by linarith))
  have b9 := BM.const_mul (-1 : ℝ) bAs
  have a9 : ∫ ω, |(-1 : ℝ) * ∑ q ∈ Finset.range N,
        Aq (phiN d σ l (m + 1)) (cK d σ) X N q ω| ∂μ ≤ 10 * (N : ℝ) ^ 2 * wN d σ l m := by
    refine (int_abs_cmul (-1 : ℝ) hAs).trans (le_of_eq ?_)
    rw [abs_neg, abs_one, one_mul]
  -- the identity for the sum over `q`
  have hT : ∀ ω, ∑ q ∈ Finset.range N, Rq σ l m X N q ω
      = ∑ q ∈ Finset.range N, Roff (Tdeg d σ l m) X N q ω + (N : ℝ) * -t2N d σ l m
        + (torusM d σ l * ∑ q ∈ Finset.range N, Hrow (phiN d σ 1 m) X N q ω
            + torusM d σ m * ∑ q ∈ Finset.range N, Hrow (phiN d σ l 1) X N q ω
            + torusM d σ 1 * ∑ q ∈ Finset.range N, Hrow (phiN d σ l m) X N q ω)
        + ((-2 : ℝ) * ∑ q ∈ Finset.range N, Hrow (phiN d σ l (m + 1)) X N q ω
            + ((N : ℝ) - 2) * ∑ q ∈ Finset.range N, Hrow (phiN d σ (l + 1) m) X N q ω
            + ((N : ℝ) - 2) * ∑ q ∈ Finset.range N, Hrow (phiN d σ 1 (l + m)) X N q ω)
        + (-(torusM d σ (l + m + 1) * (N : ℝ)))
            * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω
        + (-1 : ℝ) * ∑ q ∈ Finset.range N, Aq (phiN d σ l (m + 1)) (cK d σ) X N q ω := by
    intro ω
    rw [Finset.sum_congr rfl fun q hq => Rq_eq σ hl hm X N q hq ω]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    try ring
  have s01 := abs_int_add bS0 c7 hS0 hC7
  have s12 := abs_int_add b1 b2 a1 a2
  have sG2 := abs_int_add (b1.add b2) b3 s12 a3
  have s45 := abs_int_add b4 b5 a4 a5
  have sG3 := abs_int_add (b4.add b5) b6 s45 a6
  have s012 := abs_int_add (bS0.add c7) ((b1.add b2).add b3) s01 sG2
  have s0123 := abs_int_add ((bS0.add c7).add ((b1.add b2).add b3)) ((b4.add b5).add b6)
    s012 sG3
  have s4 := abs_int_add (((bS0.add c7).add ((b1.add b2).add b3)).add ((b4.add b5).add b6)) b8
    s0123 a8
  have s5 := abs_int_add
    ((((bS0.add c7).add ((b1.add b2).add b3)).add ((b4.add b5).add b6)).add b8) b9 s4 a9
  have key : ∫ ω, |∑ q ∈ Finset.range N, Rq σ l m X N q ω| ∂μ
      ≤ 53 * (N : ℝ) ^ 2 * wN d σ l m := by
    simp_rw [hT]
    refine s5.trans (le_of_eq ?_)
    ring
  have hfun : (fun ω => |Zs0three N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))|)
      = fun ω => 1 / (N : ℝ) ^ 3 * |∑ q ∈ Finset.range N, Rq σ l m X N q ω| := by
    funext ω
    rw [Z0_Km_conv σ l m N X ω, abs_mul, abs_of_nonneg hpos]
  rw [hfun, integral_const_mul]
  exact ar_Z0 hNpos key (le_refl _)

theorem BM_Z0Km {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) (N : ℕ) :
    BM (fun ω => Zs0three N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))) := by
  have e : (fun ω => Zs0three N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω)))
      = fun ω => 1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N, Rq σ l m X N q ω :=
    funext fun ω => Z0_Km_conv σ l m N X ω
  rw [e]
  exact BM.const_mul _ (BM.sum (Finset.range N) (fun q => Rq σ l m X N q) fun q _ =>
    BM_Rq X hX hσ hl hm N q)

theorem BM_Z1Km {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) (N : ℕ) :
    BM (fun ω => Zs1three3 N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
      (cmat d σ N (fun j => X j ω))) := by
  have e : (fun ω => Zs1three3 N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
        (cmat d σ N (fun j => X j ω)))
      = fun ω => 1 / (N : ℝ) ^ 4
          * ∑ q ∈ Finset.range N, Rq σ l m X N q ω * Hrow (cK d σ) X N q ω :=
    funext fun ω => Z1_Km_conv σ l m N X ω
  have bH : ∀ q, BM (Hrow (cK d σ) X N q) := fun q => by
    show BM (fun ω => ∑ v ∈ Finset.range N, cK d σ (X q ω - X v ω))
    exact BM.sum (Finset.range N) (fun v ω => cK d σ (X q ω - X v ω)) fun v _ =>
      BM_cK X hX hσ q v
  rw [e]
  exact BM.const_mul _ (BM.sum (Finset.range N)
    (fun q ω => Rq σ l m X N q ω * Hrow (cK d σ) X N q ω) fun q _ =>
    (BM_Rq X hX hσ hl hm N q).mul (bH q))

/-- **One middle summand of `Π_k` completely**: for `l, m ≥ 1`, `N ≥ 1`, `M = p(0) ≤ N`:
    `E |N⁻² ∑_{i,b} p_l(x_i - x_b) ĥ_m^{(i)}(b)| ≤ 171 (√2)^d (M/N) m_{l+m}`
    (stated with `w/N`, `w = (√2)^d M m_{l+m}`), together with its measurability/boundedness. -/
theorem mid_term_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {l m : ℕ} (hl : 1 ≤ l)
    (hm : 1 ≤ m) (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    BM (fun ω => 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) l i b * torusHhat d σ N (fun j => X j ω) m i b)
    ∧ ∫ ω, |1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) l i b * torusHhat d σ N (fun j => X j ω) m i b| ∂μ
      ≤ 171 * (wN d σ l m / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have b0 := BM_Z0Km X hX hσ hl hm N
  have b1 := BM_Z1Km X hX hσ hl hm N
  have hpt : ∀ ω, 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) l i b * torusHhat d σ N (fun j => X j ω) m i b
      = Zs0three N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
        + (-1 : ℝ) * Zs1three3 N (fun i b j : Fin N => Km d σ l m (X i ω) (X b ω) (X j ω))
          (cmat d σ N (fun j => X j ω)) := by
    intro ω
    rw [mid_term d σ N hN0 (fun j => X j ω) l m]
    ring
  have h := abs_int_add b0 (BM.const_mul (-1 : ℝ) b1)
    (Z0_Km_bound X h_indep hX hlaw hσ hl hm N hN hMN)
    (int_abs_cmul (-1 : ℝ) (Z1_Km_bound X h_indep hX hlaw hσ hl hm N hN hMN))
  constructor
  · simp_rw [hpt]
    exact b0.add (BM.const_mul (-1 : ℝ) b1)
  · simp_rw [hpt]
    refine h.trans (le_of_eq ?_)
    rw [abs_neg, abs_one, one_mul]
    ring

end SampleMid2

/-! ### the bound for `Π_k` -/

/-- The constant of `pi_bound`: `C_Π(d) = 76 + 171 (√2)^d`. -/
noncomputable def piC (d : ℕ) : ℝ := 76 + 171 * Real.sqrt 2 ^ d

theorem ar_pi {u A κ c S : ℝ} (hu : 0 ≤ u) (hA : 0 ≤ A) (hκ : 1 ≤ κ) (hc : c ≤ κ)
    (hS : S ≤ 63 * u + c * (171 * (A * u)) + 13 * u) : S ≤ (76 + 171 * A) * κ * u := by
  have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ κ - 1) hu
  have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ κ - c) (mul_nonneg hA hu)
  linarith [show (κ - 1) * u = κ * u - u by ring,
    show (κ - c) * (A * u) = κ * (A * u) - c * (A * u) by ring,
    show (76 + 171 * A) * κ * u = 76 * (κ * u) + 171 * (κ * (A * u)) by ring,
    show c * (171 * (A * u)) = 171 * (c * (A * u)) by ring]

section SamplePi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The first summand of `Π_k` is a bounded measurable function of the sample. -/
theorem BM_first {d : ℕ} (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) {σ : ℝ}
    (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN0 : (N : ℝ) ≠ 0) :
    BM (fun ω => 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
      torusQ d σ N (fun j => X j ω) k i b * torusQ d σ N (fun j => X j ω) 1 b i
        * torusTheta1 d σ N (fun j => X j ω) b i) := by
  have bF := BM_FA X hX hσ k hk
  have bp := BM_pker X hX hσ
  have bc := BM_cK X hX hσ
  have z1 : BM (fun ω => Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
      (cmat d σ N (fun j => X j ω))) := by
    have e : (fun ω => Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
          (cmat d σ N (fun j => X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω) :=
      funext fun ω => Z1_FA1_conv σ k N (fun j => X j ω)
    rw [e]
    exact BM.const_mul _ (BM.sum (Finset.range N)
      (fun i ω => ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω)) fun i _ =>
      BM.sum (Finset.range N) (fun b ω => ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω)) fun b _ =>
      BM.sum (Finset.range N) (fun v ω => FA d σ k (X i ω) (X b ω) * cK d σ (X i ω - X v ω))
        fun v _ => (bF i b).mul (bc i v))
  have z2 : BM (fun ω => Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
      (cmat d σ N (fun j => X j ω))) := by
    have e : (fun ω => Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
          (cmat d σ N (fun j => X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ v ∈ Finset.range N, FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω) :=
      funext fun ω => Z1_FA2_conv σ k N (fun j => X j ω)
    rw [e]
    exact BM.const_mul _ (BM.sum (Finset.range N)
      (fun i ω => ∑ b ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)) fun i _ =>
      BM.sum (Finset.range N) (fun b ω => ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω)) fun b _ =>
      BM.sum (Finset.range N) (fun v ω => FA d σ k (X i ω) (X b ω) * cK d σ (X b ω - X v ω))
        fun v _ => (bF i b).mul (bc b v))
  have z3 : BM (fun ω => Zs1three3 N
      (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
      (cmat d σ N (fun j => X j ω))) := by
    have e : (fun ω => Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
          (cmat d σ N (fun j => X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ b ∈ Finset.range N,
            ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
              FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω) :=
      funext fun ω => Z1_FA3_conv σ k N (fun j => X j ω)
    rw [e]
    exact BM.const_mul _ (BM.sum (Finset.range N)
      (fun i ω => ∑ b ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
        FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
      fun i _ => BM.sum (Finset.range N)
        (fun b ω => ∑ q ∈ Finset.range N, ∑ v ∈ Finset.range N,
          FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
        fun b _ => BM.sum (Finset.range N)
          (fun q ω => ∑ v ∈ Finset.range N,
            FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
          fun q _ => BM.sum (Finset.range N)
            (fun v ω =>
              FA d σ k (X i ω) (X b ω) * pker d σ (X b ω - X q ω) * cK d σ (X q ω - X v ω))
            fun v _ => ((bF i b).mul (bp b q)).mul (bc q v))
  have hpt : ∀ ω, 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) k i b * torusQ d σ N (fun j => X j ω) 1 b i
          * torusTheta1 d σ N (fun j => X j ω) b i
      = (-1 : ℝ) * Zs1two1 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
            (cmat d σ N (fun j => X j ω))
        + (-1 : ℝ) * Zs1two2 N (fun i b : Fin N => FA d σ k (X i ω) (X b ω))
            (cmat d σ N (fun j => X j ω))
        + Zs1three3 N (fun i b j : Fin N => FA' d σ k (X i ω) (X b ω) (X j ω))
            (cmat d σ N (fun j => X j ω)) := by
    intro ω
    rw [first_term d σ N hN0 (fun j => X j ω) k]
    ring
  simp_rw [hpt]
  exact ((BM.const_mul (-1 : ℝ) z1).add (BM.const_mul (-1 : ℝ) z2)).add z3

/-- The last summand of `Π_k` is a bounded measurable function of the sample. -/
theorem BM_last [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN0 : (N : ℝ) ≠ 0) :
    BM (fun ω => 1 / (N : ℝ) * ∑ i : Fin N, torusHhat d σ N (fun j => X j ω) k i i) := by
  have H := torus_deg3 X h_indep hX hlaw hσ k hk
  have z0 : BM (fun ω => Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))) := by
    have f0 : (fun ω => Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            psiK d σ k (X i ω - X j ω) :=
      funext fun ω => Z0_Psi_conv σ k N (fun j => X j ω)
    rw [f0]
    exact BM.const_mul _ (H.hψ.BM_full N)
  have z1 : BM (fun ω => Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
      (cmat d σ N (fun j => X j ω))) := by
    have f1 : (fun ω => Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
          (cmat d σ N (fun j => X j ω)))
        = fun ω => 1 / (N : ℝ) ^ 3 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            ∑ v ∈ Finset.range N, psiK d σ k (X i ω - X j ω) * cK d σ (X j ω - X v ω) :=
      funext fun ω => Z1_Psi_conv σ k N (fun j => X j ω)
    rw [f1]
    exact BM.const_mul _ (BM.sum (Finset.range N)
      (fun i ω => ∑ j ∈ Finset.range N, ∑ v ∈ Finset.range N,
        psiK d σ k (X i ω - X j ω) * cK d σ (X j ω - X v ω)) fun i _ =>
      BM.sum (Finset.range N) (fun j ω => ∑ v ∈ Finset.range N,
        psiK d σ k (X i ω - X j ω) * cK d σ (X j ω - X v ω)) fun j _ =>
      BM.sum (Finset.range N) (fun v => aP (psiK d σ k) (cK d σ) X i j v) fun v _ =>
        H.BM_aP i j v)
  have hpt : ∀ ω, 1 / (N : ℝ) * ∑ i : Fin N, torusHhat d σ N (fun j => X j ω) k i i
      = Zs0two N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
        + (-1 : ℝ) * Zs1two2 N (fun i j : Fin N => Psi d σ k (X i ω) (X j ω))
            (cmat d σ N (fun j => X j ω)) := by
    intro ω
    rw [last_term d σ N hN0 (fun j => X j ω) k]
    ring
  simp_rw [hpt]
  exact z0.add (BM.const_mul (-1 : ℝ) z1)

/-- **`lem:pibound` with an explicit constant.** For independent uniform points on the flat
    torus of dimension `d`, the Gaussian walk kernel of variance `σ > 0` with self-loops,
    `k ≥ 1`, `N ≥ 1` and `M = p(0) ≤ N`:
    `E|Π_k| ≤ C_Π (M/N) k m_k`, `C_Π = 76 + 171 (√2)^d`; and `Π_k` is a bounded measurable
    function of the sample.  No further condition on `σ` or `k σ`. -/
theorem pi_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) :
    BM (fun ω => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)))
    ∧ ∫ ω, |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))| ∂μ
      ≤ piC d * (torusM d σ 1 / N) * k * torusM d σ k := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hM0 : 0 ≤ torusM d σ 1 := by linarith [torusM_one_ge hσ d]
  have hk0 := tM0 hσ d hk
  have bP1 := BM_first X hX hσ k hk N hN0
  have bP3 := BM_last X h_indep hX hlaw hσ k hk N hN0
  have hmid : ∀ m ∈ Finset.Icc 1 (k - 1),
      BM (fun ω => 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
          torusQ d σ N (fun j => X j ω) (k - m) i b * torusHhat d σ N (fun j => X j ω) m i b)
      ∧ ∫ ω, |1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
          torusQ d σ N (fun j => X j ω) (k - m) i b
            * torusHhat d σ N (fun j => X j ω) m i b| ∂μ
        ≤ 171 * (Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ k / N) := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have hl : 1 ≤ k - m := by omega
    have h := mid_term_bound X h_indep hX hlaw hσ hl hm'.1 N hN hMN
    have ek : k - m + m = k := by omega
    have ew : wN d σ (k - m) m = Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ k := by
      unfold wN; rw [ek]
    rw [ew] at h
    exact h
  have bS2 : BM (fun ω => ∑ m ∈ Finset.Icc 1 (k - 1),
      1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) (k - m) i b * torusHhat d σ N (fun j => X j ω) m i b) :=
    BM.sum (Finset.Icc 1 (k - 1)) (fun m ω => 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
      torusQ d σ N (fun j => X j ω) (k - m) i b * torusHhat d σ N (fun j => X j ω) m i b)
      fun m hm => (hmid m hm).1
  have hS2 : ∫ ω, |∑ m ∈ Finset.Icc 1 (k - 1),
      1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) (k - m) i b
          * torusHhat d σ N (fun j => X j ω) m i b| ∂μ
      ≤ ((Finset.Icc 1 (k - 1)).card : ℝ)
        * (171 * (Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ k / N)) :=
    abs_int_sum (μ := μ) (Finset.Icc 1 (k - 1))
      (fun m ω => 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
        torusQ d σ N (fun j => X j ω) (k - m) i b * torusHhat d σ N (fun j => X j ω) m i b)
      (fun m hm => (hmid m hm).1) (fun m hm => (hmid m hm).2)
  have h12 := abs_int_add bP1 bS2 (first_term_bound X h_indep hX hlaw hσ k hk N hN hMN) hS2
  have h123 := abs_int_add (bP1.add bS2) bP3 h12
    (last_term_bound X h_indep hX hlaw hσ k hk N hN hMN)
  have h123' : ∫ ω, |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))| ∂μ
      ≤ 63 * (torusM d σ 1 / N) * torusM d σ k
        + ((Finset.Icc 1 (k - 1)).card : ℝ)
          * (171 * (Real.sqrt 2 ^ d * torusM d σ 1 * torusM d σ k / N))
        + 13 * (torusM d σ 1 / N) * torusM d σ k := h123
  refine ⟨(bP1.add bS2).add bP3, ?_⟩
  have hcard : ((Finset.Icc 1 (k - 1)).card : ℝ) ≤ (k : ℝ) := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : k - 1 + 1 - 1 ≤ k)
  have hκ : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hu : 0 ≤ torusM d σ 1 / N * torusM d σ k := mul_nonneg (div_nonneg hM0 hNpos.le) hk0
  have hA : (0 : ℝ) ≤ Real.sqrt 2 ^ d := pow_nonneg (Real.sqrt_nonneg 2) d
  have h := ar_pi (u := torusM d σ 1 / N * torusM d σ k) (A := Real.sqrt 2 ^ d)
    (c := ((Finset.Icc 1 (k - 1)).card : ℝ)) hu hA hκ hcard (h123'.trans (le_of_eq (by ring)))
  have e : piC d * (torusM d σ 1 / N) * k * torusM d σ k
      = (76 + 171 * Real.sqrt 2 ^ d) * (k : ℝ) * (torusM d σ 1 / N * torusM d σ k) := by
    unfold piC; ring
  rw [e]
  exact h

/-- **Markov's inequality for `Π_k`**: `P(|Π_k| ≥ t) ≤ C_Π (M/N) k m_k / t` for `t > 0`. -/
theorem pi_markov [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) (hMN : torusM d σ 1 ≤ N) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t ≤ |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|}
      ≤ piC d * (torusM d σ 1 / N) * k * torusM d σ k / t := by
  obtain ⟨bP, hP⟩ := pi_bound X h_indep hX hlaw hσ k hk N hN hMN
  have h : t * μ.real {ω | t ≤ |torusPi d σ N (fun j => X j ω) k
        (torusHhat d σ N (fun j => X j ω))|}
      ≤ ∫ ω, |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))| ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
      bP.absv.integrable t
  rw [le_div_iff₀ ht]
  calc μ.real {ω | t ≤ |torusPi d σ N (fun j => X j ω) k
          (torusHhat d σ N (fun j => X j ω))|} * t
      = t * μ.real {ω | t ≤ |torusPi d σ N (fun j => X j ω) k
          (torusHhat d σ N (fun j => X j ω))|} := mul_comm _ _
    _ ≤ ∫ ω, |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))| ∂μ := h
    _ ≤ piC d * (torusM d σ 1 / N) * k * torusM d σ k := hP

end SamplePi



end PiBound

/-! ## Almost sure statements with the regime in place of the smallness hypothesis.
Regime (R'): `N σ_N^{d/2+1}/log N → ∞` (with `σ = ξ²` this is `N ξ^{d+2}/log N → ∞`). No rate is stated. -/

namespace Regime

open Filter Topology
open CTG.Reals.TraceG29 CTG.Reals.Assembled

theorem eigC3_nonneg (d : ℕ) : 0 ≤ eigC3 d := by
  unfold eigC3
  have h1 := TraceG29.kernelC1_nonneg d
  have h2 : 0 ≤ (6 * (6 * Real.sqrt (3 * (d : ℝ) + 5)) + 2
      + Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) * (1 + 2 * Real.sqrt 2 ^ d))
    * ((1 + Real.sqrt (2 * Real.pi)) ^ d) ^ 2 := by positivity
  linarith

/-! ### The smallness condition derived from the regime -/

/-! ### Stage 1: pure analysis -/

/-- `1 + (2πσ)^{-1/2} ≤ 2 σ^{-1/2}` for `0 < σ ≤ 1`. -/
theorem one_add_sqrt_le {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ)) ≤ 2 / Real.sqrt σ := by
  have hs : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hs1 : Real.sqrt σ ≤ 1 := (Real.sqrt_le_sqrt hσ1).trans_eq Real.sqrt_one
  have hpi := Real.two_le_pi
  have h1 : (1 : ℝ) ≤ 1 / Real.sqrt σ := (one_le_div hs).mpr hs1
  have h2 : Real.pi / (2 * Real.pi ^ 2 * σ) ≤ 1 / σ := by
    rw [div_le_div_iff₀ (by positivity) hσ]
    nlinarith [mul_pos (mul_pos hσ Real.pi_pos) (by linarith : (0 : ℝ) < 2 * Real.pi - 1)]
  have h3 : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ)) ≤ 1 / Real.sqrt σ := by
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at this
  calc 1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))
      ≤ 1 / Real.sqrt σ + 1 / Real.sqrt σ := add_le_add h1 h3
    _ = 2 / Real.sqrt σ := by ring

/-- Core of the smallness condition (real numbers only). -/
theorem small_core {C M L n s K η : ℝ} (d : ℕ) (hC : 0 ≤ C) (hη : 0 < η)
    (hM : M ≤ 2 ^ d / s) (hs : 0 < s) (hL : 0 < L) (hn : 0 < n) (hK : 0 < K)
    (hR : C ^ 2 * 2 ^ d / η ^ 2 + 1 ≤ n * s / (L * K)) :
    C * Real.sqrt (M * L / n) * Real.sqrt K ≤ η := by
  have hLK : 0 < L * K := mul_pos hL hK
  have hC2 : 0 ≤ C ^ 2 := _root_.sq_nonneg C
  have hη2 : 0 < η ^ 2 := pow_pos hη 2
  have hA : 0 ≤ C ^ 2 * 2 ^ d / η ^ 2 := by positivity
  have hB : 0 < C ^ 2 * 2 ^ d / η ^ 2 + 1 := by linarith
  have hx : M * L / n * K ≤ 2 ^ d / (C ^ 2 * 2 ^ d / η ^ 2 + 1) := by
    have h1 : M * L / n * K ≤ 2 ^ d / s * L / n * K :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM hL.le) hn.le) hK.le
    have h2 : 2 ^ d / s * L / n * K = 2 ^ d / (n * s / (L * K)) := by
      field_simp
    rw [h2] at h1
    exact h1.trans (div_le_div_of_nonneg_left (by positivity) hB hR)
  have hx2 : C ^ 2 * (M * L / n * K) ≤ η ^ 2 := by
    refine (mul_le_mul_of_nonneg_left hx hC2).trans ?_
    rw [← mul_div_assoc, div_le_iff₀ hB]
    have h5 : η ^ 2 * (C ^ 2 * 2 ^ d / η ^ 2) = C ^ 2 * 2 ^ d := by
      field_simp
    rw [mul_add, h5]
    linarith
  have e : C * Real.sqrt (M * L / n) * Real.sqrt K
      = Real.sqrt (C ^ 2 * (M * L / n * K)) := by
    rw [Real.sqrt_mul hC2, Real.sqrt_sq hC, Real.sqrt_mul' _ hK.le, mul_assoc]
  rw [e]
  exact (Real.sqrt_le_sqrt hx2).trans_eq (Real.sqrt_sq hη.le)

/-- Core of the smallness of the Poisson-tail term `4M/N²`. -/
theorem tail_core {M L n s J η : ℝ} (d : ℕ) (hη : 0 < η)
    (hM : M ≤ 2 ^ d / s) (hs : 0 < s) (hL : Real.log 2 ≤ L) (hn : 2 ≤ n) (hJ : 2 ≤ J)
    (hR : 4 * 2 ^ d / η ≤ n * s / (L * J)) :
    4 * M / n ^ 2 ≤ η := by
  have hl2 := Real.log_two_gt_d9
  have hLJ : 1 ≤ L * J := by
    nlinarith [mul_nonneg (sub_nonneg.2 (hl2.le.trans hL)) (sub_nonneg.2 hJ)]
  have hn0 : (0 : ℝ) < n := by linarith
  have hdiv : n * s / (L * J) ≤ n * s := div_le_self (mul_pos hn0 hs).le hLJ
  have h1 : 4 * 2 ^ d ≤ n * s * η := (div_le_iff₀ hη).1 (hR.trans hdiv)
  have h2 : n * s * η ≤ η * n ^ 2 * s := by
    nlinarith [mul_nonneg (mul_pos (mul_pos hη hs) hn0).le (by linarith : (0 : ℝ) ≤ n - 1)]
  have h4 : 4 * (2 ^ d / s) ≤ η * n ^ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hs]; linarith
  rw [div_le_iff₀ (pow_pos hn0 2)]
  linarith

/-- `N / (log N)^n → ∞`. -/
theorem tendsto_nat_div_log_pow (n : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ n) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ n / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ n / (1 * x + 0)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨h0, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    exact div_pos (pow_pos hl n) (by linarith)
  have h2 := (tendsto_inv_nhdsGT_zero.comp h1).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h2.congr (fun N => ?_)
  simp [Function.comp]

/-- Core of: `N σ^{d/2+1}/log N` large and `N/(log N)^{d+2}` large imply
    `N σ^{d/2+1}/(log N (1 + σ log N))` large. -/
theorem log_core {n σ L b : ℝ} (d : ℕ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : 1 ≤ L) (hn : 0 < n)
    (h1 : 2 * b ≤ n * Real.sqrt σ ^ d * σ / L) (h2 : 2 * b ≤ n / L ^ (d + 2)) :
    b ≤ n * Real.sqrt σ ^ d * σ / (L * (1 + σ * L)) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hr0 : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hr1 : Real.sqrt σ ≤ 1 := (Real.sqrt_le_sqrt hσ1).trans_eq Real.sqrt_one
  have hX : 0 ≤ n * Real.sqrt σ ^ d * σ :=
    (mul_pos (mul_pos hn (pow_pos hr0 d)) hσ).le
  have hden0 : 0 < L * (1 + σ * L) := mul_pos hL0 (by nlinarith [mul_pos hσ hL0])
  by_cases h : σ * L ≤ 1
  · have hden : L * (1 + σ * L) ≤ 2 * L := by
      nlinarith [mul_nonneg hL0.le (sub_nonneg.2 h)]
    calc b ≤ n * Real.sqrt σ ^ d * σ / L / 2 := by linarith
      _ = n * Real.sqrt σ ^ d * σ / (2 * L) := by rw [div_div, mul_comm L 2]
      _ ≤ n * Real.sqrt σ ^ d * σ / (L * (1 + σ * L)) :=
          div_le_div_of_nonneg_left hX hden0 hden
  · rw [not_le] at h
    have hσr : σ ≤ Real.sqrt σ := by
      have hr2 : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
      nlinarith [mul_nonneg hr0.le (sub_nonneg.2 hr1)]
    have hsq : 1 / L ≤ Real.sqrt σ :=
      (((div_lt_iff₀ hL0).2 h).le).trans hσr
    have hs : 1 / L ^ d ≤ Real.sqrt σ ^ d := by
      rw [← _root_.one_div_pow]
      exact pow_le_pow_left₀ (div_pos one_pos hL0).le hsq d
    have hden : L * (1 + σ * L) ≤ 2 * σ * L ^ 2 := by
      nlinarith [mul_nonneg hL0.le (by linarith : (0 : ℝ) ≤ σ * L - 1)]
    have hLd : (0 : ℝ) < L ^ d := pow_pos hL0 d
    have e : n / L ^ (d + 2) / 2 = n * (1 / L ^ d) * σ / (2 * σ * L ^ 2) := by
      rw [pow_add]
      field_simp
    calc b ≤ n / L ^ (d + 2) / 2 := by linarith
      _ = n * (1 / L ^ d) * σ / (2 * σ * L ^ 2) := e
      _ ≤ n * Real.sqrt σ ^ d * σ / (2 * σ * L ^ 2) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hn.le) hσ.le)
            (mul_nonneg (mul_nonneg zero_le_two hσ.le) (_root_.sq_nonneg L))
      _ ≤ n * Real.sqrt σ ^ d * σ / (L * (1 + σ * L)) :=
          div_le_div_of_nonneg_left hX hden0 hden

/-! ### Stage 1 (continued): the heat kernel at zero and the smallness condition -/

/-- `M = p_σ(0) ≤ 2^d σ^{-d/2}` for `0 < σ ≤ 1` (written with `(√σ)^d`). -/
theorem heatM_bound {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) :
    heatTorus d (2 * Real.pi ^ 2 * σ) 0 ≤ 2 ^ d / Real.sqrt σ ^ d := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have h0 : (0 : ℝ) ≤ 1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ)) := by positivity
  exact (heatTorus_le hc d 0).trans
    ((pow_le_pow_left₀ h0 (one_add_sqrt_le hσ hσ1) d).trans_eq (div_pow _ _ d))

/-- **The smallness condition follows from the regime.** If `0 < σ_N ≤ 1`, `K_N ≥ 1` eventually and
    `N σ_N^{d/2} / (log N · K_N) → ∞`, then for every constant `C ≥ 0` and every `η > 0`,
    eventually `C √(M_N log N / N) √K_N ≤ η`. -/
theorem eventually_small (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (σ : ℕ → ℝ) (K : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hK : ∀ᶠ N in atTop, 0 < K N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * K N))
      atTop atTop) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
        * Real.sqrt (K N) ≤ η := by
  filter_upwards [hσ, hK, hreg.eventually_ge_atTop (C ^ 2 * 2 ^ d / η ^ 2 + 1),
    eventually_ge_atTop 2] with N h1 h2 h3 h4
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast h4
  exact small_core d hC hη (heatM_bound h1.1 h1.2 d) (pow_pos (Real.sqrt_pos.mpr h1.1) d)
    (Real.log_pos (by linarith)) (by linarith) (by exact_mod_cast h2) h3

/-- Under the regime, `C δ'_N √K_N → 0`. -/
theorem tendsto_small (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (σ : ℕ → ℝ) (K : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hK : ∀ᶠ N in atTop, 0 < K N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * K N))
      atTop atTop) :
    Tendsto (fun N : ℕ =>
      C * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
        * Real.sqrt (K N)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall (fun N => lt_of_lt_of_le ha
      (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))), fun a ha => ?_⟩
  exact (eventually_small d hC σ K hσ hK hreg (half_pos ha)).mono
    (fun N h => lt_of_le_of_lt h (half_lt_self ha))

/-- Under the regime with `J_N ≥ 2`, the tail term `4 M_N / N²` is eventually `≤ η`. -/
theorem eventually_tail_small (d : ℕ) (σ : ℕ → ℝ) (J : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hJ : ∀ᶠ N in atTop, 2 ≤ J N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * J N))
      atTop atTop) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, 4 * heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / (N : ℝ) ^ 2 ≤ η := by
  filter_upwards [hσ, hJ, hreg.eventually_ge_atTop (4 * 2 ^ d / η),
    eventually_ge_atTop 2] with N h1 h2 h3 h4
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast h4
  exact tail_core d hη (heatM_bound h1.1 h1.2 d) (pow_pos (Real.sqrt_pos.mpr h1.1) d)
    (Real.log_le_log (by norm_num) hN) hN (by exact_mod_cast h2) h3

/-- The regime for the concrete choice `K_N = ⌈c/σ_N⌉`: `N σ_N^{d/2+1}/log N → ∞`
    (with `σ = ξ²` this is `N ξ^{d+2}/log N → ∞`) implies the regime of `eventually_small`. -/
theorem regime_ceil (d : ℕ) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d
      / (Real.log N * ((⌈c / σ N⌉₊ : ℕ) : ℝ))) atTop atTop := by
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  refine tendsto_atTop_mono' atTop ?_ (hreg.atTop_div_const hc1)
  filter_upwards [hσ, eventually_ge_atTop 2] with N h1 h4
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast h4
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hσ0 := h1.1
  have hcσ : 0 < c / σ N := div_pos hc hσ0
  have hKpos : (0 : ℝ) < ((⌈c / σ N⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr hcσ
  have hKb : ((⌈c / σ N⌉₊ : ℕ) : ℝ) ≤ (c + 1) / σ N := by
    have h5 := (Nat.ceil_lt_add_one hcσ.le).le
    have h6 : (1 : ℝ) ≤ 1 / σ N := (one_le_div hσ0).mpr h1.2
    have h7 : (c + 1) / σ N = c / σ N + 1 / σ N := by ring
    linarith
  have hX : 0 ≤ (N : ℝ) * Real.sqrt (σ N) ^ d :=
    mul_nonneg (by linarith) (pow_nonneg (Real.sqrt_nonneg _) d)
  have e : (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N / (c + 1)
      = (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * ((c + 1) / σ N)) := by
    field_simp
  show (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N / (c + 1)
      ≤ (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * ((⌈c / σ N⌉₊ : ℕ) : ℝ))
  rw [e]
  exact div_le_div_of_nonneg_left hX (mul_pos hL hKpos) (mul_le_mul_of_nonneg_left hKb hL.le)

/-- `N σ^{d/2+1}/log N → ∞` implies `N σ^{d/2+1}/(log N (1 + σ log N)) → ∞` (the reciprocal of the
    quantity in the bound of the corollary "joint regime, almost surely"). -/
theorem regime_log (d : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N
      / (Real.log N * (1 + σ N * Real.log N))) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [hσ, hreg.eventually_ge_atTop (2 * b),
    (tendsto_nat_div_log_pow (d + 2)).eventually_ge_atTop (2 * b),
    eventually_ge_atTop 3] with N h1 h2 h3 h4
  have hN : (3 : ℝ) ≤ N := by exact_mod_cast h4
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  exact log_core d h1.1 h1.2 hL (by linarith) h2 h3

/-- The regime for the concrete choice `J_N = ⌈3c/σ_N + 2 log N⌉` (trace):
    `N σ^{d/2+1}/(log N (1 + σ log N)) → ∞` implies the regime of `eventually_small` for `J_N`. -/
theorem regime_ceil_trace (d : ℕ) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N
      / (Real.log N * (1 + σ N * Real.log N))) atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d
      / (Real.log N * ((⌈3 * c / σ N + 2 * Real.log N⌉₊ : ℕ) : ℝ))) atTop atTop := by
  have hc1 : (0 : ℝ) < 3 * c + 2 := by linarith
  refine tendsto_atTop_mono' atTop ?_ (hreg.atTop_div_const hc1)
  filter_upwards [hσ, eventually_ge_atTop 2] with N h1 h4
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast h4
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hσ0 := h1.1
  have hcσ : 0 < 3 * c / σ N := div_pos (by linarith) hσ0
  have harg : 0 < 3 * c / σ N + 2 * Real.log N := by linarith
  have hKpos : (0 : ℝ) < ((⌈3 * c / σ N + 2 * Real.log N⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr harg
  have hKb : ((⌈3 * c / σ N + 2 * Real.log N⌉₊ : ℕ) : ℝ)
      ≤ (3 * c + 2) * (1 + σ N * Real.log N) / σ N := by
    have h5 := (Nat.ceil_lt_add_one harg.le).le
    have h6 : (1 : ℝ) ≤ 1 / σ N := (one_le_div hσ0).mpr h1.2
    have h7 : (3 * c + 2) * (1 + σ N * Real.log N) / σ N
        = 3 * c / σ N + 2 * (1 / σ N) + (3 * c + 2) * Real.log N := by
      field_simp
    have h8 : 0 ≤ c * Real.log N := (mul_pos hc hL).le
    rw [h7]
    nlinarith
  have hX : 0 ≤ (N : ℝ) * Real.sqrt (σ N) ^ d :=
    mul_nonneg (by linarith) (pow_nonneg (Real.sqrt_nonneg _) d)
  have h1L : 0 < 1 + σ N * Real.log N := by nlinarith [mul_pos hσ0 hL]
  have e : (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / (Real.log N * (1 + σ N * Real.log N))
        / (3 * c + 2)
      = (N : ℝ) * Real.sqrt (σ N) ^ d
        / (Real.log N * ((3 * c + 2) * (1 + σ N * Real.log N) / σ N)) := by
    field_simp
  show (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / (Real.log N * (1 + σ N * Real.log N))
        / (3 * c + 2)
      ≤ (N : ℝ) * Real.sqrt (σ N) ^ d
        / (Real.log N * ((⌈3 * c / σ N + 2 * Real.log N⌉₊ : ℕ) : ℝ))
  rw [e]
  exact div_le_div_of_nonneg_left hX (mul_pos hL hKpos) (mul_le_mul_of_nonneg_left hKb hL.le)

/-- `J_N = ⌈3c/σ_N + 2 log N⌉ ≥ 2` for `N ≥ 2`. -/
theorem ceil_trace_ge_two (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ ⌈3 * c / σ N + 2 * Real.log N⌉₊ := by
  filter_upwards [hσ, eventually_ge_atTop 2] with N h1 h4
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast h4
  have hl2 := Real.log_two_gt_d9
  have hL : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hcσ : 0 < 3 * c / σ N := div_pos (by linarith) h1.1
  have : ((1 : ℕ) : ℝ) < 3 * c / σ N + 2 * Real.log N := by
    push_cast; linarith
  exact Nat.lt_ceil.mpr this

/-! ### Stage 2: almost sure statements with the regime as the only condition -/

/-- **Kernel estimate, almost surely, regime derived.** Independent uniform points on the flat torus
    of dimension `d ≥ 1`; `σ_N` (kernel variance, `σ = ξ²`) and `K_N` may depend on `N`.
    Conditions on the sequences: eventually `0 < σ_N ≤ 1`, `K_N ≥ 1`, and the REGIME
    `N σ_N^{d/2} / (log N · K_N) → ∞`. Then almost surely, for all large `N`, all `1 ≤ k ≤ K_N` and
    all entries, `|N P^k(a,i) - p_{kσ_N}(x_a - x_i)| ≤ C₁ δ'_N √k m_k`. -/
theorem kernel_theorem_G28_regime {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) (K : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hK : ∀ᶠ N in atTop, 0 < K N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * K N))
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K N → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k) a i
            - heatP d (σ N) k (X a ω - X i ω)|
          ≤ kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
            * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 :=
  AlmostSure.kernel_theorem_G28_ae d hd X h_indep hX hlaw σ K hσ hK
    (eventually_small d (kernelC1_nonneg d) σ K hσ hK hreg one_pos)

/-- **Stage 3, kernel: convergence.** Under the same regime, almost surely: for EVERY `η > 0`, for
    all large `N`, all `1 ≤ k ≤ K_N` and all entries,
    `|N P^k(a,i) - p_{kσ_N}(x_a - x_i)| ≤ η m_k` (`m_k = p_{kσ_N}(0)`): the relative error, uniformly
    in `k ≤ K_N` and the entries, tends to zero. No rate is claimed. -/
theorem kernel_theorem_G28_regime_tendsto {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) (K : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hK : ∀ᶠ N in atTop, 0 < K N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * K N))
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K N → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k) a i
            - heatP d (σ N) k (X a ω - X i ω)|
          ≤ η * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 := by
  filter_upwards [kernel_theorem_G28_regime d hd X h_indep hX hlaw σ K hσ hK hreg] with ω hω
  intro η hη
  filter_upwards [hω, eventually_small d (kernelC1_nonneg d) σ K hσ hK hreg hη, hσ]
    with N h1 h2 h3 k hk1 hk2 a i
  refine (h1 k hk1 hk2 a i).trans ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hσ0 := h3.1
  have hm : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 :=
    (heatTorus_zero_pos (by positivity) d).le
  have hkK : Real.sqrt (k : ℝ) ≤ Real.sqrt (K N) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hk2)
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hkK
      (mul_nonneg (kernelC1_nonneg d) (Real.sqrt_nonneg _))).trans h2) hm

/-- **Kernel, concrete step range `K_N = ⌈c/σ_N⌉`.** For fixed `c > 0`: if eventually `0 < σ_N ≤ 1`
    and `N σ_N^{d/2+1} / log N → ∞` (with `σ = ξ²`: `N ξ^{d+2}/log N → ∞`), then almost surely, for
    every `η > 0`, for all large `N`, all `1 ≤ k ≤ ⌈c/σ_N⌉` and all entries, both
    `|N P^k(a,i) - p_k| ≤ C₁ δ'_N √k m_k` and `|N P^k(a,i) - p_k| ≤ η m_k`. -/
theorem kernel_theorem_G28_regime_ceil {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ ⌈c / σ N⌉₊ →
      ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k) a i
            - heatP d (σ N) k (X a ω - X i ω)|
          ≤ kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
            * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0
        ∧ |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k) a i
            - heatP d (σ N) k (X a ω - X i ω)|
          ≤ η * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 := by
  have hK : ∀ᶠ N in atTop, 0 < ⌈c / σ N⌉₊ := by
    filter_upwards [hσ] with N h1
    exact Nat.ceil_pos.mpr (div_pos hc h1.1)
  have hreg' := regime_ceil d σ hc hσ hreg
  filter_upwards [kernel_theorem_G28_regime d hd X h_indep hX hlaw σ (fun N => ⌈c / σ N⌉₊)
      hσ hK hreg',
    kernel_theorem_G28_regime_tendsto d hd X h_indep hX hlaw σ (fun N => ⌈c / σ N⌉₊)
      hσ hK hreg'] with ω hω1 hω2
  intro η hη
  filter_upwards [hω1, hω2 η hη] with N h1 h2 k hk1 hk2 a i
  exact ⟨h1 k hk1 hk2 a i, h2 k hk1 hk2 a i⟩

/-- **Subtracted heat trace, almost surely, regime derived, with convergence.** Conditions on the
    sequences: eventually `0 < σ_N ≤ 1`, `J_N ≥ 2`, and `N σ_N^{d/2} / (log N · J_N) → ∞`. Then
    almost surely, for every `η > 0`, for all large `N` and ALL `τ ≥ 2` with
    `3τ + 2 log N ≤ J_N + 1` (EMPTY unless `J_N ≥ 5 + 2 log N`):
    `|(Tr exp(τ(S-1)) - N e^{-τ})/T(τ) - 1| ≤ C₁ δ'_N √J_N + 4 M_N/N²` and the right-hand side
    is `≤ η`. -/
theorem heat_trace_G29_regime {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) (J : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hJ : ∀ᶠ N in atTop, 2 ≤ J N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * J N))
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
      ∀ τ : ℝ, 2 ≤ τ → 3 * τ + 2 * Real.log N ≤ (J N : ℝ) + 1 →
        |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d (σ N) τ - 1|
          ≤ kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
              * Real.sqrt (J N)
            + 4 * heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / (N : ℝ) ^ 2
        ∧ kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
              * Real.sqrt (J N)
            + 4 * heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / (N : ℝ) ^ 2 ≤ η := by
  have hJ0 : ∀ᶠ N in atTop, 0 < J N := hJ.mono (fun N h => by omega)
  filter_upwards [AlmostSure.heat_trace_G29_ae d hd X h_indep hX hlaw σ J hσ hJ
    (eventually_small d (kernelC1_nonneg d) σ J hσ hJ0 hreg one_pos)] with ω hω
  intro η hη
  filter_upwards [hω, eventually_small d (kernelC1_nonneg d) σ J hσ hJ0 hreg (half_pos hη),
    eventually_tail_small d σ J hσ hJ hreg (half_pos hη)] with N h1 h2 h3 τ hτ1 hτ2
  exact ⟨h1 τ hτ1 hτ2, by linarith⟩

/-- **Subtracted heat trace, concrete `J_N = ⌈3c/σ_N + 2 log N⌉`.** For fixed `c > 0`: if eventually
    `0 < σ_N ≤ 1` and `N σ_N^{d/2+1} / log N → ∞` (with `σ = ξ²`: `N ξ^{d+2}/log N → ∞`), then
    almost surely, for every `η > 0`, for all large `N` and all `τ` with `2 ≤ τ ≤ c/σ_N`:
    `|(Tr exp(τ(S-1)) - N e^{-τ})/T(τ) - 1| ≤ η`. -/
theorem heat_trace_G29_regime_ceil {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
      ∀ τ : ℝ, 2 ≤ τ → τ ≤ c / σ N →
        |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d (σ N) τ - 1| ≤ η := by
  have hreg' := regime_ceil_trace d σ hc hσ (regime_log d σ hσ hreg)
  filter_upwards [heat_trace_G29_regime d hd X h_indep hX hlaw σ
    (fun N => ⌈3 * c / σ N + 2 * Real.log N⌉₊) hσ (ceil_trace_ge_two σ hc hσ) hreg'] with ω hω
  intro η hη
  filter_upwards [hω η hη, hσ] with N h1 h3 τ hτ1 hτ2
  have hσ0 := h3.1
  have h5 : 3 * τ ≤ 3 * c / σ N := by
    have : 3 * c / σ N = 3 * (c / σ N) := by ring
    linarith
  have h6 := Nat.le_ceil (3 * c / σ N + 2 * Real.log N)
  have key : 3 * τ + 2 * Real.log N
      ≤ ((⌈3 * c / σ N + 2 * Real.log N⌉₊ : ℕ) : ℝ) + 1 := by linarith
  have h7 := h1 τ hτ1 key
  exact h7.1.trans h7.2

/-- **Eigenvalues, part (i), almost surely, regime derived, with a bound `η · m_k` (small RELATIVE TO
    `m_k = p_{kσ}(0)`; not convergence of the eigenvalues, and trivial as long as `η m_k ≥ 1`).** Conditions on the
    sequences: eventually `0 < σ_N ≤ 1`, `K_N ≥ 1`, and `N σ_N^{d/2} / (log N · K_N) → ∞`. Then
    almost surely, for every `η > 0`, for all large `N`, all `1 ≤ k ≤ K_N` and all indices `j`
    (counted from zero): `s_0 = 1`, and for `j ≥ 1`, with `q = shellIndex d j`,
    `|s_j^k - e^{-k 2π²σ_N q}| ≤ C₃ δ'_N √k m_k` and `C₃ δ'_N √k m_k ≤ η m_k`. -/
theorem eig_theorem_G38_i_regime {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) (K : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hK : ∀ᶠ N in atTop, 0 < K N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d / (Real.log N * K N))
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K N →
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
                * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0
            ∧ eigC3 d
                * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
                * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0
              ≤ η * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0) := by
  filter_upwards [AlmostSure.eig_theorem_G38_i_ae d hd X h_indep hX hlaw σ K hσ hK
    (eventually_small d (kernelC1_nonneg d) σ K hσ hK hreg one_pos)] with ω hω
  intro η hη
  filter_upwards [hω, eventually_small d (eigC3_nonneg d) σ K hσ hK hreg hη, hσ]
    with N h1 h2 h3 k hk1 hk2 hS j
  refine ⟨(h1 k hk1 hk2 hS j).1, fun hj => ⟨(h1 k hk1 hk2 hS j).2 hj, ?_⟩⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hσ0 := h3.1
  have hm : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 :=
    (heatTorus_zero_pos (by positivity) d).le
  have hkK : Real.sqrt (k : ℝ) ≤ Real.sqrt (K N) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hk2)
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hkK
      (mul_nonneg (eigC3_nonneg d) (Real.sqrt_nonneg _))).trans h2) hm

/-- **Eigenvalues (i), concrete `K_N = ⌈c/σ_N⌉`**, under `N σ_N^{d/2+1}/log N → ∞`. -/
theorem eig_theorem_G38_i_regime_ceil {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ ⌈c / σ N⌉₊ →
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
                * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0
            ∧ eigC3 d
                * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
                * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0
              ≤ η * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0) := by
  have hK : ∀ᶠ N in atTop, 0 < ⌈c / σ N⌉₊ := by
    filter_upwards [hσ] with N h1
    exact Nat.ceil_pos.mpr (div_pos hc h1.1)
  exact eig_theorem_G38_i_regime d hd X h_indep hX hlaw σ (fun N => ⌈c / σ N⌉₊) hσ hK
    (regime_ceil d σ hc hσ hreg)



end Regime

/-! ## The second stage for a fixed sample size: reduction and the bound for `Π_k` combined.
No Poisson summation, no statement on the heat trace, no limit. -/

/-! ## The second stage in probability, finite form: the reduction (`H5.torus_reduction_paper`)
combined with Markov's inequality for `Π_k` (`PiBound.pi_markov`), for a FIXED sample size `N`.
Statements for each step number `k` separately (indices `j = k + 1 ≥ 2` of `Tr P^j`; the term
`j = 1` is not covered here). The paper does NOT take a union over `k`: it sums the expectations with
Poisson weights and applies Markov once (see `SecondStageTrace` below). The Poisson
summation and the statement about the heat trace are NOT formalised here. -/

namespace SecondStage

open CTG.Reals.TorusReduction TorusReductionL1 H5 PiBound

/-- Abstract step: if `|f - g| ≤ B` except with probability `p1` and `|g| ≥ t` has probability
    at most `p2`, then `|f| > B + t` has probability at most `p1 + p2`. No measurability needed. -/
theorem union_markov {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (f g : Ω → ℝ) {B t p1 p2 : ℝ}
    (h1 : μ.real {ω | ¬ |f ω - g ω| ≤ B} ≤ p1) (h2 : μ.real {ω | t ≤ |g ω|} ≤ p2) :
    μ.real {ω | B + t < |f ω|} ≤ p1 + p2 := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _))
    ((measureReal_union_le _ _).trans (add_le_add h1 h2))
  intro ω hω
  have hω' : B + t < |f ω| := hω
  by_cases h : |f ω - g ω| ≤ B
  · refine Or.inr ?_
    show t ≤ |g ω|
    have c := abs_sub_abs_le_abs_sub (f ω) (g ω)
    linarith
  · exact Or.inl h

/-- The same for finitely many indices `1 ≤ k ≤ K` with ONE exceptional event for the first
    hypothesis: the probability `p1` is paid once, the Markov terms are summed. -/
theorem union_markov_fin {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    (K : ℕ) (f g : ℕ → Ω → ℝ) (B t p2 : ℕ → ℝ) {p1 : ℝ}
    (h1 : μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K → |f k ω - g k ω| ≤ B k} ≤ p1)
    (h2 : ∀ k, 1 ≤ k → k ≤ K → μ.real {ω | t k ≤ |g k ω|} ≤ p2 k) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K → |f k ω| ≤ B k + t k}
      ≤ p1 + ∑ k ∈ Finset.Icc 1 K, p2 k := by
  have hU : μ.real (⋃ k ∈ Finset.Icc 1 K, {ω | t k ≤ |g k ω|})
      ≤ ∑ k ∈ Finset.Icc 1 K, p2 k :=
    (measureReal_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun k hk => h2 k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _))
    ((measureReal_union_le _ _).trans (add_le_add h1 hU))
  intro ω hω
  have hω' : ¬ ∀ k, 1 ≤ k → k ≤ K → |f k ω| ≤ B k + t k := hω
  by_cases h : ∀ k, 1 ≤ k → k ≤ K → |f k ω - g k ω| ≤ B k
  · refine Or.inr ?_
    by_contra hno
    apply hω'
    intro k hk hkK
    by_contra hlt
    apply hno
    refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk, hkK⟩, ?_⟩
    show t k ≤ |g k ω|
    have c := abs_sub_abs_le_abs_sub (f k ω) (g k ω)
    have a := h k hk hkK
    have b := not_le.mp hlt
    linarith
  · exact Or.inl h

/-- The constant of the reduction `H5.torus_reduction_paper` (depends only on `d`). -/
noncomputable def redC (d : ℕ) : ℝ :=
  (Real.sqrt 2) ^ d
    * (2 * (4 * normC d) * kernelC1 d + 2 * (14 * normC d ^ 2) + h5Ca d
        + 2 * (2 * (Real.sqrt 2) ^ d * h5Ca d + h5Ca d
            + (Real.sqrt 2) ^ d * kernelC1 d * h5Cb d + h4C d * h5Cb d))

/-- `redC d` is the constant written out in `H5.torus_reduction_paper`. -/
theorem redC_eq (d : ℕ) :
    redC d = (Real.sqrt 2) ^ d
      * (2 * (4 * normC d) * kernelC1 d + 2 * (14 * normC d ^ 2) + h5Ca d
          + 2 * (2 * (Real.sqrt 2) ^ d * h5Ca d + h5Ca d
              + (Real.sqrt 2) ^ d * kernelC1 d * h5Cb d + h4C d * h5Cb d)) := rfl

/-- `H5.torus_reduction_paper` with the constant named `redC d`. -/
theorem torus_reduction_redC {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)
            - torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|
          ≤ redC d * δp ^ 2 * k * torusM d σ (k + 1)}
      ≤ 8 / (N : ℝ) ^ 3 := by
  unfold redC
  exact torus_reduction_paper hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange

/-- Consequences of the smallness hypothesis of `kernel_theorem_G28`: `1 ≤ M`, `1152 M ≤ N`
    (in particular `M ≤ N`), `δ' ≥ 0`, `δ'² = M log N / N` and `log N ≥ 1/2`.
    (`kernelC1 d ≥ 48` and `√K ≥ 1` give `δ' ≤ 1/48`.) -/
theorem ss_setup {σ : ℝ} (hσ : 0 < σ) (d N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K) {Mp δp : ℝ}
    (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    1 ≤ Mp ∧ 1152 * Mp ≤ N ∧ 0 ≤ δp ∧ δp ^ 2 = Mp * Real.log N / N
      ∧ (1 / 2 : ℝ) ≤ Real.log N := by
  have hpi := Real.pi_pos
  have hM1 : 1 ≤ Mp := by
    rw [hMp]; exact heatTorus_zero_ge_one (by positivity) d
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log N := by
    have h1 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
    have h2 := Real.log_two_gt_d9
    linarith
  have hδ0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hnn : 0 ≤ Mp * Real.log N / N :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hNpos.le
  have hsq : δp ^ 2 = Mp * Real.log N / N := by rw [hδp]; exact Real.sq_sqrt hnn
  have hr : (48 : ℝ) ≤ rateCfin3 d := by
    have h := (rateCfin3_ge d).1
    have h1 : (1 : ℝ) ≤ Real.sqrt (3 * (d : ℝ) + 5) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (3 * (d : ℝ) + 5) :=
          Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
    linarith
  have hC : (48 : ℝ) ≤ kernelC1 d := by
    unfold kernelC1
    have hA : (1 : ℝ) ≤ ((1 + Real.sqrt (2 * Real.pi)) ^ d) ^ 2 :=
      one_le_pow₀ (one_le_pow₀ (by linarith [Real.sqrt_nonneg (2 * Real.pi)]))
    calc (48 : ℝ) = 48 * 1 := by norm_num
      _ ≤ rateCfin3 d * ((1 + Real.sqrt (2 * Real.pi)) ^ d) ^ 2 :=
        mul_le_mul hr hA zero_le_one (by linarith)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hK
  have hsK : (1 : ℝ) ≤ Real.sqrt K := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hK1
  have hδ48 : δp ≤ 1 / 48 := by
    have h1 : 48 * δp ≤ kernelC1 d * δp := mul_le_mul_of_nonneg_right hC hδ0
    have h2 : kernelC1 d * δp * 1 ≤ kernelC1 d * δp * Real.sqrt K :=
      mul_le_mul_of_nonneg_left hsK (mul_nonneg (by linarith) hδ0)
    linarith
  have hmm : δp * δp ≤ 1 / 48 * (1 / 48) := mul_le_mul hδ48 hδ48 hδ0 (by norm_num)
  have hsq48 : δp ^ 2 ≤ 1 / 2304 := by
    calc δp ^ 2 = δp * δp := pow_two δp
      _ ≤ 1 / 48 * (1 / 48) := hmm
      _ = 1 / 2304 := by norm_num
  rw [hsq] at hsq48
  have h3 : Mp * Real.log N ≤ 1 / 2304 * N := (div_le_iff₀ hNpos).mp hsq48
  have h4 : Mp * (1 / 2) ≤ Mp * Real.log N := mul_le_mul_of_nonneg_left hlog (by linarith)
  refine ⟨hM1, by linarith, hδ0, hsq, hlog⟩

/-- Markov's inequality for `Π_k` at the threshold `s · (M/N) · k · m_k`: probability `≤ C_Π/s`. -/
theorem pi_markov_scaled {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) (hk : 1 ≤ k)
    (N : ℕ) (hN : 1 ≤ N) {Mp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hMN : Mp ≤ N) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | s * (Mp / N * k * torusM d σ k)
        ≤ |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|}
      ≤ piC d / s := by
  have hpi := Real.pi_pos
  have hM1e : torusM d σ 1 = Mp := by rw [hMp]; unfold torusM; simp
  have hM1 : 1 ≤ Mp := by rw [hMp]; exact heatTorus_zero_ge_one (by positivity) d
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hmk : 1 ≤ torusM d σ k := by
    unfold torusM
    exact heatTorus_zero_ge_one (mul_pos (by positivity) (mul_pos hkpos hσ)) d
  have hu : 0 < Mp / N * k * torusM d σ k :=
    mul_pos (mul_pos (div_pos (by linarith) hNpos) hkpos) (by linarith)
  have h := pi_markov X h_indep hX hlaw hσ k hk N hN (by rw [hM1e]; exact hMN)
    (s * (Mp / N * k * torusM d σ k)) (mul_pos hs hu)
  rw [hM1e] at h
  have e : piC d * (Mp / N) * k * torusM d σ k / (s * (Mp / N * k * torusM d σ k))
      = piC d / s := by
    rw [show piC d * (Mp / N) * k * torusM d σ k = piC d * (Mp / N * k * torusM d σ k) by ring]
    exact mul_div_mul_right _ _ hu.ne'
  rw [e] at h
  exact h

/-- Arithmetic: the Markov threshold against `δ'² k m_{k+1}`. -/
theorem ss_term {s u δ2 κ mk m1 A : ℝ} (hs : 0 ≤ s) (hu2 : u ≤ 2 * δ2) (hκ : 0 ≤ κ)
    (hmk : 0 ≤ mk) (hr : mk ≤ A * m1) (hδ2 : 0 ≤ δ2) :
    s * (u * κ * mk) ≤ 2 * s * A * δ2 * κ * m1 := by
  have a1 : u * κ * mk ≤ 2 * δ2 * κ * (A * m1) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hu2 hκ) hr hmk
      (mul_nonneg (mul_nonneg (by norm_num) hδ2) hκ)
  calc s * (u * κ * mk) ≤ s * (2 * δ2 * κ * (A * m1)) := mul_le_mul_of_nonneg_left a1 hs
    _ = 2 * s * A * δ2 * κ * m1 := by ring

/-- The threshold `B_k + t_k` of the scaled form is at most `(C_red + 2 s (√2)^d) δ'² k m_{k+1}`. -/
theorem ss_threshold {σ : ℝ} (hσ : 0 < σ) (d N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K) {Mp δp : ℝ}
    (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 0 < s) :
    redC d * δp ^ 2 * k * torusM d σ (k + 1) + s * (Mp / N * k * torusM d σ k)
      ≤ (redC d + 2 * s * (Real.sqrt 2) ^ d) * δp ^ 2 * k * torusM d σ (k + 1) := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N K hN2 hK hMp hδp hrange
  have hpi := Real.pi_pos
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hmk : 1 ≤ torusM d σ k := by
    unfold torusM
    exact heatTorus_zero_ge_one (mul_pos (by positivity) (mul_pos hkpos hσ)) d
  have hMN0 : 0 ≤ Mp / N := div_nonneg (by linarith) hNpos.le
  have e1 : Mp / N ≤ 2 * δp ^ 2 := by
    rw [hsq]
    have h1 : Mp / N * (1 / 2) ≤ Mp / N * Real.log N := mul_le_mul_of_nonneg_left hlog hMN0
    have h2 : Mp * Real.log N / N = Mp / N * Real.log N := by ring
    rw [h2]; linarith
  have hratio : torusM d σ k ≤ (Real.sqrt 2) ^ d * torusM d σ (k + 1) :=
    torusM_ratio hσ d hk (Nat.le_succ k) (by omega)
  have h := ss_term (s := s) (u := Mp / N) (δ2 := δp ^ 2) (κ := (k : ℝ))
    (mk := torusM d σ k) (m1 := torusM d σ (k + 1)) (A := (Real.sqrt 2) ^ d)
    hs.le e1 hkpos.le (by linarith) hratio (pow_nonneg hδ0 2)
  have e : (redC d + 2 * s * (Real.sqrt 2) ^ d) * δp ^ 2 * k * torusM d σ (k + 1)
      = redC d * δp ^ 2 * k * torusM d σ (k + 1)
        + 2 * s * (Real.sqrt 2) ^ d * δp ^ 2 * k * torusM d σ (k + 1) := by ring
  rw [e]; linarith

/-- **The second stage for one `k`, finite form.** Under the hypotheses of
    `H5.torus_reduction_paper` (those of `kernel_theorem_G28`), for fixed `1 ≤ k ≤ K` and `t > 0`:
    `P(|Tr P^{k+1} - m_{k+1}| > C_red δ'² k m_{k+1} + t) ≤ 8/N³ + C_Π (M/N) k m_k / t`.
    (`M ≤ N`, needed by `pi_markov`, follows from the smallness hypothesis: `ss_setup`.) -/
theorem second_stage_k {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | redC d * δp ^ 2 * k * torusM d σ (k + 1) + t
        < |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)|}
      ≤ 8 / (N : ℝ) ^ 3 + piC d * (Mp / N) * k * torusM d σ k / t := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N K hN2 hK hMp hδp hrange
  have hM1e : torusM d σ 1 = Mp := by rw [hMp]; unfold torusM; simp
  have h0 := torus_reduction_redC hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have h1 : μ.real {ω | ¬ |(((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace
          - torusM d σ (k + 1))
          - torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|
        ≤ redC d * δp ^ 2 * k * torusM d σ (k + 1)} ≤ 8 / (N : ℝ) ^ 3 := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h0
    intro ω hω hall
    exact hω (hall k hk hkK)
  have h2 := pi_markov X h_indep hX hlaw hσ k hk N (by omega)
    (by rw [hM1e]; linarith) t ht
  rw [hM1e] at h2
  exact union_markov (μ := μ)
    (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1))
    (fun ω => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))) h1 h2

/-- **The second stage for one `k`, scaled threshold** `t = s (M/N) k m_k`: probability
    `≤ 8/N³ + C_Π/s`. -/
theorem second_stage_k_scaled {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | redC d * δp ^ 2 * k * torusM d σ (k + 1) + s * (Mp / N * k * torusM d σ k)
        < |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)|}
      ≤ 8 / (N : ℝ) ^ 3 + piC d / s := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N K hN2 hK hMp hδp hrange
  have h0 := torus_reduction_redC hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have h1 : μ.real {ω | ¬ |(((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace
          - torusM d σ (k + 1))
          - torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|
        ≤ redC d * δp ^ 2 * k * torusM d σ (k + 1)} ≤ 8 / (N : ℝ) ^ 3 := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h0
    intro ω hω hall
    exact hω (hall k hk hkK)
  have h2 := pi_markov_scaled X h_indep hX hlaw hσ k hk N (by omega) hMp (by linarith) s hs
  exact union_markov (μ := μ)
    (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1))
    (fun ω => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))) h1 h2

/-- **The second stage for one `k`, relative form:** for `s > 0`,
    `P(|Tr P^{k+1} - m_{k+1}| > (C_red + 2 s (√2)^d) δ'² k m_{k+1}) ≤ 8/N³ + C_Π/s`,
    with `δ'² = M log N / N`. -/
theorem second_stage_k_rel {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1)
    (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ K) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | (redC d + 2 * s * (Real.sqrt 2) ^ d) * δp ^ 2 * k * torusM d σ (k + 1)
        < |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)|}
      ≤ 8 / (N : ℝ) ^ 3 + piC d / s := by
  have h := second_stage_k_scaled hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
    k hk hkK s hs
  have hle := ss_threshold hσ d N K hN2 hK hMp hδp hrange k hk s hs
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω
  have hω' : (redC d + 2 * s * (Real.sqrt 2) ^ d) * δp ^ 2 * k * torusM d σ (k + 1)
      < |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)| := hω
  exact lt_of_le_of_lt hle hω'

/-- **The second stage for all `1 ≤ k ≤ K` on one event, general thresholds:** the reduction
    event is paid once (`8/N³`), the Markov terms are summed over `k`. -/
theorem second_stage_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1)
    (t : ℕ → ℝ) (ht : ∀ k, 1 ≤ k → k ≤ K → 0 < t k) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)|
          ≤ redC d * δp ^ 2 * k * torusM d σ (k + 1) + t k}
      ≤ 8 / (N : ℝ) ^ 3
        + ∑ k ∈ Finset.Icc 1 K, piC d * (Mp / N) * k * torusM d σ k / t k := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N K hN2 hK hMp hδp hrange
  have hM1e : torusM d σ 1 = Mp := by rw [hMp]; unfold torusM; simp
  have h0 := torus_reduction_redC hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have h2 : ∀ k, 1 ≤ k → k ≤ K →
      μ.real {ω | t k ≤ |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|}
        ≤ piC d * (Mp / N) * k * torusM d σ k / t k := by
    intro k hk hkK
    have h := pi_markov X h_indep hX hlaw hσ k hk N (by omega)
      (by rw [hM1e]; linarith) (t k) (ht k hk hkK)
    rw [hM1e] at h
    exact h
  exact union_markov_fin (μ := μ) K
    (fun k ω => ((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1))
    (fun k ω => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)))
    (fun k => redC d * δp ^ 2 * k * torusM d σ (k + 1)) t
    (fun k => piC d * (Mp / N) * k * torusM d σ k / t k) h0 h2

/-- **The second stage for all `1 ≤ k ≤ K` on one event, relative form** (a union over `k`, which
    costs the factor `K` in the probability; NOT the route of `cor:secondstage-alld`, which applies
    Markov once to the weighted sum): for `s > 0`,
    `P(∃ 1 ≤ k ≤ K: |Tr P^{k+1} - m_{k+1}| > (C_red + 2 s (√2)^d) δ'² k m_{k+1}) ≤ 8/N³ + K C_Π/s`. -/
theorem second_stage_all_rel {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)|
          ≤ (redC d + 2 * s * (Real.sqrt 2) ^ d) * δp ^ 2 * k * torusM d σ (k + 1)}
      ≤ 8 / (N : ℝ) ^ 3 + K * (piC d / s) := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N K hN2 hK hMp hδp hrange
  have h0 := torus_reduction_redC hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have h2 : ∀ k, 1 ≤ k → k ≤ K →
      μ.real {ω | s * (Mp / N * k * torusM d σ k)
          ≤ |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|}
        ≤ piC d / s := fun k hk _ =>
    pi_markov_scaled X h_indep hX hlaw hσ k hk N (by omega) hMp (by linarith) s hs
  have h := union_markov_fin (μ := μ) K
    (fun k ω => ((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1))
    (fun k ω => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)))
    (fun k => redC d * δp ^ 2 * k * torusM d σ (k + 1))
    (fun k => s * (Mp / N * k * torusM d σ k))
    (fun _ => piC d / s) h0 h2
  have hsum : ∑ _k ∈ Finset.Icc 1 K, piC d / s = K * (piC d / s) := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  rw [hsum] at h
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hall
  apply hω
  intro k hk hkK
  exact (hall k hk hkK).trans
    (ss_threshold hσ d N K hN2 hK hMp hδp hrange k hk s hs)

end SecondStage

/-! ## The Poisson summation of the second stage, finite form (`cor:secondstage-alld` for a FIXED
sample size `N`): the reduction (`H5.torus_reduction_paper`, constant `SecondStage.redC`) is summed
with the Poisson weights `w_{k+1}(τ)` on its event, the index `j = 1` is taken from the first stage
(`kernel_trace_G28`), the indices `j > J + 1` are the Poisson tail (as in `heat_trace_G29`), and
Markov's inequality is applied ONCE to the weighted sum `∑_k w_{k+1}(τ) |Π_k|`, whose mean is
bounded by `PiBound.pi_bound` and linearity.  No limit `N → ∞` and no statement `o_P(ξ²)` is
formalised here.

NOTE on the index `j = 1`: in this section it is bounded by the FIRST stage, i.e. in first order
in `δ'` (term `C₁ δ' · w_1 M / T` in `second_stage_trace_rel`), whereas the proof in the paper treats
it in second order.  The inequality of `second_stage_trace_rel` therefore implies the `o(ξ²)` part of
`cor:secondstage-alld` under `N ξ^(d+4)/log N → ∞` (as an inequality for fixed `N`), but NOT the first
display of that corollary.  The second-order treatment of `j = 1` is in `SecondStageTrace2` below. -/

namespace SecondStageTrace

open CTG.Reals.TorusReduction CTG.Reals.TraceG29 TorusReductionL1 H5 PiBound SecondStage

/-! ### elementary steps -/

/-- Shift of a sum over `1 ≤ k ≤ J` to a sum over `j < J`. -/
theorem sum_Icc_shift (J : ℕ) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 J, F k = ∑ j ∈ Finset.range J, F (j + 1) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `(k + 1) w_{k+1}(τ) = τ w_k(τ)` for the Poisson weights. -/
theorem pw_step (τ : ℝ) (k : ℕ) : pw τ (k + 1) * ((k : ℝ) + 1) = τ * pw τ k := by
  have hk : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have key : ∀ a b f : ℝ, b ≠ 0 → a / (b * f) * b = a / f := by
    intro a b f hb
    rw [div_mul_eq_mul_div, mul_comm a b, mul_div_mul_left _ _ hb]
  unfold pw
  rw [hk, pow_succ]
  calc Real.exp (-τ) * (τ ^ k * τ / (((k : ℝ) + 1) * (k.factorial : ℝ))) * ((k : ℝ) + 1)
      = Real.exp (-τ) * (τ ^ k * τ / (((k : ℝ) + 1) * (k.factorial : ℝ)) * ((k : ℝ) + 1)) := by
        ring
    _ = Real.exp (-τ) * (τ ^ k * τ / (k.factorial : ℝ)) := by rw [key _ _ _ hk1]
    _ = τ * (Real.exp (-τ) * (τ ^ k / (k.factorial : ℝ))) := by ring

/-- `k w_{k+1}(τ) ≤ τ w_k(τ)` for `τ ≥ 0`. -/
theorem pw_step_le {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ) : pw τ (k + 1) * (k : ℝ) ≤ τ * pw τ k := by
  have e := pw_step τ k
  have w0 := pw_nonneg hτ (k + 1)
  have e2 : pw τ (k + 1) * ((k : ℝ) + 1) = pw τ (k + 1) * (k : ℝ) + pw τ (k + 1) := by ring
  linarith

theorem pw_pos {τ : ℝ} (hτ : 0 < τ) (j : ℕ) : 0 < pw τ j :=
  mul_pos (Real.exp_pos _) (div_pos (pow_pos hτ j) (Nat.cast_pos.mpr (Nat.factorial_pos j)))

/-- The constant of the reduction is nonnegative. -/
theorem redC_nonneg (d : ℕ) : 0 ≤ redC d := by
  obtain ⟨ha, hb⟩ := h5C_nonneg d
  have hn := normC_nonneg d
  have hk := kernelC1_nonneg d
  have h4 := h4C_nonneg d
  have hs : (0 : ℝ) ≤ (Real.sqrt 2) ^ d := pow_nonneg (Real.sqrt_nonneg 2) d
  have a1 := mul_nonneg hn hk
  have a2 := pow_nonneg hn 2
  have a3 := mul_nonneg hs ha
  have a4 := mul_nonneg (mul_nonneg hs hk) hb
  have a5 := mul_nonneg h4 hb
  unfold redC
  refine mul_nonneg hs ?_
  linarith

theorem piC_pos (d : ℕ) : 0 < piC d := by
  have hs : (0 : ℝ) ≤ Real.sqrt 2 ^ d := pow_nonneg (Real.sqrt_nonneg 2) d
  unfold piC
  linarith

/-! ### Stage 1: the deterministic summation -/

/-- Splitting of a Poisson mean with ABSOLUTE errors `E_j` for `1 ≤ j ≤ J` (from
    `TraceG29.poisson_split`). HYPOTHESES: the two sums exist (`hA`, `hT`). -/
theorem poisson_split_abs {τ : ℝ} (hτ : 0 ≤ τ) (a m E : ℕ → ℝ) (J : ℕ) {A T B B' : ℝ}
    (hA : HasSum (fun j : ℕ => pw τ (j + 1) * a (j + 1)) A)
    (hT : HasSum (fun j : ℕ => pw τ (j + 1) * m (j + 1)) T)
    (hm : ∀ j, 1 ≤ j → 0 < m j)
    (hlow : ∀ j, 1 ≤ j → j ≤ J → |a j - m j| ≤ E j)
    (hB : ∀ j, J < j → |a j| ≤ B) (hB' : ∀ j, J < j → |m j| ≤ B') :
    |A - T| ≤ ∑ j ∈ Finset.range J, pw τ (j + 1) * E (j + 1) + (B + B') * ptail τ J := by
  have hlow' : ∀ j, 1 ≤ j → j ≤ J → |a j - m j| ≤ E j / m j * m j := by
    intro j hj hjJ
    rw [div_mul_cancel₀ _ (hm j hj).ne']
    exact hlow j hj hjJ
  have h : |A - T| ≤ ∑ j ∈ Finset.range J, pw τ (j + 1) * (E (j + 1) / m (j + 1) * m (j + 1))
      + (B + B') * ptail τ J :=
    poisson_split hτ a m (fun j => E j / m j) J hA hT hlow' hB hB'
  have e : ∑ j ∈ Finset.range J, pw τ (j + 1) * (E (j + 1) / m (j + 1) * m (j + 1))
      = ∑ j ∈ Finset.range J, pw τ (j + 1) * E (j + 1) :=
    Finset.sum_congr rfl (fun j _ => by rw [div_mul_cancel₀ _ (hm (j + 1) (by omega)).ne'])
  rw [e] at h
  exact h

/-- **The Poisson summation of the second stage, abstract form.** `τ ≥ 0`; sequences `a_j`,
    `m_j > 0`, `Π_k`; first stage at `j = 1`: `|a_1 - m_1| ≤ c m_1`; second stage
    `|a_{k+1} - m_{k+1} - Π_k| ≤ R k m_{k+1}` for `1 ≤ k ≤ J`; bounds `B`, `B'` beyond `J + 1`. Then
    `|∑ w_j a_j - ∑ w_j m_j| ≤ c w_1 m_1 + R ∑_{k=1}^J w_{k+1} k m_{k+1} + ∑_{k=1}^J w_{k+1} |Π_k|
      + (B + B') (1 - ∑_{j ≤ J+1} w_j)`.
    HYPOTHESES: the two sums exist (`hA`, `hT`). -/
theorem poisson_split_second {τ : ℝ} (hτ : 0 ≤ τ) (a m Pi : ℕ → ℝ) (J : ℕ) {A T B B' c R : ℝ}
    (hA : HasSum (fun j : ℕ => pw τ (j + 1) * a (j + 1)) A)
    (hT : HasSum (fun j : ℕ => pw τ (j + 1) * m (j + 1)) T)
    (hm : ∀ j, 1 ≤ j → 0 < m j)
    (h1 : |a 1 - m 1| ≤ c * m 1)
    (hred : ∀ k : ℕ, 1 ≤ k → k ≤ J → |a (k + 1) - m (k + 1) - Pi k| ≤ R * (k : ℝ) * m (k + 1))
    (hB : ∀ j, J + 1 < j → |a j| ≤ B) (hB' : ∀ j, J + 1 < j → |m j| ≤ B') :
    |A - T| ≤ c * (pw τ 1 * m 1)
        + R * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * m (k + 1))
        + ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * |Pi k|
        + (B + B') * ptail τ (J + 1) := by
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ, E = fun j : ℕ =>
      if j = 1 then c * m 1 else R * ((j - 1 : ℕ) : ℝ) * m j + |Pi (j - 1)| := ⟨_, rfl⟩
  have hE1 : E 1 = c * m 1 := by
    subst hE
    exact if_pos (rfl : (1 : ℕ) = 1)
  have hE2 : ∀ k : ℕ, E (k + 1 + 1) = R * ((k + 1 : ℕ) : ℝ) * m (k + 1 + 1) + |Pi (k + 1)| := by
    intro k
    subst hE
    exact (if_neg (by omega : ¬ k + 1 + 1 = 1)).trans (by
      have e : k + 1 + 1 - 1 = k + 1 := by omega
      rw [e])
  have hlow : ∀ j, 1 ≤ j → j ≤ J + 1 → |a j - m j| ≤ E j := by
    intro j hj hjJ
    by_cases h : j = 1
    · subst h
      rw [hE1]
      exact h1
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 + 1 := ⟨j - 2, by omega⟩
      rw [hE2 k]
      have hk := hred (k + 1) (by omega) (by omega)
      have t := abs_sub_abs_le_abs_sub (a (k + 1 + 1) - m (k + 1 + 1)) (Pi (k + 1))
      linarith
  have h := poisson_split_abs hτ a m E (J + 1) hA hT hm hlow hB hB'
  have hs : ∑ j ∈ Finset.range (J + 1), pw τ (j + 1) * E (j + 1)
      = ∑ j ∈ Finset.range J, pw τ (j + 1 + 1) * E (j + 1 + 1) + pw τ 1 * E 1 :=
    Finset.sum_range_succ' (fun j => pw τ (j + 1) * E (j + 1)) J
  have a1 : ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * m (k + 1))
      = ∑ j ∈ Finset.range J, pw τ (j + 1 + 1) * (((j + 1 : ℕ) : ℝ) * m (j + 1 + 1)) :=
    sum_Icc_shift J (fun k => pw τ (k + 1) * ((k : ℝ) * m (k + 1)))
  have a2 : ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * |Pi k|
      = ∑ j ∈ Finset.range J, pw τ (j + 1 + 1) * |Pi (j + 1)| :=
    sum_Icc_shift J (fun k => pw τ (k + 1) * |Pi k|)
  have hs2 : ∑ j ∈ Finset.range J, pw τ (j + 1 + 1) * E (j + 1 + 1)
      = R * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * m (k + 1))
        + ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * |Pi k| := by
    rw [a1, a2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE2 j]
    ring
  rw [hs, hs2, hE1] at h
  linarith

/-- **Stage 1 (deterministic).** Points `x_0, …, x_{N-1}` on the flat torus, kernel of variance
    `σ`, graph with self-loops, `P` the walk and `S` the symmetric matrix; `2 ≤ J`, `τ ≥ 0`.
    HYPOTHESES: the first stage `|Tr P^k - m_k| ≤ c √k m_k` for `1 ≤ k ≤ J` with `c √J ≤ 1`
    (used for `k = 1` and, for the tail, `k = 2`), and the reduction
    `|Tr P^{k+1} - m_{k+1} - Π_k| ≤ R k m_{k+1}` for `1 ≤ k ≤ J` (any numbers `Π_k`). Then with
    `T = ∑_{j≥1} w_j m_j` and `M = m_1 = p_σ(0)`:
    `|Tr exp(τ(S-1)) - N e^{-τ} - T| ≤ c w_1 M + R ∑_{k=1}^J w_{k+1} k m_{k+1}
        + ∑_{k=1}^J w_{k+1} |Π_k| + 3 M (1 - ∑_{j ≤ J+1} w_j)`. -/
theorem trace_second_det {σ : ℝ} (hσ : 0 < σ) (d N J : ℕ) (hN : 0 < N) (hJ : 2 ≤ J)
    (x : ℕ → FlatTorus d) {τ c R : ℝ} (hτ : 0 ≤ τ) (hc : 0 ≤ c) (hc1 : c * Real.sqrt J ≤ 1)
    (Pi : ℕ → ℝ)
    (hfirst : ∀ k : ℕ, 1 ≤ k → k ≤ J →
      |((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ k).trace - torusM d σ k|
        ≤ c * Real.sqrt k * torusM d σ k)
    (hred : ∀ k : ℕ, 1 ≤ k → k ≤ J →
      |((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ (k + 1)).trace - torusM d σ (k + 1) - Pi k|
        ≤ R * (k : ℝ) * torusM d σ (k + 1)) :
    |(NormedSpace.exp (τ • (symGraph
            (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a) - 1))).trace
        - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|
      ≤ c * (pw τ 1 * torusM d σ 1)
        + R * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
        + ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * |Pi k|
        + 3 * torusM d σ 1 * ptail τ (J + 1) := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Fin N → Fin N → ℝ,
      K = fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j) := ⟨_, rfl⟩
  obtain ⟨rho, hrhodef⟩ : ∃ rho : Fin N → ℝ,
      rho = fun a : Fin N => heatRho d σ N x a := ⟨_, rfl⟩
  rw [← hKdef, ← hrhodef] at hfirst hred ⊢
  have hKpos : ∀ a j, 0 < K a j := fun a j => by rw [hKdef]; exact heatTorus_pos hcσ d _
  have hKsymm : ∀ a j, K a j = K j a := fun a j => by
    rw [hKdef]
    show heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j) = heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x a)
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
  have hm1 : ∀ j : ℕ, 1 ≤ j → 1 ≤ torusM d σ j := fun j hj => heatMode_ge_one hσ d hj
  have hmM : ∀ j : ℕ, 1 ≤ j → torusM d σ j ≤ torusM d σ 1 := fun j hj =>
    torusM_anti hσ d (le_refl 1) hj
  have hlow : ∀ j : ℕ, 1 ≤ j → j ≤ J →
      |(symGraph K rho ^ j).trace - torusM d σ j| ≤ c * Real.sqrt j * torusM d σ j := by
    intro j hj hjJ
    rw [symGraph_trace_pow K rho hD j]
    exact hfirst j hj hjJ
  have h1 : |(symGraph K rho ^ 1).trace - torusM d σ 1| ≤ c * torusM d σ 1 := by
    have h := hlow 1 (le_refl 1) (by omega)
    rw [Nat.cast_one, Real.sqrt_one, mul_one] at h
    exact h
  have hred' : ∀ k : ℕ, 1 ≤ k → k ≤ J →
      |(symGraph K rho ^ (k + 1)).trace - torusM d σ (k + 1) - Pi k|
        ≤ R * (k : ℝ) * torusM d σ (k + 1) := by
    intro k hk hkJ
    rw [symGraph_trace_pow K rho hD (k + 1)]
    exact hred k hk hkJ
  have h2 : (symGraph K rho ^ 2).trace ≤ 2 * torusM d σ 1 := by
    have h := hlow 2 (by omega) hJ
    have hsq : c * Real.sqrt ((2 : ℕ) : ℝ) ≤ 1 := by
      have h2J : (((2 : ℕ) : ℝ)) ≤ (J : ℝ) := by exact_mod_cast hJ
      exact le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2J) hc) hc1
    have hm0 : 0 ≤ torusM d σ 2 := le_trans zero_le_one (hm1 2 (by omega))
    have h' := mul_le_mul_of_nonneg_right hsq hm0
    have h'' := (abs_le.mp h).2
    have := hmM 2 (by omega)
    linarith
  have hB : ∀ j, J + 1 < j → |(symGraph K rho ^ j).trace| ≤ 2 * torusM d σ 1 := fun j hj =>
    le_trans ((symGraph_trace_bounds K rho hKsymm (fun a j => (hKpos a j).le) hrho hD j).2
      (by omega)) h2
  have hB' : ∀ j, J + 1 < j → |torusM d σ j| ≤ torusM d σ 1 := fun j hj => by
    rw [abs_of_nonneg (le_trans zero_le_one (hm1 j (by omega)))]
    exact hmM j (by omega)
  have h := poisson_split_second hτ (fun j => (symGraph K rho ^ j).trace) (torusM d σ) Pi J
    (subtracted_trace_hasSum (symGraph K rho) hS τ) (poissonMean_hasSum hσ d hτ)
    (fun j hj => lt_of_lt_of_le one_pos (hm1 j hj)) h1 hred' hB hB'
  rw [Fintype.card_fin] at h
  linarith

/-! ### Stage 2: the mean of the weighted sum and Markov's inequality -/

/-- Linearity: a weighted sum of absolute values of bounded measurable functions is bounded
    measurable, and its mean is at most the weighted sum of the bounds of the means. -/
theorem weighted_abs_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (s : Finset ℕ) (P : ℕ → Ω → ℝ) (w b : ℕ → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hP : ∀ k ∈ s, BM (P k) ∧ ∫ ω, |P k ω| ∂μ ≤ b k) :
    BM (fun ω => ∑ k ∈ s, w k * |P k ω|)
      ∧ ∫ ω, ∑ k ∈ s, w k * |P k ω| ∂μ ≤ ∑ k ∈ s, w k * b k := by
  have bm : ∀ k ∈ s, BM (fun ω => w k * |P k ω|) := fun k hk =>
    BM.const_mul (w k) (hP k hk).1.absv
  refine ⟨BM.sum s (fun k ω => w k * |P k ω|) bm, ?_⟩
  calc ∫ ω, ∑ k ∈ s, w k * |P k ω| ∂μ = ∑ k ∈ s, ∫ ω, w k * |P k ω| ∂μ :=
        integral_finset_sum _ fun k hk => (bm k hk).integrable
    _ = ∑ k ∈ s, w k * ∫ ω, |P k ω| ∂μ :=
        Finset.sum_congr rfl (fun k _ => integral_const_mul _ _)
    _ ≤ ∑ k ∈ s, w k * b k :=
        Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hP k hk).2 (hw k hk))

/-- Markov's inequality for a nonnegative bounded measurable function. -/
theorem markov_bm {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : BM f) (h0 : ∀ ω, 0 ≤ f ω) {E t : ℝ} (hE : ∫ ω, f ω ∂μ ≤ E)
    (ht : 0 < t) : μ.real {ω | t ≤ f ω} ≤ E / t := by
  have h : t * μ.real {ω | t ≤ f ω} ≤ ∫ ω, f ω ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall h0) hf.integrable t
  rw [le_div_iff₀ ht]
  calc μ.real {ω | t ≤ f ω} * t = t * μ.real {ω | t ≤ f ω} := mul_comm _ _
    _ ≤ ∫ ω, f ω ∂μ := h
    _ ≤ E := hE

/-- Two exceptional events and one Markov event. No measurability needed. -/
theorem three_step {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {P1 P2 : Ω → Prop} {G Z : Ω → ℝ} {A t p1 p2 p3 : ℝ}
    (h1 : μ.real {ω | ¬ P1 ω} ≤ p1) (h2 : μ.real {ω | ¬ P2 ω} ≤ p2)
    (h3 : μ.real {ω | t ≤ G ω} ≤ p3) (hdet : ∀ ω, P1 ω → P2 ω → |Z ω| ≤ A + G ω) :
    μ.real {ω | A + t < |Z ω|} ≤ p1 + p2 + p3 := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _))
    ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans (add_le_add h1 h2)) h3))
  intro ω hω
  have hω' : A + t < |Z ω| := hω
  by_cases c1 : P1 ω
  · by_cases c2 : P2 ω
    · refine Or.inr ?_
      show t ≤ G ω
      have := hdet ω c1 c2
      linarith
    · exact Or.inl (Or.inr c2)
  · exact Or.inl (Or.inl c1)

/-- The weighted sums against the Poisson mean: `∑_{k=1}^J w_{k+1} k m_k ≤ τ T`
    (from `k w_{k+1} ≤ τ w_k`). -/
theorem weighted_sum_le {σ : ℝ} (hσ : 0 < σ) (d J : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k) ≤ τ * poissonMean d σ τ := by
  have hT := poissonMean_hasSum hσ d hτ
  have hm1 : ∀ j : ℕ, 1 ≤ j → 1 ≤ torusM d σ j := fun j hj => heatMode_ge_one hσ d hj
  have hnn : ∀ j : ℕ, 0 ≤ pw τ (j + 1) * heatMode d σ (j + 1) := fun j =>
    mul_nonneg (pw_nonneg hτ (j + 1)) (le_trans zero_le_one (heatMode_ge_one hσ d (by omega)))
  have h2 : ∑ j ∈ Finset.range J, pw τ (j + 1) * heatMode d σ (j + 1) ≤ poissonMean d σ τ :=
    sum_le_hasSum (Finset.range J) (fun j _ => hnn j) hT
  have h3 : ∑ k ∈ Finset.Icc 1 J, pw τ k * torusM d σ k ≤ poissonMean d σ τ :=
    le_trans (le_of_eq (sum_Icc_shift J (fun k => pw τ k * torusM d σ k))) h2
  calc ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k)
      ≤ ∑ k ∈ Finset.Icc 1 J, τ * (pw τ k * torusM d σ k) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk1 := (Finset.mem_Icc.mp hk).1
        have m0 : 0 ≤ torusM d σ k := le_trans zero_le_one (hm1 k hk1)
        calc pw τ (k + 1) * ((k : ℝ) * torusM d σ k)
            = pw τ (k + 1) * (k : ℝ) * torusM d σ k := by ring
          _ ≤ τ * pw τ k * torusM d σ k := mul_le_mul_of_nonneg_right (pw_step_le hτ k) m0
          _ = τ * (pw τ k * torusM d σ k) := by ring
    _ = τ * ∑ k ∈ Finset.Icc 1 J, pw τ k * torusM d σ k := (Finset.mul_sum _ _ _).symm
    _ ≤ τ * poissonMean d σ τ := mul_le_mul_of_nonneg_left h3 hτ

/-- `∑_{k=1}^J w_{k+1} k m_{k+1} ≤ τ T` (as `weighted_sum_le`, with `m_{k+1} ≤ m_k`). -/
theorem weighted_sum_le' {σ : ℝ} (hσ : 0 < σ) (d J : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
      ≤ τ * poissonMean d σ τ := by
  refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) (weighted_sum_le hσ d J hτ)
  have hk1 := (Finset.mem_Icc.mp hk).1
  have ha : torusM d σ (k + 1) ≤ torusM d σ k := torusM_anti hσ d hk1 (Nat.le_succ k)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg k)) (pw_nonneg hτ (k + 1))

/-- `w_1 m_1 ≤ T`: the first term of the Poisson mean. -/
theorem pw_one_le_poissonMean {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    pw τ 1 * torusM d σ 1 ≤ poissonMean d σ τ := by
  have hnn : ∀ j : ℕ, 0 ≤ pw τ (j + 1) * heatMode d σ (j + 1) := fun j =>
    mul_nonneg (pw_nonneg hτ (j + 1)) (le_trans zero_le_one (heatMode_ge_one hσ d (by omega)))
  have h := sum_le_hasSum (Finset.range 1) (fun j _ => hnn j) (poissonMean_hasSum hσ d hτ)
  rw [Finset.sum_range_one] at h
  exact h

/-! ### Stage 3: the sample statement -/

/-- **The Poisson summation of the second stage for random samples, finite form** (a form of
    `cor:secondstage-alld` for fixed `N`). Independent uniform points on the flat torus of
    dimension `d ≥ 1`, periodised Gaussian kernel of variance `σ = ξ² ≤ 1`, graph with self-loops,
    `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`, an integer `J ≥ 2` with `C₁ δ' √J ≤ 1`
    (`C₁ = kernelC1 d`), `τ ≥ 0`, `T = poissonMean d σ τ`, and any `t > 0`. With
    `A(τ) = C₁ δ' w_1(τ) M + C_red δ'² ∑_{k=1}^J w_{k+1}(τ) k m_{k+1} + 3 M (1 - ∑_{j ≤ J+1} w_j(τ))`,
    `B(τ) = C_Π (M/N) ∑_{k=1}^J w_{k+1}(τ) k m_k`:
    `P(|Tr exp(τ(S-1)) - N e^{-τ} - T| > A(τ) + t) ≤ 11/N³ + B(τ)/t`.
    (`8/N³` for the event of the reduction, `3/N³` for the event of the first stage, which is used
    for the index `j = 1` and for the tail; Markov's inequality is applied once, to
    `∑_k w_{k+1} |Π_k|`.) -/
theorem second_stage_trace {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | kernelC1 d * δp * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1) + t
        < |(NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|}
      ≤ 11 / (N : ℝ) ^ 3
        + piC d * (Mp / N) * (∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k)) / t := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N J hN2 (by omega) hMp hδp hrange
  have hM1e : torusM d σ 1 = Mp := by rw [hMp]; unfold torusM; simp
  have hc : 0 ≤ kernelC1 d * δp := mul_nonneg (kernelC1_nonneg d) hδ0
  have h0 := torus_reduction_redC hσ hσ1 d hd X h_indep hX hlaw N J hN2 (by omega) hMp hδp hrange
  have hf := kernel_trace_G28 hσ hσ1 d hd X h_indep hX hlaw N J hN2 (by omega) hMp hδp hrange
  obtain ⟨bG, hG⟩ := weighted_abs_bound (μ := μ) (Finset.Icc 1 J)
    (fun k ω => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)))
    (fun k => pw τ (k + 1)) (fun k => piC d * (torusM d σ 1 / N) * k * torusM d σ k)
    (fun k _ => pw_nonneg hτ (k + 1))
    (fun k hk => pi_bound X h_indep hX hlaw hσ k (Finset.mem_Icc.mp hk).1 N (by omega)
      (by rw [hM1e]; linarith))
  have hB : ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * (piC d * (torusM d σ 1 / N) * k * torusM d σ k)
      = piC d * (Mp / N) * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k) := by
    rw [hM1e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hG' : ∫ ω, ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1)
        * |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))| ∂μ
      ≤ piC d * (Mp / N) * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k) :=
    le_trans hG (le_of_eq hB)
  have hmk := markov_bm bG
    (fun ω => Finset.sum_nonneg (fun k _ => mul_nonneg (pw_nonneg hτ (k + 1)) (abs_nonneg _)))
    hG' ht
  refine le_trans (three_step (μ := μ)
    (Z := fun ω => (NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ)
    (A := kernelC1 d * δp * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1))
    h0 hf hmk ?_) (le_of_eq (by ring))
  intro ω g1 g2
  have hdet := trace_second_det hσ d N J (by omega) hJ (fun j => X j ω) hτ hc hrange
    (fun k => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)))
    (fun k hk hkJ => g2 k hk hkJ) (fun k hk hkJ => g1 k hk hkJ)
  rw [hM1e] at hdet
  exact le_trans hdet (le_of_eq (by ring))

/-- **The same with the Markov threshold scaled:** for `τ > 0` and `s > 0`,
    `P(|Tr exp(τ(S-1)) - N e^{-τ} - T| > A(τ) + s B(τ)) ≤ 11/N³ + 1/s`. -/
theorem second_stage_trace_scaled {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 0 < τ) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | kernelC1 d * δp * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1)
          + s * (piC d * (Mp / N)
              * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k))
        < |(NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|}
      ≤ 11 / (N : ℝ) ^ 3 + 1 / s := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N J hN2 (by omega) hMp hδp hrange
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm1 : ∀ j : ℕ, 1 ≤ j → 1 ≤ torusM d σ j := fun j hj => heatMode_ge_one hσ d hj
  have hSpos : 0 < ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k) :=
    Finset.sum_pos (fun k hk => mul_pos (pw_pos hτ (k + 1))
        (mul_pos (Nat.cast_pos.mpr (Finset.mem_Icc.mp hk).1)
          (lt_of_lt_of_le one_pos (hm1 k (Finset.mem_Icc.mp hk).1))))
      ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩⟩
  have hBpos : 0 < piC d * (Mp / N)
      * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k) :=
    mul_pos (mul_pos (piC_pos d) (div_pos (by linarith) hNpos)) hSpos
  have h := second_stage_trace hσ hσ1 d hd X h_indep hX hlaw N J hN2 hJ hMp hδp hrange hτ.le
    (s * (piC d * (Mp / N) * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k)))
    (mul_pos hs hBpos)
  have e : piC d * (Mp / N) * (∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k))
      / (s * (piC d * (Mp / N)
          * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k))) = 1 / s := by
    rw [mul_comm s, ← div_div, div_self hBpos.ne']
  rw [e] at h
  exact h

/-! ### Stage 4: the relative form -/

/-- Arithmetic of the relative form. -/
theorem rel_arith {X T c pw1 Mp r S τ pt u q : ℝ} (hT : 3 / 4 ≤ T) (hr : 0 ≤ r)
    (hS : S ≤ τ * T) (hq : 0 ≤ q) (hpt : Mp * pt ≤ q)
    (h : (r + u) * τ + c * (pw1 * Mp / T) + 4 * q < |X / T - 1|) :
    c * (pw1 * Mp) + r * S + 3 * Mp * pt + u * τ * T < |X - T| := by
  have hTpos : 0 < T := by linarith
  have hT0 : T ≠ 0 := hTpos.ne'
  have e0 : X / T - 1 = (X - T) / T := by field_simp
  rw [e0, abs_div, abs_of_pos hTpos, lt_div_iff₀ hTpos] at h
  have e1 : c * (pw1 * Mp / T) * T = c * (pw1 * Mp) := by
    rw [mul_assoc, div_mul_cancel₀ _ hT0]
  have e : ((r + u) * τ + c * (pw1 * Mp / T) + 4 * q) * T
      = r * (τ * T) + u * τ * T + c * (pw1 * Mp / T) * T + 4 * q * T := by ring
  rw [e, e1] at h
  have f1 := mul_le_mul_of_nonneg_left hS hr
  have f2 : 0 ≤ q * (T - 3 / 4) := mul_nonneg hq (by linarith)
  have f3 : q * (T - 3 / 4) = q * T - 3 / 4 * q := by ring
  linarith

/-- **The second stage for the heat trace, relative form.** In the situation of
    `second_stage_trace` let moreover `τ ≥ 2`, `3τ + 2 log N ≤ J + 2` and `s > 0`. Then
    `P(|(Tr exp(τ(S-1)) - N e^{-τ})/T - 1| > (C_red δ'² + s C_Π M/N) τ + C₁ δ' (w_1(τ) M/T) + 4M/N²)
       ≤ 11/N³ + 1/s`.
    (The factor `k` of the reduction and of `pi_bound` has become the factor `τ`, by
    `k w_{k+1}(τ) ≤ τ w_k(τ)`. The term `C₁ δ' w_1 M/T ≤ C₁ δ'` is the first stage at `j = 1`.) -/
theorem second_stage_trace_rel {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 2 ≤ τ)
    (hJτ : 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 2) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | (redC d * δp ^ 2 + s * piC d * (Mp / N)) * τ
          + kernelC1 d * δp * (pw τ 1 * Mp / poissonMean d σ τ)
          + 4 * (Mp / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|}
      ≤ 11 / (N : ℝ) ^ 3 + 1 / s := by
  have hτ0 : 0 ≤ τ := by linarith
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N J hN2 (by omega) hMp hδp hrange
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMp0 : 0 ≤ Mp := by linarith
  have hT : 3 / 4 ≤ poissonMean d σ τ := by
    have h1 := poissonMean_ge hσ d hτ0
    have h2 := exp_neg_le_quarter hτ
    linarith
  have hu : 0 < s * piC d * (Mp / N) :=
    mul_pos (mul_pos hs (piC_pos d)) (div_pos (by linarith) hNpos)
  have ht : 0 < s * piC d * (Mp / N) * τ * poissonMean d σ τ :=
    mul_pos (mul_pos hu (by linarith)) (by linarith)
  have h := second_stage_trace hσ hσ1 d hd X h_indep hX hlaw N J hN2 hJ hMp hδp hrange hτ0
    (s * piC d * (Mp / N) * τ * poissonMean d σ τ) ht
  have hS1 := weighted_sum_le hσ d J hτ0
  have hS2 := weighted_sum_le' hσ d J hτ0
  have hprob : piC d * (Mp / N)
        * (∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k))
        / (s * piC d * (Mp / N) * τ * poissonMean d σ τ) ≤ 1 / s := by
    rw [div_le_iff₀ ht]
    have e : 1 / s * (s * piC d * (Mp / N) * τ * poissonMean d σ τ)
        = piC d * (Mp / N) * (τ * poissonMean d σ τ) := by
      calc 1 / s * (s * piC d * (Mp / N) * τ * poissonMean d σ τ)
          = s / s * (piC d * (Mp / N) * (τ * poissonMean d σ τ)) := by ring
        _ = piC d * (Mp / N) * (τ * poissonMean d σ τ) := by rw [div_self hs.ne', one_mul]
    rw [e]
    exact mul_le_mul_of_nonneg_left hS1
      (mul_nonneg (piC_pos d).le (div_nonneg hMp0 hNpos.le))
  have hpt : Mp * ptail τ (J + 1) ≤ Mp / (N : ℝ) ^ 2 := by
    have hJ' : 3 * τ + 2 * Real.log N ≤ ((J + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hp := ptail_le_inv_sq hτ0 (J + 1) N (by omega) hJ'
    have := mul_le_mul_of_nonneg_left hp hMp0
    rw [mul_one_div] at this
    exact this
  have hq : 0 ≤ Mp / (N : ℝ) ^ 2 := div_nonneg hMp0 (by positivity)
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (h.trans (add_le_add le_rfl hprob))
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  exact rel_arith hT (mul_nonneg (redC_nonneg d) (pow_nonneg hδ0 2)) hS2 hq hpt hω

end SecondStageTrace

/-! ## The Poisson index `j = 1` of the second stage in SECOND order (`cor:secondstage`,
`cor:secondstage-alld`, for a FIXED sample size `N`).

In `SecondStageTrace.second_stage_trace_rel` the index `j = 1` is taken from the first stage
(`|Tr P - m_1| ≤ C₁ δ' m_1`, first order in `δ'`). The proof of `cor:secondstage` treats it in
second order: `Tr P - m_1 = (M/N) ∑_i θ_ii`, `(1/N) ∑_i θ¹_ii = -ε̄ + (1/N) ∑_l ε_l²`, hence
`|Tr P - m_1| ≤ M (|ε̄| + (1/N) ∑_l ε_l² + 14 δ²)` on the normalisation event, and
`E(|ε̄| + (1/N) ∑_l ε_l²) ≤ 7 M/N`. This is formalised here; the result is
`second_stage_trace_rel2`, in which no term of first order in `δ'` is left.
No limit `N → ∞` and no statement `o_P(ξ²)` is formalised here. -/

namespace SecondStageTrace2

open CTG.Reals.TorusReduction CTG.Reals.TraceG29 TorusReductionL1 H5 PiBound SecondStage
  SecondStageTrace

/-! ### Step 1: the index `j = 1`, deterministic -/

/-- `∑_i θ¹_ii = -∑_i ε_i + ∑_i ε_i²` for `θ¹_bi = -ε_i - ε_b + (1/c) ∑_j K_bj ε_j`, when the
    COLUMN sums of `K` are `c (1 + ε_j)` (over ℝ; the statement of `theta1_diagonal_sum` of the
    core file). -/
theorem theta1_diag_sum {N : ℕ} (K : Fin N → Fin N → ℝ) (ε : Fin N → ℝ) {c : ℝ} (hc : c ≠ 0)
    (hcol : ∀ j, ∑ i, K i j = c * (1 + ε j)) :
    ∑ i, (-ε i - ε i + (∑ j, K i j * ε j) / c) = -∑ i, ε i + ∑ i, ε i ^ 2 := by
  have h1 : ∑ i, (∑ j, K i j * ε j) / c = ∑ j, (ε j + ε j ^ 2) := by
    rw [← Finset.sum_div, Finset.sum_comm]
    have h2 : ∀ j ∈ (Finset.univ : Finset (Fin N)),
        ∑ i, K i j * ε j = c * (ε j + ε j ^ 2) := fun j _ => by
      rw [← Finset.sum_mul, hcol j]; ring
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, mul_div_cancel_left₀ _ hc]
  rw [Finset.sum_add_distrib, h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

/-- **Step 1 (deterministic): the trace of the walk itself, in second order.** On the
    normalisation event `|ρ_a - 1| ≤ δ ≤ 1/8`, with `ε_a = ρ_a - 1` and `M = m_1 = p_σ(0)`:
    `|Tr P - M| ≤ M (|(1/N) ∑_a ε_a| + (1/N) ∑_a ε_a² + 14 δ²)`.
    (`Tr P = (1/N) ∑_i K_ii (1 + θ_ii)`, `K_ii = M`, `|θ - θ¹| ≤ 14 δ²`, and
    `∑_i θ¹_ii = -∑ ε_i + ∑ ε_i²`; the last identity uses the column sums of the kernel
    matrix, i.e. its symmetry.) -/
theorem trace_one_det {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 1 ≤ N) (x : ℕ → FlatTorus d)
    {δ : ℝ} (hδ : δ ≤ 1 / 8) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ) :
    |(torusWalk d σ N x).trace - torusM d σ 1|
      ≤ torusM d σ 1 * (|1 / (N : ℝ) * ∑ a : Fin N, (heatRho d σ N x a - 1)|
          + 1 / (N : ℝ) * ∑ a : Fin N, (heatRho d σ N x a - 1) ^ 2 + 14 * δ ^ 2) := by
  obtain ⟨hδ0, hP0, hrow, hq0, hqm, hqd, hH1, hH1a, hH1b, hH2⟩ := torus_hyps hσ d N hN x hδ hρ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hM0 : 0 ≤ torusM d σ 1 := le_trans zero_le_one (heatMode_ge_one hσ d (le_refl 1))
  obtain ⟨θ, hθ⟩ : ∃ θ : Fin N → ℝ, θ = fun i =>
      ShellAndWalk.walkTheta (torusK d σ N x) (torusRho d σ N x) i i := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : Fin N → ℝ, ε = fun i : Fin N => heatRho d σ N x i - 1 := ⟨_, rfl⟩
  have hdiag : ∀ i : Fin N, (N : ℝ) * torusWalk d σ N x i i = torusM d σ 1 * (1 + θ i) := by
    intro i
    rw [hH1 i i, hqd 1 (le_refl 1) i, hθ]
  -- the column sums of the kernel matrix
  have hcol : ∀ j : Fin N, ∑ i : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j)
      = (N : ℝ) * (1 + ε j) := by
    intro j
    have e1 : ∀ i ∈ (Finset.univ : Finset (Fin N)),
        heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j)
          = heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x i) := fun i _ => by
      rw [← heatTorus_even d _ (x j - x i), neg_sub]
    have e2 : ∑ i : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x i)
        = ∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l) :=
      Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l)) N
    have e3 : heatRho d σ N x j
        = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l)) / (N : ℝ) := rfl
    rw [Finset.sum_congr rfl e1, e2, hε]
    show _ = (N : ℝ) * (1 + (heatRho d σ N x j - 1))
    rw [e3]
    obtain ⟨S, hS⟩ : ∃ S : ℝ,
        S = ∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l) := ⟨_, rfl⟩
    rw [← hS, show (N : ℝ) * (1 + (S / (N : ℝ) - 1)) = S * ((N : ℝ) / (N : ℝ)) by ring,
      div_self hN0, mul_one]
  have hth1 : ∀ i : Fin N, torusTheta1 d σ N x i i
      = -ε i - ε i + (∑ j : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j) * ε j)
          / (N : ℝ) := by
    intro i
    rw [torusTheta1_eq, hε]
  have hsum1 : ∑ i : Fin N, torusTheta1 d σ N x i i = -∑ i, ε i + ∑ i, ε i ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hth1 i)]
    exact theta1_diag_sum (fun i j => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j)) ε hN0 hcol
  -- the remainder of the linearisation
  have hD : |∑ i : Fin N, (θ i - torusTheta1 d σ N x i i)| ≤ (N : ℝ) * (14 * δ ^ 2) := by
    calc |∑ i : Fin N, (θ i - torusTheta1 d σ N x i i)|
        ≤ ∑ i : Fin N, |θ i - torusTheta1 d σ N x i i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, 14 * δ ^ 2 := Finset.sum_le_sum (fun i _ => by
          rw [hθ]; exact hH1b i i)
      _ = (N : ℝ) * (14 * δ ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hΘ : ∑ i : Fin N, θ i
      = -∑ i, ε i + ∑ i, ε i ^ 2 + ∑ i : Fin N, (θ i - torusTheta1 d σ N x i i) := by
    rw [← hsum1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have htr : (N : ℝ) * (torusWalk d σ N x).trace
      = torusM d σ 1 * (N : ℝ) + torusM d σ 1 * ∑ i : Fin N, θ i := by
    have e : (torusWalk d σ N x).trace = ∑ i : Fin N, torusWalk d σ N x i i := rfl
    rw [e, Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hdiag i), ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, mul_add]
  have hE2 : 0 ≤ 1 / (N : ℝ) * ∑ i, ε i ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => _root_.sq_nonneg (ε i)))
  have hD' : |1 / (N : ℝ) * ∑ i : Fin N, (θ i - torusTheta1 d σ N x i i)| ≤ 14 * δ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)), one_div_mul_eq_div,
      div_le_iff₀ hNpos]
    linarith
  have hkey : (torusWalk d σ N x).trace - torusM d σ 1
      = torusM d σ 1 * (-(1 / (N : ℝ) * ∑ i, ε i) + 1 / (N : ℝ) * ∑ i, ε i ^ 2
          + 1 / (N : ℝ) * ∑ i : Fin N, (θ i - torusTheta1 d σ N x i i)) := by
    have h : (torusWalk d σ N x).trace
        = torusM d σ 1 + torusM d σ 1 * (1 / (N : ℝ) * ∑ i : Fin N, θ i) := by
      have h' : (torusWalk d σ N x).trace
          = (torusM d σ 1 * (N : ℝ) + torusM d σ 1 * ∑ i : Fin N, θ i) / (N : ℝ) := by
        rw [← htr, mul_div_cancel_left₀ _ hN0]
      rw [h', add_div, show torusM d σ 1 * (N : ℝ) / (N : ℝ)
        = torusM d σ 1 * ((N : ℝ) / (N : ℝ)) by ring, div_self hN0, mul_one]
      ring
    rw [h, hΘ]
    ring
  have hfin : |(torusWalk d σ N x).trace - torusM d σ 1|
      ≤ torusM d σ 1 * (|1 / (N : ℝ) * ∑ i, ε i| + 1 / (N : ℝ) * ∑ i, ε i ^ 2 + 14 * δ ^ 2) := by
    rw [hkey, abs_mul, abs_of_nonneg hM0]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have a1 := neg_abs_le (1 / (N : ℝ) * ∑ i, ε i)
    have a2 := le_abs_self (1 / (N : ℝ) * ∑ i, ε i)
    have a3 := abs_le.mp hD'
    exact abs_le.mpr ⟨by linarith [a3.1], by linarith [a3.2]⟩
  rw [hε] at hfin
  exact hfin

/-! ### Step 2: the mean of the statistic of the index `j = 1` -/

/-- `ε_q = ρ_q - 1 = (1/N) ∑_v c(X_q - X_v)`: the normalisation error is the row sum of
    `c = p - 1`. -/
theorem eps_eq_Hrow {Ω : Type*} (d : ℕ) (σ : ℝ) (N : ℕ) (hN : 0 < N) (X : ℕ → Ω → FlatTorus d)
    (ω : Ω) (q : ℕ) :
    heatRho d σ N (fun j => X j ω) q - 1 = 1 / (N : ℝ) * Hrow (cK d σ) X N q ω := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : Hrow (cK d σ) X N q ω
      = ∑ v ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X q ω - X v ω) - (N : ℝ) := by
    show ∑ v ∈ Finset.range N, (heatTorus d (2 * Real.pi ^ 2 * σ) (X q ω - X v ω) - 1) = _
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have e3 : heatRho d σ N (fun j => X j ω) q
      = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X q ω - X l ω)) / (N : ℝ) :=
    rfl
  rw [e, e3, mul_sub, one_div_mul_eq_div, one_div_mul_cancel hN0]

/-- The statistic of the index `j = 1`: `|ε̄| + (1/N) ∑_q ε_q²`, written with the kernel
    `c = p - 1`: `ε̄ = N⁻² ∑_{i,j} c(X_i - X_j)` (a degenerate two-point statistic, the diagonal
    included) and `ε_q = (1/N) ∑_v c(X_q - X_v)`. -/
noncomputable def j1stat {Ω : Type*} (d : ℕ) (σ : ℝ) (N : ℕ) (X : ℕ → Ω → FlatTorus d)
    (ω : Ω) : ℝ :=
  |1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, cK d σ (X i ω - X j ω)|
    + 1 / (N : ℝ) * ∑ q ∈ Finset.range N, (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2

theorem j1stat_nonneg {Ω : Type*} (d : ℕ) (σ : ℝ) (N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    0 ≤ j1stat d σ N X ω := by
  unfold j1stat
  exact add_nonneg (abs_nonneg _)
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun q _ => _root_.sq_nonneg _)))

/-- The statistic of Step 1 at the sample is `j1stat`. -/
theorem j1stat_eq {Ω : Type*} (d : ℕ) (σ : ℝ) (N : ℕ) (hN : 0 < N) (X : ℕ → Ω → FlatTorus d)
    (ω : Ω) :
    |1 / (N : ℝ) * ∑ a : Fin N, (heatRho d σ N (fun j => X j ω) a - 1)|
        + 1 / (N : ℝ) * ∑ a : Fin N, (heatRho d σ N (fun j => X j ω) a - 1) ^ 2
      = j1stat d σ N X ω := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have s1 : ∑ a : Fin N, (heatRho d σ N (fun j => X j ω) a - 1)
      = ∑ q ∈ Finset.range N, 1 / (N : ℝ) * Hrow (cK d σ) X N q ω :=
    (Fin.sum_univ_eq_sum_range (fun q => heatRho d σ N (fun j => X j ω) q - 1) N).trans
      (Finset.sum_congr rfl (fun q _ => eps_eq_Hrow d σ N hN X ω q))
  have s2 : ∑ a : Fin N, (heatRho d σ N (fun j => X j ω) a - 1) ^ 2
      = ∑ q ∈ Finset.range N, (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2 :=
    (Fin.sum_univ_eq_sum_range (fun q => (heatRho d σ N (fun j => X j ω) q - 1) ^ 2) N).trans
      (Finset.sum_congr rfl (fun q _ => by rw [eps_eq_Hrow d σ N hN X ω q]))
  have s3 : 1 / (N : ℝ) * ∑ q ∈ Finset.range N, 1 / (N : ℝ) * Hrow (cK d σ) X N q ω
      = 1 / (N : ℝ) ^ 2
        * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, cK d σ (X i ω - X j ω) := by
    rw [← Finset.mul_sum]
    show 1 / (N : ℝ) * (1 / (N : ℝ) * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω)
      = 1 / (N : ℝ) ^ 2 * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω
    ring
  unfold j1stat
  rw [s1, s2, s3]

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Step 2: `E(|ε̄| + (1/N) ∑_q ε_q²) ≤ 7 M/N`** for independent uniform points, `N ≥ 1`,
    `4M ≤ N` (`E|ε̄| ≤ (√(2M) + |c(0)|)/N` by `Deg2.Z0_bound` for `c`, and
    `E ε_q² ≤ (4NM + 2c(0)²)/N²` by `Deg2.Hrow_sq`; in the paper: `E|ε̄| ≤ C M/N`,
    `E ε_l² ≤ 4M/N`). -/
theorem j1stat_bound [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    (hMN : 4 * torusM d σ 1 ≤ N) :
    BM (fun ω => j1stat d σ N X ω)
      ∧ ∫ ω, j1stat d σ N X ω ∂μ ≤ 7 * (torusM d σ 1 / N) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have H := cK_deg2 X h_indep hX hlaw hσ
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  have bH : ∀ q, BM (Hrow (cK d σ) X N q) := fun q => H.BM_Hrow N q
  have bA0 : BM (fun ω => 1 / (N : ℝ) ^ 2 * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω) :=
    BM.const_mul _ (BM.sum _ _ (fun q _ => bH q))
  have bA : BM (fun ω => |1 / (N : ℝ) ^ 2
      * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, cK d σ (X i ω - X j ω)|) := bA0.absv
  have bQ : ∀ q, BM (fun ω => (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2) := fun q =>
    (BM.const_mul _ (bH q)).sqr
  have bB : BM (fun ω => 1 / (N : ℝ)
      * ∑ q ∈ Finset.range N, (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2) :=
    BM.const_mul _ (BM.sum _ _ (fun q _ => bQ q))
  refine ⟨bA.add bB, ?_⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = cK d σ 0 := ⟨_, rfl⟩
  have hc0M : |c0| ≤ torusM d σ 1 := by rw [hc0]; exact (cK_facts hσ d 0).1
  have hc0sq : c0 ^ 2 ≤ torusM d σ 1 ^ 2 := by
    rw [← sq_abs c0]
    exact pow_le_pow_left₀ (abs_nonneg _) hc0M 2
  have iA : ∫ ω, |1 / (N : ℝ) ^ 2
        * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, cK d σ (X i ω - X j ω)| ∂μ
      ≤ (Real.sqrt (2 * torusM d σ 1) + |c0|) / N := by
    rw [hc0]; exact H.Z0_bound N hN
  have hq : ∀ q ∈ Finset.range N, ∫ ω, (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2 ∂μ
      ≤ (1 / (N : ℝ)) ^ 2 * (4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2) := by
    intro q hq
    have e : (fun ω => (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2)
        = fun ω => (1 / (N : ℝ)) ^ 2 * Hrow (cK d σ) X N q ω ^ 2 := by
      funext ω; ring
    rw [e, integral_const_mul, hc0]
    exact mul_le_mul_of_nonneg_left (H.Hrow_sq N q hq) (by positivity)
  have iB : ∫ ω, 1 / (N : ℝ)
        * ∑ q ∈ Finset.range N, (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2 ∂μ
      ≤ 1 / (N : ℝ) * ∑ _q ∈ Finset.range N,
          (1 / (N : ℝ)) ^ 2 * (4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2) := by
    rw [integral_const_mul, integral_finset_sum _ (fun q _ => (bQ q).integrable)]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hq) (by positivity)
  have hsplit : ∫ ω, j1stat d σ N X ω ∂μ
      = ∫ ω, |1 / (N : ℝ) ^ 2
          * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, cK d σ (X i ω - X j ω)| ∂μ
        + ∫ ω, 1 / (N : ℝ)
          * ∑ q ∈ Finset.range N, (1 / (N : ℝ) * Hrow (cK d σ) X N q ω) ^ 2 ∂μ := by
    unfold j1stat
    exact integral_add bA.integrable bB.integrable
  -- arithmetic
  have hsqrt : Real.sqrt (2 * torusM d σ 1) ≤ 3 / 2 * torusM d σ 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ torusM d σ 1)
      (by linarith : (0 : ℝ) ≤ 9 / 4 * torusM d σ 1 - 2)
    linarith [show (3 / 2 * torusM d σ 1) ^ 2
      = torusM d σ 1 * (9 / 4 * torusM d σ 1 - 2) + 2 * torusM d σ 1 by ring]
  have p1 : (Real.sqrt (2 * torusM d σ 1) + |c0|) / N ≤ (5 / 2 * torusM d σ 1) / N :=
    div_le_div_of_nonneg_right (by linarith) hNpos.le
  have p2 : 1 / (N : ℝ) * ∑ _q ∈ Finset.range N,
        (1 / (N : ℝ)) ^ 2 * (4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2)
      = (4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2) / (N : ℝ) ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show 1 / (N : ℝ) * ((N : ℝ) * ((1 / (N : ℝ)) ^ 2
          * (4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2)))
        = (N : ℝ) / (N : ℝ) * ((4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2) / (N : ℝ) ^ 2) by ring,
      div_self hNpos.ne', one_mul]
  have h4 : 2 * c0 ^ 2 ≤ 1 / 2 * torusM d σ 1 * (N : ℝ) := by
    have t1 := mul_le_mul_of_nonneg_left hMN (by linarith : (0 : ℝ) ≤ torusM d σ 1)
    have e : torusM d σ 1 * (4 * torusM d σ 1) = 4 * torusM d σ 1 ^ 2 := by ring
    rw [e] at t1
    linarith
  have p3 : (4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2) / (N : ℝ) ^ 2
      ≤ (9 / 2 * torusM d σ 1) / N := by
    rw [div_le_div_iff₀ (by positivity) hNpos]
    have t2 := mul_le_mul_of_nonneg_right h4 hNpos.le
    have e1 : (4 * (N : ℝ) * torusM d σ 1 + 2 * c0 ^ 2) * (N : ℝ)
        = 4 * torusM d σ 1 * (N : ℝ) ^ 2 + 2 * c0 ^ 2 * (N : ℝ) := by ring
    have e2 : 9 / 2 * torusM d σ 1 * (N : ℝ) ^ 2
        = 4 * torusM d σ 1 * (N : ℝ) ^ 2 + 1 / 2 * torusM d σ 1 * (N : ℝ) * (N : ℝ) := by ring
    rw [e1, e2]
    linarith
  have e7 : (5 / 2 * torusM d σ 1) / N + (9 / 2 * torusM d σ 1) / N
      = 7 * (torusM d σ 1 / N) := by ring
  rw [hsplit, ← e7]
  rw [p2] at iB
  linarith

end Sample

/-! ### Step 3: the Poisson summation with the index `j = 1` in second order -/

/-- **The deterministic summation** (`SecondStageTrace.trace_second_det` with separate
    hypotheses for the indices `1` and `2`). HYPOTHESES: `|Tr P - m_1| ≤ c₁ m_1` (any `c₁`),
    `|Tr P² - m_2| ≤ m_2` (for the tail), and the reduction
    `|Tr P^{k+1} - m_{k+1} - Π_k| ≤ R k m_{k+1}` for `1 ≤ k ≤ J` (any numbers `Π_k`). Then
    `|Tr exp(τ(S-1)) - N e^{-τ} - T| ≤ c₁ w_1 M + R ∑_{k=1}^J w_{k+1} k m_{k+1}
        + ∑_{k=1}^J w_{k+1} |Π_k| + 3 M (1 - ∑_{j ≤ J+1} w_j)`. -/
theorem trace_second_det2 {σ : ℝ} (hσ : 0 < σ) (d N J : ℕ) (hN : 0 < N)
    (x : ℕ → FlatTorus d) {τ c1 R : ℝ} (hτ : 0 ≤ τ) (Pi : ℕ → ℝ)
    (hone : |((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ 1).trace - torusM d σ 1|
        ≤ c1 * torusM d σ 1)
    (htwo : |((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ 2).trace - torusM d σ 2|
        ≤ torusM d σ 2)
    (hred : ∀ k : ℕ, 1 ≤ k → k ≤ J →
      |((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ (k + 1)).trace - torusM d σ (k + 1) - Pi k|
        ≤ R * (k : ℝ) * torusM d σ (k + 1)) :
    |(NormedSpace.exp (τ • (symGraph
            (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a) - 1))).trace
        - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|
      ≤ c1 * (pw τ 1 * torusM d σ 1)
        + R * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
        + ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * |Pi k|
        + 3 * torusM d σ 1 * ptail τ (J + 1) := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Fin N → Fin N → ℝ,
      K = fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j) := ⟨_, rfl⟩
  obtain ⟨rho, hrhodef⟩ : ∃ rho : Fin N → ℝ,
      rho = fun a : Fin N => heatRho d σ N x a := ⟨_, rfl⟩
  rw [← hKdef, ← hrhodef] at hone htwo hred ⊢
  have hKpos : ∀ a j, 0 < K a j := fun a j => by rw [hKdef]; exact heatTorus_pos hcσ d _
  have hKsymm : ∀ a j, K a j = K j a := fun a j => by
    rw [hKdef]
    show heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j) = heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x a)
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
  have hm1 : ∀ j : ℕ, 1 ≤ j → 1 ≤ torusM d σ j := fun j hj => heatMode_ge_one hσ d hj
  have hmM : ∀ j : ℕ, 1 ≤ j → torusM d σ j ≤ torusM d σ 1 := fun j hj =>
    torusM_anti hσ d (le_refl 1) hj
  have h1 : |(symGraph K rho ^ 1).trace - torusM d σ 1| ≤ c1 * torusM d σ 1 := by
    rw [symGraph_trace_pow K rho hD 1]
    exact hone
  have hred' : ∀ k : ℕ, 1 ≤ k → k ≤ J →
      |(symGraph K rho ^ (k + 1)).trace - torusM d σ (k + 1) - Pi k|
        ≤ R * (k : ℝ) * torusM d σ (k + 1) := by
    intro k hk hkJ
    rw [symGraph_trace_pow K rho hD (k + 1)]
    exact hred k hk hkJ
  have h2 : (symGraph K rho ^ 2).trace ≤ 2 * torusM d σ 1 := by
    rw [symGraph_trace_pow K rho hD 2]
    have h'' := (abs_le.mp htwo).2
    have := hmM 2 (by omega)
    linarith
  have hB : ∀ j, J + 1 < j → |(symGraph K rho ^ j).trace| ≤ 2 * torusM d σ 1 := fun j hj =>
    le_trans ((symGraph_trace_bounds K rho hKsymm (fun a j => (hKpos a j).le) hrho hD j).2
      (by omega)) h2
  have hB' : ∀ j, J + 1 < j → |torusM d σ j| ≤ torusM d σ 1 := fun j hj => by
    rw [abs_of_nonneg (le_trans zero_le_one (hm1 j (by omega)))]
    exact hmM j (by omega)
  have h := poisson_split_second hτ (fun j => (symGraph K rho ^ j).trace) (torusM d σ) Pi J
    (subtracted_trace_hasSum (symGraph K rho) hS τ) (poissonMean_hasSum hσ d hτ)
    (fun j hj => lt_of_lt_of_le one_pos (hm1 j hj)) h1 hred' hB hB'
  rw [Fintype.card_fin] at h
  linarith

/-- Three exceptional events and one Markov event. No measurability needed. -/
theorem four_step {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {P1 P2 P3 : Ω → Prop} {G Z : Ω → ℝ} {A t p1 p2 p3 p4 : ℝ}
    (h1 : μ.real {ω | ¬ P1 ω} ≤ p1) (h2 : μ.real {ω | ¬ P2 ω} ≤ p2)
    (h3 : μ.real {ω | ¬ P3 ω} ≤ p3) (h4 : μ.real {ω | t ≤ G ω} ≤ p4)
    (hdet : ∀ ω, P1 ω → P2 ω → P3 ω → |Z ω| ≤ A + G ω) :
    μ.real {ω | A + t < |Z ω|} ≤ p1 + p2 + p3 + p4 := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _))
    ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans
        (add_le_add ((measureReal_union_le _ _).trans (add_le_add h1 h2)) h3)) h4))
  intro ω hω
  have hω' : A + t < |Z ω| := hω
  by_cases c1 : P1 ω
  · by_cases c2 : P2 ω
    · by_cases c3 : P3 ω
      · refine Or.inr ?_
        show t ≤ G ω
        have := hdet ω c1 c2 c3
        linarith
      · exact Or.inl (Or.inr c3)
    · exact Or.inl (Or.inl (Or.inr c2))
  · exact Or.inl (Or.inl (Or.inl c1))

/-- **The Poisson summation of the second stage with the index `j = 1` in second order, finite
    form.** Situation of `SecondStageTrace.second_stage_trace` (`J ≥ 2`, `C₁ δ' √J ≤ 1`, `τ ≥ 0`,
    `t > 0`), `δ = normC d · δ'`. With
    `A₂(τ) = 14 δ² w_1(τ) M + C_red δ'² ∑_{k=1}^J w_{k+1}(τ) k m_{k+1} + 3 M (1 - ∑_{j ≤ J+1} w_j(τ))`,
    `B₂(τ) = 7 (M/N) w_1(τ) M + C_Π (M/N) ∑_{k=1}^J w_{k+1}(τ) k m_k`:
    `P(|Tr exp(τ(S-1)) - N e^{-τ} - T| > A₂(τ) + t) ≤ 12/N³ + B₂(τ)/t`.
    (`8/N³` for the event of the reduction, `3/N³` for the event of the first stage, which is now
    used ONLY for the tail (index `k = 2`), `1/N³` for the normalisation event; Markov's
    inequality is applied ONCE, to `w_1 M (|ε̄| + (1/N) ∑ ε_l²) + ∑_k w_{k+1} |Π_k|`.) -/
theorem second_stage_trace2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | 14 * (normC d * δp) ^ 2 * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1) + t
        < |(NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|}
      ≤ 12 / (N : ℝ) ^ 3
        + (7 * (Mp / N) * (pw τ 1 * Mp) + piC d * (Mp / N)
            * (∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k))) / t := by
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N J hN2 (by omega) hMp hδp hrange
  have hM1e : torusM d σ 1 = Mp := by rw [hMp]; unfold torusM; simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hc : 0 ≤ kernelC1 d * δp := mul_nonneg (kernelC1_nonneg d) hδ0
  have hw1 : 0 ≤ pw τ 1 * Mp := mul_nonneg (pw_nonneg hτ 1) (by linarith)
  have h0 := torus_reduction_redC hσ hσ1 d hd X h_indep hX hlaw N J hN2 (by omega) hMp hδp hrange
  have hf := kernel_trace_G28 hσ hσ1 d hd X h_indep hX hlaw N J hN2 (by omega) hMp hδp hrange
  obtain ⟨hn8, hn⟩ := norm_sample hσ hσ1 d hd X h_indep hX hlaw N J hN2 (by omega) hMp hδp
    hrange
  obtain ⟨bG, hG⟩ := weighted_abs_bound (μ := μ) (Finset.Icc 1 J)
    (fun k ω => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)))
    (fun k => pw τ (k + 1)) (fun k => piC d * (torusM d σ 1 / N) * k * torusM d σ k)
    (fun k _ => pw_nonneg hτ (k + 1))
    (fun k hk => pi_bound X h_indep hX hlaw hσ k (Finset.mem_Icc.mp hk).1 N (by omega)
      (by rw [hM1e]; linarith))
  have hB : ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * (piC d * (torusM d σ 1 / N) * k * torusM d σ k)
      = piC d * (Mp / N) * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k) := by
    rw [hM1e, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hG' : ∫ ω, ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1)
        * |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))| ∂μ
      ≤ piC d * (Mp / N) * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k) :=
    le_trans hG (le_of_eq hB)
  obtain ⟨bJ, hJ1⟩ := j1stat_bound (μ := μ) X h_indep hX hlaw hσ N (by omega)
    (by rw [hM1e]; linarith)
  rw [hM1e] at hJ1
  have bJ' : BM (fun ω => pw τ 1 * Mp * j1stat d σ N X ω) := BM.const_mul _ bJ
  have hsum : ∫ ω, (pw τ 1 * Mp * j1stat d σ N X ω
        + ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1)
          * |torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|) ∂μ
      ≤ 7 * (Mp / N) * (pw τ 1 * Mp) + piC d * (Mp / N)
          * (∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k)) := by
    rw [integral_add bJ'.integrable bG.integrable, integral_const_mul]
    have := mul_le_mul_of_nonneg_left hJ1 hw1
    linarith
  have hmk := markov_bm (bJ'.add bG)
    (fun ω => add_nonneg (mul_nonneg hw1 (j1stat_nonneg d σ N X ω))
      (Finset.sum_nonneg (fun k _ => mul_nonneg (pw_nonneg hτ (k + 1)) (abs_nonneg _))))
    hsum ht
  refine le_trans (four_step (μ := μ)
    (Z := fun ω => (NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ)
    (A := 14 * (normC d * δp) ^ 2 * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1))
    h0 hf hn hmk ?_) (le_of_eq (by ring))
  intro ω g1 g2 g3
  have hone0 := trace_one_det hσ d N (by omega) (fun j => X j ω) hn8 g3
  rw [j1stat_eq d σ N (by omega) X ω] at hone0
  have hone : |((walkMatrix
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
          (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ 1).trace - torusM d σ 1|
      ≤ (j1stat d σ N X ω + 14 * (normC d * δp) ^ 2) * torusM d σ 1 := by
    rw [pow_one]
    exact le_trans hone0 (le_of_eq (mul_comm _ _))
  have hm2 : 0 ≤ torusM d σ 2 := le_trans zero_le_one (heatMode_ge_one hσ d (by omega))
  have htwo : |((walkMatrix
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
          (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ 2).trace - torusM d σ 2|
      ≤ torusM d σ 2 := by
    have h := g2 2 (by omega) hJ
    have hsq2 : kernelC1 d * δp * Real.sqrt ((2 : ℕ) : ℝ) ≤ 1 := by
      have h2J : (((2 : ℕ) : ℝ)) ≤ (J : ℝ) := by exact_mod_cast hJ
      exact le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2J) hc) hrange
    exact le_trans h (mul_le_of_le_one_left hm2 hsq2)
  have hdet := trace_second_det2 hσ d N J (by omega) (fun j => X j ω) hτ
    (fun k => torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)))
    hone htwo (fun k hk hkJ => g1 k hk hkJ)
  rw [hM1e] at hdet
  exact le_trans hdet (le_of_eq (by ring))

/-! ### Step 4: the relative form -/

/-- **The second stage for the heat trace, relative form, with the index `j = 1` in second
    order.** In the situation of `second_stage_trace2` let moreover `τ ≥ 2`,
    `3τ + 2 log N ≤ J + 2` and `s > 0`; `δ = normC d · δ'`, `T = poissonMean d σ τ`. Then
    `P(|(Tr exp(τ(S-1)) - N e^{-τ})/T - 1|
         > (C_red δ'² + s C_Π M/N) τ + (14 δ² + 7 s M/N)(w_1(τ) M/T) + 4M/N²) ≤ 12/N³ + 1/s`.
    No term of first order in `δ'` is left (`δ² = normC² δ'²`, `δ'² = M log N/N`,
    `w_1 M/T ≤ 1`). -/
theorem second_stage_trace_rel2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 2 ≤ τ)
    (hJτ : 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 2) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | (redC d * δp ^ 2 + s * piC d * (Mp / N)) * τ
          + (14 * (normC d * δp) ^ 2 + 7 * s * (Mp / N)) * (pw τ 1 * Mp / poissonMean d σ τ)
          + 4 * (Mp / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|}
      ≤ 12 / (N : ℝ) ^ 3 + 1 / s := by
  have hτ0 : 0 ≤ τ := by linarith
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N J hN2 (by omega) hMp hδp hrange
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMp0 : 0 ≤ Mp := by linarith
  have hM1e : torusM d σ 1 = Mp := by rw [hMp]; unfold torusM; simp
  have hT : 3 / 4 ≤ poissonMean d σ τ := by
    have h1 := poissonMean_ge hσ d hτ0
    have h2 := exp_neg_le_quarter hτ
    linarith
  have hMN0 : 0 < Mp / N := div_pos (by linarith) hNpos
  have hw1 : 0 ≤ pw τ 1 * Mp := mul_nonneg (pw_nonneg hτ0 1) hMp0
  have hB0 : 0 < piC d * (Mp / N) * (τ * poissonMean d σ τ) + 7 * (Mp / N) * (pw τ 1 * Mp) :=
    add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos (piC_pos d) hMN0) (mul_pos (by linarith) (by linarith)))
      (mul_nonneg (mul_nonneg (by norm_num) hMN0.le) hw1)
  have ht : 0 < s * (piC d * (Mp / N) * (τ * poissonMean d σ τ)
      + 7 * (Mp / N) * (pw τ 1 * Mp)) := mul_pos hs hB0
  have h := second_stage_trace2 hσ hσ1 d hd X h_indep hX hlaw N J hN2 hJ hMp hδp hrange hτ0
    (s * (piC d * (Mp / N) * (τ * poissonMean d σ τ) + 7 * (Mp / N) * (pw τ 1 * Mp))) ht
  have hS1 := weighted_sum_le hσ d J hτ0
  have hS2 := weighted_sum_le' hσ d J hτ0
  have hprob : (7 * (Mp / N) * (pw τ 1 * Mp) + piC d * (Mp / N)
        * (∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k)))
        / (s * (piC d * (Mp / N) * (τ * poissonMean d σ τ) + 7 * (Mp / N) * (pw τ 1 * Mp)))
      ≤ 1 / s := by
    rw [div_le_iff₀ ht]
    have e : 1 / s * (s * (piC d * (Mp / N) * (τ * poissonMean d σ τ)
          + 7 * (Mp / N) * (pw τ 1 * Mp)))
        = piC d * (Mp / N) * (τ * poissonMean d σ τ) + 7 * (Mp / N) * (pw τ 1 * Mp) := by
      rw [show 1 / s * (s * (piC d * (Mp / N) * (τ * poissonMean d σ τ)
            + 7 * (Mp / N) * (pw τ 1 * Mp)))
          = s / s * (piC d * (Mp / N) * (τ * poissonMean d σ τ)
            + 7 * (Mp / N) * (pw τ 1 * Mp)) by ring, div_self hs.ne', one_mul]
    rw [e]
    have := mul_le_mul_of_nonneg_left hS1 (mul_nonneg (piC_pos d).le hMN0.le)
    linarith
  have hpt : Mp * ptail τ (J + 1) ≤ Mp / (N : ℝ) ^ 2 := by
    have hJ' : 3 * τ + 2 * Real.log N ≤ ((J + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hp := ptail_le_inv_sq hτ0 (J + 1) N (by omega) hJ'
    have := mul_le_mul_of_nonneg_left hp hMp0
    rw [mul_one_div] at this
    exact this
  have hq : 0 ≤ Mp / (N : ℝ) ^ 2 := div_nonneg hMp0 (by positivity)
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (h.trans (add_le_add le_rfl hprob))
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  have hr := rel_arith (c := 14 * (normC d * δp) ^ 2 + 7 * s * (Mp / N))
    (u := s * piC d * (Mp / N)) hT (mul_nonneg (redC_nonneg d) (pow_nonneg hδ0 2)) hS2 hq hpt hω
  refine lt_of_eq_of_lt ?_ hr
  ring

/-- **The same without the weight of the index `j = 1`** (`w_1 M ≤ T`):
    `P(|(Tr exp(τ(S-1)) - N e^{-τ})/T - 1|
         > (C_red δ'² + s C_Π M/N) τ + 14 δ² + 7 s M/N + 4M/N²) ≤ 12/N³ + 1/s`,
    `δ = normC d · δ'`. Every term is of the order `δ'² τ = (M log N/N) τ`, `s (M/N) τ` or
    smaller: the first display of `cor:secondstage-alld` for fixed `N`, with `τ` in place of `J`,
    with the constants and the exceptional event of this file. -/
theorem second_stage_trace_rel2' {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 2 ≤ τ)
    (hJτ : 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 2) (s : ℝ) (hs : 0 < s) :
    μ.real {ω | (redC d * δp ^ 2 + s * piC d * (Mp / N)) * τ
          + 14 * (normC d * δp) ^ 2 + 7 * s * (Mp / N) + 4 * (Mp / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|}
      ≤ 12 / (N : ℝ) ^ 3 + 1 / s := by
  have hτ0 : 0 ≤ τ := by linarith
  obtain ⟨hM1, hMN, hδ0, hsq, hlog⟩ := ss_setup hσ d N J hN2 (by omega) hMp hδp hrange
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hM1e : torusM d σ 1 = Mp := by rw [hMp]; unfold torusM; simp
  have hT : 3 / 4 ≤ poissonMean d σ τ := by
    have h1 := poissonMean_ge hσ d hτ0
    have h2 := exp_neg_le_quarter hτ
    linarith
  have hTpos : 0 < poissonMean d σ τ := by linarith
  have hw : pw τ 1 * Mp / poissonMean d σ τ ≤ 1 := by
    rw [div_le_one hTpos, ← hM1e]
    exact pw_one_le_poissonMean hσ d hτ0
  have hc0 : 0 ≤ 14 * (normC d * δp) ^ 2 + 7 * s * (Mp / N) :=
    add_nonneg (mul_nonneg (by norm_num) (_root_.sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hs.le) (div_nonneg (by linarith) hNpos.le))
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _))
    (second_stage_trace_rel2 hσ hσ1 d hd X h_indep hX hlaw N J hN2 hJ hMp hδp hrange hτ hJτ s hs)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  have := mul_le_mul_of_nonneg_left hw hc0
  linarith

end SecondStageTrace2

/-! ## The second stage as a LIMIT STATEMENT in probability (`cor:secondstage-alld`).

`SecondStageTrace2.second_stage_trace_rel2'` is a bound for a fixed sample size `N`, with free
parameters `J` (truncation of the Poisson sum) and `s` (Markov). Here the parameters are chosen
as functions of `N` and the smallness condition `C₁ δ' √J ≤ 1` is derived from the regime, as in
`namespace Regime`. The sample is nested: the first `N` points of one sequence
`X : ℕ → Ω → FlatTorus d`. `σ_N` is the variance of the kernel (`σ = ξ²`), `τ_N` the Poisson
parameter (`τ = 2t/ξ²`; `2 ≤ τ ≤ c/σ` is `ξ² ≤ t ≤ c/2`, so `c = 2` is `t ≤ 1`).

What is proved (independent uniform points on the flat torus of dimension `d ≥ 1`, graph with
self-loops, eventually `0 < σ_N ≤ 1` and `2 ≤ τ_N ≤ c/σ_N`):

* `second_stage_ceil`: under `N σ_N^{d/2+1}/log N → ∞` (`N ξ^{d+2}/log N → ∞`), for all large `N`
  and EVERY `s > 0`, the bound of `second_stage_trace_rel2'` with `J_N = ⌈3c/σ_N + 2 log N⌉`;
  no hypothesis on `J` or on the smallness is left.
* `second_stage_OP`, `second_stage_tight`: under the same regime the relative error of the
  subtracted heat trace is `O_P((M_N log N/N) τ_N)`: for every `ε > 0` there is a constant `C`
  with `P(error > C (M_N log N/N) τ_N) ≤ ε` for all large `N`. This is the first display of
  `cor:secondstage-alld` with `τ` in place of `J` (so the factor is `τ_N`, not `τ_N + log N`).
* `second_stage_limit_eventually`, `second_stage_limit`: under `N σ_N^{d/2+2}/log N → ∞`
  (`N ξ^{d+4}/log N → ∞`), for every `η > 0`,
  `P(|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/T - 1| > η σ_N) → 0`: the error is `o_P(ξ_N²)`.

What is NOT proved here: `poissonMean d σ τ` is the Poisson mean of the heat-kernel values
`∑_{j≥1} w_j(τ) p_{jσ}(0)`; it is not identified with `T_σ(t)` of the paper as defined there, and
`exp(τ(S-1))` is not identified with `e^{-tL}` by a theorem. The statements are for ONE sequence
`τ_N` (each `N` has its own exceptional event; no uniformity in `τ`). The exceptional events are
those of this file; their measurability is not shown (`μ.real` of a set that need not be
measurable is the outer measure). No sharp coefficient of the term of order `ξ²` is obtained:
only that the random error is `o_P(ξ²)`. Neither `ξ_N → 0` nor `τ_N → ∞` is assumed. -/

namespace SecondStageLimit

open Filter Topology
open CTG.Reals.TorusReduction CTG.Reals.TraceG29 TorusReductionL1 H5 PiBound SecondStage
  SecondStageTrace SecondStageTrace2 Regime

/-! ### Stage 1: deterministic estimates of the threshold (real numbers only) -/

/-- Abstract form of the threshold estimate for the limit: `b` stands for `M log N/N`, `m` for
    `M/N`, `q` for `M/N²`, `E σ²` bounds `b`, and `τ σ ≤ c`. -/
theorem abs_limit {b m q σ τ c s R P Q E : ℝ} (hmb : m ≤ b) (hq : q ≤ m)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hτ0 : 0 ≤ τ) (hτ : τ * σ ≤ c) (hs : 0 ≤ s)
    (hR : 0 ≤ R) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hE : 0 ≤ E) (hB : b ≤ E * σ ^ 2) :
    (R * b + s * P * m) * τ + Q * b + 7 * s * m + 4 * q
      ≤ σ * (E * ((R * c + Q + 4) + s * (P * c + 7))) := by
  have hEσ : 0 ≤ E * σ := mul_nonneg hE hσ.le
  have hb1 : b ≤ E * σ := by
    have := mul_nonneg hEσ (sub_nonneg.2 hσ1)
    nlinarith
  have hbt : b * τ ≤ E * σ * c := by
    calc b * τ ≤ E * σ ^ 2 * τ := mul_le_mul_of_nonneg_right hB hτ0
      _ = E * σ * (τ * σ) := by ring
      _ ≤ E * σ * c := mul_le_mul_of_nonneg_left hτ hEσ
  have hmt : m * τ ≤ E * σ * c := (mul_le_mul_of_nonneg_right hmb hτ0).trans hbt
  have a1 := mul_le_mul_of_nonneg_left hbt hR
  have a2 := mul_le_mul_of_nonneg_left hmt (mul_nonneg hs hP)
  have a3 := mul_le_mul_of_nonneg_left hb1 hQ
  have a4 := mul_le_mul_of_nonneg_left (hmb.trans hb1)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) hs)
  have a5 : q ≤ E * σ := hq.trans (hmb.trans hb1)
  nlinarith [a1, a2, a3, a4, a5]

/-- Abstract form of the threshold estimate for the `O_P` statement (`τ ≥ 1`). -/
theorem abs_OP {b m q τ s R P Q : ℝ} (hm0 : 0 ≤ m) (hmb : m ≤ b) (hq : q ≤ m)
    (hτ : 1 ≤ τ) (hs : 0 ≤ s) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (R * b + s * P * m) * τ + Q * b + 7 * s * m + 4 * q
      ≤ (R + Q + 4 + s * (P + 7)) * b * τ := by
  have hτ0 : 0 ≤ τ := by linarith
  have hb0 : 0 ≤ b := hm0.trans hmb
  have hbτ : b ≤ b * τ := by
    have := mul_nonneg hb0 (sub_nonneg.2 hτ)
    nlinarith
  have t1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmb hτ0) (mul_nonneg hs hP)
  have t2 := mul_le_mul_of_nonneg_left hbτ hQ
  have t3 := mul_le_mul_of_nonneg_left (hmb.trans hbτ)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7) hs)
  have t4 : q ≤ b * τ := hq.trans (hmb.trans hbτ)
  nlinarith [t1, t2, t3, t4]

/-- `0 ≤ M/n ≤ M L/n` and `M/n² ≤ M/n` for `M ≥ 0`, `n ≥ 1`, `L ≥ 1`. -/
theorem ratio_facts {M n L : ℝ} (hM : 0 ≤ M) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    0 ≤ M / n ∧ M / n ≤ M * L / n ∧ M / n ^ 2 ≤ M / n := by
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨div_nonneg hM hn0.le, div_le_div_of_nonneg_right ?_ hn0.le,
    div_le_div_of_nonneg_left hM hn0 ?_⟩
  · have := mul_nonneg hM (sub_nonneg.2 hL)
    nlinarith
  · have := mul_nonneg hn0.le (sub_nonneg.2 hn)
    nlinarith

/-- `M ≤ 2^d/r` gives `M L/n ≤ (2^d/A) σ²` for `A = n r σ²/L`. -/
theorem hB_core {M n L r σ : ℝ} (d : ℕ) (hM : M ≤ 2 ^ d / r) (hr : 0 < r) (hL : 0 < L)
    (hn : 0 < n) (hσ : 0 < σ) :
    M * L / n ≤ 2 ^ d / (n * r * σ ^ 2 / L) * σ ^ 2 := by
  have e : 2 ^ d / (n * r * σ ^ 2 / L) * σ ^ 2 = 2 ^ d / r * L / n := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM hL.le) hn.le

/-- **The threshold of `second_stage_trace_rel2'` with `s = √A` is at most `η σ`** as soon as
    `A ≥ 1` and `A ≥ (2^d (R c + 14 Nc² + 4 + P c + 7)/η)²`; here `δ² = M L/n ≤ (2^d/A) σ²`
    and `τ ≤ c/σ`. -/
theorem thr_sqrt {M n L σ τ c R P Nc δ A η : ℝ} (d : ℕ) (hM : 0 ≤ M) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hτ0 : 0 ≤ τ) (hτ : τ ≤ c / σ) (hR : 0 ≤ R) (hP : 0 ≤ P)
    (hδ : δ ^ 2 = M * L / n) (hη : 0 < η) (hA1 : 1 ≤ A)
    (hB : M * L / n ≤ 2 ^ d / A * σ ^ 2)
    (hAη : (2 ^ d * ((R * c + 14 * Nc ^ 2 + 4) + (P * c + 7)) / η) ^ 2 ≤ A) :
    (R * δ ^ 2 + Real.sqrt A * P * (M / n)) * τ + 14 * (Nc * δ) ^ 2
        + 7 * Real.sqrt A * (M / n) + 4 * (M / n ^ 2) ≤ η * σ := by
  have hA0 : 0 < A := by linarith
  have hw0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hw : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0.le
  have hw1 : 1 ≤ Real.sqrt A := Real.sqrt_one.symm.le.trans (Real.sqrt_le_sqrt hA1)
  have h3 : τ * σ ≤ c := (le_div_iff₀ hσ).1 hτ
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hτ0 hσ.le) h3
  have hQ : 0 ≤ 14 * Nc ^ 2 := mul_nonneg (by norm_num) (_root_.sq_nonneg Nc)
  have hK1 : 0 ≤ R * c + 14 * Nc ^ 2 + 4 :=
    add_nonneg (add_nonneg (mul_nonneg hR hc0) hQ) (by norm_num)
  have hG : (0 : ℝ) ≤ 2 ^ d := pow_nonneg (by norm_num) d
  have hE : 0 ≤ 2 ^ d / A := div_nonneg hG hA0.le
  obtain ⟨f1, f2, f3⟩ := ratio_facts hM hn hL
  have core := abs_limit (s := Real.sqrt A) (R := R) (P := P) (Q := 14 * Nc ^ 2)
    f2 f3 hσ hσ1 hτ0 h3 hw0 hR hP hQ hE hB
  have hwη : 2 ^ d * ((R * c + 14 * Nc ^ 2 + 4) + (P * c + 7)) / η ≤ Real.sqrt A :=
    (le_abs_self _).trans (Real.abs_le_sqrt hAη)
  have hwη' : 2 ^ d * ((R * c + 14 * Nc ^ 2 + 4) + (P * c + 7)) ≤ Real.sqrt A * η :=
    (div_le_iff₀ hη).1 hwη
  have hηA : η * A = Real.sqrt A * η * Real.sqrt A := by
    calc η * A = η * (Real.sqrt A * Real.sqrt A) := by rw [hw]
      _ = Real.sqrt A * η * Real.sqrt A := by ring
  have hfin : 2 ^ d / A * ((R * c + 14 * Nc ^ 2 + 4) + Real.sqrt A * (P * c + 7)) ≤ η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hA0, hηA]
    have ha : 0 ≤ 2 ^ d * (R * c + 14 * Nc ^ 2 + 4) * (Real.sqrt A - 1) :=
      mul_nonneg (mul_nonneg hG hK1) (by linarith)
    have hb := mul_le_mul_of_nonneg_right hwη' hw0
    nlinarith [ha, hb]
  have e : (R * δ ^ 2 + Real.sqrt A * P * (M / n)) * τ + 14 * (Nc * δ) ^ 2
        + 7 * Real.sqrt A * (M / n) + 4 * (M / n ^ 2)
      = (R * (M * L / n) + Real.sqrt A * P * (M / n)) * τ + 14 * Nc ^ 2 * (M * L / n)
        + 7 * Real.sqrt A * (M / n) + 4 * (M / n ^ 2) := by
    rw [mul_pow, hδ]; ring
  rw [e]
  calc (R * (M * L / n) + Real.sqrt A * P * (M / n)) * τ + 14 * Nc ^ 2 * (M * L / n)
        + 7 * Real.sqrt A * (M / n) + 4 * (M / n ^ 2)
      ≤ σ * (2 ^ d / A * ((R * c + 14 * Nc ^ 2 + 4) + Real.sqrt A * (P * c + 7))) := core
    _ ≤ σ * η := mul_le_mul_of_nonneg_left hfin hσ.le
    _ = η * σ := mul_comm _ _

/-- **The threshold of `second_stage_trace_rel2'` is at most a constant times `(M L/n) τ`**
    (`τ ≥ 1`, `n ≥ 1`, `L ≥ 1`, `δ² = M L/n`). -/
theorem thr_OP {M n L τ s R P Nc δ : ℝ} (hM : 0 ≤ M) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hτ : 1 ≤ τ) (hs : 0 ≤ s) (hP : 0 ≤ P) (hδ : δ ^ 2 = M * L / n) :
    (R * δ ^ 2 + s * P * (M / n)) * τ + 14 * (Nc * δ) ^ 2 + 7 * s * (M / n) + 4 * (M / n ^ 2)
      ≤ (R + 14 * Nc ^ 2 + 4 + s * (P + 7)) * (M * L / n) * τ := by
  obtain ⟨f1, f2, f3⟩ := ratio_facts hM hn hL
  have hQ : 0 ≤ 14 * Nc ^ 2 := mul_nonneg (by norm_num) (_root_.sq_nonneg Nc)
  have core := abs_OP (R := R) f1 f2 f3 hτ hs hP hQ
  have e : (R * δ ^ 2 + s * P * (M / n)) * τ + 14 * (Nc * δ) ^ 2 + 7 * s * (M / n)
        + 4 * (M / n ^ 2)
      = (R * (M * L / n) + s * P * (M / n)) * τ + 14 * Nc ^ 2 * (M * L / n)
        + 7 * s * (M / n) + 4 * (M / n ^ 2) := by
    rw [mul_pow, hδ]; ring
  rw [e]
  exact core

/-- The regime with exponent `d/2+2` implies the regime with exponent `d/2+1` (`σ ≤ 1`):
    `N ξ^{d+4}/log N → ∞` implies `N ξ^{d+2}/log N → ∞`. -/
theorem regime_four_to_two (d : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N)
      atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ hreg
  filter_upwards [hσ, eventually_ge_atTop 2] with N h1 h4
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast h4
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hX : 0 ≤ (N : ℝ) * Real.sqrt (σ N) ^ d :=
    mul_nonneg (by linarith) (pow_nonneg (Real.sqrt_nonneg _) d)
  have hσσ : σ N ^ 2 ≤ σ N := by
    have := mul_nonneg h1.1.le (sub_nonneg.2 h1.2)
    nlinarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσσ hX) hL.le

/-- `12/N³ → 0`. -/
theorem tendsto_twelve_div_cube :
    Tendsto (fun N : ℕ => 12 / (N : ℝ) ^ 3) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

/-! ### Stage 2: statements about the sample -/

/-- **The finite form with `J_N = ⌈3c/σ_N + 2 log N⌉`, smallness derived from the regime.**
    If eventually `0 < σ_N ≤ 1`, `2 ≤ τ_N ≤ c/σ_N`, and `N σ_N^{d/2+1}/log N → ∞`, then for all
    large `N` and EVERY `s > 0`, with `M = p_{σ_N}(0)`, `δ' = √(M log N/N)`:
    `P(|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/T - 1|
         > (C_red δ'² + s C_Π M/N) τ_N + 14 (normC δ')² + 7 s M/N + 4M/N²) ≤ 12/N³ + 1/s`. -/
theorem second_stage_ceil {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ τ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hτ : ∀ᶠ N in atTop, 2 ≤ τ N ∧ τ N ≤ c / σ N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℝ, 0 < s →
      μ.real {ω | (redC d
              * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N) ^ 2
            + s * piC d * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / N)) * τ N
          + 14 * (normC d
              * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)) ^ 2
          + 7 * s * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / N)
          + 4 * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|}
        ≤ 12 / (N : ℝ) ^ 3 + 1 / s := by
  have hJ2 := ceil_trace_ge_two σ hc hσ
  have hJ0 : ∀ᶠ N in atTop, 0 < ⌈3 * c / σ N + 2 * Real.log N⌉₊ :=
    hJ2.mono (fun N h => by omega)
  have hsmall := eventually_small d (kernelC1_nonneg d) σ
    (fun N => ⌈3 * c / σ N + 2 * Real.log N⌉₊) hσ hJ0
    (regime_ceil_trace d σ hc hσ (regime_log d σ hσ hreg)) one_pos
  filter_upwards [hσ, hτ, hsmall, hJ2, eventually_ge_atTop 2] with N h1 h2 h3 h4 h5
  intro s hs
  have h6 := Nat.le_ceil (3 * c / σ N + 2 * Real.log N)
  have h7 : 3 * c / σ N = 3 * (c / σ N) := by ring
  have hJτ : 3 * τ N + 2 * Real.log N
      ≤ ((⌈3 * c / σ N + 2 * Real.log N⌉₊ : ℕ) : ℝ) + 2 := by
    have := h2.2
    linarith
  exact second_stage_trace_rel2' h1.1 h1.2 d hd X h_indep hX hlaw N
    ⌈3 * c / σ N + 2 * Real.log N⌉₊ h5 h4 rfl rfl h3 h2.1 hJτ s hs

/-- **`O_P` form (first display of `cor:secondstage-alld`, with `τ` in place of `J`).** Under
    the assumptions of `second_stage_ceil` (`N ξ^{d+2}/log N → ∞`), for every `s > 0`, for all
    large `N`:
    `P(|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/T - 1|
         > (C_red + 14 normC² + 4 + s (C_Π + 7)) (M_N log N/N) τ_N) ≤ 12/N³ + 1/s`. -/
theorem second_stage_OP {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ τ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hτ : ∀ᶠ N in atTop, 2 ≤ τ N ∧ τ N ≤ c / σ N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop,
      μ.real {ω | (redC d + 14 * normC d ^ 2 + 4 + s * (piC d + 7))
            * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N) * τ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|}
        ≤ 12 / (N : ℝ) ^ 3 + 1 / s := by
  filter_upwards [second_stage_ceil d hd X h_indep hX hlaw σ τ hc hσ hτ hreg, hσ, hτ,
    eventually_ge_atTop 3] with N hfin h1 h2 h6
  have hN : (3 : ℝ) ≤ N := by exact_mod_cast h6
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hM : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ N) 0 :=
    (heatTorus_zero_pos (mul_pos (by positivity) h1.1) d).le
  have hnn : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N :=
    div_nonneg (mul_nonneg hM (by linarith)) (by linarith)
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (hfin s hs)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  refine lt_of_le_of_lt ?_ hω
  exact thr_OP hM (by linarith) hL (by linarith [h2.1]) hs.le (piC_pos d).le
    (Real.sq_sqrt hnn)

/-- **Tightness form of `second_stage_OP`:** the relative error of the subtracted heat trace is
    `O_P((M_N log N/N) τ_N)`. For every `ε > 0` there is a constant `C > 0` (depending on `d`
    and `ε` only) such that, for all large `N`,
    `P(|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/T - 1| > C (M_N log N/N) τ_N) ≤ ε`. -/
theorem second_stage_tight {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ τ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hτ : ∀ᶠ N in atTop, 2 ≤ τ N ∧ τ N ≤ c / σ N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      μ.real {ω | C * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N) * τ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|}
        ≤ ε := by
  have hs : 0 < 2 / ε := div_pos (by norm_num) hε
  have hC : 0 < redC d + 14 * normC d ^ 2 + 4 + 2 / ε * (piC d + 7) := by
    have h1 := redC_nonneg d
    have h2 : 0 ≤ 14 * normC d ^ 2 := mul_nonneg (by norm_num) (_root_.sq_nonneg _)
    have h3 : 0 ≤ 2 / ε * (piC d + 7) := mul_nonneg hs.le (by linarith [piC_pos d])
    linarith
  refine ⟨redC d + 14 * normC d ^ 2 + 4 + 2 / ε * (piC d + 7), hC, ?_⟩
  filter_upwards [second_stage_OP d hd X h_indep hX hlaw σ τ hc hσ hτ hreg (2 / ε) hs,
    (tendsto_order.1 tendsto_twelve_div_cube).2 (ε / 2) (half_pos hε)] with N h1 h2
  have e : 1 / (2 / ε) = ε / 2 := one_div_div 2 ε
  rw [e] at h1
  have h2' : 12 / (N : ℝ) ^ 3 < ε / 2 := h2
  linarith

/-- **The second stage in the limit, quantitative.** If eventually `0 < σ_N ≤ 1`,
    `2 ≤ τ_N ≤ c/σ_N`, and `A_N := N σ_N^{d/2+2}/log N → ∞` (with `σ = ξ²`:
    `N ξ^{d+4}/log N → ∞`), then for every `η > 0`, for all large `N`,
    `P(|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/T - 1| > η σ_N) ≤ 12/N³ + 1/√A_N`.
    (The Markov parameter of the finite form is `s_N = √A_N`.) -/
theorem second_stage_limit_eventually {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ τ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hτ : ∀ᶠ N in atTop, 2 ≤ τ N ∧ τ N ≤ c / σ N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N)
      atTop atTop) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      μ.real {ω | η * σ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|}
        ≤ 12 / (N : ℝ) ^ 3
          + 1 / Real.sqrt ((N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N) := by
  filter_upwards [second_stage_ceil d hd X h_indep hX hlaw σ τ hc hσ hτ
      (regime_four_to_two d σ hσ hreg), hσ, hτ,
    hreg.eventually_ge_atTop (max 1 ((2 ^ d * ((redC d * c + 14 * normC d ^ 2 + 4)
      + (piC d * c + 7)) / η) ^ 2)), eventually_ge_atTop 3] with N hfin h1 h2 h5 h6
  have hN : (3 : ℝ) ≤ N := by exact_mod_cast h6
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hM : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ N) 0 :=
    (heatTorus_zero_pos (mul_pos (by positivity) h1.1) d).le
  have hnn : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N :=
    div_nonneg (mul_nonneg hM (by linarith)) (by linarith)
  have hA1 : 1 ≤ (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N :=
    (le_max_left _ _).trans h5
  have hAη : (2 ^ d * ((redC d * c + 14 * normC d ^ 2 + 4) + (piC d * c + 7)) / η) ^ 2
      ≤ (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N := (le_max_right _ _).trans h5
  have hs : 0 < Real.sqrt ((N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N) :=
    Real.sqrt_pos.mpr (by linarith)
  have hB := hB_core (n := (N : ℝ)) (L := Real.log N) d (heatM_bound h1.1 h1.2 d)
    (pow_pos (Real.sqrt_pos.mpr h1.1) d) (by linarith) (by linarith) h1.1
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (hfin _ hs)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  refine lt_of_le_of_lt ?_ hω
  exact thr_sqrt d hM (by linarith) hL h1.1 h1.2 (by linarith [h2.1]) h2.2 (redC_nonneg d)
    (piC_pos d).le (Real.sq_sqrt hnn) hη hA1 hB hAη

/-- **The second stage as a limit in probability (`o_P(ξ²)` statement of
    `cor:secondstage-alld`).** Independent uniform points on the flat torus of dimension
    `d ≥ 1` (nested sample), kernel variance `σ_N = ξ_N²`, graph with self-loops. If eventually
    `0 < σ_N ≤ 1` and `2 ≤ τ_N ≤ c/σ_N`, and `N σ_N^{d/2+2}/log N → ∞` (`N ξ^{d+4}/log N → ∞`),
    then for every `η > 0`
    `P(|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/poissonMean d σ_N τ_N - 1| > η σ_N) → 0` as `N → ∞`. -/
theorem second_stage_limit {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ τ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hτ : ∀ᶠ N in atTop, 2 ≤ τ N ∧ τ N ≤ c / σ N)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N)
      atTop atTop) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      μ.real {ω | η * σ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|})
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ =>
      1 / Real.sqrt ((N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hreg)
  have h2 : Tendsto (fun N : ℕ => 12 / (N : ℝ) ^ 3
      + 1 / Real.sqrt ((N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N))
      atTop (𝓝 0) := by
    have := tendsto_twelve_div_cube.add h1
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall (fun N => measureReal_nonneg))
    (second_stage_limit_eventually d hd X h_indep hX hlaw σ τ hc hσ hτ hreg hη)

end SecondStageLimit

/-! ### The heat trace of the graph WITHOUT self-loops, for a fixed sample size

A finite form of the second display of Corollary "The graph without self-loops"
(`cor:kernel-noloops`). What is proved here, and what is not:

* `noloopSym` is the symmetric matrix `S° = D°^{-1/2} W° D°^{-1/2}` of the graph whose kernel has
  the diagonal removed (`symGraph` of the second file with the kernel and the normalisation of
  `NoLoops.noloopWalk`). For `N ≥ 2` and every configuration of points it is symmetric,
  `Tr (S°)^k = Tr (P°)^k` for every `k`, and `|Tr (S°)^k| ≤ Tr (S°)²` for `k ≥ 2`
  (`noloop_sym_facts`); `Tr P° = 0` (`noloopWalk_trace`). No event is needed for these.
* `noloop_heat_trace_det` (deterministic) and `noloop_heat_trace_sample` (probability):
  `|Tr exp(τ(S° - 1)) - N e^{-τ} - (T - w_1 M)|
      ≤ C₁ δ' √J (T - w_1 M) + 96 (M²/N) τ (1 - e^{-τ}) + (3M + 192 M²/N) (1 - ∑_{j≤J} w_j)`,
  with `T = poissonMean`, `w_1 M = τ e^{-τ} M` (the term `τ e^{-τ} M` of the paper), except on the
  event of `NoLoops.noloop_trace_sample` (probability at most `4/N³`).
* `noloop_heat_trace_ratio`: the same divided by `T`, for `τ ≥ 2`, `3τ + 2 log N ≤ J + 1`.
* `noloop_heat_trace_ratio_small`: under the ADDITIONAL condition `M ≤ C₁ log N` the additional
  term is absorbed, and the bound has the form `(C₁ + 96) δ' √J + 5M/N²` of the corollary.

NOT the corollary of the paper: fixed `N` (no "almost surely for all large `N`"); `J` is a free
integer with `C₁ δ' √J ≤ 1` (the paper takes `J = ⌈8τ⌉ + ⌈2 log N⌉`); the comparison of the walk
without self-loops goes through the walk WITH self-loops (perturbation), which produces the
additional term `96 (M²/N) τ` instead of the constant `C₁' = C₁ + 3·2^{d/2}` of the paper; the
constant `C₁ = kernelC1 d` and the exceptional event are those of the file; that
`Tr exp(τ(S° - 1))` is `Tr e^{-tL°}` with `τ = 2t/ξ²` and that `poissonMean` is `T_σ(t)` are not
statements of the file; the last assertion of the corollary (`τ e^{-τ} M ≤ C τ^{1+d/2} e^{-τ} Θ`,
and the statements on the rate) is not formalised; the exceptional sets are not shown to be
measurable (the bounds are bounds for the outer measure). -/

namespace NoLoopsTrace

open CTG.Reals.TraceG29 NoLoops

/-- The kernel with the diagonal removed. -/
noncomputable def noloopK (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) : Fin N → Fin N → ℝ :=
  fun a j : Fin N => if a = j then 0 else heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j)

/-- The normalisation of the graph without self-loops, `ρ°_a = ρ_a - p_σ(0)/N`. -/
noncomputable def noloopRho (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) : Fin N → ℝ :=
  fun a : Fin N => heatRho d σ N x a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N

/-- The symmetric matrix `S° = D°^{-1/2} W° D°^{-1/2}` of the graph without self-loops. -/
noncomputable def noloopSym (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) :
    Matrix (Fin N) (Fin N) ℝ :=
  symGraph (noloopK d σ N x) (noloopRho d σ N x)

/-- The walk `NoLoops.noloopWalk` is the walk matrix of this kernel and this normalisation. -/
theorem noloopWalk_eq (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) :
    noloopWalk d σ N x = walkMatrix (noloopK d σ N x) (noloopRho d σ N x) := rfl

theorem exists_ne_fin {N : ℕ} (hN : 2 ≤ N) (a : Fin N) : ∃ b : Fin N, b ≠ a := by
  by_cases h : a.val = 0
  · refine ⟨⟨1, by omega⟩, fun hb => ?_⟩
    have h1 : (1 : ℕ) = a.val := congrArg Fin.val hb
    omega
  · refine ⟨⟨0, by omega⟩, fun hb => ?_⟩
    have h1 : (0 : ℕ) = a.val := congrArg Fin.val hb
    omega

theorem noloopK_symm (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (a j : Fin N) :
    noloopK d σ N x a j = noloopK d σ N x j a := by
  show (if a = j then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
    = (if j = a then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x a))
  by_cases h : a = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), ← heatTorus_even d _ (x j - x a), neg_sub]

theorem noloopK_nonneg {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (x : ℕ → FlatTorus d) (a j : Fin N) :
    0 ≤ noloopK d σ N x a j := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  show 0 ≤ (if a = j then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
  by_cases h : a = j
  · rw [if_pos h]
  · rw [if_neg h]; exact heatTorus_nonneg hcσ d _

theorem noloopK_pos {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (x : ℕ → FlatTorus d) {a j : Fin N}
    (h : a ≠ j) : 0 < noloopK d σ N x a j := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  show 0 < (if a = j then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
  rw [if_neg h]; exact heatTorus_pos hcσ d _

/-- `ρ°_a = (1/N) ∑_{l ≠ a} p_σ(x_a - x_l)`. -/
theorem noloopRho_eq (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (a : Fin N) :
    noloopRho d σ N x a
      = (∑ l ∈ Finset.univ.erase a, heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) / N := by
  show heatRho d σ N x a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N = _
  unfold heatRho
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ a), sub_self,
    Finset.sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l))]
  ring

theorem noloopRho_pos {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 2 ≤ N) (x : ℕ → FlatTorus d)
    (a : Fin N) : 0 < noloopRho d σ N x a := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨b, hb⟩ := exists_ne_fin hN a
  rw [noloopRho_eq]
  exact div_pos (Finset.sum_pos (fun l _ => heatTorus_pos hcσ d _)
    ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩⟩) hNpos

theorem noloop_degree_pos {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 2 ≤ N) (x : ℕ → FlatTorus d)
    (i : Fin N) :
    0 < ∑ l, noloopK d σ N x i l / (noloopRho d σ N x i * noloopRho d σ N x l) := by
  obtain ⟨b, hb⟩ := exists_ne_fin hN i
  have hrho := noloopRho_pos hσ d N hN x
  refine Finset.sum_pos' (fun l _ => div_nonneg (noloopK_nonneg hσ d N x i l)
    (mul_pos (hrho i) (hrho l)).le) ⟨b, Finset.mem_univ b, ?_⟩
  exact div_pos (noloopK_pos hσ d N x (Ne.symm hb)) (mul_pos (hrho i) (hrho b))

/-- The diagonal of the walk without self-loops vanishes, for every configuration of points. -/
theorem noloopWalk_diag (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (a : Fin N) :
    noloopWalk d σ N x a a = 0 := by
  rw [noloopWalk_eq]
  simp [walkMatrix, noloopK]

/-- `Tr P° = 0`, for every configuration of points. -/
theorem noloopWalk_trace (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) :
    (noloopWalk d σ N x).trace = 0 := by
  rw [Matrix.trace]
  exact Finset.sum_eq_zero fun a _ => by rw [Matrix.diag_apply]; exact noloopWalk_diag d σ N x a

/-- **The symmetric matrix of the graph without self-loops (deterministic, `N ≥ 2`).** `S°` is
    symmetric, `Tr (S°)^k = Tr (P°)^k` for all `k`, and `|Tr (S°)^k| ≤ Tr (S°)²` for `k ≥ 2`. -/
theorem noloop_sym_facts {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 2 ≤ N) (x : ℕ → FlatTorus d) :
    (noloopSym d σ N x).IsHermitian ∧
    (∀ k : ℕ, ((noloopSym d σ N x) ^ k).trace = ((noloopWalk d σ N x) ^ k).trace) ∧
    (∀ k : ℕ, 2 ≤ k →
      |((noloopSym d σ N x) ^ k).trace| ≤ ((noloopSym d σ N x) ^ 2).trace) := by
  have hKs := noloopK_symm d σ N x
  have hK0 := noloopK_nonneg hσ d N x
  have hrho := noloopRho_pos hσ d N hN x
  have hD := noloop_degree_pos hσ d N hN x
  refine ⟨symGraph_isHermitian _ _ hKs, fun k => ?_, fun k hk => ?_⟩
  · rw [noloopWalk_eq]
    exact symGraph_trace_pow _ _ hD k
  · exact (symGraph_trace_bounds (noloopK d σ N x) (noloopRho d σ N x) hKs hK0 hrho hD k).2 hk

/-! #### The Poisson splitting with absolute errors -/

/-- Splitting of a Poisson mean at an index `J` with absolute errors `e_j`.
    HYPOTHESES: the two sums exist (`hA`, `hT`). -/
theorem poisson_split_abs {τ : ℝ} (hτ : 0 ≤ τ) (a m e : ℕ → ℝ) (J : ℕ) {A T B B' : ℝ}
    (hA : HasSum (fun j : ℕ => pw τ (j + 1) * a (j + 1)) A)
    (hT : HasSum (fun j : ℕ => pw τ (j + 1) * m (j + 1)) T)
    (hlow : ∀ j, 1 ≤ j → j ≤ J → |a j - m j| ≤ e j)
    (hB : ∀ j, J < j → |a j| ≤ B) (hB' : ∀ j, J < j → |m j| ≤ B') :
    |A - T| ≤ ∑ j ∈ Finset.range J, pw τ (j + 1) * e (j + 1) + (B + B') * ptail τ J := by
  have hdiff : HasSum (fun j : ℕ => pw τ (j + 1) * a (j + 1) - pw τ (j + 1) * m (j + 1))
      (A - T) := hA.sub hT
  have h2 : HasSum (fun j : ℕ => if j < J then pw τ (j + 1) * e (j + 1) else 0)
      (∑ j ∈ Finset.range J, pw τ (j + 1) * e (j + 1)) := by
    have h : HasSum (fun j : ℕ => if j < J then pw τ (j + 1) * e (j + 1) else 0)
        (∑ j ∈ Finset.range J, (if j < J then pw τ (j + 1) * e (j + 1) else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by rw [Finset.mem_range] at hb; simp [hb])
    have e' : ∑ j ∈ Finset.range J, (if j < J then pw τ (j + 1) * e (j + 1) else 0)
        = ∑ j ∈ Finset.range J, pw τ (j + 1) * e (j + 1) :=
      Finset.sum_congr rfl (fun j hj => by rw [if_pos (Finset.mem_range.mp hj)])
    rw [e'] at h
    exact h
  have h3 := h2.add ((ptail_hasSum τ J).mul_left (B + B'))
  refine abs_le_of_hasSum hdiff h3 (fun j => ?_)
  have hw := pw_nonneg hτ (j + 1)
  beta_reduce
  by_cases hj : j < J
  · simp only [if_pos hj, mul_zero, add_zero]
    rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (hlow (j + 1) (by omega) (by omega)) hw
  · simp only [if_neg hj, zero_add]
    rw [← mul_sub, abs_mul, abs_of_nonneg hw, mul_comm (B + B')]
    refine mul_le_mul_of_nonneg_left ?_ hw
    have h1 := hB (j + 1) (by omega)
    have h2' := hB' (j + 1) (by omega)
    have h3' : |a (j + 1) - m (j + 1)| ≤ |a (j + 1)| + |m (j + 1)| := by
      rcases abs_cases (a (j + 1) - m (j + 1)) with h | h <;>
        rcases abs_cases (a (j + 1)) with h' | h' <;>
        rcases abs_cases (m (j + 1)) with h'' | h'' <;> linarith
    linarith

/-- `(k+1) w_{k+1}(τ) = τ w_k(τ)`. -/
theorem pw_succ_mul (τ : ℝ) (k : ℕ) : pw τ (k + 1) * ((k : ℝ) + 1) = τ * pw τ k := by
  have hk : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have key : ∀ a b f : ℝ, b ≠ 0 → a / (b * f) * b = a / f := by
    intro a b f hb
    rw [div_mul_eq_mul_div, mul_comm a b, mul_div_mul_left _ _ hb]
  unfold pw
  rw [hk, pow_succ]
  calc Real.exp (-τ) * (τ ^ k * τ / (((k : ℝ) + 1) * (k.factorial : ℝ))) * ((k : ℝ) + 1)
      = Real.exp (-τ) * (τ ^ k * τ / (((k : ℝ) + 1) * (k.factorial : ℝ)) * ((k : ℝ) + 1)) := by
        ring
    _ = Real.exp (-τ) * (τ ^ k * τ / (k.factorial : ℝ)) := by rw [key _ _ _ hk1]
    _ = τ * (Real.exp (-τ) * (τ ^ k / (k.factorial : ℝ))) := by ring

/-- The population values for the graph without self-loops: `0` for `j = 1` (because
    `Tr P° = 0`) and `m_j = p_{jσ}(0)` otherwise. -/
noncomputable def modeNL (d : ℕ) (σ : ℝ) (j : ℕ) : ℝ := if j = 1 then 0 else heatMode d σ j

/-- The weight `j` for `j ≥ 2` and `0` for `j = 1`. -/
noncomputable def stepNL (j : ℕ) : ℝ := if j = 1 then 0 else (j : ℝ)

theorem modeNL_one (d : ℕ) (σ : ℝ) : modeNL d σ 1 = 0 := by
  unfold modeNL; rw [if_pos rfl]

theorem modeNL_of_two (d : ℕ) (σ : ℝ) {j : ℕ} (hj : 2 ≤ j) : modeNL d σ j = heatMode d σ j := by
  unfold modeNL; rw [if_neg (by omega)]

theorem modeNL_succ_nonneg {σ : ℝ} (hσ : 0 < σ) (d j : ℕ) : 0 ≤ modeNL d σ (j + 1) := by
  unfold modeNL
  by_cases h : j + 1 = 1
  · rw [if_pos h]
  · rw [if_neg h]; exact le_trans zero_le_one (heatMode_ge_one hσ d (by omega))

theorem stepNL_one : stepNL 1 = 0 := by
  unfold stepNL; rw [if_pos rfl]

theorem stepNL_of_two {j : ℕ} (hj : 2 ≤ j) : stepNL j = (j : ℝ) := by
  unfold stepNL; rw [if_neg (by omega)]

theorem stepNL_nonneg (j : ℕ) : 0 ≤ stepNL j := by
  unfold stepNL
  by_cases h : j = 1
  · rw [if_pos h]
  · rw [if_neg h]; exact Nat.cast_nonneg j

/-- `∑_{j≥2} w_j m_j = T - w_1 M`: the Poisson mean without its first term. -/
theorem modeNL_hasSum {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasSum (fun j : ℕ => pw τ (j + 1) * modeNL d σ (j + 1))
      (poissonMean d σ τ - pw τ 1 * heatTorus d (2 * Real.pi ^ 2 * σ) 0) := by
  have hmode1 : heatMode d σ 1 = heatTorus d (2 * Real.pi ^ 2 * σ) 0 := by
    unfold heatMode; rw [Nat.cast_one, one_mul]
  have h1 := (poissonMean_hasSum hσ d hτ).sub
    (hasSum_ite_eq (0 : ℕ) (pw τ 1 * heatTorus d (2 * Real.pi ^ 2 * σ) 0))
  have e : (fun j : ℕ => pw τ (j + 1) * modeNL d σ (j + 1))
      = fun j : ℕ => pw τ (j + 1) * heatMode d σ (j + 1)
          - (if j = 0 then pw τ 1 * heatTorus d (2 * Real.pi ^ 2 * σ) 0 else 0) := by
    funext j
    by_cases hj : j = 0
    · rw [if_pos hj, hj]
      show pw τ 1 * modeNL d σ 1 = pw τ 1 * heatMode d σ 1 - _
      rw [modeNL_one, hmode1]; ring
    · rw [if_neg hj, modeNL_of_two d σ (by omega : 2 ≤ j + 1)]; ring
  rw [e]
  exact h1

/-- `∑_{j=2}^{J} w_j j ≤ τ (1 - e^{-τ})`. -/
theorem stepNL_sum_le {τ : ℝ} (hτ : 0 ≤ τ) (J : ℕ) :
    ∑ j ∈ Finset.range J, pw τ (j + 1) * stepNL (j + 1) ≤ τ * (1 - Real.exp (-τ)) := by
  have hG : HasSum (fun j : ℕ => τ * pw τ j - (if j = 0 then τ * pw τ 0 else 0))
      (τ * 1 - τ * pw τ 0) :=
    ((pw_hasSum τ).mul_left τ).sub (hasSum_ite_eq (0 : ℕ) (τ * pw τ 0))
  have heq : ∀ j : ℕ, pw τ (j + 1) * stepNL (j + 1)
      = τ * pw τ j - (if j = 0 then τ * pw τ 0 else 0) := by
    intro j
    by_cases hj : j = 0
    · rw [if_pos hj, hj]
      show pw τ 1 * stepNL 1 = τ * pw τ 0 - τ * pw τ 0
      rw [stepNL_one]; ring
    · rw [if_neg hj, stepNL_of_two (by omega : 2 ≤ j + 1), sub_zero]
      have h := pw_succ_mul τ j
      push_cast
      exact h
  have hnn : ∀ j : ℕ, 0 ≤ τ * pw τ j - (if j = 0 then τ * pw τ 0 else 0) := fun j => by
    rw [← heq j]; exact mul_nonneg (pw_nonneg hτ (j + 1)) (stepNL_nonneg (j + 1))
  have hle := sum_le_hasSum (Finset.range J) (fun j _ => hnn j) hG
  calc ∑ j ∈ Finset.range J, pw τ (j + 1) * stepNL (j + 1)
      = ∑ j ∈ Finset.range J, (τ * pw τ j - (if j = 0 then τ * pw τ 0 else 0)) :=
        Finset.sum_congr rfl fun j _ => heq j
    _ ≤ τ * 1 - τ * pw τ 0 := hle
    _ = τ * (1 - Real.exp (-τ)) := by rw [pw_zero]; ring

/-! #### The heat trace, deterministic part -/

/-- **Deterministic part.** Points `x_0, …, x_{N-1}` on the flat torus, `N ≥ 2`, kernel of
    variance `σ` with the diagonal removed, `P°` the walk and `S°` the symmetric matrix,
    `M = p_σ(0)`. If for `2 ≤ k ≤ J`
    `|Tr P°^k - m_k| ≤ c √k m_k + 96 (M/N) ∑_{l=1}^k m_l` (HYPOTHESIS `hgood`: the conclusion of
    `NoLoops.noloop_trace_sample`), `2 ≤ J` and `c √J ≤ 1`, then with `T = ∑_{j≥1} w_j m_j`:
    `|Tr exp(τ(S°-1)) - N e^{-τ} - (T - w_1 M)|
       ≤ c √J (T - w_1 M) + 96 (M/N) M τ (1 - e^{-τ}) + (3M + 192 (M/N) M) (1 - ∑_{j≤J} w_j)`.
    The index `j = 1` contributes exactly zero on both sides (`Tr P° = 0`). -/
theorem noloop_heat_trace_det {σ : ℝ} (hσ : 0 < σ) (d N J : ℕ) (hN : 2 ≤ N) (hJ : 2 ≤ J)
    (x : ℕ → FlatTorus d) {τ c Mp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hτ : 0 ≤ τ) (hc : 0 ≤ c) (hc1 : c * Real.sqrt J ≤ 1)
    (hgood : ∀ k, 2 ≤ k → k ≤ J →
      |((noloopWalk d σ N x) ^ k).trace - mS d σ k|
        ≤ c * Real.sqrt k * mS d σ k
          + 96 * (Mp / N) * ∑ l ∈ Finset.range k, mS d σ (l + 1)) :
    |(NormedSpace.exp (τ • (noloopSym d σ N x - 1))).trace - (N : ℝ) * Real.exp (-τ)
        - (poissonMean d σ τ - pw τ 1 * Mp)|
      ≤ c * Real.sqrt J * (poissonMean d σ τ - pw τ 1 * Mp)
        + 96 * (Mp / N) * Mp * (τ * (1 - Real.exp (-τ)))
        + (3 * Mp + 192 * (Mp / N) * Mp) * ptail τ J := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hS, htr, hbd⟩ := noloop_sym_facts hσ d N hN x
  have hMp1 : 1 ≤ Mp := by rw [hMp]; exact heatTorus_zero_ge_one hcσ d
  have hMp0 : 0 ≤ Mp := by linarith
  have hq0 : 0 ≤ 96 * (Mp / N) := mul_nonneg (by norm_num) (div_nonneg hMp0 hNpos.le)
  have hκ0 : 0 ≤ 96 * (Mp / N) * Mp := mul_nonneg hq0 hMp0
  have hm1 : ∀ j, 1 ≤ j → 1 ≤ heatMode d σ j := fun j hj => heatMode_ge_one hσ d hj
  have hmM : ∀ j, 1 ≤ j → heatMode d σ j ≤ Mp := fun j hj => by
    rw [hMp]; exact heatMode_le hσ d hj
  have hmS : ∀ j, 1 ≤ j → mS d σ j = heatMode d σ j := fun j hj => mS_of_pos d σ hj
  have hsumle : ∀ j : ℕ, ∑ l ∈ Finset.range j, mS d σ (l + 1) ≤ (j : ℝ) * Mp := by
    intro j
    calc ∑ l ∈ Finset.range j, mS d σ (l + 1) ≤ ∑ _l ∈ Finset.range j, Mp :=
          Finset.sum_le_sum fun l _ => by
            rw [hmS (l + 1) (by omega)]; exact hmM (l + 1) (by omega)
      _ = (j : ℝ) * Mp := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the series
  have hA := subtracted_trace_hasSum (noloopSym d σ N x) hS τ
  rw [Fintype.card_fin] at hA
  have hT' : HasSum (fun j : ℕ => pw τ (j + 1) * modeNL d σ (j + 1))
      (poissonMean d σ τ - pw τ 1 * Mp) := by
    rw [hMp]; exact modeNL_hasSum hσ d hτ
  -- the indices up to J
  have hlow : ∀ j, 1 ≤ j → j ≤ J →
      |((noloopSym d σ N x) ^ j).trace - modeNL d σ j|
        ≤ c * Real.sqrt J * modeNL d σ j + 96 * (Mp / N) * Mp * stepNL j := by
    intro j hj hjJ
    rw [htr j]
    by_cases h1 : j = 1
    · rw [h1, pow_one, noloopWalk_trace, modeNL_one, stepNL_one]
      simp
    · have hj2 : 2 ≤ j := by omega
      have hg := hgood j hj2 hjJ
      rw [hmS j hj] at hg
      have hsq : Real.sqrt (j : ℝ) ≤ Real.sqrt (J : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hjJ)
      have hmj0 : 0 ≤ heatMode d σ j := le_trans zero_le_one (hm1 j hj)
      have h2 : c * Real.sqrt j * heatMode d σ j ≤ c * Real.sqrt J * heatMode d σ j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc) hmj0
      have h3 : 96 * (Mp / N) * ∑ l ∈ Finset.range j, mS d σ (l + 1)
          ≤ 96 * (Mp / N) * ((j : ℝ) * Mp) := mul_le_mul_of_nonneg_left (hsumle j) hq0
      have e : 96 * (Mp / N) * Mp * (j : ℝ) = 96 * (Mp / N) * ((j : ℝ) * Mp) := by ring
      rw [modeNL_of_two d σ hj2, stepNL_of_two hj2, e]
      linarith
  -- the second moment and the tail
  have h2 : ((noloopSym d σ N x) ^ 2).trace ≤ 2 * Mp + 192 * (Mp / N) * Mp := by
    rw [htr 2]
    have hg := hgood 2 (le_refl _) hJ
    rw [hmS 2 (by omega)] at hg
    have h2J : (((2 : ℕ) : ℝ)) ≤ (J : ℝ) := by exact_mod_cast hJ
    have hsq : c * Real.sqrt ((2 : ℕ) : ℝ) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2J) hc) hc1
    have hm20 : 0 ≤ heatMode d σ 2 := le_trans zero_le_one (hm1 2 (by omega))
    have h' := mul_le_mul_of_nonneg_right hsq hm20
    have h3 : 96 * (Mp / N) * ∑ l ∈ Finset.range 2, mS d σ (l + 1)
        ≤ 96 * (Mp / N) * ((((2 : ℕ) : ℝ)) * Mp) := mul_le_mul_of_nonneg_left (hsumle 2) hq0
    have e : 96 * (Mp / N) * ((((2 : ℕ) : ℝ)) * Mp) = 192 * (Mp / N) * Mp := by
      push_cast; ring
    rw [e] at h3
    have h'' := (abs_le.mp hg).2
    have hm2 := hmM 2 (by omega)
    have key : ∀ t m A B q : ℝ, t - m ≤ A + B → A ≤ 1 * m → B ≤ q → m ≤ Mp →
        t ≤ 2 * Mp + q := by
      intro t m A B q k1 k2 k3 k4; linarith
    exact key _ _ _ _ _ h'' h' h3 hm2
  have hB : ∀ j, J < j → |((noloopSym d σ N x) ^ j).trace| ≤ 2 * Mp + 192 * (Mp / N) * Mp :=
    fun j hj => le_trans (hbd j (by omega)) h2
  have hB' : ∀ j, J < j → |modeNL d σ j| ≤ Mp := fun j hj => by
    rw [modeNL_of_two d σ (by omega : 2 ≤ j),
      abs_of_nonneg (le_trans zero_le_one (hm1 j (by omega)))]
    exact hmM j (by omega)
  have h := poisson_split_abs hτ (fun j => ((noloopSym d σ N x) ^ j).trace) (modeNL d σ)
    (fun j => c * Real.sqrt J * modeNL d σ j + 96 * (Mp / N) * Mp * stepNL j) J hA hT' hlow hB hB'
  -- the finite sum
  have hs1 : ∑ j ∈ Finset.range J, pw τ (j + 1)
        * (c * Real.sqrt J * modeNL d σ (j + 1) + 96 * (Mp / N) * Mp * stepNL (j + 1))
      = c * Real.sqrt J * ∑ j ∈ Finset.range J, pw τ (j + 1) * modeNL d σ (j + 1)
        + 96 * (Mp / N) * Mp * ∑ j ∈ Finset.range J, pw τ (j + 1) * stepNL (j + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hs2 : ∑ j ∈ Finset.range J, pw τ (j + 1) * modeNL d σ (j + 1)
      ≤ poissonMean d σ τ - pw τ 1 * Mp :=
    sum_le_hasSum (Finset.range J)
      (fun j _ => mul_nonneg (pw_nonneg hτ (j + 1)) (modeNL_succ_nonneg hσ d j)) hT'
  have hs3 := stepNL_sum_le hτ J
  have h4 := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hc (Real.sqrt_nonneg (J : ℝ)))
  have h5 := mul_le_mul_of_nonneg_left hs3 hκ0
  have hsum_all : ∑ j ∈ Finset.range J, pw τ (j + 1)
        * (c * Real.sqrt J * modeNL d σ (j + 1) + 96 * (Mp / N) * Mp * stepNL (j + 1))
      ≤ c * Real.sqrt J * (poissonMean d σ τ - pw τ 1 * Mp)
        + 96 * (Mp / N) * Mp * (τ * (1 - Real.exp (-τ))) := by
    rw [hs1]; linarith
  have e : (2 * Mp + 192 * (Mp / N) * Mp + Mp) * ptail τ J
      = (3 * Mp + 192 * (Mp / N) * Mp) * ptail τ J := by ring
  exact le_trans h (add_le_add hsum_all (le_of_eq e))

/-! #### The heat trace for samples -/

/-- **The heat trace of the graph without self-loops, for a fixed sample size.** Independent
    uniform points on the flat torus of dimension `d ≥ 1`, periodised Gaussian kernel of variance
    `σ = ξ² ≤ 1` with the diagonal removed, `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`,
    `C₁ = kernelC1 d`, an integer `J ≥ 2` with `C₁ δ' √J ≤ 1`, `τ ≥ 0`,
    `T = poissonMean d σ τ = ∑_{j≥1} w_j p_{jσ}(0)`, `w_j = e^{-τ} τ^j/j!`. Except on an event of
    probability at most `4/N³` (the event of `NoLoops.noloop_trace_sample`),
    `|Tr exp(τ(S°-1)) - N e^{-τ} - (T - τ e^{-τ} M)|
       ≤ C₁ δ' √J (T - τ e^{-τ} M) + 96 (M²/N) τ (1 - e^{-τ}) + (3M + 192 M²/N) (1 - ∑_{j≤J} w_j)`
    (`τ e^{-τ} = pw τ 1`). -/
theorem noloop_heat_trace_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ¬ |(NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - (poissonMean d σ τ - pw τ 1 * Mp)|
          ≤ kernelC1 d * δp * Real.sqrt J * (poissonMean d σ τ - pw τ 1 * Mp)
            + 96 * (Mp / N) * Mp * (τ * (1 - Real.exp (-τ)))
            + (3 * Mp + 192 * (Mp / N) * Mp) * ptail τ J}
      ≤ 4 / (N : ℝ) ^ 3 := by
  have h := noloop_trace_sample hσ hσ1 d hd X h_indep hX hlaw N J hN2 (by omega) hMp hδp hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  have hc : 0 ≤ kernelC1 d * δp := by
    rw [hδp]; exact mul_nonneg (kernelC1_nonneg d) (Real.sqrt_nonneg _)
  exact noloop_heat_trace_det hσ d N J hN2 hJ (fun j => X j ω) hMp hτ hc hrange
    (fun k hk hkJ => hgood k hk hkJ)

/-- From the absolute to the relative form. -/
theorem ratio_form_noloop {X T T' c s κ τ q Mp pt N2 r : ℝ} (hT : 3 / 4 ≤ T) (hq : q ≤ T)
    (hT' : T' ≤ T) (hcs : 0 ≤ c * s) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (h : |X - T'| ≤ c * s * T' + κ * (τ * q) + (3 * Mp + r * Mp) * pt)
    (hMp : 0 ≤ Mp) (hr : r ≤ 1 / 6) (hpt0 : 0 ≤ pt) (hpt : pt ≤ 1 / N2) (hN2 : 0 < N2) :
    |(X - T') / T| ≤ c * s + κ * τ + 5 * Mp / N2 := by
  have hTpos : 0 < T := by linarith
  rw [abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]
  have hQ : 0 ≤ Mp / N2 := div_nonneg hMp hN2.le
  have h1 : c * s * T' ≤ c * s * T := mul_le_mul_of_nonneg_left hT' hcs
  have h2 : κ * (τ * q) ≤ κ * (τ * T) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hτ) hκ
  have h3 : Mp * pt ≤ Mp / N2 := by
    have h := mul_le_mul_of_nonneg_left hpt hMp
    rw [mul_one_div] at h
    exact h
  have h4 : r * (Mp * pt) ≤ 1 / 6 * (Mp * pt) :=
    mul_le_mul_of_nonneg_right hr (mul_nonneg hMp hpt0)
  have h5 : 0 ≤ Mp / N2 * (T - 3 / 4) := mul_nonneg hQ (by linarith)
  have h6 : 0 ≤ Mp * pt := mul_nonneg hMp hpt0
  have e : (c * s + κ * τ + 5 * Mp / N2) * T
      = c * s * T + κ * (τ * T) + 5 * (Mp / N2 * T) := by ring
  have e2 : (3 * Mp + r * Mp) * pt = 3 * (Mp * pt) + r * (Mp * pt) := by ring
  have e3 : Mp / N2 * (T - 3 / 4) = Mp / N2 * T - 3 / 4 * (Mp / N2) := by ring
  rw [e]
  rw [e2] at h
  rw [e3] at h5
  linarith

/-- **The relative form.** In the situation of `noloop_heat_trace_sample` let moreover `τ ≥ 2`
    and `3τ + 2 log N ≤ J + 1`. Except on an event of probability at most `4/N³`,
    `|(Tr exp(τ(S°-1)) - N e^{-τ} - (T - τ e^{-τ} M)) / T| ≤ C₁ δ' √J + 96 (M²/N) τ + 5 M/N²`. -/
theorem noloop_heat_trace_ratio {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 2 ≤ τ)
    (hJτ : 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1) :
    μ.real {ω | ¬ |((NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - (poissonMean d σ τ - pw τ 1 * Mp)) / poissonMean d σ τ|
          ≤ kernelC1 d * δp * Real.sqrt J + 96 * (Mp / N) * Mp * τ + 5 * Mp / (N : ℝ) ^ 2}
      ≤ 4 / (N : ℝ) ^ 3 := by
  have hτ0 : 0 ≤ τ := by linarith
  have h := noloop_heat_trace_sample hσ hσ1 d hd X h_indep hX hlaw N J hN2 hJ hMp hδp hrange hτ0
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hM1152 := (norm_event hσ hσ1 d hd X h_indep hX hlaw N J hN2 (by omega) hMp hδp hrange).2.2
  have hMp0 : 0 ≤ Mp := by
    rw [hMp]; exact le_trans zero_le_one (heatTorus_zero_ge_one hcσ d)
  have hq := poissonMean_ge hσ d hτ0
  have hquart := exp_neg_le_quarter hτ
  have hT : 3 / 4 ≤ poissonMean d σ τ := by linarith
  have hT' : poissonMean d σ τ - pw τ 1 * Mp ≤ poissonMean d σ τ := by
    have := mul_nonneg (pw_nonneg hτ0 1) hMp0
    linarith
  have hcs : 0 ≤ kernelC1 d * δp * Real.sqrt J := by
    rw [hδp]
    exact mul_nonneg (mul_nonneg (kernelC1_nonneg d) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hκ : 0 ≤ 96 * (Mp / N) * Mp :=
    mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hMp0 hNpos.le)) hMp0
  have hr : 192 * (Mp / N) ≤ 1 / 6 := by
    have h1 : Mp / N ≤ 1 / 1152 := by rw [div_le_iff₀ hNpos]; linarith
    linarith
  exact ratio_form_noloop hT hq hT' hcs hκ hτ0 hgood hMp0 hr (ptail_nonneg hτ0 J)
    (ptail_le_inv_sq hτ0 J N (by omega) hJτ) (by positivity)

/-- **The relative form when the additional term is absorbed.** In the situation of
    `noloop_heat_trace_ratio` let moreover `p_σ(0) ≤ kernelC1 d · log N`. Except on an event of
    probability at most `4/N³`,
    `|(Tr exp(τ(S°-1)) - N e^{-τ} - (T - τ e^{-τ} M)) / T| ≤ (C₁ + 96) δ' √J + 5 M/N²`. -/
theorem noloop_heat_trace_ratio_small {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 2 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt J ≤ 1) {τ : ℝ} (hτ : 2 ≤ τ)
    (hJτ : 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1)
    (hsmall : Mp ≤ kernelC1 d * Real.log N) :
    μ.real {ω | ¬ |((NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - (poissonMean d σ τ - pw τ 1 * Mp)) / poissonMean d σ τ|
          ≤ (kernelC1 d + 96) * δp * Real.sqrt J + 5 * Mp / (N : ℝ) ^ 2}
      ≤ 4 / (N : ℝ) ^ 3 := by
  have h := noloop_heat_trace_ratio hσ hσ1 d hd X h_indep hX hlaw N J hN2 hJ hMp hδp hrange hτ hJτ
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  refine hgood.trans ?_
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hJr2 : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hlg : 0 < Real.log N := Real.log_pos (by linarith)
  have hMp0 : 0 ≤ Mp := by rw [hMp]; exact heatTorus_nonneg hcσ d 0
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hδ2 : δp ^ 2 = Mp * Real.log N / N := by
    rw [hδp, Real.sq_sqrt (div_nonneg (mul_nonneg hMp0 hlg.le) hNpos.le)]
  have hτJ : τ ≤ (J : ℝ) := by linarith
  have hab := absorb hNpos hlg hMp0 hδ2 hδp0 (Nat.cast_nonneg J) hrange hsmall (le_refl (1 : ℝ))
  have hq : 0 ≤ Mp / N * Mp := mul_nonneg (div_nonneg hMp0 hNpos.le) hMp0
  have h1 : Mp / N * Mp * τ ≤ Mp / N * Mp * (J : ℝ) := mul_le_mul_of_nonneg_left hτJ hq
  have e1 : Mp / N * Mp * (J : ℝ) = Mp / N * ((J : ℝ) * Mp) := by ring
  have e2 : 96 * (Mp / N) * Mp * τ = 96 * (Mp / N * Mp * τ) := by ring
  have e3 : (kernelC1 d + 96) * δp * Real.sqrt J
      = kernelC1 d * δp * Real.sqrt J + 96 * (δp * Real.sqrt J * 1) := by ring
  rw [e1] at h1
  rw [e2, e3]
  linarith

end NoLoopsTrace

/-! ## Measurability of the exceptional sets of the sample statements of this file

For the closing statements of this file whose probability is bounded as `μ.real {ω | …}`, the set
`{ω | …}`, verbatim, is shown to be measurable; hypotheses: `σ > 0` and measurability of the `X_j`
only. Not covered: `EigenspaceSample.eigspace_sample` (its set contains `specProj`, built from
Mathlib's chosen eigenvector basis; see the note at the end of the namespace). -/

namespace Reals2Sets

open Filter Topology

open CTG.Reals.ExceptionalSets AssembledSets

/-! ### Generic lemmas -/

theorem ms_forall {α : Type*} [MeasurableSpace α] {ι : Type*} [Countable ι] {Q : ι → α → Prop}
    (h : ∀ i, MeasurableSet {x | Q i x}) : MeasurableSet {x | ∀ i, Q i x} := by
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter h

theorem isClosed_setOf_forall {α : Type*} [TopologicalSpace α] {ι : Sort*} {p : ι → α → Prop}
    (h : ∀ i, IsClosed {x | p i x}) : IsClosed {x | ∀ i, p i x} := by
  rw [Set.setOf_forall]
  exact isClosed_iInter h

/-- A statement about all proofs of symmetry and all ordered eigenvalues of a measurable family
    of symmetric matrices is a measurable condition, if it is one in the eigenvalue. -/
theorem herm_forall_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    (M : Ω → Matrix (Fin N) (Fin N) ℝ) (hM : ∀ a b, Measurable fun ω => M ω a b)
    (hH : ∀ ω, (M ω).IsHermitian) (Φ : Fin (Fintype.card (Fin N)) → ℝ → Prop)
    (hΦ : ∀ j, MeasurableSet {x | Φ j x}) :
    MeasurableSet {ω | ∀ (hS : (M ω).IsHermitian) (j : Fin (Fintype.card (Fin N))),
      Φ j (hS.eigenvalues₀ j)} := by
  have e : {ω | ∀ (hS : (M ω).IsHermitian) (j : Fin (Fintype.card (Fin N))),
        Φ j (hS.eigenvalues₀ j)}
      = {ω | ∀ j, Φ j (eigTot N j (fun a b => M ω a b))} := by
    ext ω
    exact forall_herm_iff (M ω) (hH ω) Φ
  rw [e]
  refine ms_forall fun j => ?_
  exact (eigTot_measurable_comp j (fun ω a b => M ω a b)
    (measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hM a b)
    (fun ω => hH ω)) (hΦ j)

/-- Entries of `S` with the normalisation `heatRho`. -/
theorem symGraph_rho_entry_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ} (hσ : 0 < σ)
    (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ) (a b : Fin N) :
    Measurable fun ω => symGraph
      (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
      (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) a b := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  exact symGraph_entry_measurable
    (fun ω (a j : Fin N) => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
    (fun ω (a : Fin N) => heatRho d σ N (fun j => X j ω) a)
    (fun a b => heatTorus_sample_measurable hc d X hX a b)
    (fun a => heatRho_sample_measurable hσ d X hX N a) a b

theorem symGraph_rho_isHermitian {Ω : Type*} {σ : ℝ} (d N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    (symGraph
      (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
      (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian := by
  refine symGraph_isHermitian _ _ fun i j => ?_
  rw [← heatTorus_even d (2 * Real.pi ^ 2 * σ) (X j ω - X i ω), neg_sub]

/-- Entries of `S` with the normalisation written as a sum over `Fin N`. -/
theorem symGraph_fin_entry_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ} (hσ : 0 < σ)
    (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ) (a b : Fin N) :
    Measurable fun ω => symGraph
      (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
      (fun i : Fin N =>
        (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) a b := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  have hR : ∀ a : Fin N, Measurable fun ω =>
      (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X l ω)) / (N : ℝ) := fun a =>
    (Finset.measurable_sum Finset.univ fun (l : Fin N) _ =>
      heatTorus_sample_measurable hc d X hX a l).div_const _
  exact symGraph_entry_measurable
    (fun ω (i j : Fin N) => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
    (fun ω (i : Fin N) =>
      (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)
    (fun a b => heatTorus_sample_measurable hc d X hX a b)
    hR a b

theorem heatP_neg_eq (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) :
    heatP d σ k (-u) = heatP d σ k u := by
  unfold heatP
  split_ifs
  · rfl
  · exact heatTorus_even d _ u

/-! ### (1) The reduction: `H5.torus_reduction_paper` -/

section Reduction

open CTG.Reals.TorusReduction TorusReductionL1 H5

/-- The linearised defect `ĥ` is a measurable function of the sample. -/
theorem torusHhat_sample_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ} (hσ : 0 < σ)
    (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N m : ℕ) (i b : Fin N) :
    Measurable fun ω => torusHhat d σ N (fun j => X j ω) m i b := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  have hK : ∀ a j : Fin N, Measurable fun ω => torusK d σ N (fun j => X j ω) a j := fun a j =>
    heatTorus_sample_measurable hc d X hX a j
  have hR : ∀ a : Fin N, Measurable fun ω => torusRho d σ N (fun j => X j ω) a := fun a =>
    heatRho_sample_measurable hσ d X hX N a
  have hQ : ∀ (s : ℕ) (a b : Fin N), Measurable fun ω => torusQ d σ N (fun j => X j ω) s a b :=
    fun s a b => heatP_sample_measurable hσ d X hX s a b
  unfold torusHhat
  exact Finset.measurable_sum _ fun j _ =>
    (((hK b j).div_const _).mul (((hR j).sub_const 1).const_sub 1)).mul
      ((hQ m j i).sub (hQ (m + 1) b i))

/-- The statistic `Π_k` (with the `ĥ` of the paper) is a measurable function of the sample. -/
theorem torusPi_sample_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ} (hσ : 0 < σ)
    (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N k : ℕ) :
    Measurable fun ω =>
      torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω)) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  have hK : ∀ a j : Fin N, Measurable fun ω => torusK d σ N (fun j => X j ω) a j := fun a j =>
    heatTorus_sample_measurable hc d X hX a j
  have hR : ∀ a : Fin N, Measurable fun ω => torusRho d σ N (fun j => X j ω) a := fun a =>
    heatRho_sample_measurable hσ d X hX N a
  have hQ : ∀ (s : ℕ) (a b : Fin N), Measurable fun ω => torusQ d σ N (fun j => X j ω) s a b :=
    fun s a b => heatP_sample_measurable hσ d X hX s a b
  have hH : ∀ (m : ℕ) (i b : Fin N), Measurable fun ω =>
      torusHhat d σ N (fun j => X j ω) m i b := fun m i b =>
    torusHhat_sample_measurable hσ d X hX N m i b
  have hTh : ∀ b i : Fin N, Measurable fun ω => torusTheta1 d σ N (fun j => X j ω) b i := by
    intro b i
    unfold torusTheta1 ShellAndWalk.walkTheta1
    exact ((((hR i).sub_const 1).neg).sub ((hR b).sub_const 1)).add
      ((Finset.measurable_sum _ fun j _ => (hK b j).mul ((hR j).sub_const 1)).div_const _)
  unfold torusPi
  exact (((Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun b _ =>
      ((hQ k i b).mul (hQ 1 b i)).mul (hTh b i)).const_mul _).add
    (Finset.measurable_sum _ fun m _ =>
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun b _ =>
        (hQ (k - m) i b).mul (hH m i b)).const_mul _)).add
    ((Finset.measurable_sum _ fun i _ => hH k i i).const_mul _)

/-- The exceptional set of `H5.torus_reduction_paper`, verbatim, is measurable. -/
theorem torus_reduction_paper_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N K : ℕ)
    (δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)
            - torusPi d σ N (fun j => X j ω) k (torusHhat d σ N (fun j => X j ω))|
          ≤ (Real.sqrt 2) ^ d
              * (2 * (4 * normC d) * kernelC1 d + 2 * (14 * normC d ^ 2) + h5Ca d
                  + 2 * (2 * (Real.sqrt 2) ^ d * h5Ca d + h5Ca d
                      + (Real.sqrt 2) ^ d * kernelC1 d * h5Cb d + h4C d * h5Cb d))
              * δp ^ 2 * k * torusM d σ (k + 1)} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp ?_)
  exact measurableSet_le
    ((((pow_trace_measurable (fun ω => torusWalk d σ N (fun j => X j ω))
        (fun a b => walk_entry_measurable hσ d X hX N a b) (k + 1)).sub measurable_const).sub
      (torusPi_sample_measurable hσ d X hX N k)).abs) measurable_const

end Reduction

/-! ### (2) The second stage for the heat trace -/

section SecondStageSets

open CTG.Reals.TorusReduction CTG.Reals.TraceG29 TorusReductionL1 H5 PiBound SecondStage

/-- The exceptional set of `SecondStageTrace.second_stage_trace_rel`, verbatim, is measurable. -/
theorem second_stage_trace_rel_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ)
    (Mp δp τ s : ℝ) :
    MeasurableSet {ω | (redC d * δp ^ 2 + s * piC d * (Mp / N)) * τ
          + kernelC1 d * δp * (pw τ 1 * Mp / poissonMean d σ τ)
          + 4 * (Mp / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N τ).sub measurable_const).div_const _).sub
      measurable_const).abs)

/-- The exceptional set of `SecondStageTrace2.second_stage_trace_rel2`, verbatim, is
    measurable. -/
theorem second_stage_trace_rel2_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ)
    (Mp δp τ s : ℝ) :
    MeasurableSet {ω | (redC d * δp ^ 2 + s * piC d * (Mp / N)) * τ
          + (14 * (normC d * δp) ^ 2 + 7 * s * (Mp / N)) * (pw τ 1 * Mp / poissonMean d σ τ)
          + 4 * (Mp / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N τ).sub measurable_const).div_const _).sub
      measurable_const).abs)

/-- The exceptional set of `SecondStageTrace2.second_stage_trace_rel2'`, verbatim, is
    measurable. -/
theorem second_stage_trace_rel2'_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ)
    (Mp δp τ s : ℝ) :
    MeasurableSet {ω | (redC d * δp ^ 2 + s * piC d * (Mp / N)) * τ
          + 14 * (normC d * δp) ^ 2 + 7 * s * (Mp / N) + 4 * (Mp / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N τ).sub measurable_const).div_const _).sub
      measurable_const).abs)

/-- The set in `SecondStageLimit.second_stage_limit` (for each `N` with `σ_N > 0`), verbatim, is
    measurable. -/
theorem second_stage_limit_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ τ : ℕ → ℝ) (η : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | η * σ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N (τ N)).sub measurable_const).div_const _).sub
      measurable_const).abs)

end SecondStageSets

/-! ### (3) Eigenvalues: `KernelMatrix.eig_G44_i`, `eig_G44_ii`, `kernelQ_sample` -/

section KernelMatrixSets

open KernelMatrix

/-- The exceptional set of `KernelMatrix.eig_G44_i`, verbatim, is measurable. -/
theorem eig_G44_i_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N K : ℕ)
    (δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
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
                  * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp ?_)
  refine herm_forall_measurable
    (fun ω => symGraph
      (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
      (fun a : Fin N => heatRho d σ N (fun j => X j ω) a))
    (fun a b => symGraph_rho_entry_measurable hσ d X hX N a b)
    (fun ω => symGraph_rho_isHermitian d N X ω)
    (fun j x => (j.val = 0 → |x ^ k - 1|
              ≤ EigenvaluesL1.eigL1C d * δp * Real.sqrt k
                + kernelQC d * Real.sqrt (Real.log N / N)
                  * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
          ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            |x ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ EigenvaluesL1.eigL1C d * δp * Real.sqrt k
                + kernelQC d * Real.sqrt (Real.log N / N)
                  * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
    (fun j => ?_)
  beta_reduce
  apply IsClosed.measurableSet
  refine IsClosed.inter ?_ ?_
  · exact isClosed_forall fun _ => isClosed_le (by fun_prop) continuous_const
  · refine isClosed_forall fun r => isClosed_forall fun _ => isClosed_forall fun Hlt =>
      isClosed_forall fun Hle => isClosed_forall fun _ => isClosed_forall fun _ =>
      isClosed_forall fun _ => isClosed_forall fun _ => ?_
    exact isClosed_le (by fun_prop) continuous_const

/-- The exceptional set of `KernelMatrix.eig_G44_ii`, verbatim, is measurable. -/
theorem eig_G44_ii_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ)
    (δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ r : ℝ, 1 ≤ r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
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
                + Real.sqrt (Real.log N / N) * (2 * Real.pi * Real.sqrt r) ^ (d + 2))} := by
  refine MeasurableSet.compl ?_
  refine (herm_forall_measurable
    (fun ω => symGraph
      (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
      (fun a : Fin N => heatRho d σ N (fun j => X j ω) a))
    (fun a b => symGraph_rho_entry_measurable hσ d X hX N a b)
    (fun ω => symGraph_rho_isHermitian d N X ω)
    (fun j x => ∀ r : ℝ, 1 ≤ r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
        eigC9 d * (δp / Real.sqrt σ / (2 * Real.pi * Real.sqrt r)
          + Real.sqrt (Real.log N / N) * (2 * Real.pi * Real.sqrt r) ^ d) ≤ 1 →
        ∀ Hlt Hle : Finset (Fin d → ℤ),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
          |(1 - x) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ eigC10 d * (δp / Real.sqrt σ * (2 * Real.pi * Real.sqrt r)
                + Real.sqrt (Real.log N / N) * (2 * Real.pi * Real.sqrt r) ^ (d + 2)))
    (fun j => ?_)).congr ?_
  · beta_reduce
    apply IsClosed.measurableSet
    refine isClosed_forall fun r => isClosed_forall fun _ => isClosed_forall fun _ =>
      isClosed_forall fun _ => isClosed_forall fun Hlt =>
      isClosed_forall fun Hle => isClosed_forall fun _ => isClosed_forall fun _ =>
      isClosed_forall fun _ => isClosed_forall fun _ => ?_
    exact isClosed_le (by fun_prop) continuous_const
  · exact Set.ext fun ω =>
      ⟨fun h r h1 h2 h3 hS j Hlt Hle => h hS j r h1 h2 h3 Hlt Hle,
        fun h hS j r h1 h2 h3 Hlt Hle => h r h1 h2 h3 hS j Hlt Hle⟩

/-- The exceptional set of `KernelMatrix.kernelQ_sample`, verbatim, is measurable. -/
theorem kernelQ_sample_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k →
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
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp ?_
  refine herm_forall_measurable
    (fun ω => Matrix.of fun a i : Fin N => heatP d σ k (X a ω - X i ω) / (N : ℝ))
    (fun a b => ?_) (fun ω => ?_)
    (fun j x => 0 ≤ x
          ∧ (j.val = 0 → |x - 1|
              ≤ kernelQC d * Real.sqrt (Real.log N / N)
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
          ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            |x - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ kernelQC d * Real.sqrt (Real.log N / N)
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
    (fun j => ?_)
  · show Measurable fun ω => heatP d σ k (X a ω - X b ω) / (N : ℝ)
    exact (heatP_sample_measurable hσ d X hX k a b).div_const _
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, star_trivial]
    rw [← heatP_neg_eq d σ k (X i ω - X j ω), neg_sub]
  · beta_reduce
    apply IsClosed.measurableSet
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_le continuous_const continuous_id
    · exact isClosed_forall fun _ => isClosed_le (by fun_prop) continuous_const
    · refine isClosed_forall fun r => isClosed_forall fun _ => isClosed_forall fun Hlt =>
        isClosed_forall fun Hle => isClosed_forall fun _ => isClosed_forall fun _ =>
        isClosed_forall fun _ => isClosed_forall fun _ => ?_
      exact isClosed_le (by fun_prop) continuous_const

end KernelMatrixSets

/-! ### (4a) `LatticeEnumeration.eig_theorem_G38_i_enum` -/

/-- The exceptional set of `LatticeEnumeration.eig_theorem_G38_i_enum`, verbatim, is measurable
    (for every map `e`; no hypothesis on `e` is needed). -/
theorem eig_theorem_G38_i_enum_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d N K : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (δp : ℝ) (e : ℕ → (Fin d → ℤ)) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          |hS.eigenvalues₀ j ^ k
              - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ t, ((e j.val t : ℤ) : ℝ) ^ 2) ^ k|
            ≤ eigC3 d * δp * Real.sqrt k
              * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp ?_)
  refine herm_forall_measurable
    (fun ω => symGraph
      (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
      (fun i : Fin N =>
        (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N))
    (fun a b => symGraph_fin_entry_measurable hσ d X hX N a b)
    (fun ω => symGraph_sample_isHermitian d N X ω)
    (fun j x => |x ^ k
              - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ t, ((e j.val t : ℤ) : ℝ) ^ 2) ^ k|
            ≤ eigC3 d * δp * Real.sqrt k
              * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
    (fun j => ?_)
  beta_reduce
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

/-! ### (4b) The walk without self-loops: `NoLoops.noloop_kernel_sample`, `noloop_trace_sample` -/

section NoLoopsSets

open NoLoops

/-- The entries of the walk without self-loops are measurable. -/
theorem noloop_entry_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ} (hσ : 0 < σ)
    (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ) (a i : Fin N) :
    Measurable fun ω => (noloopWalk d σ N (fun j => X j ω)) a i := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  have hK : ∀ a j : Fin N, Measurable fun ω =>
      (if a = j then 0 else heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω)) := by
    intro a j
    by_cases h : a = j
    · simp only [if_pos h]
      exact measurable_const
    · simp only [if_neg h]
      exact heatTorus_sample_measurable hc d X hX a j
  have hR : ∀ a : Fin N, Measurable fun ω =>
      heatRho d σ N (fun j => X j ω) a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N := fun a =>
    (heatRho_sample_measurable hσ d X hX N a).sub_const _
  unfold noloopWalk
  simp only [walkMatrix, Matrix.of_apply]
  exact ((hK a i).div ((hR a).mul (hR i))).div
    (Finset.measurable_sum _ fun l _ => (hK a l).div ((hR a).mul (hR l)))

/-- The exceptional set of `NoLoops.noloop_kernel_sample`, verbatim, is measurable. -/
theorem noloop_kernel_sample_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N K : ℕ)
    (Mp δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((noloopWalk d σ N (fun j => X j ω)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ kernelC1 d * δp * Real.sqrt k * mS d σ k
            + 96 * (Mp / N) * ∑ l ∈ Finset.range k, mS d σ (l + 1)} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp (ms_forall fun a => ms_forall fun i => ?_))
  exact measurableSet_le
    ((((pow_entry_measurable (fun ω => noloopWalk d σ N (fun j => X j ω))
        (fun a b => noloop_entry_measurable hσ d X hX N a b) k a i).const_mul _).sub
      (heatP_sample_measurable hσ d X hX k a i)).abs) measurable_const

/-- The exceptional set of `NoLoops.noloop_trace_sample`, verbatim, is measurable. -/
theorem noloop_trace_sample_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N K : ℕ)
    (Mp δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 2 ≤ k → k ≤ K →
        |((noloopWalk d σ N (fun j => X j ω)) ^ k).trace - mS d σ k|
          ≤ kernelC1 d * δp * Real.sqrt k * mS d σ k
            + 96 * (Mp / N) * ∑ l ∈ Finset.range k, mS d σ (l + 1)} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp ?_)
  exact measurableSet_le
    (((pow_trace_measurable (fun ω => noloopWalk d σ N (fun j => X j ω))
        (fun a b => noloop_entry_measurable hσ d X hX N a b) k).sub measurable_const).abs)
    measurable_const

end NoLoopsSets

/-! ### (4b') The heat trace of the graph without self-loops:
`NoLoopsTrace.noloop_heat_trace_ratio` -/

section NoLoopsTraceSets

open NoLoopsTrace CTG.Reals.TraceG29

/-- The exceptional set of `NoLoopsTrace.noloop_heat_trace_ratio`, verbatim, is measurable. -/
theorem noloop_heat_trace_ratio_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp τ : ℝ) :
    MeasurableSet {ω | ¬ |((NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - (poissonMean d σ τ - pw τ 1 * Mp)) / poissonMean d σ τ|
          ≤ kernelC1 d * δp * Real.sqrt J + 96 * (Mp / N) * Mp * τ + 5 * Mp / (N : ℝ) ^ 2} := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  have hK : ∀ a b : Fin N, Measurable fun ω => noloopK d σ N (fun j => X j ω) a b := by
    intro a b
    show Measurable fun ω =>
      (if a = b then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X b ω))
    by_cases h : a = b
    · simp only [if_pos h]
      exact measurable_const
    · simp only [if_neg h]
      exact heatTorus_sample_measurable hc d X hX a b
  have hR : ∀ a : Fin N, Measurable fun ω => noloopRho d σ N (fun j => X j ω) a := by
    intro a
    show Measurable fun ω =>
      heatRho d σ N (fun j => X j ω) a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N
    exact (heatRho_sample_measurable hσ d X hX N a).sub_const _
  have hsym : ∀ (ω : Ω) (i j : Fin N),
      noloopK d σ N (fun j => X j ω) i j = noloopK d σ N (fun j => X j ω) j i := by
    intro ω i j
    show (if i = j then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
      = (if j = i then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X i ω))
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), ← heatTorus_even d _ (X j ω - X i ω), neg_sub]
  have htr : Measurable fun ω =>
      (NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace :=
    trace_exp_measurable (fun ω => noloopSym d σ N (fun j => X j ω))
      (fun a b => symGraph_entry_measurable
        (fun ω => noloopK d σ N (fun j => X j ω)) (fun ω => noloopRho d σ N (fun j => X j ω))
        hK hR a b)
      (fun ω => symGraph_isHermitian _ _ (hsym ω)) τ
  refine MeasurableSet.compl ?_
  exact measurableSet_le
    ((((htr.sub measurable_const).sub measurable_const).div_const _).abs) measurable_const

end NoLoopsTraceSets

/-! ### (4c) The corrected estimator: `Corrected.corrected_G30` -/

section CorrectedSets

open Corrected CTG.Reals.TraceG29

/-- A bound `h ω τ ≤ g τ` for all `τ` with `p τ` is a measurable condition, if `h` is measurable
    in `ω` and `h`, `g` are continuous in `τ` on the bounded parts of `{τ | p τ}`. -/
theorem forall_param_measurable' {Ω : Type*} {mΩ : MeasurableSpace Ω} {p : ℝ → Prop}
    {h : Ω → ℝ → ℝ} {g : ℝ → ℝ} (hm : ∀ τ, Measurable fun ω => h ω τ)
    (hc : ∀ (ω : Ω) (B : ℝ), ContinuousOn (h ω) {τ | p τ ∧ τ ≤ B})
    (hg : ∀ B : ℝ, ContinuousOn g {τ | p τ ∧ τ ≤ B}) :
    MeasurableSet {ω | ∀ τ : ℝ, p τ → h ω τ ≤ g τ} := by
  refine (ms_forall fun n : ℕ => forall_param_measurable (p := p) (q := fun τ => τ ≤ (n : ℝ))
    (h := fun ω τ => h ω τ - g τ) (c := 0) (fun τ => (hm τ).sub_const _)
    (fun ω => (hc ω n).sub (hg n))).congr ?_
  exact Set.ext fun ω => ⟨fun H τ hτ => by
      obtain ⟨n, hn⟩ := exists_nat_ge τ
      exact sub_nonpos.1 (H n τ hτ hn),
    fun H n τ hτ _ => sub_nonpos.2 (H τ hτ)⟩

/-- The corrected series of the traces of the powers of a measurable family of symmetric
    matrices is measurable (limit of its partial sums). -/
theorem corrSeries_trace_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    (M : Ω → Matrix (Fin N) (Fin N) ℝ) (hM : ∀ a b, Measurable fun ω => M ω a b)
    (hH : ∀ ω, (M ω).IsHermitian) (τ : ℝ) :
    Measurable fun ω => corrSeries τ (fun k : ℕ => ((M ω) ^ k).trace) := by
  have htr : ∀ k : ℕ, Measurable fun ω => ((M ω) ^ k).trace := fun k =>
    pow_trace_measurable M hM k
  have hzs : ∀ j : ℕ, Measurable fun ω => zs (fun k : ℕ => ((M ω) ^ k).trace) j := by
    intro j
    by_cases hj : j = 0
    · simp only [zs, if_pos hj]
      exact measurable_const
    · simp only [zs, if_neg hj]
      exact htr j
  have hterm : ∀ j : ℕ, Measurable fun ω => corrTerm τ (fun k : ℕ => ((M ω) ^ k).trace) j := by
    intro j
    unfold corrTerm
    exact ((hzs j).sub ((((htr (j + 2)).sub ((htr (j + 1)).const_mul 2)).add (hzs j)).const_mul
      (τ / 2))).const_mul _
  have hpart : ∀ n : ℕ, Measurable fun ω =>
      ∑ j ∈ Finset.range n, corrTerm τ (fun k : ℕ => ((M ω) ^ k).trace) j := fun n =>
    Finset.measurable_sum _ fun j _ => hterm j
  have hlim : Tendsto
      (fun (n : ℕ) (ω : Ω) =>
        ∑ j ∈ Finset.range n, corrTerm τ (fun k : ℕ => ((M ω) ^ k).trace) j)
      atTop (𝓝 fun ω => corrSeries τ (fun k : ℕ => ((M ω) ^ k).trace)) :=
    tendsto_pi_nhds.2 fun ω =>
      (corr_matrix_hasSum (M ω) (hH ω) τ).summable.hasSum.tendsto_sum_nat
  exact measurable_of_tendsto_metrizable hpart hlim

/-- The corrected series of the heat-kernel values is continuous in `τ` on bounded sets of
    nonnegative `τ`. -/
theorem corrSeries_heatMode_continuousOn {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (B : ℝ) :
    ContinuousOn (fun τ => corrSeries τ (heatMode d σ)) (Set.Icc 0 B) := by
  unfold corrSeries
  have hM1 : ∀ j : ℕ, 1 ≤ j → 0 ≤ heatMode d σ j ∧
      heatMode d σ j ≤ heatTorus d (2 * Real.pi ^ 2 * σ) 0 := fun j hj =>
    ⟨le_trans zero_le_one (heatMode_ge_one hσ d hj), heatMode_le hσ d hj⟩
  have hMb : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ) 0 :=
    le_trans (hM1 1 le_rfl).1 (hM1 1 le_rfl).2
  have hz : ∀ j : ℕ, 0 ≤ zs (heatMode d σ) j ∧
      zs (heatMode d σ) j ≤ heatTorus d (2 * Real.pi ^ 2 * σ) 0 := by
    intro j
    by_cases hj : j = 0
    · simp only [zs, if_pos hj]
      exact ⟨le_rfl, hMb⟩
    · simp only [zs, if_neg hj]
      exact hM1 j (by omega)
  refine continuousOn_tsum
    (u := fun j : ℕ => B ^ j / (j.factorial : ℝ)
      * ((1 + 2 * B) * heatTorus d (2 * Real.pi ^ 2 * σ) 0)) (fun j => ?_) ?_ (fun j τ hτ => ?_)
  · have h1 : Continuous fun τ : ℝ => corrTerm τ (heatMode d σ) j := by
      unfold corrTerm pw
      fun_prop
    exact h1.continuousOn
  · exact (Real.summable_pow_div_factorial B).mul_right _
  · have hτ0 : 0 ≤ τ := hτ.1
    have hτB : τ ≤ B := hτ.2
    have hw := pw_nonneg hτ0 j
    have hfac : (0 : ℝ) ≤ (j.factorial : ℝ) := Nat.cast_nonneg _
    have h1 : pw τ j ≤ B ^ j / (j.factorial : ℝ) := by
      unfold pw
      have he : Real.exp (-τ) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      have hp : τ ^ j / (j.factorial : ℝ) ≤ B ^ j / (j.factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hτ0 hτB j) hfac
      have hp0 : 0 ≤ τ ^ j / (j.factorial : ℝ) := div_nonneg (pow_nonneg hτ0 _) hfac
      calc Real.exp (-τ) * (τ ^ j / (j.factorial : ℝ))
          ≤ 1 * (B ^ j / (j.factorial : ℝ)) := mul_le_mul he hp hp0 zero_le_one
        _ = B ^ j / (j.factorial : ℝ) := one_mul _
    obtain ⟨x0, x1⟩ := hz j
    obtain ⟨y0, y1⟩ := hM1 (j + 2) (by omega)
    obtain ⟨z0, z1⟩ := hM1 (j + 1) (by omega)
    have hin : |zs (heatMode d σ) j - τ / 2 * (heatMode d σ (j + 2) - 2 * heatMode d σ (j + 1)
          + zs (heatMode d σ) j)|
        ≤ (1 + 2 * B) * heatTorus d (2 * Real.pi ^ 2 * σ) 0 := by
      have p1 : τ * zs (heatMode d σ) j ≤ B * heatTorus d (2 * Real.pi ^ 2 * σ) 0 :=
        mul_le_mul hτB x1 x0 (le_trans hτ0 hτB)
      have p2 : τ * heatMode d σ (j + 2) ≤ B * heatTorus d (2 * Real.pi ^ 2 * σ) 0 :=
        mul_le_mul hτB y1 y0 (le_trans hτ0 hτB)
      have p3 : τ * heatMode d σ (j + 1) ≤ B * heatTorus d (2 * Real.pi ^ 2 * σ) 0 :=
        mul_le_mul hτB z1 z0 (le_trans hτ0 hτB)
      have q1 : 0 ≤ τ * zs (heatMode d σ) j := mul_nonneg hτ0 x0
      have q2 : 0 ≤ τ * heatMode d σ (j + 2) := mul_nonneg hτ0 y0
      have q3 : 0 ≤ τ * heatMode d σ (j + 1) := mul_nonneg hτ0 z0
      rw [abs_le]
      constructor <;> linarith
    have hu0 : 0 ≤ (1 + 2 * B) * heatTorus d (2 * Real.pi ^ 2 * σ) 0 :=
      le_trans (abs_nonneg _) hin
    show ‖corrTerm τ (heatMode d σ) j‖ ≤ B ^ j / (j.factorial : ℝ)
      * ((1 + 2 * B) * heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    unfold corrTerm
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    exact mul_le_mul h1 hin (abs_nonneg _) (le_trans hw h1)

/-- The exceptional set of `Corrected.corrected_G30`, verbatim, is measurable. -/
theorem corrected_G30_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ τ : ℝ, 2 ≤ τ →
        |corrSeries τ (fun k : ℕ => ((symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace)
            - corrSeries τ (heatMode d σ)|
          ≤ (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ)) * poissonMean d σ τ
            + (3 + 6 * τ) * Mp * ptail τ J} := by
  refine MeasurableSet.compl ?_
  refine forall_param_measurable' (p := fun τ : ℝ => 2 ≤ τ)
    (h := fun ω τ => |corrSeries τ (fun k : ℕ => ((symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace)
            - corrSeries τ (heatMode d σ)|)
    (g := fun τ => (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ))
            * poissonMean d σ τ
            + (3 + 6 * τ) * Mp * ptail τ J) ?_ ?_ ?_
  · intro τ
    exact ((corrSeries_trace_measurable
      (fun ω => symGraph
        (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
        (fun a : Fin N => heatRho d σ N (fun j => X j ω) a))
      (fun a b => symGraph_rho_entry_measurable hσ d X hX N a b)
      (fun ω => symGraph_rho_isHermitian d N X ω) τ).sub measurable_const).abs
  · intro ω B
    have hsub : {τ : ℝ | 2 ≤ τ ∧ τ ≤ B} ⊆ Set.Icc 0 B := fun τ hτ =>
      ⟨le_trans (by norm_num) hτ.1, hτ.2⟩
    have hS : Continuous fun τ : ℝ => corrSeries τ (fun k : ℕ => ((symGraph
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
          (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace) := by
      have e := fun τ : ℝ => corrSeries_matrix (symGraph
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
          (fun a : Fin N => heatRho d σ N (fun j => X j ω) a))
        (symGraph_rho_isHermitian d N X ω) τ
      rw [funext e]
      fun_prop
    exact (hS.continuousOn.sub ((corrSeries_heatMode_continuousOn hσ d B).mono hsub)).abs
  · intro B
    have hsub : {τ : ℝ | 2 ≤ τ ∧ τ ≤ B} ⊆ Set.Icc 0 B := fun τ hτ =>
      ⟨le_trans (by norm_num) hτ.1, hτ.2⟩
    have hT := (poissonMean_continuousOn hσ d B).mono hsub
    have hpt : Continuous fun τ : ℝ => ptail τ J := by
      unfold ptail pw
      fun_prop
    have h1 : Continuous fun τ : ℝ =>
        (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ)) := by fun_prop
    have h2 : Continuous fun τ : ℝ => (3 + 6 * τ) * Mp := by fun_prop
    exact (h1.continuousOn.mul hT).add (h2.continuousOn.mul hpt.continuousOn)

end CorrectedSets

/-! ### (4d) Delocalisation: `Delocalisation.deloc_sample`, `DelocalisationFinal.deloc_sample_shell`

The sets quantify over all eigenvectors `u`. The bad set of matrices is the projection, along the
`σ`-compact parameter space, of the intersection of a closed and an open set; such a projection
is a countable union of closed sets. -/

theorem closed_proj {Y P : Type*} [TopologicalSpace Y] [TopologicalSpace P] {C : Set (Y × P)}
    (hC : IsClosed C) {Kc : Set P} (hK : IsCompact Kc) :
    IsClosed {y | ∃ p ∈ Kc, (y, p) ∈ C} := by
  haveI : CompactSpace Kc := isCompact_iff_compactSpace.mp hK
  have h1 : IsClosed ((fun q : Y × Kc => (q.1, (q.2 : P))) ⁻¹' C) :=
    hC.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have h2 := isClosedMap_fst_of_compactSpace _ h1
  have e : {y | ∃ p ∈ Kc, (y, p) ∈ C}
      = Prod.fst '' ((fun q : Y × Kc => (q.1, (q.2 : P))) ⁻¹' C) := by
    ext y
    constructor
    · rintro ⟨p, hp, hy⟩
      exact ⟨(y, ⟨p, hp⟩), hy, rfl⟩
    · rintro ⟨⟨y', p⟩, hq, rfl⟩
      exact ⟨p.1, p.2, hq⟩
  rw [e]
  exact h2

/-- The projection of `C ∩ U` (`C` closed, `U` open) along a `σ`-compact factor is measurable. -/
theorem proj_measurable {Y P : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] [PseudoMetricSpace P] [SigmaCompactSpace P] {C U : Set (Y × P)}
    (hC : IsClosed C) (hU : IsOpen U) :
    MeasurableSet {y | ∃ p, (y, p) ∈ C ∧ (y, p) ∈ U} := by
  obtain ⟨F, hFc, hFs, hFu, -⟩ := hU.exists_iUnion_isClosed
  have e : {y | ∃ p, (y, p) ∈ C ∧ (y, p) ∈ U}
      = ⋃ n : ℕ, ⋃ m : ℕ, {y | ∃ p ∈ compactCovering P m, (y, p) ∈ C ∩ F n} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨p, hc, hu⟩
      rw [← hFu] at hu
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hu
      have hp : p ∈ ⋃ m, compactCovering P m := by
        rw [iUnion_compactCovering]; exact Set.mem_univ p
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hp
      exact ⟨n, m, p, hm, hc, hn⟩
    · rintro ⟨n, m, p, -, hc, hn⟩
      exact ⟨p, hc, hFs n hn⟩
  rw [e]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    (closed_proj (hC.inter (hFc n)) (isCompact_compactCovering P m)).measurableSet

theorem mulVec_eq_iff {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ) (s : ℝ) :
    A *ᵥ u = s • u ↔ ∀ i, ∑ l, A i l * u l = s * u i := by
  constructor
  · intro h i
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct] using this
  · intro h
    funext i
    simpa [Matrix.mulVec, dotProduct] using h i

/-- A bound `u_a² ≤ c/(N s^k)` for all eigenvectors `u` of unit length with eigenvalue `s > 0`
    is a measurable condition on a family of matrices with measurable entries. -/
theorem eigvec_pos_good_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    (M : Ω → Matrix (Fin N) (Fin N) ℝ) (hM : ∀ a b, Measurable fun ω => M ω a b) (a : Fin N)
    (c : ℝ) (k : ℕ) :
    MeasurableSet {ω | ∀ (u : Fin N → ℝ) (s : ℝ), 0 < s → M ω *ᵥ u = s • u →
      ∑ b, u b ^ 2 = 1 → u a ^ 2 ≤ c / ((N : ℝ) * s ^ k)} := by
  have hN : (0 : ℝ) < N := by exact_mod_cast a.pos
  have hC : IsClosed {q : (Fin N → Fin N → ℝ) × ((Fin N → ℝ) × ℝ) |
      (∀ i, ∑ l, q.1 i l * q.2.1 l = q.2.2 * q.2.1 i) ∧ ∑ b, q.2.1 b ^ 2 = 1} := by
    have c1 : ∀ i : Fin N, Continuous fun q : (Fin N → Fin N → ℝ) × ((Fin N → ℝ) × ℝ) =>
        ∑ l, q.1 i l * q.2.1 l := fun i => by fun_prop
    have c2 : ∀ i : Fin N, Continuous fun q : (Fin N → Fin N → ℝ) × ((Fin N → ℝ) × ℝ) =>
        q.2.2 * q.2.1 i := fun i => by fun_prop
    have c3 : Continuous fun q : (Fin N → Fin N → ℝ) × ((Fin N → ℝ) × ℝ) =>
        ∑ b, q.2.1 b ^ 2 := by fun_prop
    refine IsClosed.inter ?_ ?_
    · exact isClosed_setOf_forall fun i => isClosed_eq (c1 i) (c2 i)
    · exact isClosed_eq c3 continuous_const
  have hU : IsOpen {q : (Fin N → Fin N → ℝ) × ((Fin N → ℝ) × ℝ) |
      0 < q.2.2 ∧ c < q.2.1 a ^ 2 * ((N : ℝ) * q.2.2 ^ k)} := by
    have c4 : Continuous fun q : (Fin N → Fin N → ℝ) × ((Fin N → ℝ) × ℝ) => q.2.2 := by
      fun_prop
    have c5 : Continuous fun q : (Fin N → Fin N → ℝ) × ((Fin N → ℝ) × ℝ) =>
        q.2.1 a ^ 2 * ((N : ℝ) * q.2.2 ^ k) := by fun_prop
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt continuous_const c4
    · exact isOpen_lt continuous_const c5
  have hF : Measurable fun ω => (fun a b => M ω a b : Fin N → Fin N → ℝ) :=
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hM a b
  refine (MeasurableSet.compl (hF (proj_measurable hC hU))).congr ?_
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage]
  constructor
  · intro h u s hs h1 h2
    by_contra hcon
    refine h ⟨(u, s), ⟨(mulVec_eq_iff (M ω) u s).1 h1, h2⟩, ⟨hs, ?_⟩⟩
    have hden : 0 < (N : ℝ) * s ^ k := mul_pos hN (pow_pos hs k)
    rw [le_div_iff₀ hden] at hcon
    exact not_le.1 hcon
  · rintro h ⟨⟨u, s⟩, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hb := h u s h3 ((mulVec_eq_iff (M ω) u s).2 h1) h2
    have hden : 0 < (N : ℝ) * s ^ k := mul_pos hN (pow_pos h3 k)
    rw [le_div_iff₀ hden] at hb
    exact absurd h4 (not_lt.2 hb)

/-- The exceptional set of `Delocalisation.deloc_sample`, verbatim, is measurable. -/
theorem deloc_sample_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N K : ℕ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → 2 * k ≤ K → ∀ (a : Fin N) (u : Fin N → ℝ) (s : ℝ), 0 < s →
        symGraph (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
            (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) *ᵥ u = s • u →
        ∑ b, u b ^ 2 = 1 →
        u a ^ 2 ≤ 2 * heatTorus d (2 * Real.pi ^ 2 * (((2 * k : ℕ) : ℝ) * σ)) 0
            / ((N : ℝ) * s ^ (2 * k))} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp (ms_forall fun a => ?_))
  exact eigvec_pos_good_measurable
    (fun ω => symGraph
      (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
      (fun a : Fin N => heatRho d σ N (fun j => X j ω) a))
    (fun a b => symGraph_rho_entry_measurable hσ d X hX N a b) a
    (2 * heatTorus d (2 * Real.pi ^ 2 * (((2 * k : ℕ) : ℝ) * σ)) 0) (2 * k)

/-- A closed condition on the coordinate `u_a` of all unit eigenvectors `u` to the `j`-th ordered
    eigenvalue is a measurable condition on a measurable family of symmetric matrices. -/
theorem eigvec_good_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    (M : Ω → Matrix (Fin N) (Fin N) ℝ) (hM : ∀ a b, Measurable fun ω => M ω a b)
    (hH : ∀ ω, (M ω).IsHermitian) (j : Fin (Fintype.card (Fin N))) (a : Fin N) (G : Set ℝ)
    (hG : IsClosed G) :
    MeasurableSet {ω | ∀ u : Fin N → ℝ,
      M ω *ᵥ u = eigTot N j (fun a b => M ω a b) • u → ∑ b, u b ^ 2 = 1 → u a ∈ G} := by
  have hcont : Continuous fun q :
      ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian} × (Fin N → ℝ) =>
      eigTot N j (q.1 : Fin N → Fin N → ℝ) :=
    (continuousOn_iff_continuous_restrict.1 (eigTot_continuousOn j)).comp continuous_fst
  have hC : IsClosed {q : ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian} × (Fin N → ℝ) |
      (∀ i, ∑ l, (q.1 : Fin N → Fin N → ℝ) i l * q.2 l
          = eigTot N j (q.1 : Fin N → Fin N → ℝ) * q.2 i) ∧ ∑ b, q.2 b ^ 2 = 1} := by
    have c1 : ∀ i : Fin N, Continuous fun q :
        ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian} × (Fin N → ℝ) =>
        ∑ l, (q.1 : Fin N → Fin N → ℝ) i l * q.2 l := fun i =>
      continuous_finset_sum _ fun l _ =>
        ((continuous_apply l).comp ((continuous_apply i).comp
          (continuous_subtype_val.comp continuous_fst))).mul
          ((continuous_apply l).comp continuous_snd)
    have c2 : ∀ i : Fin N, Continuous fun q :
        ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian} × (Fin N → ℝ) => q.2 i := fun i =>
      (continuous_apply i).comp continuous_snd
    have c3 : Continuous fun q :
        ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian} × (Fin N → ℝ) =>
        ∑ b, q.2 b ^ 2 :=
      continuous_finset_sum _ fun b _ => ((continuous_apply b).comp continuous_snd).pow 2
    refine IsClosed.inter ?_ ?_
    · exact isClosed_setOf_forall fun i => isClosed_eq (c1 i) (hcont.mul (c2 i))
    · exact isClosed_eq c3 continuous_const
  have hU : IsOpen {q : ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian} × (Fin N → ℝ) |
      q.2 a ∉ G} := by
    have c0 : Continuous fun q :
        ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian} × (Fin N → ℝ) => q.2 a :=
      (continuous_apply a).comp continuous_snd
    exact (hG.preimage c0).isOpen_compl
  have hF : Measurable fun ω =>
      (⟨fun a b => M ω a b, hH ω⟩ : ↥{A : Fin N → Fin N → ℝ | (Matrix.of A).IsHermitian}) :=
    (measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hM a b).subtype_mk
  refine (MeasurableSet.compl (hF (proj_measurable hC hU))).congr ?_
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage]
  constructor
  · intro h u h1 h2
    by_contra hcon
    exact h ⟨u, ⟨(mulVec_eq_iff (M ω) u _).1 h1, h2⟩, hcon⟩
  · rintro h ⟨u, ⟨h1, h2⟩, h3⟩
    exact h3 (h u ((mulVec_eq_iff (M ω) u _).2 h1) h2)

/-- An index in the range of a shell: the shell parameter is a value of `|n|²` on the lattice. -/
theorem shell_value_exists {d : ℕ} {r : ℝ} {j : ℕ} {Hlt Hle : Finset (Fin d → ℤ)}
    (hlt : ∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r)
    (hle : ∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r)
    (h1 : 1 + 2 * Hlt.card ≤ j) (h2 : j ≤ 2 * Hle.card) :
    ∃ n : Fin d → ℤ, ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r := by
  have hcard : Hlt.card < Hle.card := by omega
  obtain ⟨n, hn, hn'⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have ha := (hle n).1 hn
  refine ⟨n, le_antisymm ha.2 ?_⟩
  by_contra hc
  exact hn' ((hlt n).2 ⟨ha.1, not_le.1 hc⟩)

/-- The exceptional set of `DelocalisationFinal.deloc_sample_shell`, verbatim, is measurable. -/
theorem deloc_sample_shell_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d N K : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (δp : ℝ) :
    MeasurableSet {ω | ¬
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
                  * (4 * Real.pi * (1 + r)) ^ ((d : ℝ) / 4) / Real.sqrt N} := by
  have hH : ∀ ω, (symGraph
      (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
      (fun i : Fin N =>
        (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian :=
    fun ω => symGraph_sample_isHermitian d N X ω
  have hgood : MeasurableSet {ω | ∀ (j : Fin (Fintype.card (Fin N))) (n : Fin d → ℤ),
      (0 < ∑ i, ((n i : ℤ) : ℝ) ^ 2 ∧ ∃ Hlt Hle : Finset (Fin d → ℤ),
        (∀ m, m ∈ Hlt ↔ lexPos d m ∧ ∑ i, ((m i : ℤ) : ℝ) ^ 2 < ∑ i, ((n i : ℤ) : ℝ) ^ 2) ∧
        (∀ m, m ∈ Hle ↔ lexPos d m ∧ ∑ i, ((m i : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) ∧
        1 + 2 * Hlt.card ≤ j.val ∧ j.val ≤ 2 * Hle.card ∧
        2 * Real.pi ^ 2 * σ * (∑ i, ((n i : ℤ) : ℝ) ^ 2) ≤ 1 / 2 ∧
        1 ≤ (K : ℝ) * (Real.pi ^ 2 * σ * (∑ i, ((n i : ℤ) : ℝ) ^ 2)) ∧
        2 * Real.exp 1 * (eigC3 d * δp)
            * (1 + Real.sqrt (2 * Real.pi * (∑ i, ((n i : ℤ) : ℝ) ^ 2))) ^ d
          ≤ Real.sqrt (2 * Real.pi ^ 2 * σ * (∑ i, ((n i : ℤ) : ℝ) ^ 2))) →
      ∀ (a : Fin N) (u : Fin N → ℝ),
        symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) *ᵥ u
          = eigTot N j (fun a b => symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) a b) • u →
        ∑ b, u b ^ 2 = 1 →
        u a ∈ {x : ℝ |
          x ^ 2 ≤ 8 * Real.exp 1 ^ 2
              * (1 + Real.sqrt (2 * Real.pi * (∑ i, ((n i : ℤ) : ℝ) ^ 2))) ^ d / N
          ∧ x ^ 4 ≤ 64 * Real.exp 1 ^ 4
              * (4 * Real.pi * (1 + ∑ i, ((n i : ℤ) : ℝ) ^ 2)) ^ d / (N : ℝ) ^ 2
          ∧ |x| ≤ (64 * Real.exp 1 ^ 4) ^ (1 / 4 : ℝ)
              * (4 * Real.pi * (1 + ∑ i, ((n i : ℤ) : ℝ) ^ 2)) ^ ((d : ℝ) / 4)
                / Real.sqrt N}} := by
    refine ms_forall fun j => ms_forall fun n => ms_imp (ms_forall fun a => ?_)
    refine eigvec_good_measurable
      (fun ω => symGraph
        (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
        (fun i : Fin N =>
          (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N))
      (fun a b => symGraph_fin_entry_measurable hσ d X hX N a b) hH j a _ ?_
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_le (continuous_pow 2) continuous_const
    · exact isClosed_le (continuous_pow 4) continuous_const
    · exact isClosed_le continuous_abs continuous_const
  refine MeasurableSet.compl ?_
  refine hgood.congr ?_
  ext ω
  constructor
  · intro h hS j r hr Hlt Hle hlt hle h1 h2 c1 c2 c3 u a hSu hu
    obtain ⟨n, hn⟩ := shell_value_exists hlt hle h1 h2
    subst hn
    rw [← eigTot_eq _ hS j] at hSu
    exact h j n ⟨hr, Hlt, Hle, hlt, hle, h1, h2, c1, c2, c3⟩ a u hSu hu
  · rintro h j n ⟨hr, Hlt, Hle, hlt, hle, h1, h2, c1, c2, c3⟩ a u hSu hu
    rw [eigTot_eq _ (hH ω) j] at hSu
    exact h (hH ω) j _ hr Hlt Hle hlt hle h1 h2 c1 c2 c3 u a hSu hu

/-! ### Not covered: `EigenspaceSample.eigspace_sample`

Its exceptional set contains `specProj hS J w`, the projection onto the span of the vectors with
index in `J` of the eigenvector basis that Mathlib CHOOSES for the matrix (`hS.eigenvectorBasis`).
The statement does not require `E_k < g`, so `J` need not be a union of full eigenspaces; when an
eigenvalue is degenerate and its indices lie partly in `J`, the value of `specProj` depends on the
chosen basis, about whose dependence on the matrix nothing is known. Measurability of that set,
verbatim, is therefore not provable by the methods used here. -/

end Reals2Sets

end CTG.Reals2
