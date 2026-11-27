/-
Forty-second file: the Laplace–Beltrami limit of the population operator on the sphere `S²` on the harmonics
`Re (a·y)^l`.  Imports `CorrelationsToGeometryFunkHeckeLink` (which loads the seventh file; compiled modules
under `.tools/leanbuild`); namespace `CTG.FunkHecke.SphereLB`; check with `./check_funk_hecke_sphere_lb.sh`.
With `λ = l(l+1)`, `s_l = sphS ξ l`, `0 < ξ ≤ 1/20`:
`eig_limit`:  `|(2/ξ²)(1 − s_l) − λ| ≤ (ξ²/6 + 5ξ⁴/12) λ + (51/200) ξ² λ² + (27/200) ξ⁴ λ³`;
`eig_limit2`: `|(2/ξ²)(1 − s_l) − λ + ξ²(λ/6 + λ²/4)| ≤ ξ⁴((5/12) λ + (1/3 + 5ξ²/24) λ² + (27/200) λ³)`.
`Lxi ξ f x = (2/ξ²)(f x − Pinf (gk ξ) f x)`; `Lxi_harmonic` (exact eigen-relation for `f = Re (a·y)^l`, `a`
isotropic, every `ξ`), `Lxi_limit`, `Lxi_limit2` (the two bounds times `|f(x)|`).
Extension to `ℝ³`: `laplacian_G`, `laplacian_F` (`(a·y)^l` and its real part are harmonic, Mathlib's Laplacian),
`Fext_homogeneous`, `euler_F`.
NOT claimed and NOT formalised: `−Δ_{S²} f = l(l+1) f` (there is no Laplace–Beltrami operator of the sphere in
Mathlib); the limit for general smooth `f` (completeness, summation over `l`).
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeLink

open MeasureTheory Set Metric Real
open scoped RealInnerProductSpace

namespace CTG.FunkHecke.SphereLB

open CTG.FunkHecke (S2 E3 gk Pinf cdot Isotropic Pinf_harmonic)
open CTG.Reals2.SphereOneDim (sphere_F1_true sphere_constants sphSigma sphM sphSigma_expansion)

/-! ### (1) Eigenvalue limit -/

/-- Arithmetic core, first order.  `e`-notation: `s` is `s_l`, `λ = l(l+1)`, `σ = σ_ξ`,
`a = m₄/64`, `b = m₆/720`. -/
theorem eig_arith {ξ σ a b s lam : ℝ} (hξ : 0 < ξ) (hlam : 0 ≤ lam)
    (hF : |s - 1 + σ * lam - a * lam ^ 2| ≤ b * lam ^ 3)
    (hA : |σ - ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6)| ≤ 5 / 24 * (ξ ^ 2) ^ 3)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ ξ ^ 2 / 2)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 51 / 100 * σ ^ 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 27 / 50 * σ ^ 3) :
    |2 / ξ ^ 2 * (1 - s) - lam|
      ≤ (ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * lam + 51 / 200 * ξ ^ 2 * lam ^ 2
        + 27 / 200 * ξ ^ 4 * lam ^ 3 := by
  set w : ℝ := 2 / ξ ^ 2 with hwdef
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have hw0 : 0 < w := by positivity
  have hw : w * ξ ^ 2 = 2 := by rw [hwdef]; field_simp
  set A := σ - ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6) with hAdef
  set e := s - 1 + σ * lam - a * lam ^ 2 with hedef
  have key : w * (1 - s) - lam = w * A * lam - ξ ^ 2 / 6 * lam - w * a * lam ^ 2 - w * e := by
    have : w * (1 - s) - lam = w * (σ * lam - a * lam ^ 2 - e) - lam := by rw [hedef]; ring
    rw [this, hAdef]
    have h2 : w * (ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6)) = 1 - ξ ^ 2 / 6 := by
      have : w * (ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6)) = (w * ξ ^ 2) / 2 * (1 - ξ ^ 2 / 6) := by ring
      rw [this, hw]; ring
    linear_combination (-lam) * h2 + (lam - lam * ξ ^ 2 / 6) * hw
  -- term 1
  have t1 : |w * A * lam| ≤ 5 / 12 * ξ ^ 4 * lam := by
    rw [abs_mul, abs_mul, abs_of_pos hw0, abs_of_nonneg hlam]
    have : w * |A| ≤ w * (5 / 24 * (ξ ^ 2) ^ 3) := mul_le_mul_of_nonneg_left hA hw0.le
    have e1 : w * (5 / 24 * (ξ ^ 2) ^ 3) = 5 / 12 * ξ ^ 4 := by
      have : w * (5 / 24 * (ξ ^ 2) ^ 3) = (w * ξ ^ 2) * (5 / 24 * ξ ^ 4) := by ring
      rw [this, hw]; ring
    exact mul_le_mul_of_nonneg_right (this.trans e1.le) hlam
  -- term 3
  have hσsq : σ ^ 2 ≤ (ξ ^ 2 / 2) ^ 2 := pow_le_pow_left₀ hσ0.le hσ1 2
  have hσcube : σ ^ 3 ≤ (ξ ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hσ0.le hσ1 3
  have t3a : 0 ≤ w * a * lam ^ 2 := by positivity
  have t3b : w * a * lam ^ 2 ≤ 51 / 200 * ξ ^ 2 * lam ^ 2 := by
    have h1 : a ≤ 51 / 100 * (ξ ^ 2 / 2) ^ 2 := by nlinarith
    have h2 : w * a ≤ w * (51 / 100 * (ξ ^ 2 / 2) ^ 2) := mul_le_mul_of_nonneg_left h1 hw0.le
    have e1 : w * (51 / 100 * (ξ ^ 2 / 2) ^ 2) = 51 / 200 * ξ ^ 2 := by
      have : w * (51 / 100 * (ξ ^ 2 / 2) ^ 2) = (w * ξ ^ 2) * (51 / 400 * ξ ^ 2) := by ring
      rw [this, hw]; ring
    exact mul_le_mul_of_nonneg_right (h2.trans e1.le) (by positivity)
  -- term 4
  have t4 : |w * e| ≤ 27 / 200 * ξ ^ 4 * lam ^ 3 := by
    rw [abs_mul, abs_of_pos hw0]
    have h1 : b ≤ 27 / 50 * (ξ ^ 2 / 2) ^ 3 := by nlinarith
    have h2 : |e| ≤ 27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3 :=
      hF.trans (mul_le_mul_of_nonneg_right h1 (by positivity))
    have h3 : w * |e| ≤ w * (27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3) :=
      mul_le_mul_of_nonneg_left h2 hw0.le
    have e1 : w * (27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3) = 27 / 200 * ξ ^ 4 * lam ^ 3 := by
      have : w * (27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3)
          = (w * ξ ^ 2) * (27 / 400 * ξ ^ 4 * lam ^ 3) := by ring
      rw [this, hw]; ring
    exact h3.trans e1.le
  rw [key]
  have hl6 : 0 ≤ ξ ^ 2 / 6 * lam := by positivity
  rw [abs_le] at t1 t4 ⊢
  constructor <;> nlinarith [abs_nonneg A]

/-- Arithmetic core, second order (leading correction identified). -/
theorem eig_arith2 {ξ σ a b s lam : ℝ} (hξ : 0 < ξ) (hlam : 0 ≤ lam)
    (hF : |s - 1 + σ * lam - a * lam ^ 2| ≤ b * lam ^ 3)
    (hA : |σ - ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6)| ≤ 5 / 24 * (ξ ^ 2) ^ 3)
    (hA2 : |a - σ ^ 2 / 2| ≤ (ξ ^ 2) ^ 3 / 8)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ ξ ^ 2 / 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 27 / 50 * σ ^ 3) :
    |2 / ξ ^ 2 * (1 - s) - lam + ξ ^ 2 * (lam / 6 + lam ^ 2 / 4)|
      ≤ ξ ^ 4 * (5 / 12 * lam + (1 / 3 + 5 / 24 * ξ ^ 2) * lam ^ 2 + 27 / 200 * lam ^ 3) := by
  set w : ℝ := 2 / ξ ^ 2 with hwdef
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have hw0 : 0 < w := by positivity
  have hw : w * ξ ^ 2 = 2 := by rw [hwdef]; field_simp
  set A := σ - ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6) with hAdef
  set e := s - 1 + σ * lam - a * lam ^ 2 with hedef
  set B := w * a - ξ ^ 2 / 4 with hBdef
  have key : w * (1 - s) - lam + ξ ^ 2 * (lam / 6 + lam ^ 2 / 4)
      = w * A * lam - B * lam ^ 2 - w * e := by
    have : w * (1 - s) - lam = w * (σ * lam - a * lam ^ 2 - e) - lam := by rw [hedef]; ring
    rw [this, hAdef, hBdef]
    have h2 : w * (ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6)) = 1 - ξ ^ 2 / 6 := by
      have : w * (ξ ^ 2 / 2 * (1 - ξ ^ 2 / 6)) = (w * ξ ^ 2) / 2 * (1 - ξ ^ 2 / 6) := by ring
      rw [this, hw]; ring
    linear_combination (-lam) * h2 + (lam - lam * ξ ^ 2 / 6) * hw
  have t1 : |w * A * lam| ≤ 5 / 12 * ξ ^ 4 * lam := by
    rw [abs_mul, abs_mul, abs_of_pos hw0, abs_of_nonneg hlam]
    have : w * |A| ≤ w * (5 / 24 * (ξ ^ 2) ^ 3) := mul_le_mul_of_nonneg_left hA hw0.le
    have e1 : w * (5 / 24 * (ξ ^ 2) ^ 3) = 5 / 12 * ξ ^ 4 := by
      have : w * (5 / 24 * (ξ ^ 2) ^ 3) = (w * ξ ^ 2) * (5 / 24 * ξ ^ 4) := by ring
      rw [this, hw]; ring
    exact mul_le_mul_of_nonneg_right (this.trans e1.le) hlam
  -- the coefficient of λ²
  have tB : |B| ≤ ξ ^ 4 / 3 + 5 / 24 * ξ ^ 6 := by
    have split : B = w * (a - σ ^ 2 / 2) + w / 2 * ((σ - ξ ^ 2 / 2) * (σ + ξ ^ 2 / 2)) := by
      rw [hBdef]
      have : w / 2 * ((σ - ξ ^ 2 / 2) * (σ + ξ ^ 2 / 2)) = w * σ ^ 2 / 2 - (w * ξ ^ 2) * ξ ^ 2 / 8 := by
        ring
      rw [this, hw]; ring
    have p1 : |w * (a - σ ^ 2 / 2)| ≤ ξ ^ 4 / 4 := by
      rw [abs_mul, abs_of_pos hw0]
      have : w * |a - σ ^ 2 / 2| ≤ w * ((ξ ^ 2) ^ 3 / 8) := mul_le_mul_of_nonneg_left hA2 hw0.le
      have e1 : w * ((ξ ^ 2) ^ 3 / 8) = ξ ^ 4 / 4 := by
        have : w * ((ξ ^ 2) ^ 3 / 8) = (w * ξ ^ 2) * (ξ ^ 4 / 8) := by ring
        rw [this, hw]; ring
      exact this.trans e1.le
    have hd : |σ - ξ ^ 2 / 2| ≤ ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6 := by
      have : σ - ξ ^ 2 / 2 = A - ξ ^ 4 / 12 := by rw [hAdef]; ring
      rw [this]
      calc |A - ξ ^ 4 / 12| ≤ |A| + |ξ ^ 4 / 12| := abs_sub _ _
        _ ≤ 5 / 24 * (ξ ^ 2) ^ 3 + ξ ^ 4 / 12 := by
            rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ξ ^ 4 / 12)]; linarith
        _ = ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6 := by ring
    have p2 : |w / 2 * ((σ - ξ ^ 2 / 2) * (σ + ξ ^ 2 / 2))| ≤ ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6 := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < w / 2),
        abs_of_pos (by positivity : (0:ℝ) < σ + ξ ^ 2 / 2)]
      have h1 : |σ - ξ ^ 2 / 2| * (σ + ξ ^ 2 / 2) ≤ (ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6) * ξ ^ 2 :=
        mul_le_mul hd (by linarith) (by positivity) (by positivity)
      have h2 : w / 2 * (|σ - ξ ^ 2 / 2| * (σ + ξ ^ 2 / 2))
          ≤ w / 2 * ((ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6) * ξ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have e1 : w / 2 * ((ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6) * ξ ^ 2) = ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6 := by
        have : w / 2 * ((ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6) * ξ ^ 2)
            = (w * ξ ^ 2) / 2 * (ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6) := by ring
        rw [this, hw]; ring
      exact h2.trans e1.le
    rw [split]
    calc _ ≤ |w * (a - σ ^ 2 / 2)| + |w / 2 * ((σ - ξ ^ 2 / 2) * (σ + ξ ^ 2 / 2))| :=
          abs_add_le _ _
      _ ≤ ξ ^ 4 / 4 + (ξ ^ 4 / 12 + 5 / 24 * ξ ^ 6) := add_le_add p1 p2
      _ = ξ ^ 4 / 3 + 5 / 24 * ξ ^ 6 := by ring
  have t3 : |B * lam ^ 2| ≤ (ξ ^ 4 / 3 + 5 / 24 * ξ ^ 6) * lam ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam ^ 2)]
    exact mul_le_mul_of_nonneg_right tB (by positivity)
  have hσcube : σ ^ 3 ≤ (ξ ^ 2 / 2) ^ 3 := pow_le_pow_left₀ hσ0.le hσ1 3
  have t4 : |w * e| ≤ 27 / 200 * ξ ^ 4 * lam ^ 3 := by
    rw [abs_mul, abs_of_pos hw0]
    have h1 : b ≤ 27 / 50 * (ξ ^ 2 / 2) ^ 3 := by nlinarith
    have h2 : |e| ≤ 27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3 :=
      hF.trans (mul_le_mul_of_nonneg_right h1 (by positivity))
    have h3 : w * |e| ≤ w * (27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3) :=
      mul_le_mul_of_nonneg_left h2 hw0.le
    have e1 : w * (27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3) = 27 / 200 * ξ ^ 4 * lam ^ 3 := by
      have : w * (27 / 50 * (ξ ^ 2 / 2) ^ 3 * lam ^ 3)
          = (w * ξ ^ 2) * (27 / 400 * ξ ^ 4 * lam ^ 3) := by ring
      rw [this, hw]; ring
    exact h3.trans e1.le
  rw [key]
  calc |w * A * lam - B * lam ^ 2 - w * e|
      ≤ |w * A * lam| + |B * lam ^ 2| + |w * e| := by
        have := abs_sub (w * A * lam - B * lam ^ 2) (w * e)
        have := abs_sub (w * A * lam) (B * lam ^ 2)
        linarith
    _ ≤ 5 / 12 * ξ ^ 4 * lam + (ξ ^ 4 / 3 + 5 / 24 * ξ ^ 6) * lam ^ 2
        + 27 / 200 * ξ ^ 4 * lam ^ 3 := by linarith
    _ = _ := by ring

/-- The constants of `sphere_constants` in the form used above: `a = m₄/64 ≤ (51/100) σ²`,
`b = m₆/720 ≤ (27/50) σ³`. -/
theorem consts {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) :
    0 < sphSigma ξ ∧ sphSigma ξ ≤ ξ ^ 2 / 2 ∧
    0 ≤ sphM ξ 4 / 64 ∧ sphM ξ 4 / 64 ≤ 51 / 100 * sphSigma ξ ^ 2 ∧
    0 ≤ sphM ξ 6 / 720 ∧ sphM ξ 6 / 720 ≤ 27 / 50 * sphSigma ξ ^ 3 := by
  obtain ⟨hσ0, hσ1, ha0, ha1, hb0, hb1⟩ := sphere_constants hξ hξ1
  have hs2 : 0 < sphSigma ξ ^ 2 := by positivity
  have hs3 : 0 < sphSigma ξ ^ 3 := by positivity
  have ea : sphM ξ 4 / 64 = sphM ξ 4 / (32 * sphSigma ξ ^ 2) * (sphSigma ξ ^ 2 / 2) := by
    field_simp; ring
  have eb : sphM ξ 6 / 720 = sphM ξ 6 / (720 * sphSigma ξ ^ 3) * sphSigma ξ ^ 3 := by
    field_simp
  refine ⟨hσ0, hσ1, ?_, ?_, ?_, ?_⟩
  · rw [ea]; positivity
  · rw [ea]; nlinarith
  · rw [eb]; positivity
  · rw [eb]; nlinarith

/-- **Eigenvalue limit on `S²`, first order.**  For `0 < ξ ≤ 1/20` and every `l`, with
`λ = l(l+1)`:
`|(2/ξ²)(1 − s_l) − λ| ≤ (ξ²/6 + 5ξ⁴/12) λ + (51/200) ξ² λ² + (27/200) ξ⁴ λ³`. -/
theorem eig_limit {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (l : ℕ) :
    |2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) - (l : ℝ) * (l + 1)|
      ≤ (ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * ((l : ℝ) * (l + 1))
        + 51 / 200 * ξ ^ 2 * ((l : ℝ) * (l + 1)) ^ 2
        + 27 / 200 * ξ ^ 4 * ((l : ℝ) * (l + 1)) ^ 3 := by
  rw [CTG.FunkHeckeLink.sphS_eq]
  obtain ⟨hσ0, hσ1, ha0, ha1, hb0, hb1⟩ := consts hξ hξ1
  have hF := sphere_F1_true ξ l
  have hA := (sphSigma_expansion hξ (by linarith)).1
  refine eig_arith hξ (by positivity) ?_ hA hσ0 hσ1 ha0 ha1 hb0 hb1
  have e : sphSigma ξ = sphM ξ 2 / 4 + sphM ξ 4 / 96 := rfl
  rw [e]
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hF

/-- **Eigenvalue limit on `S²`, second order**: the leading correction is `−ξ²(λ/6 + λ²/4)`;
for `0 < ξ ≤ 1/20`:
`|(2/ξ²)(1 − s_l) − λ + ξ²(λ/6 + λ²/4)| ≤ ξ⁴ ((5/12) λ + (1/3 + 5ξ²/24) λ² + (27/200) λ³)`. -/
theorem eig_limit2 {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (l : ℕ) :
    |2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) - (l : ℝ) * (l + 1)
        + ξ ^ 2 * ((l : ℝ) * (l + 1) / 6 + ((l : ℝ) * (l + 1)) ^ 2 / 4)|
      ≤ ξ ^ 4 * (5 / 12 * ((l : ℝ) * (l + 1)) + (1 / 3 + 5 / 24 * ξ ^ 2) * ((l : ℝ) * (l + 1)) ^ 2
        + 27 / 200 * ((l : ℝ) * (l + 1)) ^ 3) := by
  rw [CTG.FunkHeckeLink.sphS_eq]
  obtain ⟨hσ0, hσ1, -, -, hb0, hb1⟩ := consts hξ hξ1
  have hF := sphere_F1_true ξ l
  obtain ⟨hA, hA2⟩ := sphSigma_expansion hξ (by linarith)
  have hA2' : |sphM ξ 4 / 64 - sphSigma ξ ^ 2 / 2| ≤ (ξ ^ 2) ^ 3 / 8 := hA2
  refine eig_arith2 hξ (by positivity) ?_ hA hA2' hσ0 hσ1 hb0 hb1
  have e : sphSigma ξ = sphM ξ 2 / 4 + sphM ξ 4 / 96 := rfl
  rw [e]
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hF

/-! ### (2) Operator form on the harmonics -/

/-- The graph-Laplacian limit operator of the population walk on `S²`:
`L_ξ f(x) = (2/ξ²)(f(x) − P_∞ f(x))` (here `c_h = 1`, the Gaussian profile in the angle). -/
noncomputable def Lxi (ξ : ℝ) (f : S2 → ℝ) (x : S2) : ℝ :=
  2 / ξ ^ 2 * (f x - Pinf (gk ξ) f x)

/-- `L_ξ` acts on `Re (a·y)^l` (`a` isotropic) as multiplication by `(2/ξ²)(1 − s_l)`. -/
theorem Lxi_harmonic (ξ : ℝ) (p q : E3) (h : Isotropic p q) (l : ℕ) (x : S2) :
    Lxi ξ (fun y => (cdot p q y ^ l).re) x
      = 2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) * (cdot p q x ^ l).re := by
  unfold Lxi
  rw [Pinf_harmonic ξ p q h l x]
  ring

/-- **`thm:LB` on `S²` for the harmonics `Re (a·y)^l`**: for `0 < ξ ≤ 1/20`, every isotropic
`a = p + i q`, every `l` and every `x ∈ S²`, with `λ = l(l+1)` and `f(y) = Re (a·y)^l`:
`|L_ξ f(x) − λ f(x)| ≤ [(ξ²/6 + 5ξ⁴/12) λ + (51/200) ξ² λ² + (27/200) ξ⁴ λ³] · |f(x)|`. -/
theorem Lxi_limit {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (p q : E3) (h : Isotropic p q)
    (l : ℕ) (x : S2) :
    |Lxi ξ (fun y => (cdot p q y ^ l).re) x - (l : ℝ) * (l + 1) * (cdot p q x ^ l).re|
      ≤ ((ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * ((l : ℝ) * (l + 1))
          + 51 / 200 * ξ ^ 2 * ((l : ℝ) * (l + 1)) ^ 2
          + 27 / 200 * ξ ^ 4 * ((l : ℝ) * (l + 1)) ^ 3) * |(cdot p q x ^ l).re| := by
  rw [Lxi_harmonic ξ p q h l x, ← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (eig_limit hξ hξ1 l) (abs_nonneg _)

/-- Second-order form of `Lxi_limit`: `L_ξ f = [λ − ξ²(λ/6 + λ²/4)] f + O(ξ⁴)` on the harmonics. -/
theorem Lxi_limit2 {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (p q : E3) (h : Isotropic p q)
    (l : ℕ) (x : S2) :
    |Lxi ξ (fun y => (cdot p q y ^ l).re) x
        - ((l : ℝ) * (l + 1) - ξ ^ 2 * ((l : ℝ) * (l + 1) / 6 + ((l : ℝ) * (l + 1)) ^ 2 / 4))
          * (cdot p q x ^ l).re|
      ≤ ξ ^ 4 * (5 / 12 * ((l : ℝ) * (l + 1)) + (1 / 3 + 5 / 24 * ξ ^ 2) * ((l : ℝ) * (l + 1)) ^ 2
          + 27 / 200 * ((l : ℝ) * (l + 1)) ^ 3) * |(cdot p q x ^ l).re| := by
  rw [Lxi_harmonic ξ p q h l x, ← sub_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have := eig_limit2 hξ hξ1 l
  convert this using 2; ring

/-! ### (3) The extension to `ℝ³`: harmonic, homogeneous, Euler -/

/-- The complex linear form `y ↦ a·y = ⟨p,y⟩ + i⟨q,y⟩` as a real-linear continuous map. -/
noncomputable def Lform (p q : E3) : E3 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ p) + Complex.I • Complex.ofRealCLM.comp (innerSL ℝ q)

theorem Lform_apply (p q y : E3) : Lform p q y = cdot p q y := by
  simp [Lform, cdot]

/-- `Σ_i (a·b_i)² = ⟨p,p⟩ − ⟨q,q⟩ + 2i⟨p,q⟩` for any orthonormal basis. -/
theorem sum_Lform_sq {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E3) (p q : E3) :
    ∑ i, Lform p q (v i) * Lform p q (v i)
      = ((⟪p, p⟫ - ⟪q, q⟫ : ℝ) : ℂ) + Complex.I * ((2 * ⟪p, q⟫ : ℝ) : ℂ) := by
  have hpp := v.sum_inner_mul_inner p p
  have hqq := v.sum_inner_mul_inner q q
  have hpq := v.sum_inner_mul_inner p q
  simp only [Lform_apply, cdot]
  have e : ∀ i, ((⟪p, v i⟫ : ℂ) + Complex.I * ⟪q, v i⟫) * ((⟪p, v i⟫ : ℂ) + Complex.I * ⟪q, v i⟫)
      = ((⟪p, v i⟫ * ⟪v i, p⟫ - ⟪q, v i⟫ * ⟪v i, q⟫ : ℝ) : ℂ)
        + Complex.I * ((2 * (⟪p, v i⟫ * ⟪v i, q⟫) : ℝ) : ℂ) := by
    intro i
    rw [real_inner_comm (v i) p, real_inner_comm (v i) q]
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · rw [← hpp, ← hqq]; push_cast; rfl
  · rw [← hpq]; push_cast; rfl

/-- For isotropic `a`, `Σ_i (a·b_i)² = 0`. -/
theorem sum_Lform_sq_iso {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E3) (p q : E3)
    (h : Isotropic p q) : ∑ i, Lform p q (v i) * Lform p q (v i) = 0 := by
  rw [sum_Lform_sq, h.1, h.2]; simp

/-- The complex extension `G(y) = (a·y)^l`. -/
noncomputable def Gext (p q : E3) (l : ℕ) (y : E3) : ℂ := Lform p q y ^ l

/-- The first derivative of `G`. -/
noncomputable def DG (p q : E3) (l : ℕ) (y : E3) : E3 →L[ℝ] ℂ :=
  (l • Lform p q y ^ (l - 1)) • Lform p q

theorem hasFDerivAt_G (p q : E3) (l : ℕ) (y : E3) :
    HasFDerivAt (Gext p q l) (DG p q l y) y :=
  (Lform p q).hasFDerivAt.pow l

theorem fderiv_G (p q : E3) (l : ℕ) : fderiv ℝ (Gext p q l) = DG p q l :=
  funext fun y => (hasFDerivAt_G p q l y).fderiv

/-- The scalar tower `ℝ → ℂ → (E3 →L[ℝ] ℂ)` (not found by instance search). -/
instance instTowerA154 : IsScalarTower ℝ ℂ (E3 →L[ℝ] ℂ) :=
  ⟨fun r z f => by
    ext v; simp [smul_eq_mul, mul_assoc, Complex.real_smul]
    first | rw [Complex.real_smul] | exact (Complex.real_smul (x := r)).symm | rfl⟩

/-- The derivative of the coefficient `y ↦ l (a·y)^{l−1}`. -/
theorem hasFDerivAt_coef (p q : E3) (l : ℕ) (y : E3) :
    HasFDerivAt (fun y => l • Lform p q y ^ (l - 1))
      (l • (((l - 1) • Lform p q y ^ (l - 1 - 1)) • Lform p q)) y :=
  ((Lform p q).hasFDerivAt.pow (l - 1)).const_smul l

theorem hasFDerivAt_DG (p q : E3) (l : ℕ) (y : E3) :
    HasFDerivAt (DG p q l)
      ((l • (((l - 1) • Lform p q y ^ (l - 1 - 1)) • Lform p q)).smulRight (Lform p q)) y :=
  (hasFDerivAt_coef p q l y).smul_const (Lform p q)

theorem iteratedFDeriv_G (p q : E3) (l : ℕ) (y v : E3) :
    iteratedFDeriv ℝ 2 (Gext p q l) y ![v, v]
      = (l • ((l - 1) • Lform p q y ^ (l - 1 - 1))) * (Lform p q v * Lform p q v) := by
  rw [iteratedFDeriv_two_apply, fderiv_G, (hasFDerivAt_DG p q l y).fderiv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [nsmul_eq_mul]
  ring

theorem contDiff_G (p q : E3) (l : ℕ) : ContDiff ℝ 2 (Gext p q l) :=
  (Lform p q).contDiff.pow l

open Laplacian in
/-- **The complex extension `G(y) = (a·y)^l` is harmonic on `ℝ³`** (Mathlib's Laplacian) for
isotropic `a`. -/
theorem laplacian_G (p q : E3) (h : Isotropic p q) (l : ℕ) : Δ (Gext p q l) = 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E3)]
  funext y
  simp only [iteratedFDeriv_G, Pi.zero_apply]
  rw [← Finset.mul_sum, sum_Lform_sq_iso _ p q h, mul_zero]

/-- The real extension `F(y) = Re (a·y)^l` on `ℝ³`; its restriction to `S²` is the eigenfunction of
`Pinf_harmonic`. -/
noncomputable def Fext (p q : E3) (l : ℕ) (y : E3) : ℝ := (cdot p q y ^ l).re

theorem Fext_eq (p q : E3) (l : ℕ) : Fext p q l = Complex.reCLM ∘ Gext p q l := by
  funext y; simp [Fext, Gext, Lform_apply]

theorem Fext_restrict (p q : E3) (l : ℕ) (y : S2) :
    Fext p q l (y : E3) = (cdot p q y ^ l).re := rfl

open Laplacian in
/-- **`F(y) = Re (a·y)^l` is harmonic on `ℝ³`** for isotropic `a`: `Δ F = 0`. -/
theorem laplacian_F (p q : E3) (h : Isotropic p q) (l : ℕ) : Δ (Fext p q l) = 0 := by
  funext y
  rw [Fext_eq, ((contDiff_G p q l).contDiffAt).laplacian_CLM_comp_left]
  simp [laplacian_G p q h l]

/-- **Homogeneity of degree `l`**: `F(r y) = r^l F(y)`. -/
theorem Fext_homogeneous (p q : E3) (l : ℕ) (r : ℝ) (y : E3) :
    Fext p q l (r • y) = r ^ l * Fext p q l y := by
  simp only [Fext]
  rw [← Lform_apply, ← Lform_apply, map_smul, Complex.real_smul, mul_pow, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul]

/-- **Euler's identity** for the complex extension: `DG(y) y = l G(y)`. -/
theorem euler_G (p q : E3) (l : ℕ) (y : E3) :
    fderiv ℝ (Gext p q l) y y = l * Gext p q l y := by
  rw [fderiv_G]
  simp only [DG, Gext, ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · subst h0; simp
  · obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

/-- **Euler's identity** for `F`: `DF(y) y = l F(y)`. -/
theorem euler_F (p q : E3) (l : ℕ) (y : E3) :
    fderiv ℝ (Fext p q l) y y = l * Fext p q l y := by
  rw [Fext_eq]
  have hd : HasFDerivAt (Complex.reCLM ∘ Gext p q l)
      (Complex.reCLM.comp (fderiv ℝ (Gext p q l) y)) y :=
    Complex.reCLM.hasFDerivAt.comp y (hasFDerivAt_G p q l y |>.differentiableAt.hasFDerivAt)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, euler_G, Function.comp_apply]
  simp [Gext, Lform_apply]

end CTG.FunkHecke.SphereLB
