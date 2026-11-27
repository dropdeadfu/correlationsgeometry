/-
Fifty-third file: the normalising second moment of the Gaussian profile equals one.
Namespace `CTG.GaussMoment`; imports the fifty-second file (compiled module); check with `./check_gauss_moment.sh`.
`radial`: `∫_0^∞ y^q exp(−y²/2) dy` through the Gamma function; `norm_int`: `∫_{ℝⁿ} ‖z‖^k exp(−‖z‖²/2) dz` by the
radial integration formula of Mathlib; `second_moment`: `(∫ ‖z‖² g)/(n ∫ g) = 1` for `n ≥ 1`;
`gam₂_eq_one`: the constant `gam₂ n` of the fifty-second file equals `1`, so that `m₂ = 1` in
`flat_npoint_lattice_direct` (the normalisation `c_h = 1` of the paper for the Gaussian profile).
No hypothesis.  No sorry, no axiom, no native_decide.
Written by the author-side AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryFlatNPointLatticeDirect

open MeasureTheory Real Set

noncomputable section
namespace CTG.GaussMoment

open CTG.FlatNPointGauss (gauss)
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- radial integral `∫_0^∞ y^q exp(−y²/2) dy`. -/
lemma radial (q : ℝ) (hq : -1 < q) :
    ∫ y in Ioi (0:ℝ), y ^ q * Real.exp (-(1/2) * y ^ (2:ℝ)) =
      (1/2:ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) :=
  integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num)

lemma nontriv (hn : 1 ≤ n) : Nontrivial E := by
  apply Module.nontrivial_of_finrank_pos (R := ℝ)
  rw [finrank_euclideanSpace_fin]; omega

lemma norm_int (hn : 1 ≤ n) (k : ℕ) :
    ∫ z : E, ‖z‖ ^ k * gauss ‖z‖ =
      (n : ℝ) * (volume.real (Metric.ball (0 : E) 1) *
        ((1/2:ℝ) ^ (-((n:ℝ) - 1 + k + 1) / 2) * (1 / 2) * Real.Gamma (((n:ℝ) - 1 + k + 1) / 2))) := by
  haveI := nontriv (n := n) hn
  have h := integral_fun_norm_addHaar (volume : Measure E) (fun r : ℝ => r ^ k * gauss r)
  rw [h, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  congr 2
  rw [← radial ((n:ℝ) - 1 + k) (by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy' : (0:ℝ) < y := hy
  have e1 : y ^ ((n:ℝ) - 1 + k) = y ^ (n - 1) * y ^ k := by
    rw [Real.rpow_add hy', Real.rpow_natCast, ← Real.rpow_natCast y (n - 1), Nat.cast_sub hn,
      Nat.cast_one]
  have e2 : Real.exp (-(1/2) * y ^ (2:ℝ)) = gauss y := by
    unfold gauss; rw [Real.rpow_two]; congr 1; ring
  show y ^ (n - 1) • (y ^ k * gauss y) = _
  rw [e1, e2, smul_eq_mul]; ring

/-- The second moment of the Gaussian profile per coordinate, normalised by the mass, equals `1`. -/
theorem second_moment (hn : 1 ≤ n) :
    (∫ z : E, ‖z‖ ^ 2 * gauss ‖z‖) / (n * ∫ z : E, gauss ‖z‖) = 1 := by
  have h2 := norm_int (n := n) hn 2
  have h0 := norm_int (n := n) hn 0
  simp only [pow_zero, one_mul] at h0
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  haveI := nontriv (n := n) hn
  have hV : 0 < volume.real (Metric.ball (0 : E) 1) := by
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne'
      (measure_ball_lt_top).ne
  have hG : Real.Gamma (((n:ℝ) - 1 + (2:ℕ) + 1) / 2) = (n:ℝ) / 2 * Real.Gamma ((n:ℝ) / 2) := by
    rw [show ((n:ℝ) - 1 + (2:ℕ) + 1) / 2 = (n:ℝ) / 2 + 1 by push_cast; ring]
    exact Real.Gamma_add_one (by positivity)
  have hG0 : 0 < Real.Gamma ((n:ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hp : (1/2:ℝ) ^ (-((n:ℝ) - 1 + (2:ℕ) + 1) / 2) = (1/2:ℝ) ^ (-((n:ℝ)) / 2) * 2 := by
    rw [show (-((n:ℝ) - 1 + (2:ℕ) + 1) / 2) = -(n:ℝ) / 2 + (-1) by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_neg_one]; norm_num
  have hp0 : (0:ℝ) < (1/2:ℝ) ^ (-((n:ℝ)) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  rw [h2, h0, hG, hp]
  have e0 : ((n:ℝ) - 1 + (0:ℕ) + 1) / 2 = (n:ℝ) / 2 := by push_cast; ring
  have e1 : (-((n:ℝ) - 1 + (0:ℕ) + 1) / 2) = -(n:ℝ) / 2 := by push_cast; ring
  rw [e0, e1]
  field_simp

/-- The constant `gam₂ n` of the fifty-second file equals `1`. -/
theorem gam₂_eq_one (hn : 1 ≤ n) : CTG.FlatNPointLatticeDirect.gam₂ n = 1 := by
  unfold CTG.FlatNPointLatticeDirect.gam₂ CTG.FlatNPointLatticeDirect.gaK₀
  exact second_moment hn

end CTG.GaussMoment
