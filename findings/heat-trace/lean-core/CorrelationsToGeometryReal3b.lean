/-
From Correlations to Geometry -- eleventh Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the seventh file `CorrelationsToGeometryReal3.lean` and is imported by the tenth,
`CorrelationsToGeometryReal4.lean`.  Its content (the namespaces `TimeAppendix` ... `TimeAppendix12`,
`VarianceTwo`, `DegenerateB`, `BiasGeneral` ... `BiasGeneral6`) was moved here UNCHANGED from the end of
the seventh file on 25 November 2026; it was accepted there in full runs.  Reason for the move: the
compiled module of the seventh file could no longer be written on the machine at hand (out of memory).
Check with `cd lean && ./check_real3b.sh` (against the COMPILED seventh file).
No `sorry`, no `axiom`, no `native_decide`.  Every statement is a FORM of a statement of the paper
with the constants and exceptional events of these files, or a deterministic core of a statement of
Appendix H; see the comments at the namespaces.
-/
import CorrelationsToGeometryReal3

open MeasureTheory ProbabilityTheory CTG.Reals Matrix

namespace CTG.Reals2

/-! ## Appendix H ("Time and dynamics"): the deterministic cores that can be stated without
manifolds (A72)

* `cross_quadratic`: for a symmetric bilinear form `B`,
  `B(d-a,d-a) + B(c-b,c-b) - B(c-a,c-a) - B(d-b,d-b) = 2 B(b-a, d-c)`; the identity behind
  Proposition "four nodes in general position" (`prop:lapse-cloud`).
* `line_additive`: for four points on a line the combination `r_ad + r_bc - r_ac - r_bd` of the
  distances vanishes, and it vanishes for distances of the form `r + c_x + c_y`
  (`prop:lapse-stab`: the exponential factors cancel in the cross-ratio).
* `lapse_unique_circle`: on a circle (periodic functions on `ℝ`) the equation
  `u'' Ω = Ω'' u`, that is `Hess u + E u = 0` with `E = -Ω''/Ω`, has only the periodic solutions
  `u = c Ω`.  This is Corollary `cor:ambiguity` (b) for `D = 1`.  It FALSIFIES the first wording of
  that corollary ("for D = 1 the solution space is two-dimensional") for closed manifolds.
* `cross_ratio_trivial`: the cancellation behind the statement that the cross-ratio is
  identically one if the distances are obtained by inverting the flat profile on the same
  correlators (status line of `thm:lapse-est`).  The hypothesis `k_xy = x_xy/(F_x F_y)` is the
  RESULT of such an inversion; no profile, distance or inversion occurs in the statement.

NOT formalised here: anything on curved manifolds of dimension `D ≥ 2` (for the flat torus and
flat space see the later blocks), the statements that are conditional on Theorem `thm:vargap` (b),
and all probabilistic statements of the appendix.  The refutation mentioned above is made a
statement of its own in `periodic_solutions_dependent` and `OmegaW_not_periodic` below. -/
namespace TimeAppendix

theorem cross_quadratic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (a b c d : V) :
    B (d - a) (d - a) + B (c - b) (c - b) - B (c - a) (c - a) - B (d - b) (d - b)
      = 2 * B (b - a) (d - c) := by
  simp only [map_sub, LinearMap.sub_apply]
  linarith [hB a d, hB b c, hB a c, hB b d, hB a b, hB c d]

theorem line_additive (sa sb sc sd : ℝ) :
    (sd - sa) + (sc - sb) - (sc - sa) - (sd - sb) = 0 := by ring

theorem node_shift_additive (rad rbc rac rbd ca cb cc cd : ℝ)
    (h : rad + rbc - rac - rbd = 0) :
    (rad + ca + cd) + (rbc + cb + cc) - (rac + ca + cc) - (rbd + cb + cd) = 0 := by linarith

/-- If `Z_xy = x_xy / k(z_xy)` and the distances are chosen so that `k(z_xy) = x_xy / (F_x F_y)`
(inversion of the flat profile on the same correlators, up to node factors), then the
cross-ratio is one. -/
theorem cross_ratio_trivial (Fa Fb Fc Fd xad xbc xac xbd kad kbc kac kbd : ℝ)
    (hFa : Fa ≠ 0) (hFb : Fb ≠ 0) (hFc : Fc ≠ 0) (hFd : Fd ≠ 0)
    (hxad : xad ≠ 0) (hxbc : xbc ≠ 0) (hxac : xac ≠ 0) (hxbd : xbd ≠ 0)
    (had : kad = xad / (Fa * Fd)) (hbc : kbc = xbc / (Fb * Fc))
    (hac : kac = xac / (Fa * Fc)) (hbd : kbd = xbd / (Fb * Fd)) :
    ((xad / kad) * (xbc / kbc)) / ((xac / kac) * (xbd / kbd)) = 1 := by
  subst had hbc hac hbd
  field_simp

/-- **Corollary `cor:ambiguity` (b) for `D = 1`.**  Periodic lapse `Ω > 0`, periodic `u` with
`u'' Ω = Ω'' u`: then `u` is a constant multiple of `Ω`. -/
theorem lapse_unique_circle (Ω u Ω' Ω'' u' u'' : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hΩ : ∀ x, 0 < Ω x)
    (hΩ1 : ∀ x, HasDerivAt Ω (Ω' x) x) (hΩ2 : ∀ x, HasDerivAt Ω' (Ω'' x) x)
    (hu1 : ∀ x, HasDerivAt u (u' x) x) (hu2 : ∀ x, HasDerivAt u' (u'' x) x)
    (hode : ∀ x, u'' x * Ω x = Ω'' x * u x)
    (hΩper : ∀ x, Ω (x + L) = Ω x) (huper : ∀ x, u (x + L) = u x) :
    ∃ c : ℝ, ∀ x, u x = c * Ω x := by
  -- the Wronskian is constant
  set w : ℝ → ℝ := fun x => Ω x * u' x - u x * Ω' x with hw
  have hwd : ∀ x, HasDerivAt w 0 x := by
    intro x
    have h := ((hΩ1 x).mul (hu2 x)).sub ((hu1 x).mul (hΩ2 x))
    have e : Ω' x * u' x + Ω x * u'' x - (u' x * Ω' x + u x * Ω'' x) = 0 := by
      have := hode x; linarith [mul_comm (u'' x) (Ω x), mul_comm (Ω'' x) (u x),
        mul_comm (Ω' x) (u' x)]
    rw [e] at h; exact h
  have hwc : ∀ x y, w x = w y :=
    is_const_of_deriv_eq_zero (fun x => (hwd x).differentiableAt) (fun x => (hwd x).deriv)
  set c1 : ℝ := w 0 with hc1
  have hwc1 : ∀ x, w x = c1 := fun x => hwc x 0
  -- the quotient v = u / Ω
  set v : ℝ → ℝ := fun x => u x / Ω x with hv
  have hvd : ∀ x, HasDerivAt v (c1 / (Ω x) ^ 2) x := by
    intro x
    have h := (hu1 x).div (hΩ1 x) (ne_of_gt (hΩ x))
    have e : (u' x * Ω x - u x * Ω' x) / (Ω x) ^ 2 = c1 / (Ω x) ^ 2 := by
      rw [← hwc1 x]; simp only [hw]; ring
    rw [e] at h; exact h
  have hvper : v L = v 0 := by
    simp only [hv]
    have h1 := huper 0; have h2 := hΩper 0
    simp only [zero_add] at h1 h2
    rw [h1, h2]
  have hpos : ∀ x, 0 < (Ω x) ^ 2 := fun x => pow_pos (hΩ x) 2
  have hc10 : c1 = 0 := by
    rcases lt_trichotomy c1 0 with hneg | hzero | hposc
    · exfalso
      have hanti : StrictAnti v := by
        apply strictAnti_of_deriv_neg
        intro x; rw [(hvd x).deriv]; exact div_neg_of_neg_of_pos hneg (hpos x)
      have := hanti hL
      rw [hvper] at this; exact lt_irrefl _ this
    · exact hzero
    · exfalso
      have hmono : StrictMono v := by
        apply strictMono_of_deriv_pos
        intro x; rw [(hvd x).deriv]; exact div_pos hposc (hpos x)
      have := hmono hL
      rw [hvper] at this; exact lt_irrefl _ this
  have hvc : ∀ x y, v x = v y := by
    apply is_const_of_deriv_eq_zero (fun x => (hvd x).differentiableAt)
    intro x; rw [(hvd x).deriv, hc10]; simp
  refine ⟨v 0, fun x => ?_⟩
  have := hvc x 0
  simp only [hv] at this ⊢
  have hne := ne_of_gt (hΩ x)
  field_simp at this ⊢
  linarith [this]

/-- The local solution space on the line is larger: with `W' = Ω⁻²`, `Ω W` is a second solution
of `u'' Ω = Ω'' u`.  (So the statement of `lapse_unique_circle` needs periodicity.) -/
theorem second_local_solution (Ω Ω' Ω'' W : ℝ → ℝ) (hΩ : ∀ x, 0 < Ω x)
    (hΩ1 : ∀ x, HasDerivAt Ω (Ω' x) x) (hΩ2 : ∀ x, HasDerivAt Ω' (Ω'' x) x)
    (hW : ∀ x, HasDerivAt W (1 / (Ω x) ^ 2) x) :
    ∀ x, HasDerivAt (fun y => Ω' y * W y + 1 / Ω y) (Ω'' x * W x) x
      ∧ HasDerivAt (fun y => Ω y * W y) (Ω' x * W x + 1 / Ω x) x := by
  intro x
  have hne := ne_of_gt (hΩ x)
  constructor
  · have h := ((hΩ2 x).mul (hW x)).add ((hasDerivAt_const x (1:ℝ)).div (hΩ1 x) hne)
    have e : Ω'' x * W x + Ω' x * (1 / (Ω x) ^ 2) + (0 * Ω x - 1 * Ω' x) / (Ω x) ^ 2
        = Ω'' x * W x := by field_simp; ring
    rw [e] at h; exact h
  · have h := (hΩ1 x).mul (hW x)
    have e : Ω' x * W x + Ω x * (1 / (Ω x) ^ 2) = Ω' x * W x + 1 / Ω x := by field_simp
    rw [e] at h; exact h

end TimeAppendix


/-! ## Appendix H: the arithmetic of the lapse estimator (A73)

* `gap_identity`: for gaps `g₁, g₂, g₃`, `r_ad² + r_bc² - r_ac² - r_bd² = 2 g₁ g₃`
  (the two forms of the estimator in Proposition `prop:lapse-stab` agree; the bracket in the proof
  of Lemma `lem:schwarz` is `-2 g₁ g₃`, for equal gaps `-2 ℓ²`).
* `stab_rho`: `|ρ eˣ - ρ| ≤ 2 ρ λ` for `|x| ≤ λ ≤ 1`, `ρ > 0`.
* `stab_final`: the last step of the proof of Proposition `prop:lapse-stab`:
  `|K̃ - K̂| ≤ 96 ρ λ / ℓ² + 12 ε |K̂|`.

NOT formalised: the Bessel functions `K₀`, `K₁` and the constant `c₀` (not in Mathlib); the
statement is the deterministic arithmetic after the bound `|log(ρ̃/ρ)| ≤ λ`. -/
namespace TimeAppendix

theorem gap_identity (g1 g2 g3 : ℝ) :
    (g1 + g2 + g3) ^ 2 + g2 ^ 2 - (g1 + g2) ^ 2 - (g2 + g3) ^ 2 = 2 * g1 * g3 := by ring

theorem stab_rho (ρ x lam : ℝ) (hρ : 0 < ρ) (hx : |x| ≤ lam) (hl : lam ≤ 1) :
    |ρ * Real.exp x - ρ| ≤ 2 * ρ * lam := by
  have h1 : |Real.exp x - 1| ≤ 2 * |x| := Real.abs_exp_sub_one_le (le_trans hx hl)
  have e : ρ * Real.exp x - ρ = ρ * (Real.exp x - 1) := by ring
  rw [e, abs_mul, abs_of_pos hρ]
  have h2 : ρ * |Real.exp x - 1| ≤ ρ * (2 * |x|) := mul_le_mul_of_nonneg_left h1 hρ.le
  have h3 : ρ * (2 * |x|) ≤ ρ * (2 * lam) :=
    mul_le_mul_of_nonneg_left (by linarith) hρ.le
  linarith

theorem stab_term1 (D g th ell A : ℝ) (hell : 0 < ell) (hg : ell ^ 2 / 4 ≤ g)
    (hth : 1 / 4 ≤ 1 + th) (hA : 0 ≤ A) (hD : |D| ≤ A) :
    |3 * D / (g * (1 + th))| ≤ 48 * A / ell ^ 2 := by
  have hl2 : 0 < ell ^ 2 := by positivity
  have hg0 : 0 < g := by linarith
  have hth0 : 0 < 1 + th := by linarith
  have hden : ell ^ 2 / 16 ≤ g * (1 + th) := by nlinarith
  have hden0 : 0 < g * (1 + th) := mul_pos hg0 hth0
  rw [abs_div, abs_of_pos hden0, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  rw [div_le_div_iff₀ hden0 hl2]
  have h1 : 3 * |D| ≤ 3 * A := by linarith
  have h2 : 3 * |D| * ell ^ 2 ≤ 3 * A * ell ^ 2 := mul_le_mul_of_nonneg_right h1 hl2.le
  have h3 : 3 * A * ell ^ 2 ≤ 48 * A * (g * (1 + th)) := by nlinarith
  linarith

theorem stab_term2 (Kh th eps : ℝ) (heps : 0 ≤ eps) (hth : |th| ≤ 3 * eps)
    (hth' : 1 / 4 ≤ 1 + th) :
    |Kh * (1 / (1 + th) - 1)| ≤ 12 * eps * |Kh| := by
  have hth0 : 0 < 1 + th := by linarith
  have e : 1 / (1 + th) - 1 = -th / (1 + th) := by field_simp; ring
  rw [e, abs_mul, abs_div, abs_neg, abs_of_pos hth0]
  have h1 : |th| / (1 + th) ≤ 12 * eps := by
    rw [div_le_iff₀ hth0]; nlinarith [abs_nonneg th]
  have := mul_le_mul_of_nonneg_left h1 (abs_nonneg Kh)
  linarith

/-- **Last step of Proposition `prop:lapse-stab`.**  With `K̂ = 3(ρ-1)/g`,
`K̃ = 3(ρ̃-1)/(g(1+θ))`, `|ρ̃ - ρ| ≤ 2 ρ λ`, `g ≥ ℓ²/4`, `|θ| ≤ 3ε ≤ 3/4`. -/
theorem stab_final (ρ ρt g th ell lam eps : ℝ) (hell : 0 < ell) (hρ : 0 < ρ) (hlam : 0 ≤ lam)
    (hg : ell ^ 2 / 4 ≤ g) (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 4) (hth : |th| ≤ 3 * eps)
    (hρt : |ρt - ρ| ≤ 2 * ρ * lam) :
    |3 * (ρt - 1) / (g * (1 + th)) - 3 * (ρ - 1) / g|
      ≤ 96 * ρ * lam / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| := by
  have hth' : 1 / 4 ≤ 1 + th := by
    have := abs_le.mp hth; linarith [this.1]
  have hg0 : 0 < g := by nlinarith [sq_nonneg ell, pow_pos hell 2]
  have hth0 : 0 < 1 + th := by linarith
  have e : 3 * (ρt - 1) / (g * (1 + th)) - 3 * (ρ - 1) / g
      = 3 * (ρt - ρ) / (g * (1 + th)) + (3 * (ρ - 1) / g) * (1 / (1 + th) - 1) := by
    field_simp; ring
  rw [e]
  have hA : 0 ≤ 2 * ρ * lam := by positivity
  have t1 := stab_term1 (ρt - ρ) g th ell (2 * ρ * lam) hell hg hth' hA hρt
  have t2 := stab_term2 (3 * (ρ - 1) / g) th eps heps hth hth'
  have e2 : 48 * (2 * ρ * lam) / ell ^ 2 = 96 * ρ * lam / ell ^ 2 := by ring
  calc |3 * (ρt - ρ) / (g * (1 + th)) + (3 * (ρ - 1) / g) * (1 / (1 + th) - 1)|
      ≤ |3 * (ρt - ρ) / (g * (1 + th))| + |(3 * (ρ - 1) / g) * (1 / (1 + th) - 1)| :=
        abs_add_le _ _
    _ ≤ 48 * (2 * ρ * lam) / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| := add_le_add t1 t2
    _ = 96 * ρ * lam / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| := by rw [e2]

end TimeAppendix

/-! ## Appendix H: the shear of Proposition `prop:shear` as a statement about covariance
matrices (A74)

For `n` nodes with configuration variables `φ` and momenta `π`, the substitution `π ↦ π + S φ`
with a real symmetric matrix `S` (a local shear is the case of a diagonal `S`) is symplectic,
`M J Mᵀ = J` for `M = [[1,0],[S,1]]`, and it maps the covariance matrix with blocks
`X = ⟨φφ⟩`, `Y = ⟨φπ⟩_sym`, `P = ⟨ππ⟩` to one with the same `X` and with `Y' = Y + X S`.
So the commutators and `X` are unchanged while `Y` changes by `X S`: the polarisation, and not the
canonical structure, fixes `Y`.  NOT formalised: the identification of the change `X S` with an
isotropic extrinsic curvature (the statement of the proposition for a power-law profile). -/
namespace TimeAppendix

open Matrix

theorem shear_symplectic {n : Type*} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : Sᵀ = S) :
    (fromBlocks (1 : Matrix n n ℝ) (0 : Matrix n n ℝ) S (1 : Matrix n n ℝ)) * (fromBlocks (0 : Matrix n n ℝ) (1 : Matrix n n ℝ) (-1 : Matrix n n ℝ) (0 : Matrix n n ℝ))
        * (fromBlocks (1 : Matrix n n ℝ) (0 : Matrix n n ℝ) S (1 : Matrix n n ℝ))ᵀ
      = fromBlocks (0 : Matrix n n ℝ) (1 : Matrix n n ℝ) (-1 : Matrix n n ℝ) (0 : Matrix n n ℝ) := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hS]

theorem shear_covariance {n : Type*} [Fintype n] [DecidableEq n]
    (S X Y P : Matrix n n ℝ) (hS : Sᵀ = S) :
    (fromBlocks (1 : Matrix n n ℝ) (0 : Matrix n n ℝ) S (1 : Matrix n n ℝ)) * (fromBlocks X Y Yᵀ P)
        * (fromBlocks (1 : Matrix n n ℝ) (0 : Matrix n n ℝ) S (1 : Matrix n n ℝ))ᵀ
      = fromBlocks X (Y + X * S) (Yᵀ + S * X) (P + S * Y + Yᵀ * S + S * X * S) := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [one_mul, zero_mul, add_zero, mul_one, mul_zero, transpose_one,
    transpose_zero, hS]
  congr 1
  · rw [add_comm]
  · rw [add_comm]
  · simp only [Matrix.add_mul]; abel

end TimeAppendix


/-! ## Appendix H: Proposition `prop:tidal` in one dimension and the Möbius family (A75)

* `tidal_1d`: on the line, if `Ω̃'' Ω = Ω'' Ω̃` (equal tidal function `-Ω''/Ω`) and `W' = Ω⁻²`,
  then `Ω̃ = Ω (α + κ W)` with constants `α, κ` (direction (ii) ⇒ (i) of `prop:tidal`, first step).
* `second_length_moebius`: for `κ ≠ 0` the function `W̃ = -1/(κ(α + κ W))` satisfies
  `W̃(y) - W̃(x) = (W(y) - W(x)) / ((α + κ W(x))(α + κ W(y)))`, that is `T̃ = b(x) b(y) T` with
  `b = 1/(α + κ W) = Ω/Ω̃`.
* `moebius_diff`, `cross_ratio_moebius`: the cross-ratio of four values of `W` is invariant under
  `W ↦ (αW + β)/(γW + δ)`: the node-independent data in `D = 1` do not distinguish the lapses of
  the Möbius family (Proposition `prop:crossratio`, Corollary `cor:ambiguity` (a)).

NOT formalised: the geodesic setting in dimension `D ≥ 2`. -/
namespace TimeAppendix

theorem tidal_1d (Ω Ωt Ω' Ω'' Ωt' Ωt'' W : ℝ → ℝ) (hΩ : ∀ x, 0 < Ω x)
    (hΩ1 : ∀ x, HasDerivAt Ω (Ω' x) x) (hΩ2 : ∀ x, HasDerivAt Ω' (Ω'' x) x)
    (ht1 : ∀ x, HasDerivAt Ωt (Ωt' x) x) (ht2 : ∀ x, HasDerivAt Ωt' (Ωt'' x) x)
    (hW : ∀ x, HasDerivAt W (1 / (Ω x) ^ 2) x)
    (hode : ∀ x, Ωt'' x * Ω x = Ω'' x * Ωt x) :
    ∃ α κ : ℝ, ∀ x, Ωt x = Ω x * (α + κ * W x) := by
  set w : ℝ → ℝ := fun x => Ω x * Ωt' x - Ωt x * Ω' x with hw
  have hwd : ∀ x, HasDerivAt w 0 x := by
    intro x
    have h := ((hΩ1 x).mul (ht2 x)).sub ((ht1 x).mul (hΩ2 x))
    have e : Ω' x * Ωt' x + Ω x * Ωt'' x - (Ωt' x * Ω' x + Ωt x * Ω'' x) = 0 := by
      have := hode x; linarith [mul_comm (Ωt'' x) (Ω x), mul_comm (Ω'' x) (Ωt x),
        mul_comm (Ω' x) (Ωt' x)]
    rw [e] at h; exact h
  have hwc : ∀ x y, w x = w y :=
    is_const_of_deriv_eq_zero (fun x => (hwd x).differentiableAt) (fun x => (hwd x).deriv)
  set κ : ℝ := w 0 with hκ
  have hwκ : ∀ x, w x = κ := fun x => hwc x 0
  set v : ℝ → ℝ := fun x => Ωt x / Ω x - κ * W x with hv
  have hvd : ∀ x, HasDerivAt v 0 x := by
    intro x
    have hne := ne_of_gt (hΩ x)
    have h := ((ht1 x).div (hΩ1 x) hne).sub ((hW x).const_mul κ)
    have e : (Ωt' x * Ω x - Ωt x * Ω' x) / (Ω x) ^ 2 - κ * (1 / (Ω x) ^ 2) = 0 := by
      rw [← hwκ x]; simp only [hw]; field_simp; ring
    rw [e] at h; exact h
  have hvc : ∀ x y, v x = v y :=
    is_const_of_deriv_eq_zero (fun x => (hvd x).differentiableAt) (fun x => (hvd x).deriv)
  refine ⟨v 0, κ, fun x => ?_⟩
  have h := hvc x 0
  simp only [hv] at h ⊢
  have hne := ne_of_gt (hΩ x)
  field_simp at h ⊢
  linarith [h]

theorem second_length_moebius (α κ Wx Wy : ℝ) (hκ : κ ≠ 0) (hx : α + κ * Wx ≠ 0)
    (hy : α + κ * Wy ≠ 0) :
    (-1 / (κ * (α + κ * Wy))) - (-1 / (κ * (α + κ * Wx)))
      = (Wy - Wx) / ((α + κ * Wx) * (α + κ * Wy)) := by
  field_simp
  ring

theorem moebius_diff (α β γ δ x y : ℝ) (hx : γ * x + δ ≠ 0) (hy : γ * y + δ ≠ 0) :
    (α * x + β) / (γ * x + δ) - (α * y + β) / (γ * y + δ)
      = (α * δ - β * γ) * (x - y) / ((γ * x + δ) * (γ * y + δ)) := by
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring

/-- The cross-ratio `(c-a)(d-b)/((d-a)(c-b))` is invariant under Möbius maps. -/
theorem cross_ratio_moebius (α β γ δ a b c d : ℝ) (hdet : α * δ - β * γ ≠ 0)
    (ha : γ * a + δ ≠ 0) (hb : γ * b + δ ≠ 0) (hc : γ * c + δ ≠ 0) (hd : γ * d + δ ≠ 0)
    (hda : d - a ≠ 0) (hcb : c - b ≠ 0) :
    (((α * c + β) / (γ * c + δ) - (α * a + β) / (γ * a + δ))
        * ((α * d + β) / (γ * d + δ) - (α * b + β) / (γ * b + δ)))
      / ((((α * d + β) / (γ * d + δ) - (α * a + β) / (γ * a + δ)))
        * ((α * c + β) / (γ * c + δ) - (α * b + β) / (γ * b + δ)))
      = ((c - a) * (d - b)) / ((d - a) * (c - b)) := by
  rw [moebius_diff α β γ δ c a hc ha, moebius_diff α β γ δ d b hd hb,
    moebius_diff α β γ δ d a hd ha, moebius_diff α β γ δ c b hc hb]
  field_simp

end TimeAppendix


/-! ## Appendix H: what the first time derivative cannot separate (A76)

Proposition `prop:D2` says that `∂_t C` gives `∂_t h = 2ΩK - L_β h` and not `K` and the shift
separately.  Abstractly: if `A` (here `K ↦ 2ΩK`) is a linear isomorphism and `B` (here
`β ↦ L_β h`) any linear map, then the map `(K, β) ↦ A K - B β` vanishes on `(A⁻¹ B β, β)` for
every `β`, so it is not injective as soon as the space of shifts is non-zero: the datum does
not determine the PAIR.  That `K` itself is not determined needs a shift with `B β ≠ 0` and is
`D2_K_not_determined` below.  `D2_determined_given_shift` is the positive statement: given `β`,
`K` is determined (in Corollary `cor:shift` the paper goes in the other direction: polarisation
and first derivative together give the shift). -/
namespace TimeAppendix

theorem D2_kernel {V U W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]
    [AddCommGroup W] [Module ℝ W] (A : V ≃ₗ[ℝ] W) (B : U →ₗ[ℝ] W) (β : U) :
    A (A.symm (B β)) - B β = 0 := by simp

theorem D2_not_injective {V U W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U]
    [Module ℝ U] [AddCommGroup W] [Module ℝ W] (A : V ≃ₗ[ℝ] W) (B : U →ₗ[ℝ] W)
    (hU : ∃ β : U, β ≠ 0) :
    ∃ p q : V × U, p ≠ q ∧ A p.1 - B p.2 = A q.1 - B q.2 := by
  obtain ⟨β, hβ⟩ := hU
  refine ⟨(A.symm (B β), β), (0, 0), ?_, ?_⟩
  · intro h
    exact hβ (congrArg Prod.snd h)
  · simp

theorem D2_determined_given_shift {V U W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup U] [Module ℝ U] [AddCommGroup W] [Module ℝ W] (A : V ≃ₗ[ℝ] W)
    (B : U →ₗ[ℝ] W) (β : U) (K K' : V) (h : A K - B β = A K' - B β) : K = K' := by
  have : A K = A K' := by
    have := congrArg (fun w => w + B β) h
    simpa using this
  exact A.injective this

end TimeAppendix


/-! ## Appendix H: Corollary `cor:ambiguity` (b) on the flat torus in every dimension (A77)

For a flat reconstructed metric on the torus `ℝ^d/ℤ^d` the equation `Hess u + E u = 0`,
`E = -Hess Ω/Ω`, contains for every coordinate direction the one-dimensional equation
`∂_i² u · Ω = ∂_i² Ω · u` along the lines parallel to the `i`-th axis, which are closed circles.
By `lapse_unique_circle` the quotient `u/Ω` is constant along each such line, hence constant:
`u = c Ω`.  Only the diagonal entries of the Hessian equation are used, and no integration.
This is part (b) of the corollary for the flat torus, `d ≥ 0`, for functions on `ℝ^d` that are
periodic with period one in every coordinate.  (A general flat torus `ℝ^d/Λ` is the same after a
linear change of coordinates, because the equation holds along every lattice direction; this is
not stated as a theorem.)  NOT formalised: a curved reconstructed metric, and manifolds other
than the torus. -/
namespace TimeAppendix

theorem const_of_coordinatewise {d : ℕ} (v : (Fin d → ℝ) → ℝ)
    (h : ∀ (i : Fin d) (x : Fin d → ℝ) (a : ℝ), v (Function.update x i a) = v x) :
    ∀ x y, v x = v y := by
  have key : ∀ s : Finset (Fin d), ∀ x y : Fin d → ℝ, (∀ i, i ∉ s → x i = y i) → v x = v y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y hxy
      have : x = y := funext fun i => hxy i (by simp)
      rw [this]
    | insert j s hj ih =>
      intro x y hxy
      have h1 : v (Function.update x j (y j)) = v x := h j x (y j)
      rw [← h1]
      apply ih
      intro i hi
      by_cases hij : i = j
      · subst hij; simp
      · rw [Function.update_of_ne hij]
        exact hxy i (by simp [hij, hi])
  intro x y
  exact key Finset.univ x y (fun i hi => absurd (Finset.mem_univ i) hi)

/-- **Corollary `cor:ambiguity` (b) on the flat torus.** -/
theorem lapse_unique_flat_torus {d : ℕ} (Ω u : (Fin d → ℝ) → ℝ) (hΩ : ∀ x, 0 < Ω x)
    (hline : ∀ (i : Fin d) (x : Fin d → ℝ), ∃ Ω' Ω'' u' u'' : ℝ → ℝ,
      (∀ t, HasDerivAt (fun t => Ω (Function.update x i t)) (Ω' t) t) ∧
      (∀ t, HasDerivAt Ω' (Ω'' t) t) ∧
      (∀ t, HasDerivAt (fun t => u (Function.update x i t)) (u' t) t) ∧
      (∀ t, HasDerivAt u' (u'' t) t) ∧
      (∀ t, u'' t * Ω (Function.update x i t) = Ω'' t * u (Function.update x i t)))
    (hΩper : ∀ (i : Fin d) (x : Fin d → ℝ) (t : ℝ),
      Ω (Function.update x i (t + 1)) = Ω (Function.update x i t))
    (huper : ∀ (i : Fin d) (x : Fin d → ℝ) (t : ℝ),
      u (Function.update x i (t + 1)) = u (Function.update x i t)) :
    ∃ c : ℝ, ∀ x, u x = c * Ω x := by
  have hv : ∀ (i : Fin d) (x : Fin d → ℝ) (a : ℝ),
      u (Function.update x i a) / Ω (Function.update x i a) = u x / Ω x := by
    intro i x a
    obtain ⟨Ω', Ω'', u', u'', h1, h2, h3, h4, h5⟩ := hline i x
    obtain ⟨c, hc⟩ := lapse_unique_circle (fun t => Ω (Function.update x i t))
      (fun t => u (Function.update x i t)) Ω' Ω'' u' u'' 1 one_pos
      (fun t => hΩ _) h1 h2 h3 h4 h5 (hΩper i x) (huper i x)
    have ha := hc a
    have hx := hc (x i)
    simp only [Function.update_eq_self] at hx
    simp only at ha
    rw [ha, hx]
    rw [mul_div_assoc, mul_div_assoc, div_self (ne_of_gt (hΩ _)), div_self (ne_of_gt (hΩ _))]
  have hconst := const_of_coordinatewise (fun x => u x / Ω x) hv
  refine ⟨u 0 / Ω 0, fun x => ?_⟩
  have := hconst x 0
  simp only at this
  have hne := ne_of_gt (hΩ x)
  rw [← this]
  field_simp

end TimeAppendix


/-! ## Appendix H: Lemma `lem:schwarz` in the exactly solvable case of constant curvature (A78)

For a lapse with `Ω'' = -k² Ω` (constant `𝒦 = k²`) the differences of `W = ∫Ω⁻²` are, up to
factors that cancel in the cross-ratio, `sin(k(y-x))/k`.  For four equally spaced points with
spacing `ℓ` and `θ = kℓ` the cross-ratio of Lemma `lem:schwarz` is therefore
`ρ₀ = (3ℓ·ℓ/(2ℓ·2ℓ)) · sin(2θ)²/(sin(3θ) sin θ)`.

* `schwarz_const_ratio`: `ρ₀ - 1 = sin²θ/(4cos²θ - 1)` exactly.
* `schwarz_const_bound`: `|sin²θ/(4cos²θ - 1) - θ²/3| ≤ θ⁴` for `|θ| ≤ 1/2`, that is
  `ρ₀ = 1 + 𝒦ℓ²/3 + O(ℓ⁴)` with the coefficient `1/3` of the lemma and an explicit remainder.

This is the lemma for constant `𝒦 > 0` only.  NOT formalised: the lemma for a general smooth
`W` (Taylor expansion with remainder), and the case `𝒦 < 0` (hyperbolic functions). -/
namespace TimeAppendix

theorem sin_three_factor (θ : ℝ) :
    Real.sin (3 * θ) = Real.sin θ * (4 * Real.cos θ ^ 2 - 1) := by
  rw [Real.sin_three_mul, Real.cos_sq']; ring

theorem schwarz_const_ratio (θ : ℝ) (hθ : θ ≠ 0) (hs : Real.sin θ ≠ 0)
    (hc : 4 * Real.cos θ ^ 2 - 1 ≠ 0) :
    (3 * θ * θ) / ((2 * θ) * (2 * θ))
        * (Real.sin (2 * θ) * Real.sin (2 * θ) / (Real.sin (3 * θ) * Real.sin θ)) - 1
      = Real.sin θ ^ 2 / (4 * Real.cos θ ^ 2 - 1) := by
  rw [sin_three_factor, Real.sin_two_mul]
  have h2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ; linarith
  have hA : (3 * θ * θ) / ((2 * θ) * (2 * θ)) = 3 / 4 := by
    field_simp; ring
  have hB : 2 * Real.sin θ * Real.cos θ * (2 * Real.sin θ * Real.cos θ)
      / (Real.sin θ * (4 * Real.cos θ ^ 2 - 1) * Real.sin θ)
      = 4 * Real.cos θ ^ 2 / (4 * Real.cos θ ^ 2 - 1) := by
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hs hc) hs) hc]; ring
  rw [hA, hB, h2, eq_div_iff hc]
  have e : (3 / 4 * (4 * Real.cos θ ^ 2 / (4 * Real.cos θ ^ 2 - 1)) - 1)
      * (4 * Real.cos θ ^ 2 - 1)
      = 3 / 4 * (4 * Real.cos θ ^ 2) - (4 * Real.cos θ ^ 2 - 1) := by
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hc]; ring
  rw [e]; ring

theorem schwarz_const_bound_nonneg (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    |Real.sin θ ^ 2 / (4 * Real.cos θ ^ 2 - 1) - θ ^ 2 / 3| ≤ θ ^ 4 := by
  rcases eq_or_lt_of_le h0 with h | hpos
  · subst h; simp
  have hsle : Real.sin θ ≤ θ := (Real.sin_lt hpos).le
  have hsge : θ - θ ^ 3 / 4 ≤ Real.sin θ := (Real.sin_gt_sub_cube hpos (by linarith)).le
  have hs0 : 0 ≤ Real.sin θ := by
    have : 0 ≤ θ - θ ^ 3 / 4 := by nlinarith [pow_pos hpos 2, pow_pos hpos 3]
    linarith
  set x := Real.sin θ ^ 2 with hx
  have hx_le : x ≤ θ ^ 2 := by
    simp only [hx]; nlinarith
  have hx_ge : θ ^ 2 - θ ^ 4 / 2 ≤ x := by
    have hlow : 0 ≤ θ - θ ^ 3 / 4 := by nlinarith [pow_pos hpos 2, pow_pos hpos 3]
    have h := mul_le_mul hsge hsge hlow hs0
    simp only [hx]
    nlinarith [pow_pos hpos 6, pow_pos hpos 4, h]
  have hx0 : 0 ≤ x := by simp only [hx]; positivity
  have hden : 4 * Real.cos θ ^ 2 - 1 = 3 - 4 * x := by
    simp only [hx]; rw [Real.cos_sq']; ring
  rw [hden]
  have ht2 : θ ^ 2 ≤ 1 / 4 := by nlinarith
  have hdpos : 2 ≤ 3 - 4 * x := by linarith
  have hd0 : 0 < 3 - 4 * x := by linarith
  have ht4 : 0 ≤ θ ^ 4 := by positivity
  rw [abs_le]
  constructor
  · -- lower bound: x/(3-4x) ≥ x/3 ≥ θ²/3 - θ⁴/6
    have h1' : x / 3 ≤ x / (3 - 4 * x) := by
      apply div_le_div_of_nonneg_left hx0 hd0; linarith
    linarith
  · -- upper bound
    have h1' : x / (3 - 4 * x) ≤ θ ^ 2 / (3 - 4 * θ ^ 2) := by
      rw [div_le_div_iff₀ hd0 (by linarith)]
      nlinarith
    have h2' : θ ^ 2 / (3 - 4 * θ ^ 2) - θ ^ 2 / 3 ≤ θ ^ 4 := by
      have hd2 : 0 < 3 - 4 * θ ^ 2 := by linarith
      rw [div_sub_div _ _ (ne_of_gt hd2) (by norm_num : (3:ℝ) ≠ 0), div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg ht4 (by linarith : (0:ℝ) ≤ 3 - 4 * θ ^ 2 - 2)]
    linarith

theorem schwarz_const_bound (θ : ℝ) (hθ : |θ| ≤ 1 / 2) :
    |Real.sin θ ^ 2 / (4 * Real.cos θ ^ 2 - 1) - θ ^ 2 / 3| ≤ θ ^ 4 := by
  rcases le_total 0 θ with h | h
  · exact schwarz_const_bound_nonneg θ h (by rwa [abs_of_nonneg h] at hθ)
  · have h' := schwarz_const_bound_nonneg (-θ) (by linarith) (by rwa [abs_of_nonpos h] at hθ)
    have e4 : (-θ) ^ 4 = θ ^ 4 := by ring
    simp only [Real.sin_neg, Real.cos_neg, neg_sq, e4] at h'
    exact h'

end TimeAppendix

/-! ## Appendix H: analysis steps that are statements about real functions (A79)

Suggested by the second session.

* `landau_interval`: the inequality used in the proof of Proposition `prop:dotL` in a correct form
  on a finite interval: `|G'(t)| ≤ 2 M₀/l + l M₂` if `|G| ≤ M₀` at `t` and `t + l` and
  `|G''| ≤ M₂` between (the text has `l/2` in the last term; the weaker constant is enough).
  `landau_old_form_fails`: the form quoted before, `‖G'‖ ≤ 2 (‖G‖ ‖G''‖)^{1/2}`, fails for
  `G(t) = t`, where `‖G''‖ = 0`.
* `min_not_differentiable`: `τ ↦ min(τ, -τ)` is not differentiable at `0`: a minimum of two
  smooth branches need not be differentiable where the minimiser is not unique.  This is the
  model of the statement, in the status line of Corollary `cor:dotLN-ae`, that for a fixed sample
  the distance can fail to be differentiable at sample-dependent times.
* `kernel_step_one`: Step 1 of the proof of Proposition `prop:dotLN-diff`: if `|h'(s)| ≤ A e^{-s}`
  and `d e^{-x} ≤ d' ≤ d eˣ` with `0 ≤ x ≤ 1`, then `|h(d') - h(d)| ≤ 2 x A d e^{-d/e}`.
* `sigma_inverse_sum`: `1/(3ℓ) + 1/ℓ - 1/(2ℓ) - 1/(2ℓ) = 1/(3ℓ)` (the term of order `(m̄ℓ)⁻³`
  in the remark on the numerical experiment does not cancel in the cross-ratio).

NOT formalised: the positive envelope statement (differentiability of a minimum over a compact
set at a parameter with a unique minimiser), which is the step "Differentiability" of
Corollary `cor:dotLN-ae`. -/
namespace TimeAppendix

theorem mvt_bound (h h' : ℝ → ℝ) (a b M : ℝ) (hab : a < b)
    (hd : ∀ s, HasDerivAt h (h' s) s) (hM : ∀ s, a < s → s < b → |h' s| ≤ M) :
    |h b - h a| ≤ M * (b - a) := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h h' hab
    (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
  have hba : 0 < b - a := sub_pos.mpr hab
  have e : h b - h a = h' c * (b - a) := by
    rw [hslope]; field_simp
  rw [e, abs_mul, abs_of_pos hba]
  exact mul_le_mul_of_nonneg_right (hM c hc.1 hc.2) hba.le

theorem landau_interval (G G' G'' : ℝ → ℝ) (t l M0 M2 : ℝ) (hl : 0 < l)
    (hG : ∀ s, HasDerivAt G (G' s) s) (hG' : ∀ s, HasDerivAt G' (G'' s) s)
    (h0 : |G t| ≤ M0) (h1 : |G (t + l)| ≤ M0)
    (h2 : ∀ s, t < s → s < t + l → |G'' s| ≤ M2) :
    |G' t| ≤ 2 * M0 / l + l * M2 := by
  have hab : t < t + l := by linarith
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G G' hab
    (fun s _ => (hG s).continuousAt.continuousWithinAt) (fun s _ => hG s)
  have hM2 : 0 ≤ M2 := by
    have := h2 c hc.1 hc.2; exact le_trans (abs_nonneg _) this
  have hGc : |G' c| ≤ 2 * M0 / l := by
    rw [hslope]
    have e : t + l - t = l := by ring
    rw [e, abs_div, abs_of_pos hl, div_le_div_iff_of_pos_right hl]
    have := abs_sub (G (t + l)) (G t)
    linarith
  have hdiff : |G' c - G' t| ≤ M2 * (c - t) :=
    mvt_bound G' G'' t c M2 hc.1 hG' (fun s hs1 hs2 => h2 s hs1 (lt_trans hs2 hc.2))
  have hct : c - t ≤ l := by linarith [hc.2]
  have h3 : M2 * (c - t) ≤ l * M2 := by nlinarith
  have h4 : |G' t| ≤ |G' c| + |G' c - G' t| := by
    have := abs_sub_abs_le_abs_sub (G' t) (G' c)
    rw [abs_sub_comm (G' t) (G' c)] at this
    linarith
  linarith

/-- For `G(t) = t` on `[0,1]`: `sup|G| = 1`, `sup|G''| = 0`, `G' = 1`; the bound
`2 (‖G‖ ‖G''‖)^{1/2}` is `0`. -/
theorem landau_old_form_fails : ¬ ((1 : ℝ) ≤ 2 * Real.sqrt (1 * 0)) := by
  simp

theorem min_not_differentiable : ¬ DifferentiableAt ℝ (fun τ : ℝ => min τ (-τ)) 0 := by
  intro h
  have e : (fun τ : ℝ => min τ (-τ)) = fun τ => -|τ| := by
    funext τ
    rcases le_total 0 τ with h0 | h0
    · rw [abs_of_nonneg h0, min_eq_right (by linarith)]
    · rw [abs_of_nonpos h0, min_eq_left (by linarith)]; ring
  rw [e] at h
  have h' : DifferentiableAt ℝ (fun τ : ℝ => |τ|) 0 := by
    have := h.neg
    simpa using this
  exact not_differentiableAt_abs_zero h'

theorem kernel_step_one (h h' : ℝ → ℝ) (A d d' x : ℝ) (hA : 0 ≤ A) (hd0 : 0 < d)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hder : ∀ s, HasDerivAt h (h' s) s) (hbd : ∀ s, 0 ≤ s → |h' s| ≤ A * Real.exp (-s))
    (hlo : d * Real.exp (-x) ≤ d') (hhi : d' ≤ d * Real.exp x) :
    |h d' - h d| ≤ 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) := by
  have hexp_hi : Real.exp x - 1 ≤ 2 * x := by
    have := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
    rw [abs_of_nonneg hx0] at this
    exact le_trans (le_abs_self _) this
  have hexp_lo : 1 - Real.exp (-x) ≤ 2 * x := by
    have := Real.add_one_le_exp (-x); linarith
  have he1 : Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hfloor : d * Real.exp (-1) ≤ d * Real.exp (-x) := mul_le_mul_of_nonneg_left he1 hd0.le
  have hfloor' : d * Real.exp (-1) ≤ d := by
    have : Real.exp (-1) ≤ 1 := by
      have := Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0); simpa using this
    nlinarith
  have hE : 0 ≤ Real.exp (-(d * Real.exp (-1))) := (Real.exp_pos _).le
  -- bound of the derivative on the segment
  have hseg : ∀ s, d * Real.exp (-1) ≤ s → |h' s| ≤ A * Real.exp (-(d * Real.exp (-1))) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (by positivity) hs
    refine le_trans (hbd s hs0) (mul_le_mul_of_nonneg_left ?_ hA)
    exact Real.exp_le_exp.mpr (by linarith)
  have hgap_hi : d' - d ≤ 2 * x * d := by nlinarith
  have hgap_lo : d - d' ≤ 2 * x * d := by nlinarith
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · have := mvt_bound h h' d d' (A * Real.exp (-(d * Real.exp (-1)))) hlt hder
      (fun s hs1 _ => hseg s (by linarith))
    have hM : 0 ≤ A * Real.exp (-(d * Real.exp (-1))) := mul_nonneg hA hE
    have h2 : A * Real.exp (-(d * Real.exp (-1))) * (d' - d)
        ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) :=
      mul_le_mul_of_nonneg_left hgap_hi hM
    calc |h d' - h d| ≤ A * Real.exp (-(d * Real.exp (-1))) * (d' - d) := this
      _ ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) := h2
      _ = 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) := by ring
  · have hnn : 0 ≤ 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx0) hA) hd0.le) hE
    rw [← heq, sub_self, abs_zero]; exact hnn
  · have := mvt_bound h h' d' d (A * Real.exp (-(d * Real.exp (-1)))) hgt hder
      (fun s hs1 _ => hseg s (by linarith))
    have hM : 0 ≤ A * Real.exp (-(d * Real.exp (-1))) := mul_nonneg hA hE
    have h2 : A * Real.exp (-(d * Real.exp (-1))) * (d - d')
        ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) :=
      mul_le_mul_of_nonneg_left hgap_lo hM
    rw [abs_sub_comm]
    calc |h d - h d'| ≤ A * Real.exp (-(d * Real.exp (-1))) * (d - d') := this
      _ ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) := h2
      _ = 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) := by ring

theorem sigma_inverse_sum (l : ℝ) (hl : l ≠ 0) :
    1 / (3 * l) + 1 / l - 1 / (2 * l) - 1 / (2 * l) = 1 / (3 * l) := by
  field_simp; ring

end TimeAppendix


/-! ## Appendix H: the local solution space in flat space, Corollary `cor:ambiguity` (a) (A80)

Suggested by the second session.

* `local_uniqueness_line`: on the line, a solution of `u'' Ω = Ω'' u` with `u(p) = 0` and
  `u'(p) = 0` vanishes identically.
* `local_uniqueness_flat`: in `ℝ^D` with a flat reconstructed metric, a solution of the equation
  along every line through `p` that vanishes at `p` together with all its directional derivatives
  vanishes identically.  Hence a solution is determined by its value and its gradient at one
  point: the solution space has dimension at most `D + 1`.
* `affine_of_second_deriv_zero`: for `E = 0` (constant `Ω`, or any case with `u'' = 0` along
  lines) the solutions are affine along every line, `u(p + v) = u(p) + ∂_v u(p)`; so the bound
  `D + 1` is attained in flat space with `E = 0`, in contrast to the one-dimensional space of
  global solutions on the flat torus (`lapse_unique_flat_torus`).

The statements are for functions on all of `ℝ^D` (or `ℝ`); a convex open subset is not
formalised.  The hypotheses are the one-dimensional equations along lines, as in
`lapse_unique_flat_torus`. -/
namespace TimeAppendix

theorem local_uniqueness_line (Ω u Ω' Ω'' u' u'' : ℝ → ℝ) (p : ℝ) (hΩ : ∀ x, 0 < Ω x)
    (hΩ1 : ∀ x, HasDerivAt Ω (Ω' x) x) (hΩ2 : ∀ x, HasDerivAt Ω' (Ω'' x) x)
    (hu1 : ∀ x, HasDerivAt u (u' x) x) (hu2 : ∀ x, HasDerivAt u' (u'' x) x)
    (hode : ∀ x, u'' x * Ω x = Ω'' x * u x) (h0 : u p = 0) (h1 : u' p = 0) :
    ∀ x, u x = 0 := by
  set w : ℝ → ℝ := fun x => Ω x * u' x - u x * Ω' x with hw
  have hwd : ∀ x, HasDerivAt w 0 x := by
    intro x
    have h := ((hΩ1 x).mul (hu2 x)).sub ((hu1 x).mul (hΩ2 x))
    have e : Ω' x * u' x + Ω x * u'' x - (u' x * Ω' x + u x * Ω'' x) = 0 := by
      have := hode x; linarith [mul_comm (u'' x) (Ω x), mul_comm (Ω'' x) (u x),
        mul_comm (Ω' x) (u' x)]
    rw [e] at h; exact h
  have hwc : ∀ x y, w x = w y :=
    is_const_of_deriv_eq_zero (fun x => (hwd x).differentiableAt) (fun x => (hwd x).deriv)
  have hw0 : ∀ x, w x = 0 := by
    intro x; rw [hwc x p]; simp only [hw]; rw [h0, h1]; ring
  set v : ℝ → ℝ := fun x => u x / Ω x with hv
  have hvd : ∀ x, HasDerivAt v 0 x := by
    intro x
    have h := (hu1 x).div (hΩ1 x) (ne_of_gt (hΩ x))
    have e : (u' x * Ω x - u x * Ω' x) / (Ω x) ^ 2 = 0 := by
      have := hw0 x; simp only [hw] at this
      have e2 : u' x * Ω x - u x * Ω' x = 0 := by linarith [mul_comm (u' x) (Ω x)]
      rw [e2]; simp
    rw [e] at h; exact h
  have hvc : ∀ x y, v x = v y :=
    is_const_of_deriv_eq_zero (fun x => (hvd x).differentiableAt) (fun x => (hvd x).deriv)
  intro x
  have := hvc x p
  simp only [hv] at this
  rw [h0, zero_div] at this
  have hne := ne_of_gt (hΩ x)
  field_simp at this
  simpa using this

theorem local_uniqueness_flat {D : ℕ} (Ω u : (Fin D → ℝ) → ℝ) (p : Fin D → ℝ)
    (hΩ : ∀ x, 0 < Ω x)
    (hline : ∀ v : Fin D → ℝ, ∃ Ω' Ω'' u' u'' : ℝ → ℝ,
      (∀ t, HasDerivAt (fun t : ℝ => Ω (p + t • v)) (Ω' t) t) ∧
      (∀ t, HasDerivAt Ω' (Ω'' t) t) ∧
      (∀ t, HasDerivAt (fun t : ℝ => u (p + t • v)) (u' t) t) ∧
      (∀ t, HasDerivAt u' (u'' t) t) ∧
      (∀ t, u'' t * Ω (p + t • v) = Ω'' t * u (p + t • v)) ∧ u' 0 = 0)
    (h0 : u p = 0) :
    ∀ x, u x = 0 := by
  intro x
  obtain ⟨Ω', Ω'', u', u'', h1, h2, h3, h4, h5, h6⟩ := hline (x - p)
  have hz := local_uniqueness_line (fun t : ℝ => Ω (p + t • (x - p)))
    (fun t : ℝ => u (p + t • (x - p))) Ω' Ω'' u' u'' 0 (fun t => hΩ _) h1 h2 h3 h4 h5
    (by simp [h0]) h6 1
  simpa using hz

theorem affine_of_second_deriv_zero (f f' : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' 0 t) :
    ∀ t, f t = f 0 + t * f' 0 := by
  have hc : ∀ x y, f' x = f' y :=
    is_const_of_deriv_eq_zero (fun x => (hf' x).differentiableAt) (fun x => (hf' x).deriv)
  set g : ℝ → ℝ := fun t => f t - t * f' 0 with hg
  have hgd : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h := (hf t).sub ((hasDerivAt_id t).mul_const (f' 0))
    have e : f' t - 1 * f' 0 = 0 := by rw [hc t 0]; ring
    rw [e] at h; exact h
  have hgc : ∀ x y, g x = g y :=
    is_const_of_deriv_eq_zero (fun x => (hgd x).differentiableAt) (fun x => (hgd x).deriv)
  intro t
  have := hgc t 0
  simp only [hg] at this
  linarith

end TimeAppendix

/-! ## Appendix H: complements after the reading of the statements by the second session (A81)

* `OmegaW_not_periodic`: for a periodic lapse `Ω > 0` and `W' = Ω⁻²`, the second local solution
  `Ω W` is NOT periodic.  `periodic_solutions_dependent`: any two periodic solutions of
  `u'' Ω = Ω'' u` are linearly dependent.  Together with `second_local_solution_ode` this is the
  formal refutation of the first wording of Corollary `cor:ambiguity` for `D = 1` on a circle
  ("the solution space is two-dimensional"): locally there are two independent solutions, and
  only one of them is periodic.
* `second_local_solution_ode`: `Ω W` satisfies the equation, `(ΩW)'' Ω = Ω'' (ΩW)`.
* `second_length_deriv`: for `κ ≠ 0`, `W̃ = -1/(κ(α + κW))` has the derivative `(Ω(α + κW))⁻²`,
  that is `W̃' = Ω̃⁻²` for `Ω̃ = Ω(α + κW)`.
* `stab_from_log`: `stab_rho` and `stab_final` combined: from `ρ̃ = ρ eˣ` with `|x| ≤ λ ≤ 1`.
* `D2_K_not_determined`: if some shift has `B β ≠ 0`, there are two pairs with the same datum
  `A K - B β` and DIFFERENT `K`.  (`D2_not_injective` only says that the pair is not determined.) -/
namespace TimeAppendix

theorem OmegaW_not_periodic (Ω W : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (hΩ : ∀ x, 0 < Ω x)
    (hW : ∀ x, HasDerivAt W (1 / (Ω x) ^ 2) x) (hΩper : ∀ x, Ω (x + L) = Ω x) :
    ¬ (∀ x, Ω (x + L) * W (x + L) = Ω x * W x) := by
  intro hper
  have hmono : StrictMono W := by
    apply strictMono_of_deriv_pos
    intro x; rw [(hW x).deriv]; exact div_pos one_pos (pow_pos (hΩ x) 2)
  have h0 := hper 0
  rw [hΩper 0] at h0
  have hlt : W 0 < W (0 + L) := hmono (by linarith)
  have hne := ne_of_gt (hΩ 0)
  have : W (0 + L) = W 0 := mul_left_cancel₀ hne h0
  linarith

theorem second_local_solution_ode (Ω Ω'' W : ℝ → ℝ) (x : ℝ) :
    (Ω'' x * W x) * Ω x = Ω'' x * (Ω x * W x) := by ring

theorem periodic_solutions_dependent (Ω u1 u2 Ω' Ω'' u1' u1'' u2' u2'' : ℝ → ℝ) (L : ℝ)
    (hL : 0 < L) (hΩ : ∀ x, 0 < Ω x)
    (hΩ1 : ∀ x, HasDerivAt Ω (Ω' x) x) (hΩ2 : ∀ x, HasDerivAt Ω' (Ω'' x) x)
    (h11 : ∀ x, HasDerivAt u1 (u1' x) x) (h12 : ∀ x, HasDerivAt u1' (u1'' x) x)
    (h21 : ∀ x, HasDerivAt u2 (u2' x) x) (h22 : ∀ x, HasDerivAt u2' (u2'' x) x)
    (hode1 : ∀ x, u1'' x * Ω x = Ω'' x * u1 x) (hode2 : ∀ x, u2'' x * Ω x = Ω'' x * u2 x)
    (hΩper : ∀ x, Ω (x + L) = Ω x) (hper1 : ∀ x, u1 (x + L) = u1 x)
    (hper2 : ∀ x, u2 (x + L) = u2 x) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x, a * u1 x + b * u2 x = 0 := by
  obtain ⟨c1, hc1⟩ := lapse_unique_circle Ω u1 Ω' Ω'' u1' u1'' L hL hΩ hΩ1 hΩ2 h11 h12 hode1
    hΩper hper1
  obtain ⟨c2, hc2⟩ := lapse_unique_circle Ω u2 Ω' Ω'' u2' u2'' L hL hΩ hΩ1 hΩ2 h21 h22 hode2
    hΩper hper2
  by_cases h : c1 = 0 ∧ c2 = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, fun x => ?_⟩
    rw [hc1 x, h.1]; ring
  · refine ⟨c2, -c1, ?_, fun x => ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h ⟨by linarith [hcon.2], hcon.1⟩
    · rw [hc1 x, hc2 x]; ring

theorem second_length_deriv (Ω W : ℝ → ℝ) (α κ x : ℝ) (hκ : κ ≠ 0) (hΩ : Ω x ≠ 0)
    (hx : α + κ * W x ≠ 0) (hW : HasDerivAt W (1 / (Ω x) ^ 2) x) :
    HasDerivAt (fun y => -1 / (κ * (α + κ * W y))) (1 / (Ω x * (α + κ * W x)) ^ 2) x := by
  have h1 : HasDerivAt (fun y => κ * (α + κ * W y)) (κ * (κ * (1 / (Ω x) ^ 2))) x := by
    have := ((hW.const_mul κ).const_add α).const_mul κ
    simpa using this
  have hden : κ * (α + κ * W x) ≠ 0 := mul_ne_zero hκ hx
  have h2 := (hasDerivAt_const x (-1 : ℝ)).div h1 hden
  have e : (0 * (κ * (α + κ * W x)) - -1 * (κ * (κ * (1 / (Ω x) ^ 2)))) / (κ * (α + κ * W x)) ^ 2
      = 1 / (Ω x * (α + κ * W x)) ^ 2 := by
    field_simp
    ring
  rw [e] at h2
  exact h2

theorem stab_from_log (ρ x g th ell lam eps : ℝ) (hell : 0 < ell) (hρ : 0 < ρ)
    (hx : |x| ≤ lam) (hl : lam ≤ 1) (hg : ell ^ 2 / 4 ≤ g) (heps : 0 ≤ eps)
    (heps' : eps ≤ 1 / 4) (hth : |th| ≤ 3 * eps) :
    |3 * (ρ * Real.exp x - 1) / (g * (1 + th)) - 3 * (ρ - 1) / g|
      ≤ 96 * ρ * lam / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| :=
  stab_final ρ (ρ * Real.exp x) g th ell lam eps hell hρ (le_trans (abs_nonneg x) hx) hg heps
    heps' hth (stab_rho ρ x lam hρ hx hl)

theorem D2_K_not_determined {V U W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U]
    [Module ℝ U] [AddCommGroup W] [Module ℝ W] (A : V ≃ₗ[ℝ] W) (B : U →ₗ[ℝ] W)
    (hB : ∃ β : U, B β ≠ 0) :
    ∃ p q : V × U, p.1 ≠ q.1 ∧ A p.1 - B p.2 = A q.1 - B q.2 := by
  obtain ⟨β, hβ⟩ := hB
  refine ⟨(A.symm (B β), β), (0, 0), ?_, ?_⟩
  · intro h
    apply hβ
    have : A (A.symm (B β)) = A 0 := congrArg A h
    simpa using this
  · simp

end TimeAppendix

/-! ### Appendix H, continued (A82): the envelope theorem with a unique minimiser, and
the converse direction of `prop:tidal` in one dimension -/
namespace TimeAppendix2

/-- Envelope theorem (the step "Differentiability" of `cor:dotLN-ae`, abstractly):
if `F τ = min_k g τ k` over a compact space, `g` and `∂_τ g = g'` are jointly continuous
and the minimiser at `τ0` is unique (`k0`), then `F` is differentiable at `τ0` with
derivative `g' τ0 k0`.  NOT formalised: that the Riemannian distance is of this form
(minimum of the length functional over a compact family of curves). -/
theorem envelope_min {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g g' : ℝ → K → ℝ) (F : ℝ → ℝ) (kmin : ℝ → K)
    (hg : Continuous (fun p : ℝ × K => g p.1 p.2))
    (hg' : Continuous (fun p : ℝ × K => g' p.1 p.2))
    (hd : ∀ τ k, HasDerivAt (fun s => g s k) (g' τ k) τ)
    (hF : ∀ τ k, F τ ≤ g τ k) (hmin : ∀ τ, F τ = g τ (kmin τ))
    (τ0 : ℝ) (k0 : K) (h0 : F τ0 = g τ0 k0) (huniq : ∀ k, g τ0 k = F τ0 → k = k0) :
    HasDerivAt F (g' τ0 k0) τ0 := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set c := g' τ0 k0 with hc
  have hN : {p : ℝ × K | |g' p.1 p.2 - c| < ε} ∈ nhds (τ0, k0) := by
    have hcont : ContinuousAt (fun p : ℝ × K => |g' p.1 p.2 - c|) (τ0, k0) :=
      ((hg'.sub continuous_const).abs).continuousAt
    have h2 : (fun p : ℝ × K => |g' p.1 p.2 - c|) (τ0, k0) < ε := by simp [hc, hε]
    exact hcont.eventually (gt_mem_nhds h2)
  rw [mem_nhds_prod_iff] at hN
  obtain ⟨u, hu, v, hv, huv⟩ := hN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨U, hUv, hUo, hkU⟩ := mem_nhds_iff.mp hv
  have hCc : IsCompact Uᶜ := hUo.isClosed_compl.isCompact
  set n : Set (ℝ × K) := {p | g p.1 k0 < g p.1 p.2} with hn
  have hno : IsOpen n :=
    isOpen_lt (hg.comp (continuous_fst.prodMk continuous_const)) hg
  have hsub : ({τ0} : Set ℝ) ×ˢ Uᶜ ⊆ n := by
    rintro ⟨t, k⟩ ⟨ht, hk⟩
    have ht' : t = τ0 := ht
    subst ht'
    show g t k0 < g t k
    rcases lt_or_eq_of_le (hF t k) with h | h
    · rw [← h0]; exact h
    · exact absurd (huniq k h.symm) (fun e => hk (e ▸ hkU))
  obtain ⟨V, V', hVo, _, hV, hV', hVV⟩ :=
    generalized_tube_lemma isCompact_singleton hCc hno hsub
  have hVn : V ∈ nhds τ0 := hVo.mem_nhds (hV rfl)
  filter_upwards [Metric.ball_mem_nhds τ0 hδ, hVn] with τ hτb hτV
  have hkτ : kmin τ ∈ U := by
    by_contra hk
    have h1 : g τ k0 < g τ (kmin τ) := hVV (Set.mk_mem_prod hτV (hV' (show kmin τ ∈ Uᶜ from hk)))
    have h2 := hF τ k0
    rw [hmin τ] at h2
    linarith
  have key : ∀ k ∈ U, |(g τ k - c * τ) - (g τ0 k - c * τ0)| ≤ ε * |τ - τ0| := by
    intro k hk
    have h := (convex_ball τ0 δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => g s k - c * s) (f' := fun s => g' s k - c) (C := ε)
      (fun s _ => by
        have h1 := (hd s k).sub ((hasDerivAt_id s).const_mul c)
        simp only [mul_one] at h1
        exact h1.hasDerivWithinAt)
      (fun s hs => by
        rw [Real.norm_eq_abs]
        have hm : (s, k) ∈ {p : ℝ × K | |g' p.1 p.2 - c| < ε} :=
          huv (Set.mk_mem_prod (hball hs) (hUv hk))
        exact le_of_lt hm)
      (Metric.mem_ball_self hδ) hτb
    simpa [Real.norm_eq_abs] using h
  have a := abs_le.mp (key (kmin τ) hkτ)
  have b := abs_le.mp (key k0 hkU)
  have e : (τ - τ0) * c = c * τ - c * τ0 := by ring
  have m1 := hmin τ
  have m2 := hF τ0 (kmin τ)
  have m3 := hF τ k0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- Three-point identity behind `prop:tidal`, direction (i) ⇒ (ii), in one dimension:
if the second lengths satisfy `W̃ y − W̃ x = b x · b y · (W y − W x)` for all `x, y`, with
`b ≠ 0` and `W` not constant, then `1/b` is an affine function of `W`. -/
theorem second_length_affine {X : Type*} (W Wt b : X → ℝ) (hb : ∀ x, b x ≠ 0)
    (hT : ∀ x y, Wt y - Wt x = b x * b y * (W y - W x))
    (x0 z0 : X) (hne : W x0 ≠ W z0) :
    ∃ α κ : ℝ, ∀ y, 1 / b y = α + κ * W y := by
  have hD : W z0 - W x0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  refine ⟨(1 / b x0 * W z0 - 1 / b z0 * W x0) / (W z0 - W x0),
    (1 / b z0 - 1 / b x0) / (W z0 - W x0), ?_⟩
  intro y
  have h1 := hT x0 y
  have h2 := hT y z0
  have h3 := hT x0 z0
  have hx := hb x0; have hy := hb y; have hz := hb z0
  have key : b x0 * b z0 * (W z0 - W x0)
      = b x0 * b y * (W y - W x0) + b y * b z0 * (W z0 - W y) := by linarith
  field_simp
  linear_combination key

/-- Direction (ii) ⇐ of the Möbius family: `Ω̃ = Ω (α + κ W)` with `W' = Ω⁻²` has the
same tidal function, `Ω̃'' Ω = Ω'' Ω̃`. -/
theorem tidal_1d_converse (Ω Ω' Ω'' W : ℝ → ℝ) (α κ : ℝ) (hΩ : ∀ x, Ω x ≠ 0)
    (hΩ1 : ∀ x, HasDerivAt Ω (Ω' x) x) (hΩ2 : ∀ x, HasDerivAt Ω' (Ω'' x) x)
    (hW : ∀ x, HasDerivAt W (1 / (Ω x) ^ 2) x) (x : ℝ) :
    HasDerivAt (fun y => Ω y * (α + κ * W y)) (Ω' x * (α + κ * W x) + κ / Ω x) x ∧
    HasDerivAt (fun y => Ω' y * (α + κ * W y) + κ / Ω y) (Ω'' x * (α + κ * W x)) x ∧
    (Ω'' x * (α + κ * W x)) * Ω x = Ω'' x * (Ω x * (α + κ * W x)) := by
  have hne := hΩ x
  have hg : HasDerivAt (fun y => α + κ * W y) (κ * (1 / (Ω x) ^ 2)) x :=
    ((hW x).const_mul κ).const_add α
  refine ⟨?_, ?_, by ring⟩
  · have h := (hΩ1 x).mul hg
    convert h using 1
    field_simp
  · have h := ((hΩ2 x).mul hg).add (((hΩ1 x).inv hne).const_mul κ)
    convert h using 1
    field_simp
    ring

/-- `prop:tidal`, (i) ⇒ (ii), in one dimension: proportional second lengths with
`b = Ω/Ω̃` force `Ω̃ = Ω (α + κ W)`, hence equal tidal functions. -/
theorem tidal_1d_i_ii (Ω Ωt W Wt : ℝ → ℝ) (hΩ : ∀ x, Ω x ≠ 0) (hΩt : ∀ x, Ωt x ≠ 0)
    (hT : ∀ x y, Wt y - Wt x = (Ω x / Ωt x) * (Ω y / Ωt y) * (W y - W x))
    (x0 z0 : ℝ) (hne : W x0 ≠ W z0) :
    ∃ α κ : ℝ, ∀ y, Ωt y = Ω y * (α + κ * W y) := by
  obtain ⟨α, κ, h⟩ := second_length_affine W Wt (fun x => Ω x / Ωt x)
    (fun x => div_ne_zero (hΩ x) (hΩt x)) hT x0 z0 hne
  refine ⟨α, κ, fun y => ?_⟩
  have hy := h y
  have h1 := hΩ y; have h2 := hΩt y
  rw [← hy]
  field_simp

end TimeAppendix2

/-! ### Appendix H, continued (A83): `lem:schwarz` for a general `W`, as a limit -/
namespace TimeAppendix3

open Filter

/-- Algebraic core of `lem:schwarz` for general `W`: from the third-order Peano expansion
of `W` at `τ` (HYPOTHESIS `hP`) and `W1 ≠ 0`, the cross-ratio `ρ₀` of four equally
spaced points with spacing `ℓ` and centre `τ` satisfies
`(ρ₀ − 1)/ℓ² → S/6`, `S = W3/W1 − (3/2)(W2/W1)²`.  This identifies the coefficient; the
remainder `O(ℓ⁴)` of the lemma is NOT proven here. -/
theorem schwarz_limit_core (W : ℝ → ℝ) (τ W0 W1 W2 W3 : ℝ) (h1 : W1 ≠ 0)
    (hP : Tendsto (fun h => (W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6) / h ^ 3)
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    Tendsto (fun ℓ => ((3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
        (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
         ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1) / ℓ ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds ((W3 / W1 - 3 / 2 * (W2 / W1) ^ 2) / 6)) := by
  set E : ℝ → ℝ := fun h => (W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6) / h ^ 3
    with hE
  have hℓ : Tendsto (fun ℓ : ℝ => ℓ) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hne : ∀ᶠ ℓ : ℝ in nhdsWithin 0 {0}ᶜ, ℓ ≠ 0 := eventually_mem_nhdsWithin
  have hsc : ∀ s : ℝ, s ≠ 0 → Tendsto (fun ℓ => E (s * ℓ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro s hs
    refine hP.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hℓ.const_mul s
      simpa using this
    · filter_upwards [hne] with ℓ hl
      exact mul_ne_zero hs hl
  have e1 := hsc (1 / 2) (by norm_num)
  have e2 := hsc (-(1 / 2)) (by norm_num)
  have e3 := hsc (3 / 2) (by norm_num)
  have e4 := hsc (-(3 / 2)) (by norm_num)
  set qcb : ℝ → ℝ := fun ℓ => W3 / 24 + (E (1 / 2 * ℓ) + E (-(1 / 2) * ℓ)) / 8 with hqcb
  set qda : ℝ → ℝ := fun ℓ => 9 * W3 / 8 + 27 * (E (3 / 2 * ℓ) + E (-(3 / 2) * ℓ)) / 8 with hqda
  set qca : ℝ → ℝ := fun ℓ => 7 * W3 / 12 + (E (1 / 2 * ℓ) + 27 * E (-(3 / 2) * ℓ)) / 8 with hqca
  set qdb : ℝ → ℝ := fun ℓ => 7 * W3 / 12 + (27 * E (3 / 2 * ℓ) + E (-(1 / 2) * ℓ)) / 8 with hqdb
  have tcb : Tendsto qcb (nhdsWithin 0 {0}ᶜ) (nhds (W3 / 24)) := by
    have := ((e1.add e2).div_const 8).const_add (W3 / 24)
    convert this using 2
    all_goals simp
  have tda : Tendsto qda (nhdsWithin 0 {0}ᶜ) (nhds (9 * W3 / 8)) := by
    have := (((e3.add e4).const_mul 27).div_const 8).const_add (9 * W3 / 8)
    convert this using 2
    all_goals simp
  have tca : Tendsto qca (nhdsWithin 0 {0}ᶜ) (nhds (7 * W3 / 12)) := by
    have := ((e1.add (e4.const_mul 27)).div_const 8).const_add (7 * W3 / 12)
    convert this using 2
    all_goals simp
  have tdb : Tendsto qdb (nhdsWithin 0 {0}ᶜ) (nhds (7 * W3 / 12)) := by
    have := (((e3.const_mul 27).add e2).div_const 8).const_add (7 * W3 / 12)
    convert this using 2
    all_goals simp
  -- the four differences
  have val : ∀ ℓ s : ℝ, ℓ ≠ 0 → s ≠ 0 →
      W (τ + s * ℓ) = W0 + W1 * (s * ℓ) + W2 * (s * ℓ) ^ 2 / 2 + W3 * (s * ℓ) ^ 3 / 6
        + (s * ℓ) ^ 3 * E (s * ℓ) := by
    intro ℓ s hl hs
    have : s * ℓ ≠ 0 := mul_ne_zero hs hl
    simp only [hE]
    field_simp
    ring
  have a1 : ∀ ℓ : ℝ, τ + ℓ / 2 = τ + 1 / 2 * ℓ := fun ℓ => by ring
  have a2 : ∀ ℓ : ℝ, τ - ℓ / 2 = τ + -(1 / 2) * ℓ := fun ℓ => by ring
  have a3 : ∀ ℓ : ℝ, τ + 3 * ℓ / 2 = τ + 3 / 2 * ℓ := fun ℓ => by ring
  have a4 : ∀ ℓ : ℝ, τ - 3 * ℓ / 2 = τ + -(3 / 2) * ℓ := fun ℓ => by ring
  set N : ℝ → ℝ := fun ℓ =>
    3 * (-(W2 ^ 2) + (2 * W1 - W2 * ℓ) * qdb ℓ + (2 * W1 + W2 * ℓ) * qca ℓ
        + ℓ ^ 2 * qca ℓ * qdb ℓ)
      - 4 * (W1 * qda ℓ + 3 * W1 * qcb ℓ + ℓ ^ 2 * qda ℓ * qcb ℓ) with hN
  set D : ℝ → ℝ := fun ℓ => 4 * ((3 * W1 + ℓ ^ 2 * qda ℓ) * (W1 + ℓ ^ 2 * qcb ℓ)) with hD
  have hcN : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
      3 * (-(W2 ^ 2) + (2 * W1 - W2 * p.1) * p.2.2.2.2 + (2 * W1 + W2 * p.1) * p.2.2.2.1
        + p.1 ^ 2 * p.2.2.2.1 * p.2.2.2.2)
      - 4 * (W1 * p.2.2.1 + 3 * W1 * p.2.1 + p.1 ^ 2 * p.2.2.1 * p.2.1)) := by fun_prop
  have hcD : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
      4 * ((3 * W1 + p.1 ^ 2 * p.2.2.1) * (W1 + p.1 ^ 2 * p.2.1))) := by fun_prop
  have tup := hℓ.prodMk_nhds (tcb.prodMk_nhds (tda.prodMk_nhds (tca.prodMk_nhds tdb)))
  have tN : Tendsto N (nhdsWithin 0 {0}ᶜ) (nhds (2 * W1 * W3 - 3 * W2 ^ 2)) := by
    have := (hcN.tendsto _).comp tup
    convert this using 2
    simp
    ring
  have tD : Tendsto D (nhdsWithin 0 {0}ᶜ) (nhds (12 * W1 ^ 2)) := by
    have := (hcD.tendsto _).comp tup
    convert this using 2
    simp
    ring
  have hD0 : (12 * W1 ^ 2) ≠ 0 := by positivity
  have hDne : ∀ᶠ ℓ in nhdsWithin 0 {0}ᶜ, D ℓ ≠ 0 := tD.eventually_ne hD0
  have tlim := tN.div tD hD0
  have hval : (2 * W1 * W3 - 3 * W2 ^ 2) / (12 * W1 ^ 2)
      = (W3 / W1 - 3 / 2 * (W2 / W1) ^ 2) / 6 := by
    field_simp
    ring
  rw [← hval]
  refine tlim.congr' ?_
  filter_upwards [hne, hDne] with ℓ hl hd
  have hA : 3 * W1 + ℓ ^ 2 * qda ℓ ≠ 0 := fun h => hd (by simp [hD, h])
  have hB : W1 + ℓ ^ 2 * qcb ℓ ≠ 0 := fun h => hd (by simp [hD, h])
  have dcb : W (τ + ℓ / 2) - W (τ - ℓ / 2) = ℓ * (W1 + ℓ ^ 2 * qcb ℓ) := by
    rw [a1, a2, val ℓ (1 / 2) hl (by norm_num), val ℓ (-(1 / 2)) hl (by norm_num)]
    simp only [hqcb]; ring
  have dda : W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2) = ℓ * (3 * W1 + ℓ ^ 2 * qda ℓ) := by
    rw [a3, a4, val ℓ (3 / 2) hl (by norm_num), val ℓ (-(3 / 2)) hl (by norm_num)]
    simp only [hqda]; ring
  have dca : W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2) = ℓ * (2 * W1 - W2 * ℓ + ℓ ^ 2 * qca ℓ) := by
    rw [a1, a4, val ℓ (1 / 2) hl (by norm_num), val ℓ (-(3 / 2)) hl (by norm_num)]
    simp only [hqca]; ring
  have ddb : W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2) = ℓ * (2 * W1 + W2 * ℓ + ℓ ^ 2 * qdb ℓ) := by
    rw [a3, a2, val ℓ (3 / 2) hl (by norm_num), val ℓ (-(1 / 2)) hl (by norm_num)]
    simp only [hqdb]; ring
  show N ℓ / D ℓ = _
  rw [dcb, dda, dca, ddb]
  simp only [hN, hD]
  field_simp
  ring

/-- The Schwarzian of `W` with `W' = Ω⁻²` is `−2Ω''/Ω` (pointwise algebra: `W1, W2, W3`
are the first three derivatives of `W` expressed through `Ω, Ω', Ω''`). -/
theorem schwarzian_lapse (Ω Ω1 Ω2 : ℝ) (hΩ : Ω ≠ 0) :
    ((-2 * Ω2 / Ω ^ 3 + 6 * Ω1 ^ 2 / Ω ^ 4) / (1 / Ω ^ 2)
      - 3 / 2 * ((-2 * Ω1 / Ω ^ 3) / (1 / Ω ^ 2)) ^ 2) = -2 * Ω2 / Ω := by
  field_simp
  ring

/-- `prop:tidal`, the case `κ = 0`: `Ω̃ = αΩ` has second length `W/α²`. -/
theorem second_length_kappa_zero (Ω W : ℝ → ℝ) (α : ℝ) (hα : α ≠ 0) (x : ℝ) (hΩ : Ω x ≠ 0)
    (hW : HasDerivAt W (1 / (Ω x) ^ 2) x) :
    HasDerivAt (fun y => W y / α ^ 2) (1 / (α * Ω x) ^ 2) x := by
  have h := hW.div_const (α ^ 2)
  convert h using 1
  field_simp

/-- `lem:schwarz` for `W ∈ C³`, as a limit: with `W_k` the derivatives at `τ` and
`W' (τ) ≠ 0`, `(ρ₀ − 1)/ℓ² → S(W)(τ)/6`.  No hypothesis besides smoothness. -/
theorem schwarz_limit (W : ℝ → ℝ) (τ : ℝ) (hW : ContDiff ℝ 3 W)
    (h1 : iteratedDeriv 1 W τ ≠ 0) :
    Tendsto (fun ℓ => ((3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
        (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
         ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1) / ℓ ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((iteratedDeriv 3 W τ / iteratedDeriv 1 W τ
        - 3 / 2 * (iteratedDeriv 2 W τ / iteratedDeriv 1 W τ) ^ 2) / 6)) := by
  refine schwarz_limit_core W τ (W τ) _ _ _ h1 ?_
  have ho := taylor_isLittleO_univ (x₀ := τ) (n := 3) (f := W) (by exact_mod_cast hW)
  have ht := ho.tendsto_div_nhds_zero
  have hsh : Tendsto (fun h : ℝ => τ + h) (nhdsWithin 0 {0}ᶜ) (nhds τ) := by
    have : Tendsto (fun h : ℝ => τ + h) (nhds 0) (nhds (τ + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have := ht.comp hsh
  refine this.congr' ?_
  filter_upwards with h
  simp [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ, Nat.factorial]
  ring

end TimeAppendix3

/-! ### Appendix H, continued (A84): deterministic steps of `prop:dotLN-diff` -/
namespace TimeAppendix4

/-- Step 1, the distance: from `e^{-x} d ≤ d' ≤ e^{x} d` with `0 ≤ x ≤ 1`:
`|d' − d| ≤ 2 x d` and `d/e ≤ d' ≤ e d`. -/
theorem distance_step (d d' x : ℝ) (hd : 0 ≤ d) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hlo : Real.exp (-x) * d ≤ d') (hhi : d' ≤ Real.exp x * d) :
    |d' - d| ≤ 2 * x * d ∧ d / Real.exp 1 ≤ d' ∧ d' ≤ Real.exp 1 * d := by
  have h1 : Real.exp x - 1 ≤ 2 * x := by
    have := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
    rw [abs_of_nonneg hx0] at this
    exact (le_abs_self _).trans this
  have h2 : 1 - x ≤ Real.exp (-x) := by have := Real.add_one_le_exp (-x); linarith
  have h3 : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
  have h4 : Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right h2 hd]
    · nlinarith [mul_le_mul_of_nonneg_right h1 hd]
  · rw [div_eq_mul_inv, ← Real.exp_neg, mul_comm]
    exact (mul_le_mul_of_nonneg_right h4 hd).trans hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_right h3 hd)

/-- Product and quotient rules for the difference quotient `Δ_η`. -/
theorem dq_mul (a a' b b' η : ℝ) :
    (a' * b' - a * b) / η = (a' - a) / η * b' + a * ((b' - b) / η) := by ring

theorem dq_inv (a a' η : ℝ) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    (1 / a' - 1 / a) / η = -((a' - a) / η) / (a * a') := by
  field_simp
  ring

theorem dq_quotient (n n' d d' η : ℝ) (hd : d ≠ 0) (hd' : d' ≠ 0) :
    (n' / d' - n / d) / η = ((n' - n) / η) / d' - n * ((d' - d) / η) / (d * d') := by
  field_simp
  ring

theorem abs_mul_sub_mul_le (A a B b : ℝ) :
    |A * B - a * b| ≤ |A - a| * |B| + |a| * |B - b| := by
  have e : A * B - a * b = (A - a) * B + a * (B - b) := by ring
  rw [e]
  calc |(A - a) * B + a * (B - b)| ≤ |(A - a) * B| + |a * (B - b)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

/-- A relative perturbation `|D − d| ≤ ε d` with `ε ≤ 1/2`, `d ≥ c > 0`. -/
theorem inv_perturb (D d c ε : ℝ) (hc : 0 < c) (hd : c ≤ d) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hD : |D - d| ≤ ε * d) :
    0 < D ∧ |1 / D| ≤ 2 / c ∧ |1 / D - 1 / d| ≤ 2 * ε / c := by
  have hdpos : 0 < d := lt_of_lt_of_le hc hd
  have hDlo : d / 2 ≤ D := by
    have := (abs_le.mp hD).1
    nlinarith
  have hDpos : 0 < D := by linarith
  have h2 : 1 ≤ 2 * D / c := by rw [le_div_iff₀ hc]; linarith
  refine ⟨hDpos, ?_, ?_⟩
  · rw [abs_of_pos (by positivity), div_le_div_iff₀ hDpos hc]
    linarith
  · have e : 1 / D - 1 / d = (d - D) / (D * d) := by field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hDpos hdpos), div_le_iff₀ (mul_pos hDpos hdpos)]
    calc |d - D| = |D - d| := abs_sub_comm _ _
      _ ≤ ε * d := hD
      _ ≤ ε * d * (2 * D / c) := le_mul_of_one_le_right (mul_nonneg hε0 hdpos.le) h2
      _ = 2 * ε / c * (D * d) := by ring

/-- Step 5 of `prop:dotLN-diff`, deterministic: the difference quotient of the quotient
`𝒩/𝒟` for the sample (capital letters; `X = Δ_η 𝒩`, `Y = Δ_η 𝒟`) against the population
(small letters).  With `a` the absolute error of the numerators, `ε` the relative error of
the denominators and `ε'` the error of `Δ_η 𝒟`, the difference is at most
`2a/c + 2Bε/c + 4(a(C+ε') + Bε')/c² + 6BCε/c²`.  The probabilistic inputs (Steps 2–4) are
HYPOTHESES here. -/
theorem quotient_dq_perturb (X x Nn n Y y D d D' d' a B C c ε ε' : ℝ)
    (hc : 0 < c) (hd : c ≤ d) (hd' : c ≤ d') (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hC : 0 ≤ C) (hε' : 0 ≤ ε')
    (hD : |D - d| ≤ ε * d) (hD' : |D' - d'| ≤ ε * d')
    (hX : |X - x| ≤ a) (hN : |Nn - n| ≤ a) (hY : |Y - y| ≤ ε')
    (hx : |x| ≤ B) (hn : |n| ≤ B) (hy : |y| ≤ C) :
    |(X / D' - Nn * Y / (D * D')) - (x / d' - n * y / (d * d'))|
      ≤ 2 * a / c + 2 * B * ε / c + 4 * (a * (C + ε') + B * ε') / c ^ 2
        + 6 * B * C * ε / c ^ 2 := by
  obtain ⟨hDp, hU, hUu⟩ := inv_perturb D d c ε hc hd hε0 hε hD
  obtain ⟨hDp', hU', hUu'⟩ := inv_perturb D' d' c ε hc hd' hε0 hε hD'
  have hdp : 0 < d := lt_of_lt_of_le hc hd
  have hdp' : 0 < d' := lt_of_lt_of_le hc hd'
  have hu : |1 / d| ≤ 1 / c := by
    rw [abs_of_pos (by positivity)]; exact one_div_le_one_div_of_le hc hd
  have hYb : |Y| ≤ C + ε' := by
    have := abs_sub_abs_le_abs_sub Y y; linarith
  -- first term
  have t1 : |X * (1 / D') - x * (1 / d')| ≤ a * (2 / c) + B * (2 * ε / c) :=
    (abs_mul_sub_mul_le _ _ _ _).trans
      (add_le_add (mul_le_mul hX hU' (abs_nonneg _) ha) (mul_le_mul hx hUu' (abs_nonneg _) hB))
  -- N*Y
  have tP : |Nn * Y - n * y| ≤ a * (C + ε') + B * ε' :=
    (abs_mul_sub_mul_le _ _ _ _).trans
      (add_le_add (mul_le_mul hN hYb (abs_nonneg _) ha) (mul_le_mul hn hY (abs_nonneg _) hB))
  have hny : |n * y| ≤ B * C := by rw [abs_mul]; exact mul_le_mul hn hy (abs_nonneg _) hB
  -- U*U'
  have tQ : |1 / D * (1 / D') - 1 / d * (1 / d')| ≤ 2 * ε / c * (2 / c) + 1 / c * (2 * ε / c) :=
    (abs_mul_sub_mul_le _ _ _ _).trans
      (add_le_add (mul_le_mul hUu hU' (abs_nonneg _) (by positivity))
        (mul_le_mul hu hUu' (abs_nonneg _) (by positivity)))
  have hQb : |1 / D * (1 / D')| ≤ 2 / c * (2 / c) := by
    rw [abs_mul]; exact mul_le_mul hU hU' (abs_nonneg _) (by positivity)
  have t2 : |Nn * Y * (1 / D * (1 / D')) - n * y * (1 / d * (1 / d'))|
      ≤ (a * (C + ε') + B * ε') * (2 / c * (2 / c))
        + B * C * (2 * ε / c * (2 / c) + 1 / c * (2 * ε / c)) :=
    (abs_mul_sub_mul_le _ _ _ _).trans
      (add_le_add (mul_le_mul tP hQb (abs_nonneg _) (by positivity))
        (mul_le_mul hny tQ (abs_nonneg _) (by positivity)))
  have e : (X / D' - Nn * Y / (D * D')) - (x / d' - n * y / (d * d'))
      = (X * (1 / D') - x * (1 / d'))
        - (Nn * Y * (1 / D * (1 / D')) - n * y * (1 / d * (1 / d'))) := by
    field_simp
    ring
  rw [e]
  have hfin : a * (2 / c) + B * (2 * ε / c) + ((a * (C + ε') + B * ε') * (2 / c * (2 / c))
        + B * C * (2 * ε / c * (2 / c) + 1 / c * (2 * ε / c)))
      = 2 * a / c + 2 * B * ε / c + 4 * (a * (C + ε') + B * ε') / c ^ 2
        + 6 * B * C * ε / c ^ 2 := by
    field_simp
    ring
  rw [← hfin]
  exact (abs_sub _ _).trans (add_le_add t1 t2)

/-- Step 6, first part: from `|L + Δf| ≤ C ξ²` at both times,
`|Δ_η L + Δ_η(Δf)| ≤ 2 C ξ² / |η|`. -/
theorem step_six (L L' Lap Lap' C ξ η : ℝ)
    (h : |L + Lap| ≤ C * ξ ^ 2) (h' : |L' + Lap'| ≤ C * ξ ^ 2) :
    |(L' - L) / η + (Lap' - Lap) / η| ≤ 2 * C * ξ ^ 2 / |η| := by
  have e : (L' - L) / η + (Lap' - Lap) / η = ((L' + Lap') - (L + Lap)) / η := by ring
  rw [e, abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg η)
  have := abs_sub (L' + Lap') (L + Lap)
  linarith

/-- The Landau inequality in the form `|G'| ≤ 2 (sup|G| · sup|G''|)^{1/2}` is false on a
finite interval: `G(t) = t` on `[0,1]` is a counterexample (as a statement about
functions, not only the numerical instance `landau_old_form_fails`). -/
theorem landau_old_form_counterexample :
    ¬ ∀ (G G' G'' : ℝ → ℝ) (M0 M2 : ℝ),
        (∀ t, HasDerivAt G (G' t) t) → (∀ t, HasDerivAt G' (G'' t) t) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, |G t| ≤ M0) → (∀ t ∈ Set.Icc (0 : ℝ) 1, |G'' t| ≤ M2) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, |G' t| ≤ 2 * Real.sqrt (M0 * M2) := by
  intro h
  have := h (fun t => t) (fun _ => 1) (fun _ => 0) 1 0
    (fun t => hasDerivAt_id t) (fun t => hasDerivAt_const t 1)
    (fun t ht => by rw [abs_of_nonneg ht.1]; exact ht.2) (fun t _ => by simp)
    0 ⟨le_refl _, zero_le_one⟩
  simp at this
  linarith

end TimeAppendix4

/-! ### Appendix H, continued (A85): the Bernstein step of `prop:dotLN-diff` (Steps 2–4)
in abstract form, and two estimates of `lem:dotL-far` -/
namespace TimeAppendix5

/-- The Bernstein step used in Steps 2, 3 and 4 of `prop:dotLN-diff`, abstractly: for
independent points with common law `ν`, an index `i ∉ T` and a jointly measurable `Y` with
`|Y| ≤ b`, conditional mean zero (`∫ Y x z dν(z) = 0`) and conditional second moment `≤ v`,
`P( 2bL + 2√(|T| v L) ≤ |∑_{j∈T} Y(X_i, X_j)| ) ≤ 2 e^{-L}`.
With `L = 3 log N` and a union over `i` this is the "Bernstein and a union bound" of the
proof.  NOT formalised: that the kernels of the proof (on a manifold, at two times) satisfy
the bounds `b`, `v` claimed there. -/
theorem bernstein_conditioned {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (i : ℕ) (T : Finset ℕ) (hiT : i ∉ T)
    (Y : E → E → ℝ) (hY : Measurable fun p : E × E => Y p.1 p.2) {b v L : ℝ}
    (hb : 0 < b) (hv : 0 ≤ v) (hL : 0 < L)
    (hbd : ∀ x z, |Y x z| ≤ b) (hmean : ∀ x, ∫ z, Y x z ∂ν = 0)
    (hvar : ∀ x, ∫ z, Y x z ^ 2 ∂ν ≤ v) :
    μ.real {ω | 2 * b * L + 2 * Real.sqrt (T.card * v * L)
        ≤ |∑ j ∈ T, Y (X i ω) (X j ω)|} ≤ 2 * Real.exp (-L) := by
  have hA : (0 : ℝ) ≤ T.card * v := mul_nonneg (Nat.cast_nonneg _) hv
  obtain ⟨hpos, hexp⟩ := bern_threshold (B := b) (A := T.card * v) (L := L) hb hA hL
  refine cond_pair_bound (μ := μ) X h_indep hX i i T hiT hiT (fun x _ z => Y x z)
    (hY.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    (fun _ _ => 2 * b * L + 2 * Real.sqrt (T.card * v * L)) measurable_const
    (by positivity) ?_
  intro x _
  have hf : Measurable (Y x) := hY.comp (measurable_const.prodMk measurable_id)
  have h := bernstein_two_sided_fn (μ := μ) X h_indep hX (Y x) hf T (b := b) (v := v)
    (ε := 2 * b * L + 2 * Real.sqrt (T.card * v * L)) hb (hbd x)
    (fun j _ => by
      rw [← hmean x, ← hlaw j]
      exact (integral_map (hX j).aemeasurable hf.aestronglyMeasurable).symm)
    (fun j _ => by
      have e : ∫ ω, Y x (X j ω) ^ 2 ∂μ = ∫ z, Y x z ^ 2 ∂ν := by
        rw [← hlaw j]
        exact (integral_map (hX j).aemeasurable
          (hf.pow_const 2).aestronglyMeasurable).symm
      rw [e]; exact hvar x)
    hpos
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2)
  exact this

/-- `lem:dotL-far`, the far part of the kernel: a profile with `|h s| ≤ A e^{-s}`,
multiplied by a cut-off `0 ≤ 1 − χ ≤ 1` that vanishes for `s ≤ ρ/(4ξ)`, is at most
`A e^{-ρ/(4ξ)}` everywhere. -/
theorem far_kernel_bound (h χ : ℝ → ℝ) (A ρ ξ : ℝ) (hA : 0 ≤ A)
    (hh : ∀ s, |h s| ≤ A * Real.exp (-s))
    (hχ : ∀ s, 0 ≤ χ s ∧ χ s ≤ 1) (hχ1 : ∀ s, s ≤ ρ / (4 * ξ) → χ s = 1) (s : ℝ) :
    |h s * (1 - χ s)| ≤ A * Real.exp (-(ρ / (4 * ξ))) := by
  have hE : 0 ≤ A * Real.exp (-(ρ / (4 * ξ))) := mul_nonneg hA (Real.exp_pos _).le
  rcases le_or_gt s (ρ / (4 * ξ)) with hs | hs
  · rw [hχ1 s hs]; simpa using hE
  · rw [abs_mul]
    have h1 : |1 - χ s| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [(hχ s).1, (hχ s).2]
    have h2 : A * Real.exp (-s) ≤ A * Real.exp (-(ρ / (4 * ξ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA
    calc |h s| * |1 - χ s| ≤ |h s| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ A * Real.exp (-(ρ / (4 * ξ))) := by rw [mul_one]; exact (hh s).trans h2

/-- An exponentially small factor beats every power: for `c, ξ > 0`,
`e^{-c/ξ} ≤ n! · (ξ/c)^n`. -/
theorem exp_small_le_pow (c ξ : ℝ) (hc : 0 < c) (hξ : 0 < ξ) (n : ℕ) :
    Real.exp (-(c / ξ)) ≤ n.factorial * (ξ / c) ^ n := by
  have hx : 0 < c / ξ := div_pos hc hξ
  have h := Real.pow_div_factorial_le_exp (c / ξ) hx.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp : 0 < (c / ξ) ^ n := pow_pos hx n
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  have e : ((n.factorial : ℝ) * (ξ / c) ^ n)⁻¹ = (c / ξ) ^ n / n.factorial := by
    rw [mul_inv, ← inv_pow, inv_div]; ring
  rw [e]; exact h

end TimeAppendix5

/-! ### Appendix H, continued (A86): the remainder `O(ℓ⁴)` of `lem:schwarz` -/
namespace TimeAppendix6

open Filter

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
/-- Core: from the fifth-order Peano expansion of `W` at `τ` (HYPOTHESIS `hP`) and
`W1 ≠ 0`, the quotient `(ρ₀ − 1 − S ℓ²/6)/ℓ⁴` has a finite limit as `ℓ → 0`. -/
theorem schwarz_remainder_core (W : ℝ → ℝ) (τ W0 W1 W2 W3 W4 W5 : ℝ) (h1 : W1 ≠ 0)
    (hP : Tendsto (fun h => (W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6
        - W4 * h ^ 4 / 24 - W5 * h ^ 5 / 120) / h ^ 5) (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    ∃ c4 : ℝ, Tendsto (fun ℓ => ((3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
        (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
         ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
        - (W3 / W1 - 3 / 2 * (W2 / W1) ^ 2) / 6 * ℓ ^ 2) / ℓ ^ 4)
      (nhdsWithin 0 {0}ᶜ) (nhds c4) := by
  set S : ℝ := W3 / W1 - 3 / 2 * (W2 / W1) ^ 2 with hS
  set E : ℝ → ℝ := fun h => (W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6
        - W4 * h ^ 4 / 24 - W5 * h ^ 5 / 120) / h ^ 5 with hE
  have hℓ : Tendsto (fun ℓ : ℝ => ℓ) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hne : ∀ᶠ ℓ : ℝ in nhdsWithin 0 {0}ᶜ, ℓ ≠ 0 := eventually_mem_nhdsWithin
  have hsc : ∀ s : ℝ, s ≠ 0 → Tendsto (fun ℓ => E (s * ℓ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro s hs
    refine hP.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hℓ.const_mul s
      simpa using this
    · filter_upwards [hne] with ℓ hl
      exact mul_ne_zero hs hl
  have e1 := hsc (1 / 2) (by norm_num)
  have e2 := hsc (-(1 / 2)) (by norm_num)
  have e3 := hsc (3 / 2) (by norm_num)
  have e4 := hsc (-(3 / 2)) (by norm_num)
  set qcb : ℝ → ℝ := fun ℓ => W5 / 1920 + (E (1 / 2 * ℓ) + E (-(1 / 2) * ℓ)) / 32 with hqcb
  set qda : ℝ → ℝ := fun ℓ =>
    243 * W5 / 1920 + 243 * (E (3 / 2 * ℓ) + E (-(3 / 2) * ℓ)) / 32 with hqda
  set qca : ℝ → ℝ := fun ℓ =>
    244 * W5 / 3840 + (E (1 / 2 * ℓ) + 243 * E (-(3 / 2) * ℓ)) / 32 with hqca
  set qdb : ℝ → ℝ := fun ℓ =>
    244 * W5 / 3840 + (243 * E (3 / 2 * ℓ) + E (-(1 / 2) * ℓ)) / 32 with hqdb
  have tcb : Tendsto qcb (nhdsWithin 0 {0}ᶜ) (nhds (W5 / 1920)) := by
    have := ((e1.add e2).div_const 32).const_add (W5 / 1920)
    convert this using 2
    all_goals simp
  have tda : Tendsto qda (nhdsWithin 0 {0}ᶜ) (nhds (243 * W5 / 1920)) := by
    have := (((e3.add e4).const_mul 243).div_const 32).const_add (243 * W5 / 1920)
    convert this using 2
    all_goals simp
  have tca : Tendsto qca (nhdsWithin 0 {0}ᶜ) (nhds (244 * W5 / 3840)) := by
    have := ((e1.add (e4.const_mul 243)).div_const 32).const_add (244 * W5 / 3840)
    convert this using 2
    all_goals simp
  have tdb : Tendsto qdb (nhdsWithin 0 {0}ᶜ) (nhds (244 * W5 / 3840)) := by
    have := (((e3.const_mul 243).add e2).div_const 32).const_add (244 * W5 / 3840)
    convert this using 2
    all_goals simp
  have val : ∀ ℓ s : ℝ, ℓ ≠ 0 → s ≠ 0 →
      W (τ + s * ℓ) = W0 + W1 * (s * ℓ) + W2 * (s * ℓ) ^ 2 / 2 + W3 * (s * ℓ) ^ 3 / 6
        + W4 * (s * ℓ) ^ 4 / 24 + W5 * (s * ℓ) ^ 5 / 120 + (s * ℓ) ^ 5 * E (s * ℓ) := by
    intro ℓ s hl hs
    have : s * ℓ ≠ 0 := mul_ne_zero hs hl
    simp only [hE]
    field_simp
    ring
  have a1 : ∀ ℓ : ℝ, τ + ℓ / 2 = τ + 1 / 2 * ℓ := fun ℓ => by ring
  have a2 : ∀ ℓ : ℝ, τ - ℓ / 2 = τ + -(1 / 2) * ℓ := fun ℓ => by ring
  have a3 : ∀ ℓ : ℝ, τ + 3 * ℓ / 2 = τ + 3 / 2 * ℓ := fun ℓ => by ring
  have a4 : ∀ ℓ : ℝ, τ - 3 * ℓ / 2 = τ + -(3 / 2) * ℓ := fun ℓ => by ring
  -- p = (ℓ, qcb, qda, qca, qdb)
  set Gf : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun p =>
    3 * W3 ^ 2 / 64 + (3 * W1 + 9 * W3 * p.1 ^ 2 / 8) * p.2.1
      + (W1 + W3 * p.1 ^ 2 / 24) * p.2.2.1 + p.1 ^ 4 * p.2.2.1 * p.2.1 with hGf
  set Nf : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun p =>
    49 * W3 ^ 2 / 48 - 5 * W2 * W4 / 4 - 25 * W4 ^ 2 * p.1 ^ 2 / 192
      + 3 * ((2 * W1 + 7 * W3 * p.1 ^ 2 / 12 + (W2 * p.1 + 5 * W4 * p.1 ^ 3 / 24)) * p.2.2.2.1
           + (2 * W1 + 7 * W3 * p.1 ^ 2 / 12 - (W2 * p.1 + 5 * W4 * p.1 ^ 3 / 24)) * p.2.2.2.2)
      + 3 * p.1 ^ 4 * p.2.2.2.1 * p.2.2.2.2 - 4 * Gf p
      - 5 / 6 * S * W1 * W3 - 2 * S / 3 * p.1 ^ 2 * Gf p with hNf
  set Df : ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun p =>
    4 * ((3 * W1 + 9 * W3 * p.1 ^ 2 / 8 + p.1 ^ 4 * p.2.2.1)
      * (W1 + W3 * p.1 ^ 2 / 24 + p.1 ^ 4 * p.2.1)) with hDf
  have hcG : Continuous Gf := by simp only [hGf]; fun_prop
  have hcN : Continuous Nf := by simp only [hNf]; fun_prop
  have hcD : Continuous Df := by simp only [hDf]; fun_prop
  have tup := hℓ.prodMk_nhds (tcb.prodMk_nhds (tda.prodMk_nhds (tca.prodMk_nhds tdb)))
  set pt : ℝ × ℝ × ℝ × ℝ × ℝ :=
    (0, W5 / 1920, 243 * W5 / 1920, 244 * W5 / 3840, 244 * W5 / 3840) with hpt
  have tN := (hcN.tendsto pt).comp tup
  have tD := (hcD.tendsto pt).comp tup
  have hD0 : Df pt ≠ 0 := by
    simp only [hDf, hpt]
    have : W1 ^ 2 ≠ 0 := pow_ne_zero 2 h1
    intro h
    apply this
    nlinarith
  have hDne := tD.eventually_ne hD0
  refine ⟨Nf pt / Df pt, (tN.div tD hD0).congr' ?_⟩
  filter_upwards [hne, hDne] with ℓ hl hd
  set p : ℝ × ℝ × ℝ × ℝ × ℝ := (ℓ, qcb ℓ, qda ℓ, qca ℓ, qdb ℓ) with hp
  have hd' : Df p ≠ 0 := hd
  have hA : 3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda ℓ ≠ 0 := fun h => hd' (by simp [hDf, hp, h])
  have hB : W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb ℓ ≠ 0 := fun h => hd' (by simp [hDf, hp, h])
  have dcb : W (τ + ℓ / 2) - W (τ - ℓ / 2) = ℓ * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb ℓ) := by
    rw [a1, a2, val ℓ (1 / 2) hl (by norm_num), val ℓ (-(1 / 2)) hl (by norm_num)]
    simp only [hqcb]; ring
  have dda : W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)
      = ℓ * (3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda ℓ) := by
    rw [a3, a4, val ℓ (3 / 2) hl (by norm_num), val ℓ (-(3 / 2)) hl (by norm_num)]
    simp only [hqda]; ring
  have dca : W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)
      = ℓ * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 - (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qca ℓ) := by
    rw [a1, a4, val ℓ (1 / 2) hl (by norm_num), val ℓ (-(3 / 2)) hl (by norm_num)]
    simp only [hqca]; ring
  have ddb : W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2)
      = ℓ * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 + (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qdb ℓ) := by
    rw [a3, a2, val ℓ (3 / 2) hl (by norm_num), val ℓ (-(1 / 2)) hl (by norm_num)]
    simp only [hqdb]; ring
  have hSW : S * W1 ^ 2 = W1 * W3 - 3 / 2 * W2 ^ 2 := by
    simp only [hS]; field_simp
  have gen : ∀ a b c d : ℝ, c ≠ 0 → d ≠ 0 →
      ((3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) * (((ℓ * a) * (ℓ * b)) / ((ℓ * c) * (ℓ * d))) - 1
        - S / 6 * ℓ ^ 2) / ℓ ^ 4
      = (3 * a * b - 4 * (c * d) - 2 * S / 3 * ℓ ^ 2 * (c * d)) / ℓ ^ 4 / (4 * (c * d)) := by
    intro a b c d hc hd
    field_simp
    ring
  have key : 3 * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 - (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qca ℓ)
        * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 + (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qdb ℓ)
      - 4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda ℓ)
          * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb ℓ))
      - 2 * S / 3 * ℓ ^ 2 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda ℓ)
          * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb ℓ)) = ℓ ^ 4 * Nf p := by
    simp only [hNf, hGf, hp]
    linear_combination (-2 * ℓ ^ 2) * hSW
  rw [dcb, dda, dca, ddb, gen _ _ _ _ hA hB, key, mul_div_cancel_left₀ _ (pow_ne_zero 4 hl)]
  rfl

/-- `lem:schwarz` with its remainder, for `W ∈ C⁵` and `W'(τ) ≠ 0`: there are `C` and
`ℓ₀ > 0` with `|ρ₀ − 1 − S(W)(τ) ℓ²/6| ≤ C ℓ⁴` for `0 < |ℓ| < ℓ₀`.  NOT proven: that `C`
and `ℓ₀` depend only on bounds for the derivatives and a lower bound for `W'`. -/
theorem schwarz_remainder (W : ℝ → ℝ) (τ : ℝ) (hW : ContDiff ℝ 5 W)
    (h1 : iteratedDeriv 1 W τ ≠ 0) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ ℓ : ℝ, ℓ ≠ 0 → |ℓ| < ℓ0 →
      |(3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
        (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
         ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
        - (iteratedDeriv 3 W τ / iteratedDeriv 1 W τ
            - 3 / 2 * (iteratedDeriv 2 W τ / iteratedDeriv 1 W τ) ^ 2) / 6 * ℓ ^ 2|
        ≤ C * ℓ ^ 4 := by
  have hP : Tendsto (fun h => (W (τ + h) - W τ - iteratedDeriv 1 W τ * h
        - iteratedDeriv 2 W τ * h ^ 2 / 2 - iteratedDeriv 3 W τ * h ^ 3 / 6
        - iteratedDeriv 4 W τ * h ^ 4 / 24 - iteratedDeriv 5 W τ * h ^ 5 / 120) / h ^ 5)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have ho := taylor_isLittleO_univ (x₀ := τ) (n := 5) (f := W) (by exact_mod_cast hW)
    have ht := ho.tendsto_div_nhds_zero
    have hsh : Tendsto (fun h : ℝ => τ + h) (nhdsWithin 0 {0}ᶜ) (nhds τ) := by
      have : Tendsto (fun h : ℝ => τ + h) (nhds 0) (nhds (τ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine (ht.comp hsh).congr' ?_
    filter_upwards with h
    simp [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ, Nat.factorial]
    ring
  obtain ⟨c4, hc4⟩ := schwarz_remainder_core W τ (W τ) _ _ _ _ _ h1 hP
  obtain ⟨δ, hδ, hδ'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hc4) 1 one_pos
  refine ⟨|c4| + 1, δ, hδ, fun ℓ hl hlt => ?_⟩
  have h := hδ' (x := ℓ) hl (by simpa [Real.dist_eq] using hlt)
  rw [Real.dist_eq] at h
  have hp : 0 < ℓ ^ 4 := by positivity
  set R := (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
        (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
         ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
        - (iteratedDeriv 3 W τ / iteratedDeriv 1 W τ
            - 3 / 2 * (iteratedDeriv 2 W τ / iteratedDeriv 1 W τ) ^ 2) / 6 * ℓ ^ 2 with hR
  have hb : |R / ℓ ^ 4| ≤ |c4| + 1 := by
    have := abs_sub_abs_le_abs_sub (R / ℓ ^ 4) c4
    linarith
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp] at hb
  exact hb

end TimeAppendix6

/-! ### Appendix H, continued (A87): `lem:schwarz` with constants that depend only on bounds -/
namespace TimeAppendix7

noncomputable def schG (W1 W3 ℓ qcb qda : ℝ) : ℝ :=
  3 * W3 ^ 2 / 64 + (3 * W1 + 9 * W3 * ℓ ^ 2 / 8) * qcb + (W1 + W3 * ℓ ^ 2 / 24) * qda
    + ℓ ^ 4 * qda * qcb

noncomputable def schN (W1 W2 W3 W4 S ℓ qcb qda qca qdb : ℝ) : ℝ :=
  49 * W3 ^ 2 / 48 - 5 * W2 * W4 / 4 - 25 * W4 ^ 2 * ℓ ^ 2 / 192
    + 3 * ((2 * W1 + 7 * W3 * ℓ ^ 2 / 12 + (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24)) * qca
         + (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 - (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24)) * qdb)
    + 3 * ℓ ^ 4 * qca * qdb - 4 * schG W1 W3 ℓ qcb qda
    - 5 / 6 * S * W1 * W3 - 2 * S / 3 * ℓ ^ 2 * schG W1 W3 ℓ qcb qda

theorem sch_key (W1 W2 W3 W4 S ℓ qcb qda qca qdb : ℝ)
    (hSW : S * W1 ^ 2 = W1 * W3 - 3 / 2 * W2 ^ 2) :
    3 * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 - (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qca)
        * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 + (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qdb)
      - 4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda) * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb))
      - 2 * S / 3 * ℓ ^ 2 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda)
          * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb))
      = ℓ ^ 4 * schN W1 W2 W3 W4 S ℓ qcb qda qca qdb := by
  unfold schN schG
  linear_combination (-2 * ℓ ^ 2) * hSW

theorem sch_gen (S ℓ a b c d : ℝ) (hl : ℓ ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) * (((ℓ * a) * (ℓ * b)) / ((ℓ * c) * (ℓ * d))) - 1
        - S / 6 * ℓ ^ 2
      = (3 * a * b - 4 * (c * d) - 2 * S / 3 * ℓ ^ 2 * (c * d)) / (4 * (c * d)) := by
  field_simp
  ring

set_option maxHeartbeats 3200000 in
/-- `lem:schwarz` with uniform constants: for `m > 0`, `B, B5 ≥ 0` there are `C` and `ℓ₀ > 0`,
depending only on `m, B, B5`, such that for every function `W` and every `τ` with a fourth-order
Taylor polynomial at `τ` whose coefficients satisfy `m ≤ W1`, `|W_k| ≤ B` and whose remainder is at
most `B5 |h|⁵` for `|h| ≤ 2` (HYPOTHESIS `hT`; it follows from `|W⁽⁵⁾| ≤ 120 B5` by Lagrange, which
is not derived here), `|ρ₀ − 1 − S ℓ²/6| ≤ C ℓ⁴` for `0 < |ℓ| < ℓ₀`. -/
theorem schwarz_uniform (m B B5 : ℝ) (hm : 0 < m) (hB : 0 ≤ B) (hB5 : 0 ≤ B5) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (W : ℝ → ℝ) (τ W0 W1 W2 W3 W4 : ℝ),
      m ≤ W1 → |W1| ≤ B → |W2| ≤ B → |W3| ≤ B → |W4| ≤ B →
      (∀ h, |h| ≤ 2 → |W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6
          - W4 * h ^ 4 / 24| ≤ B5 * |h| ^ 5) →
      ∀ ℓ : ℝ, ℓ ≠ 0 → |ℓ| < ℓ0 →
        |(3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
          - (W3 / W1 - 3 / 2 * (W2 / W1) ^ 2) / 6 * ℓ ^ 2| ≤ C * ℓ ^ 4 := by
  set Sb : ℝ := B / m + 3 / 2 * (B / m) ^ 2 with hSb
  have hSb0 : 0 ≤ Sb := by positivity
  set R : ℝ := B + Sb + 16 * B5 + 1 with hR
  have hR1 : 1 ≤ R := by simp only [hR]; linarith
  -- compactness bound for schN on the box
  set f : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun p =>
    schN p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
      p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2 with hf
  have hfc : Continuous f := by simp only [hf]; unfold schN schG; fun_prop
  obtain ⟨C1, hC1⟩ := (isCompact_Icc
      (a := ((-R, -R, -R, -R, -R, -R, -R, -R, -R, -R) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ))
      (b := (R, R, R, R, R, R, R, R, R, R))).exists_bound_of_continuousOn hfc.continuousOn
  set D : ℝ := 2 * B + 16 * B5 + 1 with hD
  have hD0 : 0 < D := by simp only [hD]; linarith
  set δ : ℝ := m / (2 * D) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨max C1 0 / (4 * m ^ 2), min 1 δ, lt_min one_pos hδ0, ?_⟩
  intro W τ W0 W1 W2 W3 W4 hW1 hb1 hb2 hb3 hb4 hT ℓ hl hlt
  have hl1 : |ℓ| < 1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlδ : |ℓ| < δ := lt_of_lt_of_le hlt (min_le_right _ _)
  have hW1pos : 0 < W1 := lt_of_lt_of_le hm hW1
  set u : ℝ := ℓ ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg _
  have hu1 : u ≤ |ℓ| := by
    have : u = |ℓ| * |ℓ| := by rw [hu, ← sq_abs]; ring
    rw [this]; nlinarith [abs_nonneg ℓ]
  have huδ : D * u ≤ m / 2 := by
    have h1 : u ≤ δ := hu1.trans hlδ.le
    have h2 : D * u ≤ D * δ := mul_le_mul_of_nonneg_left h1 hD0.le
    have h3 : D * δ = m / 2 := by simp only [hδ]; field_simp
    linarith
  have hu4 : ℓ ^ 4 = u * u := by simp only [hu]; ring
  have huu : u * u ≤ u := by nlinarith [hu1, hl1.le, abs_nonneg ℓ]
  -- the four Taylor remainders
  set E : ℝ → ℝ := fun h => (W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6
      - W4 * h ^ 4 / 24) / h ^ 5 with hE
  have hEb : ∀ s : ℝ, s ≠ 0 → |s| ≤ 2 → |E (s * ℓ)| ≤ B5 := by
    intro s hs hs2
    have hne : s * ℓ ≠ 0 := mul_ne_zero hs hl
    have hle : |s * ℓ| ≤ 2 := by
      rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg ℓ, hl1.le]
    have h5 : 0 < |s * ℓ| ^ 5 := pow_pos (abs_pos.mpr hne) 5
    simp only [hE]
    rw [abs_div, abs_pow, div_le_iff₀ h5]
    exact hT _ hle
  have val : ∀ s : ℝ, s ≠ 0 →
      W (τ + s * ℓ) = W0 + W1 * (s * ℓ) + W2 * (s * ℓ) ^ 2 / 2 + W3 * (s * ℓ) ^ 3 / 6
        + W4 * (s * ℓ) ^ 4 / 24 + (s * ℓ) ^ 5 * E (s * ℓ) := by
    intro s hs
    have : s * ℓ ≠ 0 := mul_ne_zero hs hl
    simp only [hE]
    field_simp
    ring
  have a1 : τ + ℓ / 2 = τ + 1 / 2 * ℓ := by ring
  have a2 : τ - ℓ / 2 = τ + -(1 / 2) * ℓ := by ring
  have a3 : τ + 3 * ℓ / 2 = τ + 3 / 2 * ℓ := by ring
  have a4 : τ - 3 * ℓ / 2 = τ + -(3 / 2) * ℓ := by ring
  set e1 := E (1 / 2 * ℓ) with he1
  set e2 := E (-(1 / 2) * ℓ) with he2
  set e3 := E (3 / 2 * ℓ) with he3
  set e4 := E (-(3 / 2) * ℓ) with he4
  have b1 : |e1| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  have b2 : |e2| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  have b3 : |e3| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  have b4 : |e4| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  set qcb : ℝ := (e1 + e2) / 32 with hqcb
  set qda : ℝ := 243 * (e3 + e4) / 32 with hqda
  set qca : ℝ := (e1 + 243 * e4) / 32 with hqca
  set qdb : ℝ := (243 * e3 + e2) / 32 with hqdb
  have q1 : |qcb| ≤ 16 * B5 := by
    simp only [hqcb]; rw [abs_le] at *; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
  have q2 : |qda| ≤ 16 * B5 := by
    simp only [hqda]; rw [abs_le] at *; constructor <;> linarith [b3.1, b3.2, b4.1, b4.2]
  have q3 : |qca| ≤ 16 * B5 := by
    simp only [hqca]; rw [abs_le] at *; constructor <;> linarith [b1.1, b1.2, b4.1, b4.2]
  have q4 : |qdb| ≤ 16 * B5 := by
    simp only [hqdb]; rw [abs_le] at *; constructor <;> linarith [b3.1, b3.2, b2.1, b2.2]
  have dcb : W (τ + ℓ / 2) - W (τ - ℓ / 2) = ℓ * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb) := by
    rw [a1, a2, val (1 / 2) (by norm_num), val (-(1 / 2)) (by norm_num)]
    simp only [hqcb, he1, he2]; ring
  have dda : W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)
      = ℓ * (3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda) := by
    rw [a3, a4, val (3 / 2) (by norm_num), val (-(3 / 2)) (by norm_num)]
    simp only [hqda, he3, he4]; ring
  have dca : W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)
      = ℓ * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 - (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qca) := by
    rw [a1, a4, val (1 / 2) (by norm_num), val (-(3 / 2)) (by norm_num)]
    simp only [hqca, he1, he4]; ring
  have ddb : W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2)
      = ℓ * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 + (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qdb) := by
    rw [a3, a2, val (3 / 2) (by norm_num), val (-(1 / 2)) (by norm_num)]
    simp only [hqdb, he3, he2]; ring
  -- lower bounds for the denominators
  have hc : 2 * m ≤ 3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda := by
    have t1 : -(B * u) ≤ W3 * u := by
      have := (abs_le.mp hb3).1; nlinarith
    have t2 : -(16 * B5 * u) ≤ u * u * qda := by
      have h1 := (abs_le.mp q2).1
      have h2 : -(16 * B5) * (u * u) ≤ qda * (u * u) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hu0 hu0)
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hB5) (sub_nonneg.mpr huu)]
    rw [hu4]
    have e : 9 * W3 * ℓ ^ 2 / 8 = 9 / 8 * (W3 * u) := by simp only [hu]; ring
    rw [e]
    simp only [hD] at huδ
    nlinarith [mul_nonneg hB hu0, mul_nonneg hB5 hu0]
  have hd : m / 2 ≤ W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb := by
    have t1 : -(B * u) ≤ W3 * u := by
      have := (abs_le.mp hb3).1; nlinarith
    have t2 : -(16 * B5 * u) ≤ u * u * qcb := by
      have h1 := (abs_le.mp q1).1
      have h2 : -(16 * B5) * (u * u) ≤ qcb * (u * u) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hu0 hu0)
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hB5) (sub_nonneg.mpr huu)]
    rw [hu4]
    have e : W3 * ℓ ^ 2 / 24 = 1 / 24 * (W3 * u) := by simp only [hu]; ring
    rw [e]
    simp only [hD] at huδ
    nlinarith [mul_nonneg hB hu0, mul_nonneg hB5 hu0]
  have hcpos : 0 < 3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda := by linarith
  have hdpos : 0 < W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb := by linarith
  set S : ℝ := W3 / W1 - 3 / 2 * (W2 / W1) ^ 2 with hS
  have hSW : S * W1 ^ 2 = W1 * W3 - 3 / 2 * W2 ^ 2 := by
    simp only [hS]; field_simp
  have hSabs : |S| ≤ Sb := by
    have r1 : |W3 / W1| ≤ B / m := by
      rw [abs_div, abs_of_pos hW1pos]
      exact div_le_div₀ hB hb3 hm hW1
    have r2 : |W2 / W1| ≤ B / m := by
      rw [abs_div, abs_of_pos hW1pos]
      exact div_le_div₀ hB hb2 hm hW1
    have r3 : (W2 / W1) ^ 2 ≤ (B / m) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) r2 2
    simp only [hS, hSb]
    rw [abs_le]
    have := abs_le.mp r1
    constructor <;> nlinarith [sq_nonneg (W2 / W1)]
  rw [dcb, dda, dca, ddb, sch_gen S ℓ _ _ _ _ hl hcpos.ne' hdpos.ne',
    sch_key W1 W2 W3 W4 S ℓ qcb qda qca qdb hSW]
  -- bound
  have hmem : (W1, W2, W3, W4, S, ℓ, qcb, qda, qca, qdb) ∈
      Set.Icc ((-R, -R, -R, -R, -R, -R, -R, -R, -R, -R) :
        ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) (R, R, R, R, R, R, R, R, R, R) := by
    have g : ∀ x b : ℝ, |x| ≤ b → b ≤ R → -R ≤ x ∧ x ≤ R := fun x b hx hbR => by
      have := abs_le.mp hx; constructor <;> linarith
    have k1 := g W1 B hb1 (by simp only [hR]; linarith)
    have k2 := g W2 B hb2 (by simp only [hR]; linarith)
    have k3 := g W3 B hb3 (by simp only [hR]; linarith)
    have k4 := g W4 B hb4 (by simp only [hR]; linarith)
    have k5 := g S Sb hSabs (by simp only [hR]; linarith)
    have k6 := g ℓ 1 hl1.le hR1
    have k7 := g qcb _ q1 (by simp only [hR]; linarith)
    have k8 := g qda _ q2 (by simp only [hR]; linarith)
    have k9 := g qca _ q3 (by simp only [hR]; linarith)
    have k10 := g qdb _ q4 (by simp only [hR]; linarith)
    exact ⟨⟨k1.1, k2.1, k3.1, k4.1, k5.1, k6.1, k7.1, k8.1, k9.1, k10.1⟩,
      ⟨k1.2, k2.2, k3.2, k4.2, k5.2, k6.2, k7.2, k8.2, k9.2, k10.2⟩⟩
  have hNb : |schN W1 W2 W3 W4 S ℓ qcb qda qca qdb| ≤ max C1 0 := by
    have := hC1 _ hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hden : 4 * m ^ 2 ≤ 4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda)
      * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb)) := by nlinarith
  have hdenpos : 0 < 4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda)
      * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb)) := by positivity
  have h4 : 0 ≤ ℓ ^ 4 := by positivity
  rw [abs_div, abs_of_pos hdenpos, abs_mul, abs_of_nonneg h4, div_le_iff₀ hdenpos]
  have hm2 : 0 < 4 * m ^ 2 := by positivity
  calc ℓ ^ 4 * |schN W1 W2 W3 W4 S ℓ qcb qda qca qdb|
      ≤ ℓ ^ 4 * max C1 0 := mul_le_mul_of_nonneg_left hNb h4
    _ = max C1 0 / (4 * m ^ 2) * ℓ ^ 4 * (4 * m ^ 2) := by field_simp
    _ ≤ max C1 0 / (4 * m ^ 2) * ℓ ^ 4 * (4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda)
          * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb))) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

end TimeAppendix7

/-! ### Appendix H, continued (A88): `schwarz_uniform` on a window -/
namespace TimeAppendix7

set_option maxHeartbeats 3200000 in
/-- `schwarz_uniform` with the Taylor bound required only on a window `|h| ≤ δ0` around `τ`
(any `δ0 > 0`); `C` and `ℓ₀` depend only on `m, B, B5, δ0`. -/
theorem schwarz_uniform_window (m B B5 δ0 : ℝ) (hm : 0 < m) (hB : 0 ≤ B) (hB5 : 0 ≤ B5)
    (hδ0 : 0 < δ0) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (W : ℝ → ℝ) (τ W0 W1 W2 W3 W4 : ℝ),
      m ≤ W1 → |W1| ≤ B → |W2| ≤ B → |W3| ≤ B → |W4| ≤ B →
      (∀ h, |h| ≤ δ0 → |W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6
          - W4 * h ^ 4 / 24| ≤ B5 * |h| ^ 5) →
      ∀ ℓ : ℝ, ℓ ≠ 0 → |ℓ| < ℓ0 →
        |(3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
          - (W3 / W1 - 3 / 2 * (W2 / W1) ^ 2) / 6 * ℓ ^ 2| ≤ C * ℓ ^ 4 := by
  set Sb : ℝ := B / m + 3 / 2 * (B / m) ^ 2 with hSb
  have hSb0 : 0 ≤ Sb := by positivity
  set R : ℝ := B + Sb + 16 * B5 + 1 with hR
  have hR1 : 1 ≤ R := by simp only [hR]; linarith
  -- compactness bound for schN on the box
  set f : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun p =>
    schN p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1
      p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2 with hf
  have hfc : Continuous f := by simp only [hf]; unfold schN schG; fun_prop
  obtain ⟨C1, hC1⟩ := (isCompact_Icc
      (a := ((-R, -R, -R, -R, -R, -R, -R, -R, -R, -R) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ))
      (b := (R, R, R, R, R, R, R, R, R, R))).exists_bound_of_continuousOn hfc.continuousOn
  set D : ℝ := 2 * B + 16 * B5 + 1 with hD
  have hD0 : 0 < D := by simp only [hD]; linarith
  set δ : ℝ := m / (2 * D) with hδ
  have hδ0' : 0 < δ := by positivity
  refine ⟨max C1 0 / (4 * m ^ 2), min (min 1 δ) (δ0 / 2),
    lt_min (lt_min one_pos hδ0') (by positivity), ?_⟩
  intro W τ W0 W1 W2 W3 W4 hW1 hb1 hb2 hb3 hb4 hT ℓ hl hlt
  have hl1 : |ℓ| < 1 := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have hlw : |ℓ| < δ0 / 2 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hlδ : |ℓ| < δ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
  have hW1pos : 0 < W1 := lt_of_lt_of_le hm hW1
  set u : ℝ := ℓ ^ 2 with hu
  have hu0 : 0 ≤ u := sq_nonneg _
  have hu1 : u ≤ |ℓ| := by
    have : u = |ℓ| * |ℓ| := by rw [hu, ← sq_abs]; ring
    rw [this]; nlinarith [abs_nonneg ℓ]
  have huδ : D * u ≤ m / 2 := by
    have h1 : u ≤ δ := hu1.trans hlδ.le
    have h2 : D * u ≤ D * δ := mul_le_mul_of_nonneg_left h1 hD0.le
    have h3 : D * δ = m / 2 := by simp only [hδ]; field_simp
    linarith
  have hu4 : ℓ ^ 4 = u * u := by simp only [hu]; ring
  have huu : u * u ≤ u := by nlinarith [hu1, hl1.le, abs_nonneg ℓ]
  -- the four Taylor remainders
  set E : ℝ → ℝ := fun h => (W (τ + h) - W0 - W1 * h - W2 * h ^ 2 / 2 - W3 * h ^ 3 / 6
      - W4 * h ^ 4 / 24) / h ^ 5 with hE
  have hEb : ∀ s : ℝ, s ≠ 0 → |s| ≤ 2 → |E (s * ℓ)| ≤ B5 := by
    intro s hs hs2
    have hne : s * ℓ ≠ 0 := mul_ne_zero hs hl
    have hle : |s * ℓ| ≤ δ0 := by
      rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg ℓ, hlw.le]
    have h5 : 0 < |s * ℓ| ^ 5 := pow_pos (abs_pos.mpr hne) 5
    simp only [hE]
    rw [abs_div, abs_pow, div_le_iff₀ h5]
    exact hT _ hle
  have val : ∀ s : ℝ, s ≠ 0 →
      W (τ + s * ℓ) = W0 + W1 * (s * ℓ) + W2 * (s * ℓ) ^ 2 / 2 + W3 * (s * ℓ) ^ 3 / 6
        + W4 * (s * ℓ) ^ 4 / 24 + (s * ℓ) ^ 5 * E (s * ℓ) := by
    intro s hs
    have : s * ℓ ≠ 0 := mul_ne_zero hs hl
    simp only [hE]
    field_simp
    ring
  have a1 : τ + ℓ / 2 = τ + 1 / 2 * ℓ := by ring
  have a2 : τ - ℓ / 2 = τ + -(1 / 2) * ℓ := by ring
  have a3 : τ + 3 * ℓ / 2 = τ + 3 / 2 * ℓ := by ring
  have a4 : τ - 3 * ℓ / 2 = τ + -(3 / 2) * ℓ := by ring
  set e1 := E (1 / 2 * ℓ) with he1
  set e2 := E (-(1 / 2) * ℓ) with he2
  set e3 := E (3 / 2 * ℓ) with he3
  set e4 := E (-(3 / 2) * ℓ) with he4
  have b1 : |e1| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  have b2 : |e2| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  have b3 : |e3| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  have b4 : |e4| ≤ B5 := hEb _ (by norm_num) (by norm_num [abs_of_pos])
  set qcb : ℝ := (e1 + e2) / 32 with hqcb
  set qda : ℝ := 243 * (e3 + e4) / 32 with hqda
  set qca : ℝ := (e1 + 243 * e4) / 32 with hqca
  set qdb : ℝ := (243 * e3 + e2) / 32 with hqdb
  have q1 : |qcb| ≤ 16 * B5 := by
    simp only [hqcb]; rw [abs_le] at *; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
  have q2 : |qda| ≤ 16 * B5 := by
    simp only [hqda]; rw [abs_le] at *; constructor <;> linarith [b3.1, b3.2, b4.1, b4.2]
  have q3 : |qca| ≤ 16 * B5 := by
    simp only [hqca]; rw [abs_le] at *; constructor <;> linarith [b1.1, b1.2, b4.1, b4.2]
  have q4 : |qdb| ≤ 16 * B5 := by
    simp only [hqdb]; rw [abs_le] at *; constructor <;> linarith [b3.1, b3.2, b2.1, b2.2]
  have dcb : W (τ + ℓ / 2) - W (τ - ℓ / 2) = ℓ * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb) := by
    rw [a1, a2, val (1 / 2) (by norm_num), val (-(1 / 2)) (by norm_num)]
    simp only [hqcb, he1, he2]; ring
  have dda : W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)
      = ℓ * (3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda) := by
    rw [a3, a4, val (3 / 2) (by norm_num), val (-(3 / 2)) (by norm_num)]
    simp only [hqda, he3, he4]; ring
  have dca : W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)
      = ℓ * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 - (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qca) := by
    rw [a1, a4, val (1 / 2) (by norm_num), val (-(3 / 2)) (by norm_num)]
    simp only [hqca, he1, he4]; ring
  have ddb : W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2)
      = ℓ * (2 * W1 + 7 * W3 * ℓ ^ 2 / 12 + (W2 * ℓ + 5 * W4 * ℓ ^ 3 / 24) + ℓ ^ 4 * qdb) := by
    rw [a3, a2, val (3 / 2) (by norm_num), val (-(1 / 2)) (by norm_num)]
    simp only [hqdb, he3, he2]; ring
  -- lower bounds for the denominators
  have hc : 2 * m ≤ 3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda := by
    have t1 : -(B * u) ≤ W3 * u := by
      have := (abs_le.mp hb3).1; nlinarith
    have t2 : -(16 * B5 * u) ≤ u * u * qda := by
      have h1 := (abs_le.mp q2).1
      have h2 : -(16 * B5) * (u * u) ≤ qda * (u * u) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hu0 hu0)
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hB5) (sub_nonneg.mpr huu)]
    rw [hu4]
    have e : 9 * W3 * ℓ ^ 2 / 8 = 9 / 8 * (W3 * u) := by simp only [hu]; ring
    rw [e]
    simp only [hD] at huδ
    nlinarith [mul_nonneg hB hu0, mul_nonneg hB5 hu0]
  have hd : m / 2 ≤ W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb := by
    have t1 : -(B * u) ≤ W3 * u := by
      have := (abs_le.mp hb3).1; nlinarith
    have t2 : -(16 * B5 * u) ≤ u * u * qcb := by
      have h1 := (abs_le.mp q1).1
      have h2 : -(16 * B5) * (u * u) ≤ qcb * (u * u) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hu0 hu0)
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hB5) (sub_nonneg.mpr huu)]
    rw [hu4]
    have e : W3 * ℓ ^ 2 / 24 = 1 / 24 * (W3 * u) := by simp only [hu]; ring
    rw [e]
    simp only [hD] at huδ
    nlinarith [mul_nonneg hB hu0, mul_nonneg hB5 hu0]
  have hcpos : 0 < 3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda := by linarith
  have hdpos : 0 < W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb := by linarith
  set S : ℝ := W3 / W1 - 3 / 2 * (W2 / W1) ^ 2 with hS
  have hSW : S * W1 ^ 2 = W1 * W3 - 3 / 2 * W2 ^ 2 := by
    simp only [hS]; field_simp
  have hSabs : |S| ≤ Sb := by
    have r1 : |W3 / W1| ≤ B / m := by
      rw [abs_div, abs_of_pos hW1pos]
      exact div_le_div₀ hB hb3 hm hW1
    have r2 : |W2 / W1| ≤ B / m := by
      rw [abs_div, abs_of_pos hW1pos]
      exact div_le_div₀ hB hb2 hm hW1
    have r3 : (W2 / W1) ^ 2 ≤ (B / m) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) r2 2
    simp only [hS, hSb]
    rw [abs_le]
    have := abs_le.mp r1
    constructor <;> nlinarith [sq_nonneg (W2 / W1)]
  rw [dcb, dda, dca, ddb, sch_gen S ℓ _ _ _ _ hl hcpos.ne' hdpos.ne',
    sch_key W1 W2 W3 W4 S ℓ qcb qda qca qdb hSW]
  -- bound
  have hmem : (W1, W2, W3, W4, S, ℓ, qcb, qda, qca, qdb) ∈
      Set.Icc ((-R, -R, -R, -R, -R, -R, -R, -R, -R, -R) :
        ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) (R, R, R, R, R, R, R, R, R, R) := by
    have g : ∀ x b : ℝ, |x| ≤ b → b ≤ R → -R ≤ x ∧ x ≤ R := fun x b hx hbR => by
      have := abs_le.mp hx; constructor <;> linarith
    have k1 := g W1 B hb1 (by simp only [hR]; linarith)
    have k2 := g W2 B hb2 (by simp only [hR]; linarith)
    have k3 := g W3 B hb3 (by simp only [hR]; linarith)
    have k4 := g W4 B hb4 (by simp only [hR]; linarith)
    have k5 := g S Sb hSabs (by simp only [hR]; linarith)
    have k6 := g ℓ 1 hl1.le hR1
    have k7 := g qcb _ q1 (by simp only [hR]; linarith)
    have k8 := g qda _ q2 (by simp only [hR]; linarith)
    have k9 := g qca _ q3 (by simp only [hR]; linarith)
    have k10 := g qdb _ q4 (by simp only [hR]; linarith)
    exact ⟨⟨k1.1, k2.1, k3.1, k4.1, k5.1, k6.1, k7.1, k8.1, k9.1, k10.1⟩,
      ⟨k1.2, k2.2, k3.2, k4.2, k5.2, k6.2, k7.2, k8.2, k9.2, k10.2⟩⟩
  have hNb : |schN W1 W2 W3 W4 S ℓ qcb qda qca qdb| ≤ max C1 0 := by
    have := hC1 _ hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hden : 4 * m ^ 2 ≤ 4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda)
      * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb)) := by
    have hmul := mul_le_mul hc hd (by positivity) hcpos.le
    have e : 4 * m ^ 2 = 4 * (2 * m * (m / 2)) := by ring
    rw [e]; linarith [hmul]
  have hdenpos : 0 < 4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda)
      * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb)) := by positivity
  have h4 : 0 ≤ ℓ ^ 4 := by positivity
  rw [abs_div, abs_of_pos hdenpos, abs_mul, abs_of_nonneg h4, div_le_iff₀ hdenpos]
  have hm2 : 0 < 4 * m ^ 2 := by positivity
  calc ℓ ^ 4 * |schN W1 W2 W3 W4 S ℓ qcb qda qca qdb|
      ≤ ℓ ^ 4 * max C1 0 := mul_le_mul_of_nonneg_left hNb h4
    _ = max C1 0 / (4 * m ^ 2) * ℓ ^ 4 * (4 * m ^ 2) := by field_simp
    _ ≤ max C1 0 / (4 * m ^ 2) * ℓ ^ 4 * (4 * ((3 * W1 + 9 * W3 * ℓ ^ 2 / 8 + ℓ ^ 4 * qda)
          * (W1 + W3 * ℓ ^ 2 / 24 + ℓ ^ 4 * qcb))) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

end TimeAppendix7

/-! ### Appendix H, continued (A89): the Lagrange bound that enters `schwarz_uniform` -/
namespace TimeAppendix8

/-- One integration step on `[0, δ]`: `g 0 = 0` and `|g' t| ≤ c tⁿ` for `0 ≤ t ≤ δ` give
`|g h| ≤ c h^{n+1}/(n+1)` for `0 ≤ h ≤ δ`. -/
theorem pow_step_nonneg (g g' : ℝ → ℝ) (c δ : ℝ) (n : ℕ) (hg0 : g 0 = 0)
    (hd : ∀ t, HasDerivAt g (g' t) t) (hb : ∀ t, 0 ≤ t → t ≤ δ → |g' t| ≤ c * t ^ n)
    (h : ℝ) (h0 : 0 ≤ h) (hδ : h ≤ δ) : |g h| ≤ c * h ^ (n + 1) / (n + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hp : ∀ t, HasDerivAt (fun t => c * t ^ (n + 1) / (n + 1)) (c * t ^ n) t := by
    intro t
    have := ((hasDerivAt_pow (n + 1) t).const_mul c).div_const ((n : ℝ) + 1)
    convert this using 1
    push_cast
    field_simp
  have mono : ∀ (φ φ' : ℝ → ℝ), (∀ t, HasDerivAt φ (φ' t) t) →
      (∀ t, 0 ≤ t → t ≤ δ → 0 ≤ φ' t) → φ 0 ≤ φ h := by
    intro φ φ' hφ hpos
    have hm : MonotoneOn φ (Set.Icc 0 h) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h)
      · exact fun t _ => (hφ t).continuousAt.continuousWithinAt
      · exact fun t _ => (hφ t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hφ t).deriv]
        exact hpos t ht.1.le (ht.2.le.trans hδ)
    exact hm ⟨le_refl _, h0⟩ ⟨h0, le_refl _⟩ h0
  have u1 := mono (fun t => c * t ^ (n + 1) / (n + 1) - g t) (fun t => c * t ^ n - g' t)
    (fun t => (hp t).sub (hd t))
    (fun t t0 tδ => by have := (abs_le.mp (hb t t0 tδ)).2; linarith)
  have u2 := mono (fun t => c * t ^ (n + 1) / (n + 1) + g t) (fun t => c * t ^ n + g' t)
    (fun t => (hp t).add (hd t))
    (fun t t0 tδ => by have := (abs_le.mp (hb t t0 tδ)).1; linarith)
  simp only [hg0, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_div, sub_zero, add_zero] at u1 u2
  rw [abs_le]
  constructor <;> linarith

/-- The same on `[-δ, δ]`. -/
theorem pow_step (g g' : ℝ → ℝ) (c δ : ℝ) (n : ℕ) (hg0 : g 0 = 0)
    (hd : ∀ t, HasDerivAt g (g' t) t) (hb : ∀ t, |t| ≤ δ → |g' t| ≤ c * |t| ^ n)
    (h : ℝ) (hh : |h| ≤ δ) : |g h| ≤ c * |h| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 h with h0 | h0
  · rw [abs_of_nonneg h0] at hh ⊢
    exact pow_step_nonneg g g' c δ n hg0 hd
      (fun t t0 tδ => by have := hb t (by rw [abs_of_nonneg t0]; exact tδ)
                         rwa [abs_of_nonneg t0] at this) h h0 hh
  · rw [abs_of_nonpos h0] at hh ⊢
    have := pow_step_nonneg (fun t => g (-t)) (fun t => -g' (-t)) c δ n (by simpa using hg0)
      (fun t => by
        have := (hd (-t)).scomp t (hasDerivAt_neg t)
        simpa using this)
      (fun t t0 tδ => by
        have := hb (-t) (by rw [abs_neg, abs_of_nonneg t0]; exact tδ)
        rw [abs_neg, abs_of_nonneg t0] at this
        rwa [abs_neg])
      (-h) (by linarith) hh
    simpa using this

/-- Lagrange bound of order five from the derivatives: if `W` has derivatives `D1, …, D5`
everywhere and `|D5| ≤ M` on `[τ − δ, τ + δ]`, then for `|h| ≤ δ`
`|W(τ+h) − W τ − D1 τ h − D2 τ h²/2 − D3 τ h³/6 − D4 τ h⁴/24| ≤ (M/120) |h|⁵`.
This is the hypothesis `hT` of `schwarz_uniform_window` with `B5 = M/120`. -/
theorem taylor_bound_of_fifth (W D1 D2 D3 D4 D5 : ℝ → ℝ) (τ δ M : ℝ)
    (h0 : ∀ t, HasDerivAt W (D1 t) t) (h1 : ∀ t, HasDerivAt D1 (D2 t) t)
    (h2 : ∀ t, HasDerivAt D2 (D3 t) t) (h3 : ∀ t, HasDerivAt D3 (D4 t) t)
    (h4 : ∀ t, HasDerivAt D4 (D5 t) t) (hM : ∀ t, |t| ≤ δ → |D5 (τ + t)| ≤ M)
    (h : ℝ) (hh : |h| ≤ δ) :
    |W (τ + h) - W τ - D1 τ * h - D2 τ * h ^ 2 / 2 - D3 τ * h ^ 3 / 6 - D4 τ * h ^ 4 / 24|
      ≤ M / 120 * |h| ^ 5 := by
  have sh : ∀ (F F' : ℝ → ℝ), (∀ t, HasDerivAt F (F' t) t) →
      ∀ t, HasDerivAt (fun s => F (τ + s)) (F' (τ + t)) t := by
    intro F F' hF t
    have := (hF (τ + t)).scomp t ((hasDerivAt_id t).const_add τ)
    simpa using this
  -- f4, f3, f2, f1, f0
  set f4 : ℝ → ℝ := fun s => D4 (τ + s) - D4 τ with hf4
  set f3 : ℝ → ℝ := fun s => D3 (τ + s) - D3 τ - D4 τ * s with hf3
  set f2 : ℝ → ℝ := fun s => D2 (τ + s) - D2 τ - D3 τ * s - D4 τ * s ^ 2 / 2 with hf2
  set f1 : ℝ → ℝ := fun s => D1 (τ + s) - D1 τ - D2 τ * s - D3 τ * s ^ 2 / 2
    - D4 τ * s ^ 3 / 6 with hf1
  set f0 : ℝ → ℝ := fun s => W (τ + s) - W τ - D1 τ * s - D2 τ * s ^ 2 / 2 - D3 τ * s ^ 3 / 6
    - D4 τ * s ^ 4 / 24 with hf0
  have d4 : ∀ t, HasDerivAt f4 (D5 (τ + t)) t := fun t => by
    have := (sh D4 D5 h4 t).sub_const (D4 τ); simpa [hf4] using this
  have d3 : ∀ t, HasDerivAt f3 (f4 t) t := fun t => by
    have := ((sh D3 D4 h3 t).sub_const (D3 τ)).sub ((hasDerivAt_id t).const_mul (D4 τ))
    simpa [hf3, hf4] using this
  have d2 : ∀ t, HasDerivAt f2 (f3 t) t := fun t => by
    have := (((sh D2 D3 h2 t).sub_const (D2 τ)).sub ((hasDerivAt_id t).const_mul (D3 τ))).sub
      (((hasDerivAt_pow 2 t).const_mul (D4 τ)).div_const 2)
    convert this using 1
    simp only [hf3]; push_cast; ring
  have d1 : ∀ t, HasDerivAt f1 (f2 t) t := fun t => by
    have := ((((sh D1 D2 h1 t).sub_const (D1 τ)).sub ((hasDerivAt_id t).const_mul (D2 τ))).sub
      (((hasDerivAt_pow 2 t).const_mul (D3 τ)).div_const 2)).sub
      (((hasDerivAt_pow 3 t).const_mul (D4 τ)).div_const 6)
    convert this using 1
    simp only [hf2]; push_cast; ring
  have d0 : ∀ t, HasDerivAt f0 (f1 t) t := fun t => by
    have := (((((sh W D1 h0 t).sub_const (W τ)).sub ((hasDerivAt_id t).const_mul (D1 τ))).sub
      (((hasDerivAt_pow 2 t).const_mul (D2 τ)).div_const 2)).sub
      (((hasDerivAt_pow 3 t).const_mul (D3 τ)).div_const 6)).sub
      (((hasDerivAt_pow 4 t).const_mul (D4 τ)).div_const 24)
    convert this using 1
    simp only [hf1]; push_cast; ring
  have b4 : ∀ t, |t| ≤ δ → |f4 t| ≤ M * |t| := fun t ht => by
    have := pow_step f4 (fun s => D5 (τ + s)) M δ 0 (by simp [hf4]) d4
      (fun s hs => by simpa using hM s hs) t ht
    simpa using this
  have b3 : ∀ t, |t| ≤ δ → |f3 t| ≤ M / 2 * |t| ^ 2 := fun t ht => by
    have := pow_step f3 f4 M δ 1 (by simp [hf3]) d3 (fun s hs => by simpa using b4 s hs) t ht
    calc |f3 t| ≤ M * |t| ^ (1 + 1) / ((1 : ℕ) + 1) := this
      _ = M / 2 * |t| ^ 2 := by push_cast; ring
  have b2 : ∀ t, |t| ≤ δ → |f2 t| ≤ M / 6 * |t| ^ 3 := fun t ht => by
    have := pow_step f2 f3 (M / 2) δ 2 (by simp [hf2]) d2 b3 t ht
    calc |f2 t| ≤ M / 2 * |t| ^ (2 + 1) / ((2 : ℕ) + 1) := this
      _ = M / 6 * |t| ^ 3 := by push_cast; ring
  have b1 : ∀ t, |t| ≤ δ → |f1 t| ≤ M / 24 * |t| ^ 4 := fun t ht => by
    have := pow_step f1 f2 (M / 6) δ 3 (by simp [hf1]) d1 b2 t ht
    calc |f1 t| ≤ M / 6 * |t| ^ (3 + 1) / ((3 : ℕ) + 1) := this
      _ = M / 24 * |t| ^ 4 := by push_cast; ring
  have := pow_step f0 f1 (M / 24) δ 4 (by simp [hf0]) d0 b1 h hh
  calc |f0 h| ≤ M / 24 * |h| ^ (4 + 1) / ((4 : ℕ) + 1) := this
    _ = M / 120 * |h| ^ 5 := by push_cast; ring

/-- `lem:schwarz` with uniform constants, in terms of derivatives: for `m > 0`, `B, M ≥ 0`, `δ0 > 0`
there are `C` and `ℓ₀ > 0`, depending only on these numbers, such that for every `W` with derivatives
`D1, …, D5` and every `τ` with `D1 τ ≥ m`, `|D_k τ| ≤ B` (`k = 1..4`) and `|D5| ≤ M` on
`[τ − δ0, τ + δ0]`: `|ρ₀ − 1 − S(W)(τ) ℓ²/6| ≤ C ℓ⁴` for `0 < |ℓ| < ℓ₀`.  No hypothesis besides the
derivatives and their bounds. -/
theorem schwarz_uniform_deriv (m B M δ0 : ℝ) (hm : 0 < m) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hδ0 : 0 < δ0) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (W D1 D2 D3 D4 D5 : ℝ → ℝ) (τ : ℝ),
      (∀ t, HasDerivAt W (D1 t) t) → (∀ t, HasDerivAt D1 (D2 t) t) →
      (∀ t, HasDerivAt D2 (D3 t) t) → (∀ t, HasDerivAt D3 (D4 t) t) →
      (∀ t, HasDerivAt D4 (D5 t) t) →
      m ≤ D1 τ → |D1 τ| ≤ B → |D2 τ| ≤ B → |D3 τ| ≤ B → |D4 τ| ≤ B →
      (∀ t, |t| ≤ δ0 → |D5 (τ + t)| ≤ M) →
      ∀ ℓ : ℝ, ℓ ≠ 0 → |ℓ| < ℓ0 →
        |(3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
          - (D3 τ / D1 τ - 3 / 2 * (D2 τ / D1 τ) ^ 2) / 6 * ℓ ^ 2| ≤ C * ℓ ^ 4 := by
  obtain ⟨C, ℓ0, hℓ0, hmain⟩ :=
    TimeAppendix7.schwarz_uniform_window m B (M / 120) δ0 hm hB (by positivity) hδ0
  refine ⟨C, ℓ0, hℓ0, ?_⟩
  intro W D1 D2 D3 D4 D5 τ h0 h1 h2 h3 h4 hm1 b1 b2 b3 b4 hM5 ℓ hl hlt
  exact hmain W τ (W τ) (D1 τ) (D2 τ) (D3 τ) (D4 τ) hm1 b1 b2 b3 b4
    (fun h hh => taylor_bound_of_fifth W D1 D2 D3 D4 D5 τ δ0 M h0 h1 h2 h3 h4 hM5 h hh) ℓ hl hlt

end TimeAppendix8

/-! ### Appendix H, continued (A90): `lem:schwarz` in terms of the lapse `Ω` -/
namespace TimeAppendix9

theorem mono_bound (c y u Lp U : ℝ) (q : ℕ) (hy : |y| ≤ Lp) (hu : |u| ≤ U) :
    |c * y * u ^ q| ≤ |c| * Lp * U ^ q := by
  rw [abs_mul, abs_mul, abs_pow]
  have hLp : 0 ≤ Lp := (abs_nonneg y).trans hy
  exact mul_le_mul (mul_le_mul_of_nonneg_left hy (abs_nonneg c))
    (pow_le_pow_left₀ (abs_nonneg u) hu q) (by positivity) (by positivity)

set_option maxHeartbeats 1600000 in
/-- `lem:schwarz` for the lapse, with uniform constants: for `0 < a ≤ b`, `L ≥ 0` there are `C` and
`ℓ₀ > 0`, depending only on `a, b, L`, such that for every `Ω` with four derivatives `Ω1, …, Ω4` on
the line, `a ≤ Ω ≤ b`, `|Ω_k| ≤ L`, every primitive `W` of `Ω⁻²` and every `τ`:
`|ρ₀ − 1 − 𝒦(τ) ℓ²/3| ≤ C ℓ⁴` for `0 < |ℓ| < ℓ₀`, where `𝒦 = −Ω''/Ω`.  No further hypothesis. -/
theorem lapse_schwarz_uniform (a b L : ℝ) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (Ω Ω1 Ω2 Ω3 Ω4 W : ℝ → ℝ) (τ : ℝ),
      (∀ t, HasDerivAt Ω (Ω1 t) t) → (∀ t, HasDerivAt Ω1 (Ω2 t) t) →
      (∀ t, HasDerivAt Ω2 (Ω3 t) t) → (∀ t, HasDerivAt Ω3 (Ω4 t) t) →
      (∀ t, HasDerivAt W (1 / (Ω t) ^ 2) t) →
      (∀ t, a ≤ Ω t ∧ Ω t ≤ b) →
      (∀ t, |Ω1 t| ≤ L ∧ |Ω2 t| ≤ L ∧ |Ω3 t| ≤ L ∧ |Ω4 t| ≤ L) →
      ∀ ℓ : ℝ, ℓ ≠ 0 → |ℓ| < ℓ0 →
        |(3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
          - (-(Ω2 τ) / Ω τ) / 3 * ℓ ^ 2| ≤ C * ℓ ^ 4 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set U : ℝ := 1 / a with hU
  have hU0 : 0 < U := by positivity
  set B : ℝ := U ^ 2 + 2 * L * U ^ 3 + (2 * L * U ^ 3 + 6 * (L * L) * U ^ 4)
    + (2 * L * U ^ 3 + 18 * (L * L) * U ^ 4 + 24 * (L * L * L) * U ^ 5) with hB
  have hB0 : 0 ≤ B := by positivity
  have n1 : 0 ≤ U ^ 2 := by positivity
  have n2 : 0 ≤ 2 * L * U ^ 3 := by positivity
  have n3 : 0 ≤ 6 * (L * L) * U ^ 4 := by positivity
  have n4 : 0 ≤ 18 * (L * L) * U ^ 4 := by positivity
  have n5 : 0 ≤ 24 * (L * L * L) * U ^ 5 := by positivity
  set Mb : ℝ := 2 * L * U ^ 3 + 24 * (L * L) * U ^ 4 + 18 * (L * L) * U ^ 4
    + 144 * (L * L * L) * U ^ 5 + 120 * (L * L * L * L) * U ^ 6 with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  obtain ⟨C, ℓ0, hℓ0, hmain⟩ := TimeAppendix8.schwarz_uniform_deriv (1 / b ^ 2) B Mb 1
    (by positivity) hB0 hMb0 one_pos
  refine ⟨C, ℓ0, hℓ0, ?_⟩
  intro Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb' ℓ hl hlt
  have hpos : ∀ t, 0 < Ω t := fun t => lt_of_lt_of_le ha (hΩ t).1
  set u : ℝ → ℝ := fun t => (Ω t)⁻¹ with hu
  have hud : ∀ t, HasDerivAt u (-(Ω1 t) * u t ^ 2) t := fun t => by
    have := (h0 t).inv (hpos t).ne'
    convert this using 1
    simp only [hu]; field_simp
  have hub : ∀ t, |u t| ≤ U := fun t => by
    simp only [hu, hU]
    rw [abs_of_pos (inv_pos.mpr (hpos t)), inv_eq_one_div]
    exact one_div_le_one_div_of_le ha (hΩ t).1
  have hulo : ∀ t, 1 / b ≤ u t := fun t => by
    simp only [hu]; rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (hpos t) (hΩ t).2
  set D1 : ℝ → ℝ := fun t => u t ^ 2 with hD1
  set D2 : ℝ → ℝ := fun t => -2 * Ω1 t * u t ^ 3 with hD2
  set D3 : ℝ → ℝ := fun t => -2 * Ω2 t * u t ^ 3 + 6 * (Ω1 t * Ω1 t) * u t ^ 4 with hD3
  set D4 : ℝ → ℝ := fun t => -2 * Ω3 t * u t ^ 3 + 18 * (Ω1 t * Ω2 t) * u t ^ 4
    - 24 * (Ω1 t * Ω1 t * Ω1 t) * u t ^ 5 with hD4
  set D5 : ℝ → ℝ := fun t => -2 * Ω4 t * u t ^ 3 + 24 * (Ω1 t * Ω3 t) * u t ^ 4
    + 18 * (Ω2 t * Ω2 t) * u t ^ 4 - 144 * (Ω1 t * Ω1 t * Ω2 t) * u t ^ 5
    + 120 * (Ω1 t * Ω1 t * Ω1 t * Ω1 t) * u t ^ 6 with hD5
  have dW : ∀ t, HasDerivAt W (D1 t) t := fun t => by
    have := hW t
    convert this using 1
    simp only [hD1, hu]; field_simp
  have d1 : ∀ t, HasDerivAt D1 (D2 t) t := fun t => by
    have := (hud t).pow 2
    convert this using 1
    simp only [hD2]; push_cast; ring
  have d2 : ∀ t, HasDerivAt D2 (D3 t) t := fun t => by
    have := ((h1 t).const_mul (-2)).mul ((hud t).pow 3)
    convert this using 1
    simp only [hD3, Pi.pow_apply, Pi.mul_apply]; push_cast; ring
  have d3 : ∀ t, HasDerivAt D3 (D4 t) t := fun t => by
    have := (((h2 t).const_mul (-2)).mul ((hud t).pow 3)).add
      ((((h1 t).mul (h1 t)).const_mul 6).mul ((hud t).pow 4))
    convert this using 1
    simp only [hD4, Pi.pow_apply, Pi.mul_apply]; push_cast; ring
  have d4 : ∀ t, HasDerivAt D4 (D5 t) t := fun t => by
    have := ((((h3 t).const_mul (-2)).mul ((hud t).pow 3)).add
      ((((h1 t).mul (h2 t)).const_mul 18).mul ((hud t).pow 4))).sub
      (((((h1 t).mul (h1 t)).mul (h1 t)).const_mul 24).mul ((hud t).pow 5))
    convert this using 1
    simp only [hD5, Pi.pow_apply, Pi.mul_apply]; push_cast; ring
  -- bounds
  have p2 : ∀ x y : ℝ, |x| ≤ L → |y| ≤ L → |x * y| ≤ L * L := fun x y hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hL
  have p3 : ∀ x y z : ℝ, |x| ≤ L → |y| ≤ L → |z| ≤ L → |x * y * z| ≤ L * L * L :=
    fun x y z hx hy hz => by
      rw [abs_mul]; exact mul_le_mul (p2 x y hx hy) hz (abs_nonneg _) (by positivity)
  have p4 : ∀ x y z w : ℝ, |x| ≤ L → |y| ≤ L → |z| ≤ L → |w| ≤ L →
      |x * y * z * w| ≤ L * L * L * L := fun x y z w hx hy hz hw => by
    rw [abs_mul]; exact mul_le_mul (p3 x y z hx hy hz) hw (abs_nonneg _) (by positivity)
  obtain ⟨l1, l2, l3, l4⟩ := hb' τ
  have bD1 : |D1 τ| ≤ B := by
    have : |D1 τ| ≤ U ^ 2 := by
      simp only [hD1]; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hub τ) 2
    simp only [hB]; linarith
  have bD2 : |D2 τ| ≤ B := by
    have := mono_bound (-2) (Ω1 τ) (u τ) L U 3 l1 (hub τ)
    simp only [hD2, hB]
    have e : |(-2 : ℝ)| = 2 := by norm_num
    rw [e] at this
    linarith
  have bD3 : |D3 τ| ≤ B := by
    have t1 := mono_bound (-2) (Ω2 τ) (u τ) L U 3 l2 (hub τ)
    have t2 := mono_bound 6 (Ω1 τ * Ω1 τ) (u τ) (L * L) U 4 (p2 _ _ l1 l1) (hub τ)
    have e : |(-2 : ℝ)| = 2 := by norm_num
    have e6 : |(6 : ℝ)| = 6 := by norm_num
    rw [e] at t1; rw [e6] at t2
    simp only [hD3, hB]
    have := abs_add_le (-2 * Ω2 τ * u τ ^ 3) (6 * (Ω1 τ * Ω1 τ) * u τ ^ 4)
    linarith
  have bD4 : |D4 τ| ≤ B := by
    have t1 := mono_bound (-2) (Ω3 τ) (u τ) L U 3 l3 (hub τ)
    have t2 := mono_bound 18 (Ω1 τ * Ω2 τ) (u τ) (L * L) U 4 (p2 _ _ l1 l2) (hub τ)
    have t3 := mono_bound 24 (Ω1 τ * Ω1 τ * Ω1 τ) (u τ) (L * L * L) U 5 (p3 _ _ _ l1 l1 l1) (hub τ)
    have e : |(-2 : ℝ)| = 2 := by norm_num
    have e18 : |(18 : ℝ)| = 18 := by norm_num
    have e24 : |(24 : ℝ)| = 24 := by norm_num
    rw [e] at t1; rw [e18] at t2; rw [e24] at t3
    simp only [hD4, hB]
    have s1 := abs_sub (-2 * Ω3 τ * u τ ^ 3 + 18 * (Ω1 τ * Ω2 τ) * u τ ^ 4)
      (24 * (Ω1 τ * Ω1 τ * Ω1 τ) * u τ ^ 5)
    have s2 := abs_add_le (-2 * Ω3 τ * u τ ^ 3) (18 * (Ω1 τ * Ω2 τ) * u τ ^ 4)
    linarith
  have bD5 : ∀ t, |t| ≤ 1 → |D5 (τ + t)| ≤ Mb := by
    intro t _
    obtain ⟨k1, k2, k3, k4⟩ := hb' (τ + t)
    set x := τ + t
    have t1 := mono_bound (-2) (Ω4 x) (u x) L U 3 k4 (hub x)
    have t2 := mono_bound 24 (Ω1 x * Ω3 x) (u x) (L * L) U 4 (p2 _ _ k1 k3) (hub x)
    have t3 := mono_bound 18 (Ω2 x * Ω2 x) (u x) (L * L) U 4 (p2 _ _ k2 k2) (hub x)
    have t4 := mono_bound 144 (Ω1 x * Ω1 x * Ω2 x) (u x) (L * L * L) U 5 (p3 _ _ _ k1 k1 k2) (hub x)
    have t5 := mono_bound 120 (Ω1 x * Ω1 x * Ω1 x * Ω1 x) (u x) (L * L * L * L) U 6
      (p4 _ _ _ _ k1 k1 k1 k1) (hub x)
    have e : |(-2 : ℝ)| = 2 := by norm_num
    have e24 : |(24 : ℝ)| = 24 := by norm_num
    have e18 : |(18 : ℝ)| = 18 := by norm_num
    have e144 : |(144 : ℝ)| = 144 := by norm_num
    have e120 : |(120 : ℝ)| = 120 := by norm_num
    rw [e] at t1; rw [e24] at t2; rw [e18] at t3; rw [e144] at t4; rw [e120] at t5
    simp only [hD5, hMb]
    have s1 := abs_add_le (-2 * Ω4 x * u x ^ 3 + 24 * (Ω1 x * Ω3 x) * u x ^ 4
      + 18 * (Ω2 x * Ω2 x) * u x ^ 4 - 144 * (Ω1 x * Ω1 x * Ω2 x) * u x ^ 5)
      (120 * (Ω1 x * Ω1 x * Ω1 x * Ω1 x) * u x ^ 6)
    have s2 := abs_sub (-2 * Ω4 x * u x ^ 3 + 24 * (Ω1 x * Ω3 x) * u x ^ 4
      + 18 * (Ω2 x * Ω2 x) * u x ^ 4) (144 * (Ω1 x * Ω1 x * Ω2 x) * u x ^ 5)
    have s3 := abs_add_le (-2 * Ω4 x * u x ^ 3 + 24 * (Ω1 x * Ω3 x) * u x ^ 4)
      (18 * (Ω2 x * Ω2 x) * u x ^ 4)
    have s4 := abs_add_le (-2 * Ω4 x * u x ^ 3) (24 * (Ω1 x * Ω3 x) * u x ^ 4)
    linarith
  have hm1 : 1 / b ^ 2 ≤ D1 τ := by
    simp only [hD1]
    have := pow_le_pow_left₀ (by positivity) (hulo τ) 2
    rwa [div_pow, one_pow] at this
  have key := hmain W D1 D2 D3 D4 D5 τ dW d1 d2 d3 d4 hm1 bD1 bD2 bD3 bD4 bD5 ℓ hl hlt
  have hS : (D3 τ / D1 τ - 3 / 2 * (D2 τ / D1 τ) ^ 2) / 6 = (-(Ω2 τ) / Ω τ) / 3 := by
    have hne : u τ ≠ 0 := (inv_pos.mpr (hpos τ)).ne'
    have hΩne := (hpos τ).ne'
    simp only [hD1, hD2, hD3]
    have : u τ = (Ω τ)⁻¹ := rfl
    rw [this]
    field_simp
    ring
  rw [hS] at key
  exact key

end TimeAppendix9

/-! ### Appendix H, continued (A91): the estimator of `thm:lapse-est`, deterministic part -/
namespace TimeAppendix10

/-- Deterministic part of `thm:lapse-est` (`D = 1`): for `0 < a ≤ b`, `L ≥ 0` there are `C` and
`ℓ₀ > 0`, depending only on `a, b, L`, such that for every lapse `Ω` on the line with four
derivatives, `a ≤ Ω ≤ b`, `|Ω_k| ≤ L`, every primitive `W` of `Ω⁻²`, every `τ`, every spacing
`0 < |ℓ| < ℓ₀` and every measured cross-ratio `ρ` with `|ρ − ρ₀| ≤ ε`:
`|3(ρ − 1)/ℓ² − 𝒦(τ)| ≤ 3 C ℓ² + 3 ε/ℓ²`, `𝒦 = −Ω''/Ω`.
The model error `ε` (in the theorem: of the order `ℓ/m̄`, from `thm:vargap`(b)) is a HYPOTHESIS. -/
theorem lapse_estimator (a b L : ℝ) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (Ω Ω1 Ω2 Ω3 Ω4 W : ℝ → ℝ) (τ : ℝ),
      (∀ t, HasDerivAt Ω (Ω1 t) t) → (∀ t, HasDerivAt Ω1 (Ω2 t) t) →
      (∀ t, HasDerivAt Ω2 (Ω3 t) t) → (∀ t, HasDerivAt Ω3 (Ω4 t) t) →
      (∀ t, HasDerivAt W (1 / (Ω t) ^ 2) t) →
      (∀ t, a ≤ Ω t ∧ Ω t ≤ b) →
      (∀ t, |Ω1 t| ≤ L ∧ |Ω2 t| ≤ L ∧ |Ω3 t| ≤ L ∧ |Ω4 t| ≤ L) →
      ∀ (ℓ ρ ε : ℝ), ℓ ≠ 0 → |ℓ| < ℓ0 →
        |ρ - (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2))))| ≤ ε →
        |3 * (ρ - 1) / ℓ ^ 2 - (-(Ω2 τ) / Ω τ)| ≤ 3 * C * ℓ ^ 2 + 3 * ε / ℓ ^ 2 := by
  obtain ⟨C, ℓ0, hℓ0, hmain⟩ := TimeAppendix9.lapse_schwarz_uniform a b L ha hab hL
  refine ⟨C, ℓ0, hℓ0, ?_⟩
  intro Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb ℓ ρ ε hl hlt hρ
  have key := hmain Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb ℓ hl hlt
  set ρ0 := (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) with hρ0
  set K := -(Ω2 τ) / Ω τ with hK
  have hl2 : 0 < ℓ ^ 2 := by positivity
  have e : 3 * (ρ - 1) / ℓ ^ 2 - K
      = 3 * (ρ0 - 1 - K / 3 * ℓ ^ 2) / ℓ ^ 2 + 3 * (ρ - ρ0) / ℓ ^ 2 := by
    field_simp
    ring
  rw [e]
  have t1 : |3 * (ρ0 - 1 - K / 3 * ℓ ^ 2) / ℓ ^ 2| ≤ 3 * C * ℓ ^ 2 := by
    rw [abs_div, abs_of_pos hl2, div_le_iff₀ hl2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have : (3 : ℝ) * C * ℓ ^ 2 * ℓ ^ 2 = 3 * (C * ℓ ^ 4) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left key (by norm_num)
  have t2 : |3 * (ρ - ρ0) / ℓ ^ 2| ≤ 3 * ε / ℓ ^ 2 := by
    rw [abs_div, abs_of_pos hl2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (by norm_num)) hl2.le
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

end TimeAppendix10

/-! ### Appendix H, continued (A92): the lapse on a window instead of the whole line -/
namespace TimeAppendix11

/-- One integration step on `[0, δ]`: `g 0 = 0` and `|g' t| ≤ c tⁿ` for `0 ≤ t ≤ δ` give
`|g h| ≤ c h^{n+1}/(n+1)` for `0 ≤ h ≤ δ`. -/
theorem pow_step_nonneg (g g' : ℝ → ℝ) (c δ : ℝ) (n : ℕ) (hg0 : g 0 = 0)
    (hd : ∀ t, 0 ≤ t → t ≤ δ → HasDerivAt g (g' t) t) (hb : ∀ t, 0 ≤ t → t ≤ δ → |g' t| ≤ c * t ^ n)
    (h : ℝ) (h0 : 0 ≤ h) (hδ : h ≤ δ) : |g h| ≤ c * h ^ (n + 1) / (n + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hp : ∀ t, HasDerivAt (fun t => c * t ^ (n + 1) / (n + 1)) (c * t ^ n) t := by
    intro t
    have := ((hasDerivAt_pow (n + 1) t).const_mul c).div_const ((n : ℝ) + 1)
    convert this using 1
    push_cast
    field_simp
  have mono : ∀ (φ φ' : ℝ → ℝ), (∀ t, 0 ≤ t → t ≤ δ → HasDerivAt φ (φ' t) t) →
      (∀ t, 0 ≤ t → t ≤ δ → 0 ≤ φ' t) → φ 0 ≤ φ h := by
    intro φ φ' hφ hpos
    have hm : MonotoneOn φ (Set.Icc 0 h) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 h)
      · exact fun t ht => (hφ t ht.1 (ht.2.trans hδ)).continuousAt.continuousWithinAt
      · intro t ht
        have ht' := interior_subset ht
        exact (hφ t ht'.1 (ht'.2.trans hδ)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hφ t ht.1.le (ht.2.le.trans hδ)).deriv]
        exact hpos t ht.1.le (ht.2.le.trans hδ)
    exact hm ⟨le_refl _, h0⟩ ⟨h0, le_refl _⟩ h0
  have u1 := mono (fun t => c * t ^ (n + 1) / (n + 1) - g t) (fun t => c * t ^ n - g' t)
    (fun t t0 tδ => (hp t).sub (hd t t0 tδ))
    (fun t t0 tδ => by have := (abs_le.mp (hb t t0 tδ)).2; linarith)
  have u2 := mono (fun t => c * t ^ (n + 1) / (n + 1) + g t) (fun t => c * t ^ n + g' t)
    (fun t t0 tδ => (hp t).add (hd t t0 tδ))
    (fun t t0 tδ => by have := (abs_le.mp (hb t t0 tδ)).1; linarith)
  simp only [hg0, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_div, sub_zero, add_zero] at u1 u2
  rw [abs_le]
  constructor <;> linarith

/-- The same on `[-δ, δ]`. -/
theorem pow_step (g g' : ℝ → ℝ) (c δ : ℝ) (n : ℕ) (hg0 : g 0 = 0)
    (hd : ∀ t, |t| ≤ δ → HasDerivAt g (g' t) t) (hb : ∀ t, |t| ≤ δ → |g' t| ≤ c * |t| ^ n)
    (h : ℝ) (hh : |h| ≤ δ) : |g h| ≤ c * |h| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 h with h0 | h0
  · rw [abs_of_nonneg h0] at hh ⊢
    exact pow_step_nonneg g g' c δ n hg0
      (fun t t0 tδ => hd t (by rw [abs_of_nonneg t0]; exact tδ))
      (fun t t0 tδ => by have := hb t (by rw [abs_of_nonneg t0]; exact tδ)
                         rwa [abs_of_nonneg t0] at this) h h0 hh
  · rw [abs_of_nonpos h0] at hh ⊢
    have := pow_step_nonneg (fun t => g (-t)) (fun t => -g' (-t)) c δ n (by simpa using hg0)
      (fun t t0 tδ => by
        have := (hd (-t) (by rw [abs_neg, abs_of_nonneg t0]; exact tδ)).scomp t (hasDerivAt_neg t)
        simpa using this)
      (fun t t0 tδ => by
        have := hb (-t) (by rw [abs_neg, abs_of_nonneg t0]; exact tδ)
        rw [abs_neg, abs_of_nonneg t0] at this
        rwa [abs_neg])
      (-h) (by linarith) hh
    simpa using this

/-- Lagrange bound of order five from the derivatives: if `W` has derivatives `D1, …, D5`
everywhere and `|D5| ≤ M` on `[τ − δ, τ + δ]`, then for `|h| ≤ δ`
`|W(τ+h) − W τ − D1 τ h − D2 τ h²/2 − D3 τ h³/6 − D4 τ h⁴/24| ≤ (M/120) |h|⁵`.
This is the hypothesis `hT` of `schwarz_uniform_window` with `B5 = M/120`. -/
theorem taylor_bound_of_fifth (W D1 D2 D3 D4 D5 : ℝ → ℝ) (τ δ M : ℝ)
    (h0 : ∀ t, |t - τ| ≤ δ → HasDerivAt W (D1 t) t) (h1 : ∀ t, |t - τ| ≤ δ → HasDerivAt D1 (D2 t) t)
    (h2 : ∀ t, |t - τ| ≤ δ → HasDerivAt D2 (D3 t) t) (h3 : ∀ t, |t - τ| ≤ δ → HasDerivAt D3 (D4 t) t)
    (h4 : ∀ t, |t - τ| ≤ δ → HasDerivAt D4 (D5 t) t) (hM : ∀ t, |t| ≤ δ → |D5 (τ + t)| ≤ M)
    (h : ℝ) (hh : |h| ≤ δ) :
    |W (τ + h) - W τ - D1 τ * h - D2 τ * h ^ 2 / 2 - D3 τ * h ^ 3 / 6 - D4 τ * h ^ 4 / 24|
      ≤ M / 120 * |h| ^ 5 := by
  have sh : ∀ (F F' : ℝ → ℝ), (∀ t, |t - τ| ≤ δ → HasDerivAt F (F' t) t) →
      ∀ t, |t| ≤ δ → HasDerivAt (fun s => F (τ + s)) (F' (τ + t)) t := by
    intro F F' hF t ht
    have := (hF (τ + t) (by simpa using ht)).scomp t ((hasDerivAt_id t).const_add τ)
    simpa using this
  -- f4, f3, f2, f1, f0
  set f4 : ℝ → ℝ := fun s => D4 (τ + s) - D4 τ with hf4
  set f3 : ℝ → ℝ := fun s => D3 (τ + s) - D3 τ - D4 τ * s with hf3
  set f2 : ℝ → ℝ := fun s => D2 (τ + s) - D2 τ - D3 τ * s - D4 τ * s ^ 2 / 2 with hf2
  set f1 : ℝ → ℝ := fun s => D1 (τ + s) - D1 τ - D2 τ * s - D3 τ * s ^ 2 / 2
    - D4 τ * s ^ 3 / 6 with hf1
  set f0 : ℝ → ℝ := fun s => W (τ + s) - W τ - D1 τ * s - D2 τ * s ^ 2 / 2 - D3 τ * s ^ 3 / 6
    - D4 τ * s ^ 4 / 24 with hf0
  have d4 : ∀ t, |t| ≤ δ → HasDerivAt f4 (D5 (τ + t)) t := fun t ht => by
    have := (sh D4 D5 h4 t ht).sub_const (D4 τ); simpa [hf4] using this
  have d3 : ∀ t, |t| ≤ δ → HasDerivAt f3 (f4 t) t := fun t ht => by
    have := ((sh D3 D4 h3 t ht).sub_const (D3 τ)).sub ((hasDerivAt_id t).const_mul (D4 τ))
    simpa [hf3, hf4] using this
  have d2 : ∀ t, |t| ≤ δ → HasDerivAt f2 (f3 t) t := fun t ht => by
    have := (((sh D2 D3 h2 t ht).sub_const (D2 τ)).sub ((hasDerivAt_id t).const_mul (D3 τ))).sub
      (((hasDerivAt_pow 2 t).const_mul (D4 τ)).div_const 2)
    convert this using 1
    simp only [hf3]; push_cast; ring
  have d1 : ∀ t, |t| ≤ δ → HasDerivAt f1 (f2 t) t := fun t ht => by
    have := ((((sh D1 D2 h1 t ht).sub_const (D1 τ)).sub ((hasDerivAt_id t).const_mul (D2 τ))).sub
      (((hasDerivAt_pow 2 t).const_mul (D3 τ)).div_const 2)).sub
      (((hasDerivAt_pow 3 t).const_mul (D4 τ)).div_const 6)
    convert this using 1
    simp only [hf2]; push_cast; ring
  have d0 : ∀ t, |t| ≤ δ → HasDerivAt f0 (f1 t) t := fun t ht => by
    have := (((((sh W D1 h0 t ht).sub_const (W τ)).sub ((hasDerivAt_id t).const_mul (D1 τ))).sub
      (((hasDerivAt_pow 2 t).const_mul (D2 τ)).div_const 2)).sub
      (((hasDerivAt_pow 3 t).const_mul (D3 τ)).div_const 6)).sub
      (((hasDerivAt_pow 4 t).const_mul (D4 τ)).div_const 24)
    convert this using 1
    simp only [hf1]; push_cast; ring
  have b4 : ∀ t, |t| ≤ δ → |f4 t| ≤ M * |t| := fun t ht => by
    have := pow_step f4 (fun s => D5 (τ + s)) M δ 0 (by simp [hf4]) d4
      (fun s hs => by simpa using hM s hs) t ht
    simpa using this
  have b3 : ∀ t, |t| ≤ δ → |f3 t| ≤ M / 2 * |t| ^ 2 := fun t ht => by
    have := pow_step f3 f4 M δ 1 (by simp [hf3]) d3 (fun s hs => by simpa using b4 s hs) t ht
    calc |f3 t| ≤ M * |t| ^ (1 + 1) / ((1 : ℕ) + 1) := this
      _ = M / 2 * |t| ^ 2 := by push_cast; ring
  have b2 : ∀ t, |t| ≤ δ → |f2 t| ≤ M / 6 * |t| ^ 3 := fun t ht => by
    have := pow_step f2 f3 (M / 2) δ 2 (by simp [hf2]) d2 b3 t ht
    calc |f2 t| ≤ M / 2 * |t| ^ (2 + 1) / ((2 : ℕ) + 1) := this
      _ = M / 6 * |t| ^ 3 := by push_cast; ring
  have b1 : ∀ t, |t| ≤ δ → |f1 t| ≤ M / 24 * |t| ^ 4 := fun t ht => by
    have := pow_step f1 f2 (M / 6) δ 3 (by simp [hf1]) d1 b2 t ht
    calc |f1 t| ≤ M / 6 * |t| ^ (3 + 1) / ((3 : ℕ) + 1) := this
      _ = M / 24 * |t| ^ 4 := by push_cast; ring
  have := pow_step f0 f1 (M / 24) δ 4 (by simp [hf0]) d0 b1 h hh
  calc |f0 h| ≤ M / 24 * |h| ^ (4 + 1) / ((4 : ℕ) + 1) := this
    _ = M / 120 * |h| ^ 5 := by push_cast; ring

/-- `lem:schwarz` with uniform constants, in terms of derivatives on a window `[τ − δ0, τ + δ0]`: for `m > 0`, `B, M ≥ 0`, `δ0 > 0`
there are `C` and `ℓ₀ > 0`, depending only on these numbers, such that for every `W` with derivatives
`D1, …, D5` and every `τ` with `D1 τ ≥ m`, `|D_k τ| ≤ B` (`k = 1..4`) and `|D5| ≤ M` on
`[τ − δ0, τ + δ0]`: `|ρ₀ − 1 − S(W)(τ) ℓ²/6| ≤ C ℓ⁴` for `0 < |ℓ| < ℓ₀`.  No hypothesis besides the
derivatives and their bounds. -/
theorem schwarz_uniform_deriv (m B M δ0 : ℝ) (hm : 0 < m) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hδ0 : 0 < δ0) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (W D1 D2 D3 D4 D5 : ℝ → ℝ) (τ : ℝ),
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt W (D1 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt D1 (D2 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt D2 (D3 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt D3 (D4 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt D4 (D5 t) t) →
      m ≤ D1 τ → |D1 τ| ≤ B → |D2 τ| ≤ B → |D3 τ| ≤ B → |D4 τ| ≤ B →
      (∀ t, |t| ≤ δ0 → |D5 (τ + t)| ≤ M) →
      ∀ ℓ : ℝ, ℓ ≠ 0 → |ℓ| < ℓ0 →
        |(3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
          - (D3 τ / D1 τ - 3 / 2 * (D2 τ / D1 τ) ^ 2) / 6 * ℓ ^ 2| ≤ C * ℓ ^ 4 := by
  obtain ⟨C, ℓ0, hℓ0, hmain⟩ :=
    TimeAppendix7.schwarz_uniform_window m B (M / 120) δ0 hm hB (by positivity) hδ0
  refine ⟨C, ℓ0, hℓ0, ?_⟩
  intro W D1 D2 D3 D4 D5 τ h0 h1 h2 h3 h4 hm1 b1 b2 b3 b4 hM5 ℓ hl hlt
  exact hmain W τ (W τ) (D1 τ) (D2 τ) (D3 τ) (D4 τ) hm1 b1 b2 b3 b4
    (fun h hh => taylor_bound_of_fifth W D1 D2 D3 D4 D5 τ δ0 M h0 h1 h2 h3 h4 hM5 h hh) ℓ hl hlt


theorem mono_bound (c y u Lp U : ℝ) (q : ℕ) (hy : |y| ≤ Lp) (hu : |u| ≤ U) :
    |c * y * u ^ q| ≤ |c| * Lp * U ^ q :=
  TimeAppendix9.mono_bound c y u Lp U q hy hu

set_option maxHeartbeats 1600000 in
/-- `lem:schwarz` for the lapse, with uniform constants: for `0 < a ≤ b`, `L ≥ 0` there are `C` and
`ℓ₀ > 0`, depending only on `a, b, L, δ0`, such that for every `Ω` with four derivatives `Ω1, …, Ω4` on
the window `[τ − δ0, τ + δ0]` (hypotheses only there), `a ≤ Ω ≤ b`, `|Ω_k| ≤ L`, every primitive `W` of `Ω⁻²` and every `τ`:
`|ρ₀ − 1 − 𝒦(τ) ℓ²/3| ≤ C ℓ⁴` for `0 < |ℓ| < ℓ₀`, where `𝒦 = −Ω''/Ω`.  No further hypothesis. -/
theorem lapse_schwarz_uniform (a b L δ0 : ℝ) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    (hδ0 : 0 < δ0) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (Ω Ω1 Ω2 Ω3 Ω4 W : ℝ → ℝ) (τ : ℝ),
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω (Ω1 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω1 (Ω2 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω2 (Ω3 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω3 (Ω4 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt W (1 / (Ω t) ^ 2) t) →
      (∀ t, |t - τ| ≤ δ0 → a ≤ Ω t ∧ Ω t ≤ b) →
      (∀ t, |t - τ| ≤ δ0 → |Ω1 t| ≤ L ∧ |Ω2 t| ≤ L ∧ |Ω3 t| ≤ L ∧ |Ω4 t| ≤ L) →
      ∀ ℓ : ℝ, ℓ ≠ 0 → |ℓ| < ℓ0 →
        |(3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) - 1
          - (-(Ω2 τ) / Ω τ) / 3 * ℓ ^ 2| ≤ C * ℓ ^ 4 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set U : ℝ := 1 / a with hU
  have hU0 : 0 < U := by positivity
  set B : ℝ := U ^ 2 + 2 * L * U ^ 3 + (2 * L * U ^ 3 + 6 * (L * L) * U ^ 4)
    + (2 * L * U ^ 3 + 18 * (L * L) * U ^ 4 + 24 * (L * L * L) * U ^ 5) with hB
  have hB0 : 0 ≤ B := by positivity
  have n1 : 0 ≤ U ^ 2 := by positivity
  have n2 : 0 ≤ 2 * L * U ^ 3 := by positivity
  have n3 : 0 ≤ 6 * (L * L) * U ^ 4 := by positivity
  have n4 : 0 ≤ 18 * (L * L) * U ^ 4 := by positivity
  have n5 : 0 ≤ 24 * (L * L * L) * U ^ 5 := by positivity
  set Mb : ℝ := 2 * L * U ^ 3 + 24 * (L * L) * U ^ 4 + 18 * (L * L) * U ^ 4
    + 144 * (L * L * L) * U ^ 5 + 120 * (L * L * L * L) * U ^ 6 with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  obtain ⟨C, ℓ0, hℓ0, hmain⟩ := schwarz_uniform_deriv (1 / b ^ 2) B Mb δ0
    (by positivity) hB0 hMb0 hδ0
  refine ⟨C, ℓ0, hℓ0, ?_⟩
  intro Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb' ℓ hl hlt
  have hτ : |τ - τ| ≤ δ0 := by simpa using hδ0.le
  have hpos : ∀ t, |t - τ| ≤ δ0 → 0 < Ω t := fun t ht => lt_of_lt_of_le ha (hΩ t ht).1
  set u : ℝ → ℝ := fun t => (Ω t)⁻¹ with hu
  have hud : ∀ t, |t - τ| ≤ δ0 → HasDerivAt u (-(Ω1 t) * u t ^ 2) t := fun t ht => by
    have hne := (hpos t ht).ne'
    have := (h0 t ht).inv hne
    convert this using 1
    simp only [hu]; field_simp
  have hub : ∀ t, |t - τ| ≤ δ0 → |u t| ≤ U := fun t ht => by
    simp only [hu, hU]
    rw [abs_of_pos (inv_pos.mpr (hpos t ht)), inv_eq_one_div]
    exact one_div_le_one_div_of_le ha (hΩ t ht).1
  have hulo : ∀ t, |t - τ| ≤ δ0 → 1 / b ≤ u t := fun t ht => by
    simp only [hu]; rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (hpos t ht) (hΩ t ht).2
  set D1 : ℝ → ℝ := fun t => u t ^ 2 with hD1
  set D2 : ℝ → ℝ := fun t => -2 * Ω1 t * u t ^ 3 with hD2
  set D3 : ℝ → ℝ := fun t => -2 * Ω2 t * u t ^ 3 + 6 * (Ω1 t * Ω1 t) * u t ^ 4 with hD3
  set D4 : ℝ → ℝ := fun t => -2 * Ω3 t * u t ^ 3 + 18 * (Ω1 t * Ω2 t) * u t ^ 4
    - 24 * (Ω1 t * Ω1 t * Ω1 t) * u t ^ 5 with hD4
  set D5 : ℝ → ℝ := fun t => -2 * Ω4 t * u t ^ 3 + 24 * (Ω1 t * Ω3 t) * u t ^ 4
    + 18 * (Ω2 t * Ω2 t) * u t ^ 4 - 144 * (Ω1 t * Ω1 t * Ω2 t) * u t ^ 5
    + 120 * (Ω1 t * Ω1 t * Ω1 t * Ω1 t) * u t ^ 6 with hD5
  have dW : ∀ t, |t - τ| ≤ δ0 → HasDerivAt W (D1 t) t := fun t ht => by
    have hne := (hpos t ht).ne'
    have := hW t ht
    convert this using 1
    simp only [hD1, hu]; field_simp
  have d1 : ∀ t, |t - τ| ≤ δ0 → HasDerivAt D1 (D2 t) t := fun t ht => by
    have := (hud t ht).pow 2
    convert this using 1
    simp only [hD2]; push_cast; ring
  have d2 : ∀ t, |t - τ| ≤ δ0 → HasDerivAt D2 (D3 t) t := fun t ht => by
    have := ((h1 t ht).const_mul (-2)).mul ((hud t ht).pow 3)
    convert this using 1
    simp only [hD3, Pi.pow_apply, Pi.mul_apply]; push_cast; ring
  have d3 : ∀ t, |t - τ| ≤ δ0 → HasDerivAt D3 (D4 t) t := fun t ht => by
    have := (((h2 t ht).const_mul (-2)).mul ((hud t ht).pow 3)).add
      ((((h1 t ht).mul (h1 t ht)).const_mul 6).mul ((hud t ht).pow 4))
    convert this using 1
    simp only [hD4, Pi.pow_apply, Pi.mul_apply]; push_cast; ring
  have d4 : ∀ t, |t - τ| ≤ δ0 → HasDerivAt D4 (D5 t) t := fun t ht => by
    have := ((((h3 t ht).const_mul (-2)).mul ((hud t ht).pow 3)).add
      ((((h1 t ht).mul (h2 t ht)).const_mul 18).mul ((hud t ht).pow 4))).sub
      (((((h1 t ht).mul (h1 t ht)).mul (h1 t ht)).const_mul 24).mul ((hud t ht).pow 5))
    convert this using 1
    simp only [hD5, Pi.pow_apply, Pi.mul_apply]; push_cast; ring
  -- bounds
  have p2 : ∀ x y : ℝ, |x| ≤ L → |y| ≤ L → |x * y| ≤ L * L := fun x y hx hy => by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hL
  have p3 : ∀ x y z : ℝ, |x| ≤ L → |y| ≤ L → |z| ≤ L → |x * y * z| ≤ L * L * L :=
    fun x y z hx hy hz => by
      rw [abs_mul]; exact mul_le_mul (p2 x y hx hy) hz (abs_nonneg _) (by positivity)
  have p4 : ∀ x y z w : ℝ, |x| ≤ L → |y| ≤ L → |z| ≤ L → |w| ≤ L →
      |x * y * z * w| ≤ L * L * L * L := fun x y z w hx hy hz hw => by
    rw [abs_mul]; exact mul_le_mul (p3 x y z hx hy hz) hw (abs_nonneg _) (by positivity)
  obtain ⟨l1, l2, l3, l4⟩ := hb' τ hτ
  have bD1 : |D1 τ| ≤ B := by
    have : |D1 τ| ≤ U ^ 2 := by
      simp only [hD1]; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hub τ hτ) 2
    simp only [hB]; linarith
  have bD2 : |D2 τ| ≤ B := by
    have := mono_bound (-2) (Ω1 τ) (u τ) L U 3 l1 (hub τ hτ)
    simp only [hD2, hB]
    have e : |(-2 : ℝ)| = 2 := by norm_num
    rw [e] at this
    linarith
  have bD3 : |D3 τ| ≤ B := by
    have t1 := mono_bound (-2) (Ω2 τ) (u τ) L U 3 l2 (hub τ hτ)
    have t2 := mono_bound 6 (Ω1 τ * Ω1 τ) (u τ) (L * L) U 4 (p2 _ _ l1 l1) (hub τ hτ)
    have e : |(-2 : ℝ)| = 2 := by norm_num
    have e6 : |(6 : ℝ)| = 6 := by norm_num
    rw [e] at t1; rw [e6] at t2
    simp only [hD3, hB]
    have := abs_add_le (-2 * Ω2 τ * u τ ^ 3) (6 * (Ω1 τ * Ω1 τ) * u τ ^ 4)
    linarith
  have bD4 : |D4 τ| ≤ B := by
    have t1 := mono_bound (-2) (Ω3 τ) (u τ) L U 3 l3 (hub τ hτ)
    have t2 := mono_bound 18 (Ω1 τ * Ω2 τ) (u τ) (L * L) U 4 (p2 _ _ l1 l2) (hub τ hτ)
    have t3 := mono_bound 24 (Ω1 τ * Ω1 τ * Ω1 τ) (u τ) (L * L * L) U 5 (p3 _ _ _ l1 l1 l1) (hub τ hτ)
    have e : |(-2 : ℝ)| = 2 := by norm_num
    have e18 : |(18 : ℝ)| = 18 := by norm_num
    have e24 : |(24 : ℝ)| = 24 := by norm_num
    rw [e] at t1; rw [e18] at t2; rw [e24] at t3
    simp only [hD4, hB]
    have s1 := abs_sub (-2 * Ω3 τ * u τ ^ 3 + 18 * (Ω1 τ * Ω2 τ) * u τ ^ 4)
      (24 * (Ω1 τ * Ω1 τ * Ω1 τ) * u τ ^ 5)
    have s2 := abs_add_le (-2 * Ω3 τ * u τ ^ 3) (18 * (Ω1 τ * Ω2 τ) * u τ ^ 4)
    linarith
  have bD5 : ∀ t, |t| ≤ δ0 → |D5 (τ + t)| ≤ Mb := by
    intro t ht
    have hx : |τ + t - τ| ≤ δ0 := by simpa using ht
    obtain ⟨k1, k2, k3, k4⟩ := hb' (τ + t) hx
    set x := τ + t
    have t1 := mono_bound (-2) (Ω4 x) (u x) L U 3 k4 (hub x hx)
    have t2 := mono_bound 24 (Ω1 x * Ω3 x) (u x) (L * L) U 4 (p2 _ _ k1 k3) (hub x hx)
    have t3 := mono_bound 18 (Ω2 x * Ω2 x) (u x) (L * L) U 4 (p2 _ _ k2 k2) (hub x hx)
    have t4 := mono_bound 144 (Ω1 x * Ω1 x * Ω2 x) (u x) (L * L * L) U 5 (p3 _ _ _ k1 k1 k2) (hub x hx)
    have t5 := mono_bound 120 (Ω1 x * Ω1 x * Ω1 x * Ω1 x) (u x) (L * L * L * L) U 6
      (p4 _ _ _ _ k1 k1 k1 k1) (hub x hx)
    have e : |(-2 : ℝ)| = 2 := by norm_num
    have e24 : |(24 : ℝ)| = 24 := by norm_num
    have e18 : |(18 : ℝ)| = 18 := by norm_num
    have e144 : |(144 : ℝ)| = 144 := by norm_num
    have e120 : |(120 : ℝ)| = 120 := by norm_num
    rw [e] at t1; rw [e24] at t2; rw [e18] at t3; rw [e144] at t4; rw [e120] at t5
    simp only [hD5, hMb]
    have s1 := abs_add_le (-2 * Ω4 x * u x ^ 3 + 24 * (Ω1 x * Ω3 x) * u x ^ 4
      + 18 * (Ω2 x * Ω2 x) * u x ^ 4 - 144 * (Ω1 x * Ω1 x * Ω2 x) * u x ^ 5)
      (120 * (Ω1 x * Ω1 x * Ω1 x * Ω1 x) * u x ^ 6)
    have s2 := abs_sub (-2 * Ω4 x * u x ^ 3 + 24 * (Ω1 x * Ω3 x) * u x ^ 4
      + 18 * (Ω2 x * Ω2 x) * u x ^ 4) (144 * (Ω1 x * Ω1 x * Ω2 x) * u x ^ 5)
    have s3 := abs_add_le (-2 * Ω4 x * u x ^ 3 + 24 * (Ω1 x * Ω3 x) * u x ^ 4)
      (18 * (Ω2 x * Ω2 x) * u x ^ 4)
    have s4 := abs_add_le (-2 * Ω4 x * u x ^ 3) (24 * (Ω1 x * Ω3 x) * u x ^ 4)
    linarith
  have hm1 : 1 / b ^ 2 ≤ D1 τ := by
    simp only [hD1]
    have := pow_le_pow_left₀ (by positivity) (hulo τ hτ) 2
    rwa [div_pow, one_pow] at this
  have key := hmain W D1 D2 D3 D4 D5 τ dW d1 d2 d3 d4 hm1 bD1 bD2 bD3 bD4 bD5 ℓ hl hlt
  have hS : (D3 τ / D1 τ - 3 / 2 * (D2 τ / D1 τ) ^ 2) / 6 = (-(Ω2 τ) / Ω τ) / 3 := by
    have hne : u τ ≠ 0 := (inv_pos.mpr (hpos τ hτ)).ne'
    have hΩne := (hpos τ hτ).ne'
    simp only [hD1, hD2, hD3]
    have : u τ = (Ω τ)⁻¹ := rfl
    rw [this]
    field_simp
    ring
  rw [hS] at key
  exact key


/-- Deterministic part of `thm:lapse-est` (`D = 1`): for `0 < a ≤ b`, `L ≥ 0` there are `C` and
`ℓ₀ > 0`, depending only on `a, b, L, δ0`, such that for every lapse `Ω` with four derivatives on
the window `[τ − δ0, τ + δ0]`, `a ≤ Ω ≤ b`, `|Ω_k| ≤ L`, every primitive `W` of `Ω⁻²`, every `τ`, every spacing
`0 < |ℓ| < ℓ₀` and every measured cross-ratio `ρ` with `|ρ − ρ₀| ≤ ε`:
`|3(ρ − 1)/ℓ² − 𝒦(τ)| ≤ 3 C ℓ² + 3 ε/ℓ²`, `𝒦 = −Ω''/Ω`.
The model error `ε` (in the theorem: of the order `ℓ/m̄`, from `thm:vargap`(b)) is a HYPOTHESIS. -/
theorem lapse_estimator (a b L δ0 : ℝ) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    (hδ0 : 0 < δ0) :
    ∃ C ℓ0 : ℝ, 0 < ℓ0 ∧ ∀ (Ω Ω1 Ω2 Ω3 Ω4 W : ℝ → ℝ) (τ : ℝ),
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω (Ω1 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω1 (Ω2 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω2 (Ω3 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω3 (Ω4 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt W (1 / (Ω t) ^ 2) t) →
      (∀ t, |t - τ| ≤ δ0 → a ≤ Ω t ∧ Ω t ≤ b) →
      (∀ t, |t - τ| ≤ δ0 → |Ω1 t| ≤ L ∧ |Ω2 t| ≤ L ∧ |Ω3 t| ≤ L ∧ |Ω4 t| ≤ L) →
      ∀ (ℓ ρ ε : ℝ), ℓ ≠ 0 → |ℓ| < ℓ0 →
        |ρ - (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2))))| ≤ ε →
        |3 * (ρ - 1) / ℓ ^ 2 - (-(Ω2 τ) / Ω τ)| ≤ 3 * C * ℓ ^ 2 + 3 * ε / ℓ ^ 2 := by
  obtain ⟨C, ℓ0, hℓ0, hmain⟩ := lapse_schwarz_uniform a b L δ0 ha hab hL hδ0
  refine ⟨C, ℓ0, hℓ0, ?_⟩
  intro Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb ℓ ρ ε hl hlt hρ
  have key := hmain Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb ℓ hl hlt
  set ρ0 := (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) with hρ0
  set K := -(Ω2 τ) / Ω τ with hK
  have hl2 : 0 < ℓ ^ 2 := by positivity
  have e : 3 * (ρ - 1) / ℓ ^ 2 - K
      = 3 * (ρ0 - 1 - K / 3 * ℓ ^ 2) / ℓ ^ 2 + 3 * (ρ - ρ0) / ℓ ^ 2 := by
    field_simp
    ring
  rw [e]
  have t1 : |3 * (ρ0 - 1 - K / 3 * ℓ ^ 2) / ℓ ^ 2| ≤ 3 * C * ℓ ^ 2 := by
    rw [abs_div, abs_of_pos hl2, div_le_iff₀ hl2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have : (3 : ℝ) * C * ℓ ^ 2 * ℓ ^ 2 = 3 * (C * ℓ ^ 4) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left key (by norm_num)
  have t2 : |3 * (ρ - ρ0) / ℓ ^ 2| ≤ 3 * ε / ℓ ^ 2 := by
    rw [abs_div, abs_of_pos hl2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (by norm_num)) hl2.le
  exact (abs_add_le _ _).trans (add_le_add t1 t2)


end TimeAppendix11

/-! ### Appendix H, continued (A93): the estimator for all spacings in the window -/
namespace TimeAppendix12

/-- Differences of a function whose derivative lies in `[lo, hi]` on a window. -/
theorem diff_bounds (W w : ℝ → ℝ) (τ δ0 lo hi x y : ℝ)
    (hW : ∀ t, |t - τ| ≤ δ0 → HasDerivAt W (w t) t)
    (hw : ∀ t, |t - τ| ≤ δ0 → lo ≤ w t ∧ w t ≤ hi)
    (hx : |x - τ| ≤ δ0) (hy : |y - τ| ≤ δ0) (hxy : x < y) :
    lo * (y - x) ≤ W y - W x ∧ W y - W x ≤ hi * (y - x) := by
  have hin : ∀ t, x ≤ t → t ≤ y → |t - τ| ≤ δ0 := fun t h1 h2 => by
    rw [abs_le] at hx hy ⊢; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope W w hxy
    (fun t ht => (hW t (hin t ht.1 ht.2)).continuousAt.continuousWithinAt)
    (fun t ht => hW t (hin t ht.1.le ht.2.le))
  have hpos : 0 < y - x := sub_pos.mpr hxy
  have e : W y - W x = w c * (y - x) := by rw [hslope]; field_simp
  obtain ⟨h1, h2⟩ := hw c (hin c hc.1.le hc.2.le)
  rw [e]
  exact ⟨mul_le_mul_of_nonneg_right h1 hpos.le, mul_le_mul_of_nonneg_right h2 hpos.le⟩

/-- The cross-ratio `ρ₀` of four equally spaced points lies in `[0, (hi/lo)²]` when `W' ∈ [lo, hi]`
with `lo > 0` on the window. -/
theorem cross_ratio_bounded (W w : ℝ → ℝ) (τ δ0 lo hi ℓ : ℝ) (hlo : 0 < lo)
    (hW : ∀ t, |t - τ| ≤ δ0 → HasDerivAt W (w t) t)
    (hw : ∀ t, |t - τ| ≤ δ0 → lo ≤ w t ∧ w t ≤ hi) (hl : 0 < ℓ) (hlδ : 3 * ℓ / 2 ≤ δ0) :
    0 ≤ (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
        (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
         ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) ∧
    (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
        (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
         ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) ≤ (hi / lo) ^ 2 := by
  have m1 : |τ + ℓ / 2 - τ| ≤ δ0 := by rw [add_sub_cancel_left, abs_of_pos (by positivity)]; linarith
  have m2 : |τ - ℓ / 2 - τ| ≤ δ0 := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]; linarith
  have m3 : |τ + 3 * ℓ / 2 - τ| ≤ δ0 := by rw [add_sub_cancel_left, abs_of_pos (by positivity)]; linarith
  have m4 : |τ - 3 * ℓ / 2 - τ| ≤ δ0 := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)]; linarith
  obtain ⟨a1, a2⟩ := diff_bounds W w τ δ0 lo hi _ _ hW hw m4 m1 (by linarith)
  obtain ⟨b1, b2⟩ := diff_bounds W w τ δ0 lo hi _ _ hW hw m2 m3 (by linarith)
  obtain ⟨c1, c2⟩ := diff_bounds W w τ δ0 lo hi _ _ hW hw m4 m3 (by linarith)
  obtain ⟨d1, d2⟩ := diff_bounds W w τ δ0 lo hi _ _ hW hw m2 m1 (by linarith)
  have e1 : τ + ℓ / 2 - (τ - 3 * ℓ / 2) = 2 * ℓ := by ring
  have e2 : τ + 3 * ℓ / 2 - (τ - ℓ / 2) = 2 * ℓ := by ring
  have e3 : τ + 3 * ℓ / 2 - (τ - 3 * ℓ / 2) = 3 * ℓ := by ring
  have e4 : τ + ℓ / 2 - (τ - ℓ / 2) = ℓ := by ring
  rw [e1] at a1 a2; rw [e2] at b1 b2; rw [e3] at c1 c2; rw [e4] at d1 d2
  set A := W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)
  set Bd := W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2)
  set Cd := W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)
  set Dd := W (τ + ℓ / 2) - W (τ - ℓ / 2)
  have hi0 : 0 < hi := lt_of_lt_of_le hlo ((hw τ (by simpa using (by linarith : (0:ℝ) ≤ δ0))).1.trans
    (hw τ (by simpa using (by linarith : (0:ℝ) ≤ δ0))).2)
  have hA : 0 < A := lt_of_lt_of_le (by positivity) a1
  have hBd : 0 < Bd := lt_of_lt_of_le (by positivity) b1
  have hCd : 0 < Cd := lt_of_lt_of_le (by positivity) c1
  have hDd : 0 < Dd := lt_of_lt_of_le (by positivity) d1
  have e34 : (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) = 3 / 4 := by field_simp; ring
  rw [e34]
  refine ⟨by positivity, ?_⟩
  have hnum : A * Bd ≤ (hi * (2 * ℓ)) * (hi * (2 * ℓ)) := mul_le_mul a2 b2 hBd.le (by positivity)
  have hden : (lo * (3 * ℓ)) * (lo * ℓ) ≤ Cd * Dd := mul_le_mul c1 d1 (by positivity) hCd.le
  have hq : A * Bd / (Cd * Dd) ≤ (hi * (2 * ℓ)) * (hi * (2 * ℓ)) / ((lo * (3 * ℓ)) * (lo * ℓ)) :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  have e : (3 : ℝ) / 4 * ((hi * (2 * ℓ)) * (hi * (2 * ℓ)) / ((lo * (3 * ℓ)) * (lo * ℓ)))
      = (hi / lo) ^ 2 := by field_simp; ring
  rw [← e]
  exact mul_le_mul_of_nonneg_left hq (by norm_num)

/-- The estimator of `thm:lapse-est` for every spacing in the window: for `0 < a ≤ b`, `L ≥ 0`,
`δ0 > 0` there is `C'`, depending only on these numbers, such that for every lapse with four
derivatives on `[τ − δ0, τ + δ0]`, `a ≤ Ω ≤ b`, `|Ω_k| ≤ L` there, every spacing `0 < ℓ ≤ 2δ0/3`
and every measured cross-ratio `ρ` with `|ρ − ρ₀| ≤ ε`:
`|3(ρ − 1)/ℓ² − 𝒦(τ)| ≤ C' ℓ² + 3 ε/ℓ²`.  The model error `ε` is a HYPOTHESIS. -/
theorem lapse_estimator_all (a b L δ0 : ℝ) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    (hδ0 : 0 < δ0) :
    ∃ C' : ℝ, ∀ (Ω Ω1 Ω2 Ω3 Ω4 W : ℝ → ℝ) (τ : ℝ),
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω (Ω1 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω1 (Ω2 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω2 (Ω3 t) t) → (∀ t, |t - τ| ≤ δ0 → HasDerivAt Ω3 (Ω4 t) t) →
      (∀ t, |t - τ| ≤ δ0 → HasDerivAt W (1 / (Ω t) ^ 2) t) →
      (∀ t, |t - τ| ≤ δ0 → a ≤ Ω t ∧ Ω t ≤ b) →
      (∀ t, |t - τ| ≤ δ0 → |Ω1 t| ≤ L ∧ |Ω2 t| ≤ L ∧ |Ω3 t| ≤ L ∧ |Ω4 t| ≤ L) →
      ∀ (ℓ ρ ε : ℝ), 0 < ℓ → 3 * ℓ / 2 ≤ δ0 →
        |ρ - (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2))))| ≤ ε →
        |3 * (ρ - 1) / ℓ ^ 2 - (-(Ω2 τ) / Ω τ)| ≤ C' * ℓ ^ 2 + 3 * ε / ℓ ^ 2 := by
  obtain ⟨C, ℓ0, hℓ0, hmain⟩ := TimeAppendix11.lapse_estimator a b L δ0 ha hab hL hδ0
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set R0 : ℝ := ((1 / a ^ 2) / (1 / b ^ 2)) ^ 2 with hR0
  have hR00 : 0 ≤ R0 := by positivity
  set C2 : ℝ := 3 * (R0 + 1) / ℓ0 ^ 4 + L / a / ℓ0 ^ 2 with hC2
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨max (3 * C) C2, ?_⟩
  intro Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb' ℓ ρ ε hl hlδ hρ
  have hl2 : 0 < ℓ ^ 2 := by positivity
  rcases lt_or_ge ℓ ℓ0 with hsmall | hbig
  · have := hmain Ω Ω1 Ω2 Ω3 Ω4 W τ h0 h1 h2 h3 hW hΩ hb' ℓ ρ ε hl.ne'
      (by rw [abs_of_pos hl]; exact hsmall) hρ
    have hmax : 3 * C * ℓ ^ 2 ≤ max (3 * C) C2 * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hl2.le
    linarith
  · have hτ : |τ - τ| ≤ δ0 := by simpa using hδ0.le
    have hwb : ∀ t, |t - τ| ≤ δ0 → 1 / b ^ 2 ≤ 1 / (Ω t) ^ 2 ∧ 1 / (Ω t) ^ 2 ≤ 1 / a ^ 2 := by
      intro t ht
      obtain ⟨g1, g2⟩ := hΩ t ht
      have hp : 0 < Ω t := lt_of_lt_of_le ha g1
      exact ⟨one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp.le g2 2),
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha.le g1 2)⟩
    obtain ⟨r1, r2⟩ := cross_ratio_bounded W (fun t => 1 / (Ω t) ^ 2) τ δ0 (1 / b ^ 2) (1 / a ^ 2) ℓ
      (by positivity) hW hwb hl hlδ
    set ρ0 := (3 * ℓ * ℓ) / ((2 * ℓ) * (2 * ℓ)) *
          (((W (τ + ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + 3 * ℓ / 2) - W (τ - ℓ / 2))) /
           ((W (τ + 3 * ℓ / 2) - W (τ - 3 * ℓ / 2)) * (W (τ + ℓ / 2) - W (τ - ℓ / 2)))) with hρ0
    set K := -(Ω2 τ) / Ω τ with hK
    have hKb : |K| ≤ L / a := by
      obtain ⟨g1, _⟩ := hΩ τ hτ
      have hp : 0 < Ω τ := lt_of_lt_of_le ha g1
      simp only [hK]
      rw [abs_div, abs_neg, abs_of_pos hp]
      exact div_le_div₀ hL (hb' τ hτ).2.1 ha g1
    have h01 : |ρ0 - 1| ≤ R0 + 1 := by
      rw [abs_le]; constructor <;> linarith
    have e : 3 * (ρ - 1) / ℓ ^ 2 - K = 3 * (ρ0 - 1) / ℓ ^ 2 - K + 3 * (ρ - ρ0) / ℓ ^ 2 := by
      field_simp; ring
    have t2 : |3 * (ρ - ρ0) / ℓ ^ 2| ≤ 3 * ε / ℓ ^ 2 := by
      rw [abs_div, abs_of_pos hl2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (by norm_num)) hl2.le
    have hl4 : ℓ0 ^ 4 ≤ ℓ ^ 4 := pow_le_pow_left₀ hℓ0.le hbig 4
    have hl2' : ℓ0 ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hℓ0.le hbig 2
    have t1a : |3 * (ρ0 - 1) / ℓ ^ 2| ≤ 3 * (R0 + 1) / ℓ0 ^ 4 * ℓ ^ 2 := by
      rw [abs_div, abs_of_pos hl2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3),
        div_le_iff₀ hl2]
      have h1 : 3 * |ρ0 - 1| ≤ 3 * (R0 + 1) := by linarith
      have h2 : 3 * (R0 + 1) = 3 * (R0 + 1) / ℓ0 ^ 4 * ℓ0 ^ 4 := by field_simp
      have h3 : 3 * (R0 + 1) / ℓ0 ^ 4 * ℓ0 ^ 4 ≤ 3 * (R0 + 1) / ℓ0 ^ 4 * ℓ ^ 4 :=
        mul_le_mul_of_nonneg_left hl4 (by positivity)
      have h4 : 3 * (R0 + 1) / ℓ0 ^ 4 * ℓ ^ 2 * ℓ ^ 2 = 3 * (R0 + 1) / ℓ0 ^ 4 * ℓ ^ 4 := by ring
      linarith
    have t1b : |K| ≤ L / a / ℓ0 ^ 2 * ℓ ^ 2 := by
      have h2 : L / a = L / a / ℓ0 ^ 2 * ℓ0 ^ 2 := by field_simp
      have h3 : L / a / ℓ0 ^ 2 * ℓ0 ^ 2 ≤ L / a / ℓ0 ^ 2 * ℓ ^ 2 :=
        mul_le_mul_of_nonneg_left hl2' (by positivity)
      linarith
    have hsum : |3 * (ρ0 - 1) / ℓ ^ 2 - K| ≤ C2 * ℓ ^ 2 := by
      have := abs_sub (3 * (ρ0 - 1) / ℓ ^ 2) K
      simp only [hC2]
      linarith [add_mul (3 * (R0 + 1) / ℓ0 ^ 4) (L / a / ℓ0 ^ 2) (ℓ ^ 2)]
    have hmax : C2 * ℓ ^ 2 ≤ max (3 * C) C2 * ℓ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hl2.le
    rw [e]
    have := abs_add_le (3 * (ρ0 - 1) / ℓ ^ 2 - K) (3 * (ρ - ρ0) / ℓ ^ 2)
    linarith

end TimeAppendix12

namespace VarianceTwo

open PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance3 VarianceOne

/-! # A94: `prop:variance` (Appendix G) for `k = 2` on the flat torus with the heat kernel

Setting as in `VarianceOne`: independent uniform points `X_0, …, X_{N-1}` on `FlatTorus d`,
kernel `p = pker d σ` (periodised Gaussian of variance `σ = ξ²`), self-loops, `P` the normalised
walk (`torusWalk`), `m_j = torusM d σ j`, `cv μ f = E (f - E f)²`, `B = m₁²`.

Structure (built on `VarianceOne`, `BiasVariance2.trace_two_expansion`):
* Part 1 (`cv_sum_le`, `tstat_var`): a tuple statistic degenerate in three coordinates has
  variance `≤ 10 n⁶ ‖F‖²/N³`.
* Part 2 (`WK`, `wIter`, `wk_of`): the family `w_j = 𝒫ʲ w̃`, `w̃ = p² - m₂`, as iterated
  convolutions with `c = p - 1`; the hypotheses `WK` are discharged on the torus (`torus_wk`).
* Parts 3, 4 (`TA1 …`, `rem2`, `Rem2_var`, `LinW_decomp`): the path statistics with one
  `w̃`-edge are `N⁻² ∑_{i,j} Φ(X_i - X_j)` (`Φ = (1 - 𝒫)⁴ w̃`, `phiW`) plus a remainder of
  variance `O(B¹⁰/N³)`, by telescoping into pieces degenerate in three coordinates.
* Part 5 (`alg1`, `alg2`): the polynomial of `trace_two_expansion` as the linear statistic
  `Q_lin,2 = m₂(1 + 2L) + LinW` plus products of averages.
* Part 6 (`psi2`, `U2`, `Qlin2`, `Qlin2_decomp`, `Rem_total_var`, `v2`): the pair kernel
  `Ψ₂ = psi2 = (1 - 𝒫)⁴ p² - 2 m₂ (1 - 𝒫)³ p = H₂/2`, `U₂ = N⁻² ∑_{i≠j} Ψ₂(X_i - X_j)
  = (1/(2N²)) ∑_{i≠j} H₂(X_i - X_j)`, `v₂ = ½ ∫ H₂² = 2 ∫ Ψ₂²`; `Q_lin,2 = const + U₂ + R`
  with `Var R ≤ 34629061120 B¹⁰/N³`.
* Part 7 (`trace2_bounds`): pointwise bounds for `Tr P² - Q_lin,2` on the events
  `max|ε| ≤ D` (`D ≤ 1/8`) and a crude bound `N + 83 B⁵` otherwise.
* Part 8 (`trace2_sq`, `variance_two_general`, `variance_two`, `variance_two_sqrt`):
  `Var U₂ = v₂ (N-1)/N³` exactly, `Var(Tr P² - U₂) ≤ varRem2`, and
  `|Var Tr P² - v₂ (N-1)/N³| ≤ θ v₂ (N-1)/N³ + (1 + 1/θ) varRem2` for every `θ > 0`.

Deviations from the paper as for `k = 1` (`VarianceOne`): remainder with `(log N)²`
(`O((log N)² N^{-5/2})` with `θ = N^{-1/2}`), main term `v₂ (N-1)/N³`, no Hoeffding decomposition
as such, the probability of `max|ε| > 1/8` explicit, constants explicit and very large
(polynomial of degree 20 in `m₁`).  NOT proved: `k ≥ 3`, the graph without self-loops, the
remainder without the logarithm.  No hypothesis beyond the sample assumptions in the final
theorems. -/


/-! ## Part 1: general structure -/

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `Var(∑_{i ∈ s} f_i) ≤ |s| ∑_{i ∈ s} Var(f_i)`. -/
theorem cv_sum_le [IsProbabilityMeasure μ] {κ : Type*} (s : Finset κ) (f : κ → Ω → ℝ)
    (hf : ∀ i, BM (f i)) :
    cv μ (fun ω => ∑ i ∈ s, f i ω) ≤ s.card * ∑ i ∈ s, cv μ (f i) := by
  unfold cv
  have e : ∀ ω, (∑ i ∈ s, f i ω - ∫ ω', ∑ i ∈ s, f i ω' ∂μ) ^ 2
      = (∑ i ∈ s, (f i ω - ∫ ω', f i ω' ∂μ)) ^ 2 := fun ω => by
    rw [integral_finset_sum _ fun i _ => (hf i).integrable, Finset.sum_sub_distrib]
  simp_rw [e]
  have bc : ∀ i, BM (fun ω => f i ω - ∫ ω', f i ω' ∂μ) := fun i => bm_center (hf i)
  have hpt : ∀ ω, (∑ i ∈ s, (f i ω - ∫ ω', f i ω' ∂μ)) ^ 2
      ≤ s.card * ∑ i ∈ s, (f i ω - ∫ ω', f i ω' ∂μ) ^ 2 := fun ω => by
    have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ))
      (fun i => f i ω - ∫ ω', f i ω' ∂μ)
    simpa using h
  have i1 : Integrable (fun ω => (∑ i ∈ s, (f i ω - ∫ ω', f i ω' ∂μ)) ^ 2) μ :=
    (BM.sum s _ fun i _ => bc i).sqr.integrable
  have i2 : Integrable (fun ω => (s.card : ℝ) * ∑ i ∈ s, (f i ω - ∫ ω', f i ω' ∂μ) ^ 2) μ :=
    (BM.const_mul _ (BM.sum s _ fun i _ => (bc i).sqr)).integrable
  refine (integral_mono i1 i2 hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_finset_sum _ fun i _ => (bc i).sqr.integrable]

variable {G : Type*} [MeasurableSpace G] {ν : Measure G} {X : ℕ → Ω → G}

/-- **A tuple statistic that is degenerate in three coordinates has variance `O(N⁻³)`**:
    `Var(N⁻ⁿ ∑_ι F(X_ι)) ≤ 10 n⁶ ‖F‖² / N³` (all tuples, injective or not). -/
theorem tstat_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X) {N : ℕ}
    (hN : 0 < N) {n : ℕ} (hn : 3 ≤ n) (F : (Fin n → G) → ℝ) (hF : BM F) {BF : ℝ}
    (hFb : ∀ y, |F y| ≤ BF) (D : Finset (Fin n)) (hD : D.card = 3)
    (hdeg : ∀ v ∈ D, ∀ x, ∫ z, F (Function.update x v z) ∂ν = 0) :
    cv μ (fun ω => 1 / (N : ℝ) ^ n * sAll X N F ω) ≤ 10 * (n : ℝ) ^ 6 * BF ^ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := piece_le H N F hF hFb D hD hn hdeg
  have h2 := H.noninj_var_le N F hF hFb
  have h3 := cv_add_le (μ := μ) (H.sInj_bm N hF) (H.sNon_bm N hF)
  have e : sAll X N F = fun ω => sInj X N F ω + sNon X N F ω := funext (sAll_split X N F)
  rw [cv_const_mul, e]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = cv μ (sInj X N F) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = cv μ (sNon X N F) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = cv μ (fun ω => sInj X N F ω + sNon X N F ω) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (N : ℝ) ^ n := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hs] at h3
  rw [← ha, ← hq] at h1
  rw [← hb, ← hq] at h2
  rw [← hs, ← hq]
  have hq0 : 0 < q := by rw [hq]; positivity
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn36 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hn1 (by norm_num)
  have hB : 0 ≤ BF ^ 2 := _root_.sq_nonneg BF
  have hs3 : (N : ℝ) ^ 3 * s ≤ 10 * (n : ℝ) ^ 6 * q ^ 2 * BF ^ 2 := by
    have h4 := mul_le_mul_of_nonneg_left h3 hN3.le
    have h5 : (n : ℝ) ^ 3 * q ^ 2 * BF ^ 2 ≤ (n : ℝ) ^ 6 * q ^ 2 * BF ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn36 (by positivity)) hB
    linarith only [h4, h1, h2, h5]
  rw [le_div_iff₀ hN3]
  have e2 : (1 / q) ^ 2 * s * (N : ℝ) ^ 3 = ((N : ℝ) ^ 3 * s) / q ^ 2 := by field_simp
  rw [e2, div_le_iff₀ (by positivity)]
  linarith only [hs3]

omit [MeasurableSpace G] in
/-- `|N⁻ⁿ ∑_ι F(X_ι)| ≤ ‖F‖`. -/
theorem tstat_abs (X : ℕ → Ω → G) {N : ℕ} (hN : 0 < N) {n : ℕ} (F : (Fin n → G) → ℝ) {BF : ℝ}
    (hFb : ∀ y, |F y| ≤ BF) (ω : Ω) : |1 / (N : ℝ) ^ n * sAll X N F ω| ≤ BF := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := abs_sum_le_univ (fun ι : Fin n → Fin N => F (fun m => X (ι m) ω)) (C := BF)
    (fun ι => hFb _)
  rw [card_tuples] at h
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ n)]
  calc 1 / (N : ℝ) ^ n * |sAll X N F ω| ≤ 1 / (N : ℝ) ^ n * ((N : ℝ) ^ n * BF) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = BF := by field_simp

end General


/-! ## Part 2: a second family of kernels: iterated convolutions with `c = p - 1` -/

/-- HYPOTHESES on a kernel `c` and a family `w j` (`w 0 = w̃`, `w (j+1) = w j * c`): measurable,
    bounded by `B ≥ 1`, even, of mean zero, `∫ w_j(x - z) c(z - y) dν(z) = w_{j+1}(x - y)`. -/
structure WK {G : Type*} [AddCommGroup G] [MeasurableSpace G] (ν : Measure G)
    (c : G → ℝ) (w : ℕ → G → ℝ) (B : ℝ) : Prop where
  c_meas : Measurable c
  c_bound : ∀ u, |c u| ≤ B
  c_even : ∀ u, c (-u) = c u
  c_mean : ∀ x, ∫ z, c (x - z) ∂ν = 0
  meas : ∀ j, Measurable (w j)
  B_one : 1 ≤ B
  bound : ∀ j u, |w j u| ≤ B
  even : ∀ j u, w j (-u) = w j u
  mean : ∀ j x, ∫ z, w j (x - z) ∂ν = 0
  conv : ∀ j x y, ∫ z, w j (x - z) * c (z - y) ∂ν = w (j + 1) (x - y)

section Kernels

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G}
  {c : G → ℝ} {w : ℕ → G → ℝ} {k : ℕ → G → ℝ} {B : ℝ}

theorem WK.wR (W : WK ν c w B) (j : ℕ) (x : G) : BM (fun z : G => w j (x - z)) :=
  ⟨(W.meas j).comp (measurable_const.sub measurable_id), B, fun _ => W.bound j _⟩

theorem WK.wL (W : WK ν c w B) (j : ℕ) (y : G) : BM (fun z : G => w j (z - y)) :=
  ⟨(W.meas j).comp (measurable_id.sub measurable_const), B, fun _ => W.bound j _⟩

theorem WK.cR (W : WK ν c w B) (x : G) : BM (fun z : G => c (x - z)) :=
  ⟨W.c_meas.comp (measurable_const.sub measurable_id), B, fun _ => W.c_bound _⟩

theorem WK.cL (W : WK ν c w B) (y : G) : BM (fun z : G => c (z - y)) :=
  ⟨W.c_meas.comp (measurable_id.sub measurable_const), B, fun _ => W.c_bound _⟩

omit [MeasurableSub₂ G] in
theorem WK.wsym (W : WK ν c w B) (j : ℕ) (a b : G) : w j (a - b) = w j (b - a) := by
  rw [← neg_sub, W.even]

omit [MeasurableSub₂ G] in
theorem WK.csym (W : WK ν c w B) (a b : G) : c (a - b) = c (b - a) := by
  rw [← neg_sub, W.c_even]

omit [MeasurableSub₂ G] in
theorem WK.mean' (W : WK ν c w B) (j : ℕ) (x : G) : ∫ z, w j (z - x) ∂ν = 0 := by
  have e : ∀ z, w j (z - x) = w j (x - z) := fun z => W.wsym j z x
  simp_rw [e]; exact W.mean j x

omit [MeasurableSub₂ G] in
theorem WK.c_mean' (W : WK ν c w B) (x : G) : ∫ z, c (z - x) ∂ν = 0 := by
  have e : ∀ z, c (z - x) = c (x - z) := fun z => W.csym z x
  simp_rw [e]; exact W.c_mean x

theorem WK.deg_conv [IsProbabilityMeasure ν] (W : WK ν c w B) (j : ℕ) (x y : G) (C : ℝ) :
    ∫ z, (w j (x - z) * c (z - y) - w (j + 1) (x - y)) * C ∂ν = 0 := by
  rw [integral_mul_const,
    integral_sub ((W.wR j x).mul (W.cL y)).integrable (integrable_const _), W.conv,
    integral_const, probReal_univ, one_smul]
  ring

theorem WK.pw (W : WK ν c w B) {n : ℕ} (j : ℕ) (a b : Fin n) :
    BM (fun x : Fin n → G => w j (x a - x b)) :=
  ⟨(W.meas j).comp ((measurable_pi_apply a).sub (measurable_pi_apply b)), B,
    fun _ => W.bound j _⟩

theorem WK.pc (W : WK ν c w B) {n : ℕ} (a b : Fin n) :
    BM (fun x : Fin n → G => c (x a - x b)) :=
  ⟨W.c_meas.comp ((measurable_pi_apply a).sub (measurable_pi_apply b)), B,
    fun _ => W.c_bound _⟩

/-- The convolution `(f * c)(u) = ∫ f(z) c(u - z) dν(z)`. -/
noncomputable def cconv (ν : Measure G) (c f : G → ℝ) (u : G) : ℝ := ∫ z, f z * c (u - z) ∂ν

/-- The iterated convolutions `w̃ * c^{*j}`. -/
noncomputable def wIter (ν : Measure G) (c w0 : G → ℝ) : ℕ → G → ℝ
  | 0 => w0
  | j + 1 => cconv ν c (wIter ν c w0 j)

/-- One convolution with `c = p - 1` (`p ≥ 0`) preserves: measurable, bounded by `Bw`, even, mean
    zero. -/
theorem cconv_props [IsProbabilityMeasure ν] (V : VK ν k B) (hge : ∀ u, -1 ≤ k 0 u)
    {f : G → ℝ} {Bw : ℝ} (hm : Measurable f) (hb : ∀ u, |f u| ≤ Bw) (he : ∀ u, f (-u) = f u)
    (h0 : ∀ x, ∫ z, f (x - z) ∂ν = 0) :
    Measurable (cconv ν (k 0) f) ∧ (∀ u, |cconv ν (k 0) f u| ≤ Bw)
      ∧ (∀ u, cconv ν (k 0) f (-u) = cconv ν (k 0) f u)
      ∧ (∀ x, ∫ z, cconv ν (k 0) f (x - z) ∂ν = 0)
      ∧ ∀ x y, ∫ z, f (x - z) * k 0 (z - y) ∂ν = cconv ν (k 0) f (x - y) := by
  have hBw : 0 ≤ Bw := (abs_nonneg _).trans (hb 0)
  have hf0 : ∫ u, f u ∂ν = 0 := by rw [← V.inv f hm 0]; exact h0 0
  have bf : BM f := ⟨hm, Bw, hb⟩
  have hjm : Measurable (fun p : G × G => f p.2 * k 0 (p.1 - p.2)) :=
    (hm.comp measurable_snd).mul ((V.meas 0).comp (measurable_fst.sub measurable_snd))
  have hmc : Measurable (cconv ν (k 0) f) :=
    (hjm.stronglyMeasurable.integral_prod_right').measurable
  have hbd : ∀ u, |cconv ν (k 0) f u| ≤ Bw := by
    intro u
    have bq : BM (fun z : G => f z * (1 + k 0 (u - z))) :=
      bf.mul ((BM.const 1).add (V.bmR 0 u))
    have e : ∀ z, f z * k 0 (u - z) = f z * (1 + k 0 (u - z)) - f z := fun z => by ring
    unfold cconv
    simp_rw [e]
    rw [integral_sub bq.integrable bf.integrable, hf0, sub_zero]
    have bg : BM (fun z : G => Bw * (1 + k 0 (u - z))) :=
      BM.const_mul Bw ((BM.const 1).add (V.bmR 0 u))
    have h1 := abs_int_le_int (μ := ν) bq.integrable bg.integrable (fun z => by
      have hp : 0 ≤ 1 + k 0 (u - z) := by linarith only [hge (u - z)]
      rw [abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_right (hb z) hp)
    have h2 : ∫ z, Bw * (1 + k 0 (u - z)) ∂ν = Bw := by
      rw [integral_const_mul,
        integral_add (integrable_const (μ := ν) (1 : ℝ)) ((V.bmR 0 u).integrable (μ := ν)),
        integral_const, probReal_univ, one_smul, V.mean 0 u]
      ring
    rw [h2] at h1
    exact h1
  have hev : ∀ u, cconv ν (k 0) f (-u) = cconv ν (k 0) f u := by
    intro u
    have gm : Measurable (fun z : G => f z * k 0 (-u - z)) :=
      hm.mul ((V.meas 0).comp (measurable_const.sub measurable_id))
    have h := V.inv (fun z : G => f z * k 0 (-u - z)) gm 0
    have e : ∀ z : G, f (0 - z) * k 0 (-u - (0 - z)) = f z * k 0 (u - z) := fun z => by
      rw [zero_sub, he z, show -u - -z = -(u - z) by abel, V.even 0]
    simp_rw [e] at h
    unfold cconv
    exact h.symm
  have cmean' : ∀ z : G, ∫ u, k 0 (u - z) ∂ν = 0 := V.mean' 0
  have hmean : ∀ x, ∫ z, cconv ν (k 0) f (x - z) ∂ν = 0 := by
    intro x
    rw [V.inv (cconv ν (k 0) f) hmc x]
    unfold cconv
    have hint : Integrable (Function.uncurry fun u z : G => f z * k 0 (u - z)) (ν.prod ν) :=
      Integrable.of_bound hjm.aestronglyMeasurable (Bw * B)
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]
          exact abs_mul_le' (hb _) (V.bound 0 _))
    rw [integral_integral_swap hint]
    have e : ∀ z : G, ∫ u, f z * k 0 (u - z) ∂ν = 0 := fun z => by
      rw [integral_const_mul, cmean' z, mul_zero]
    simp_rw [e]
    exact integral_zero _ _
  refine ⟨hmc, hbd, hev, hmean, fun x y => ?_⟩
  have gm : Measurable (fun z : G => f z * k 0 (x - y - z)) :=
    hm.mul ((V.meas 0).comp (measurable_const.sub measurable_id))
  have h := V.inv (fun z : G => f z * k 0 (x - y - z)) gm x
  have e : ∀ z : G, f (x - z) * k 0 (x - y - (x - z)) = f (x - z) * k 0 (z - y) := fun z => by
    rw [show x - y - (x - z) = z - y by abel]
  simp_rw [e] at h
  unfold cconv
  exact h

/-- **The iterated convolutions satisfy `WK`.** -/
theorem wk_of [IsProbabilityMeasure ν] (V : VK ν k B) (hge : ∀ u, -1 ≤ k 0 u)
    {w0 : G → ℝ} {Bw : ℝ} (hBw : B ≤ Bw) (hm : Measurable w0) (hb : ∀ u, |w0 u| ≤ Bw)
    (he : ∀ u, w0 (-u) = w0 u) (h0 : ∀ x, ∫ z, w0 (x - z) ∂ν = 0) :
    WK ν (k 0) (wIter ν (k 0) w0) Bw := by
  have hall : ∀ j : ℕ, Measurable (wIter ν (k 0) w0 j) ∧ (∀ u, |wIter ν (k 0) w0 j u| ≤ Bw)
      ∧ (∀ u, wIter ν (k 0) w0 j (-u) = wIter ν (k 0) w0 j u)
      ∧ (∀ x, ∫ z, wIter ν (k 0) w0 j (x - z) ∂ν = 0) := by
    intro j
    induction j with
    | zero => exact ⟨hm, hb, he, h0⟩
    | succ j ih =>
      obtain ⟨a1, a2, a3, a4⟩ := ih
      obtain ⟨b1, b2, b3, b4, _⟩ := cconv_props V hge a1 a2 a3 a4
      exact ⟨b1, b2, b3, b4⟩
  exact
    { c_meas := V.meas 0
      c_bound := fun u => (V.bound 0 u).trans hBw
      c_even := V.even 0
      c_mean := V.mean 0
      meas := fun j => (hall j).1
      B_one := V.B_one.trans hBw
      bound := fun j => (hall j).2.1
      even := fun j => (hall j).2.2.1
      mean := fun j => (hall j).2.2.2
      conv := fun j x y => by
        obtain ⟨a1, a2, a3, a4⟩ := hall j
        exact (cconv_props V hge a1 a2 a3 a4).2.2.2.2 x y }

end Kernels


/-! ## Part 3: the tuple functions for `k = 2`: telescoping pieces and trees

Coordinates `0, 1` carry the edge `w̃(x₀ - x₁)` (`w̃ = p² - m₂`); the other edges are `c`-edges.
Every function below is degenerate in three coordinates. (Generated by a script.) -/

section Pieces

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G}
  {c : G → ℝ} {w : ℕ → G → ℝ} {B : ℝ}

theorem brB0 {a b d B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) (hd : |d| ≤ B) :
    |a * b - d| ≤ 2 * B ^ 5 :=
  (abs2 hB ha hb hd).trans (by
    have := pow_le_pow_right₀ hB (by norm_num : 2 ≤ 5); linarith only [this])

theorem brB1 {a b d t B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) (hd : |d| ≤ B)
    (ht : |t| ≤ B) : |(a * b - d) * t| ≤ 2 * B ^ 5 := by
  have h := abs_mul_le' (abs2 hB ha hb hd) ht
  have := pow_le_pow_right₀ hB (by norm_num : 3 ≤ 5)
  have e : 2 * B ^ 2 * B = 2 * B ^ 3 := by ring
  rw [e] at h; linarith only [h, this]

theorem brB2 {a b d t s B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) (hd : |d| ≤ B)
    (ht : |t| ≤ B) (hs : |s| ≤ B) : |(a * b - d) * t * s| ≤ 2 * B ^ 5 := by
  have h := abs_mul_le' (abs_mul_le' (abs2 hB ha hb hd) ht) hs
  have := pow_le_pow_right₀ hB (by norm_num : 4 ≤ 5)
  have e : 2 * B ^ 2 * B * B = 2 * B ^ 4 := by ring
  rw [e] at h; linarith only [h, this]

theorem brB3 {a b d t s r B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) (hd : |d| ≤ B)
    (ht : |t| ≤ B) (hs : |s| ≤ B) (hr : |r| ≤ B) : |(a * b - d) * t * s * r| ≤ 2 * B ^ 5 := by
  have h := abs_mul_le' (abs_mul_le' (abs_mul_le' (abs2 hB ha hb hd) ht) hs) hr
  have e : 2 * B ^ 2 * B * B * B = 2 * B ^ 5 := by ring
  rw [e] at h; exact h

theorem prB3 {a b d B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) (hd : |d| ≤ B) :
    |a * b * d| ≤ 2 * B ^ 5 := by
  have h := abs_mul_le' (abs_mul_le' ha hb) hd
  have := pow_le_pow_right₀ hB (by norm_num : 3 ≤ 5)
  have e : B * B * B = B ^ 3 := by ring
  have h0 : 0 ≤ B ^ 5 := by positivity
  rw [e] at h; linarith only [h, this, h0]

theorem prB4 {a b d t B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) (hd : |d| ≤ B)
    (ht : |t| ≤ B) : |a * b * d * t| ≤ 2 * B ^ 5 := by
  have h := abs_mul_le' (abs_mul_le' (abs_mul_le' ha hb) hd) ht
  have := pow_le_pow_right₀ hB (by norm_num : 4 ≤ 5)
  have e : B * B * B * B = B ^ 4 := by ring
  have h0 : 0 ≤ B ^ 5 := by positivity
  rw [e] at h; linarith only [h, this, h0]

theorem prB5 {a b d t s B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) (hd : |d| ≤ B)
    (ht : |t| ≤ B) (hs : |s| ≤ B) : |a * b * d * t * s| ≤ 2 * B ^ 5 := by
  have h := abs_mul_le' (abs_mul_le' (abs_mul_le' (abs_mul_le' ha hb) hd) ht) hs
  have e : B * B * B * B * B = B ^ 5 := by ring
  have h0 : 0 ≤ B ^ 5 := by positivity
  rw [e] at h; linarith only [h, h0]


def TA1 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 3 → G) : ℝ :=
  (w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2))

theorem WK.TA1_bm (W : WK ν c w B) : BM (TA1 c w) :=
  ((W.pw 0 1 0).mul (W.pc 0 2)).sub (W.pw 1 1 2)

omit [MeasurableSub₂ G] in
theorem WK.TA1_bd (W : WK ν c w B) (x : Fin 3 → G) : |TA1 c w x| ≤ 2 * B ^ 5 :=
  brB0 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _)

theorem WK.TA1_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({0, 1, 2} : Finset (Fin 3)), ∀ x, ∫ z, TA1 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TA1 c w (Function.update x 0 z)
        = (w 0 (x 1 - z) * c (z - x 2) - w (0 + 1) (x 1 - x 2)) * (1) := fun z => by
      simp [TA1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 0 _ _ _
  · have e : ∀ z, TA1 c w (Function.update x 1 z)
        = (c (x 0 - x 2) * (1)) * w 0 (z - x 0) + (-(1)) * w 1 (z - x 2) := fun z => by
      simp [TA1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 0 _) (W.wL 1 _) (W.mean' 0 _) (W.mean' 1 _) _ _
  · have e : ∀ z, TA1 c w (Function.update x 2 z)
        = (w 0 (x 1 - x 0) * (1)) * c (x 0 - z) + (-(1)) * w 1 (x 1 - z) := fun z => by
      simp [TA1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 1 _) (W.c_mean _) (W.mean 1 _) _ _

def TW1 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 4 → G) : ℝ :=
  (w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * c (x 2 - x 3)

theorem WK.TW1_bm (W : WK ν c w B) : BM (TW1 c w) :=
  (((W.pw 0 1 0).mul (W.pc 0 2)).sub (W.pw 1 1 2)).mul (W.pc 2 3)

omit [MeasurableSub₂ G] in
theorem WK.TW1_bd (W : WK ν c w B) (x : Fin 4 → G) : |TW1 c w x| ≤ 2 * B ^ 5 :=
  brB1 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _) (W.c_bound _)

theorem WK.TW1_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({0, 1, 3} : Finset (Fin 4)), ∀ x, ∫ z, TW1 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TW1 c w (Function.update x 0 z)
        = (w 0 (x 1 - z) * c (z - x 2) - w (0 + 1) (x 1 - x 2)) * (c (x 2 - x 3)) := fun z => by
      simp [TW1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 0 _ _ _
  · have e : ∀ z, TW1 c w (Function.update x 1 z)
        = (c (x 0 - x 2) * (c (x 2 - x 3))) * w 0 (z - x 0) + (-(c (x 2 - x 3))) * w 1 (z - x 2) := fun z => by
      simp [TW1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 0 _) (W.wL 1 _) (W.mean' 0 _) (W.mean' 1 _) _ _
  · have e : ∀ z, TW1 c w (Function.update x 3 z)
        = ((w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * (1)) * c (x 2 - z) + 0 * c (x 2 - z) := fun z => by
      simp [TW1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def TW2 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 4 → G) : ℝ :=
  (w 1 (x 1 - x 2) * c (x 2 - x 3) - w 2 (x 1 - x 3))

theorem WK.TW2_bm (W : WK ν c w B) : BM (TW2 c w) :=
  ((W.pw 1 1 2).mul (W.pc 2 3)).sub (W.pw 2 1 3)

omit [MeasurableSub₂ G] in
theorem WK.TW2_bd (W : WK ν c w B) (x : Fin 4 → G) : |TW2 c w x| ≤ 2 * B ^ 5 :=
  brB0 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _)

theorem WK.TW2_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({2, 1, 3} : Finset (Fin 4)), ∀ x, ∫ z, TW2 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TW2 c w (Function.update x 2 z)
        = (w 1 (x 1 - z) * c (z - x 3) - w (1 + 1) (x 1 - x 3)) * (1) := fun z => by
      simp [TW2] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 1 _ _ _
  · have e : ∀ z, TW2 c w (Function.update x 1 z)
        = (c (x 2 - x 3) * (1)) * w 1 (z - x 2) + (-(1)) * w 2 (z - x 3) := fun z => by
      simp [TW2] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 1 _) (W.wL 2 _) (W.mean' 1 _) (W.mean' 2 _) _ _
  · have e : ∀ z, TW2 c w (Function.update x 3 z)
        = (w 1 (x 1 - x 2) * (1)) * c (x 2 - z) + (-(1)) * w 2 (x 1 - z) := fun z => by
      simp [TW2] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 2 _) (W.c_mean _) (W.mean 2 _) _ _

def TF11 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 4 → G) : ℝ :=
  (w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * c (x 1 - x 3)

theorem WK.TF11_bm (W : WK ν c w B) : BM (TF11 c w) :=
  (((W.pw 0 1 0).mul (W.pc 0 2)).sub (W.pw 1 1 2)).mul (W.pc 1 3)

omit [MeasurableSub₂ G] in
theorem WK.TF11_bd (W : WK ν c w B) (x : Fin 4 → G) : |TF11 c w x| ≤ 2 * B ^ 5 :=
  brB1 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _) (W.c_bound _)

theorem WK.TF11_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({0, 2, 3} : Finset (Fin 4)), ∀ x, ∫ z, TF11 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF11 c w (Function.update x 0 z)
        = (w 0 (x 1 - z) * c (z - x 2) - w (0 + 1) (x 1 - x 2)) * (c (x 1 - x 3)) := fun z => by
      simp [TF11] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 0 _ _ _
  · have e : ∀ z, TF11 c w (Function.update x 2 z)
        = (w 0 (x 1 - x 0) * (c (x 1 - x 3))) * c (x 0 - z) + (-(c (x 1 - x 3))) * w 1 (x 1 - z) := fun z => by
      simp [TF11] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 1 _) (W.c_mean _) (W.mean 1 _) _ _
  · have e : ∀ z, TF11 c w (Function.update x 3 z)
        = ((w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * (1)) * c (x 1 - z) + 0 * c (x 1 - z) := fun z => by
      simp [TF11] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def TF12 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 4 → G) : ℝ :=
  (w 1 (x 2 - x 1) * c (x 1 - x 3) - w 2 (x 2 - x 3))

theorem WK.TF12_bm (W : WK ν c w B) : BM (TF12 c w) :=
  ((W.pw 1 2 1).mul (W.pc 1 3)).sub (W.pw 2 2 3)

omit [MeasurableSub₂ G] in
theorem WK.TF12_bd (W : WK ν c w B) (x : Fin 4 → G) : |TF12 c w x| ≤ 2 * B ^ 5 :=
  brB0 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _)

theorem WK.TF12_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)), ∀ x, ∫ z, TF12 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF12 c w (Function.update x 1 z)
        = (w 1 (x 2 - z) * c (z - x 3) - w (1 + 1) (x 2 - x 3)) * (1) := fun z => by
      simp [TF12] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 1 _ _ _
  · have e : ∀ z, TF12 c w (Function.update x 2 z)
        = (c (x 1 - x 3) * (1)) * w 1 (z - x 1) + (-(1)) * w 2 (z - x 3) := fun z => by
      simp [TF12] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 1 _) (W.wL 2 _) (W.mean' 1 _) (W.mean' 2 _) _ _
  · have e : ∀ z, TF12 c w (Function.update x 3 z)
        = (w 1 (x 2 - x 1) * (1)) * c (x 1 - z) + (-(1)) * w 2 (x 2 - z) := fun z => by
      simp [TF12] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 2 _) (W.c_mean _) (W.mean 2 _) _ _

def TF21 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 5 → G) : ℝ :=
  (w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * c (x 1 - x 3) * c (x 3 - x 4)

theorem WK.TF21_bm (W : WK ν c w B) : BM (TF21 c w) :=
  ((((W.pw 0 1 0).mul (W.pc 0 2)).sub (W.pw 1 1 2)).mul (W.pc 1 3)).mul (W.pc 3 4)

omit [MeasurableSub₂ G] in
theorem WK.TF21_bd (W : WK ν c w B) (x : Fin 5 → G) : |TF21 c w x| ≤ 2 * B ^ 5 :=
  brB2 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _) (W.c_bound _) (W.c_bound _)

theorem WK.TF21_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({0, 2, 4} : Finset (Fin 5)), ∀ x, ∫ z, TF21 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF21 c w (Function.update x 0 z)
        = (w 0 (x 1 - z) * c (z - x 2) - w (0 + 1) (x 1 - x 2)) * (c (x 1 - x 3) * c (x 3 - x 4)) := fun z => by
      simp [TF21] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 0 _ _ _
  · have e : ∀ z, TF21 c w (Function.update x 2 z)
        = (w 0 (x 1 - x 0) * (c (x 1 - x 3) * c (x 3 - x 4))) * c (x 0 - z) + (-(c (x 1 - x 3) * c (x 3 - x 4))) * w 1 (x 1 - z) := fun z => by
      simp [TF21] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 1 _) (W.c_mean _) (W.mean 1 _) _ _
  · have e : ∀ z, TF21 c w (Function.update x 4 z)
        = ((w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * (c (x 1 - x 3))) * c (x 3 - z) + 0 * c (x 3 - z) := fun z => by
      simp [TF21] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def TF22 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 5 → G) : ℝ :=
  (w 1 (x 2 - x 1) * c (x 1 - x 3) - w 2 (x 2 - x 3)) * c (x 3 - x 4)

theorem WK.TF22_bm (W : WK ν c w B) : BM (TF22 c w) :=
  (((W.pw 1 2 1).mul (W.pc 1 3)).sub (W.pw 2 2 3)).mul (W.pc 3 4)

omit [MeasurableSub₂ G] in
theorem WK.TF22_bd (W : WK ν c w B) (x : Fin 5 → G) : |TF22 c w x| ≤ 2 * B ^ 5 :=
  brB1 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _) (W.c_bound _)

theorem WK.TF22_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({1, 2, 4} : Finset (Fin 5)), ∀ x, ∫ z, TF22 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF22 c w (Function.update x 1 z)
        = (w 1 (x 2 - z) * c (z - x 3) - w (1 + 1) (x 2 - x 3)) * (c (x 3 - x 4)) := fun z => by
      simp [TF22] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 1 _ _ _
  · have e : ∀ z, TF22 c w (Function.update x 2 z)
        = (c (x 1 - x 3) * (c (x 3 - x 4))) * w 1 (z - x 1) + (-(c (x 3 - x 4))) * w 2 (z - x 3) := fun z => by
      simp [TF22] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 1 _) (W.wL 2 _) (W.mean' 1 _) (W.mean' 2 _) _ _
  · have e : ∀ z, TF22 c w (Function.update x 4 z)
        = ((w 1 (x 2 - x 1) * c (x 1 - x 3) - w 2 (x 2 - x 3)) * (1)) * c (x 3 - z) + 0 * c (x 3 - z) := fun z => by
      simp [TF22] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def TF23 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 5 → G) : ℝ :=
  (w 2 (x 2 - x 3) * c (x 3 - x 4) - w 3 (x 2 - x 4))

theorem WK.TF23_bm (W : WK ν c w B) : BM (TF23 c w) :=
  ((W.pw 2 2 3).mul (W.pc 3 4)).sub (W.pw 3 2 4)

omit [MeasurableSub₂ G] in
theorem WK.TF23_bd (W : WK ν c w B) (x : Fin 5 → G) : |TF23 c w x| ≤ 2 * B ^ 5 :=
  brB0 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _)

theorem WK.TF23_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({3, 2, 4} : Finset (Fin 5)), ∀ x, ∫ z, TF23 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF23 c w (Function.update x 3 z)
        = (w 2 (x 2 - z) * c (z - x 4) - w (2 + 1) (x 2 - x 4)) * (1) := fun z => by
      simp [TF23] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 2 _ _ _
  · have e : ∀ z, TF23 c w (Function.update x 2 z)
        = (c (x 3 - x 4) * (1)) * w 2 (z - x 3) + (-(1)) * w 3 (z - x 4) := fun z => by
      simp [TF23] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 2 _) (W.wL 3 _) (W.mean' 2 _) (W.mean' 3 _) _ _
  · have e : ∀ z, TF23 c w (Function.update x 4 z)
        = (w 2 (x 2 - x 3) * (1)) * c (x 3 - z) + (-(1)) * w 3 (x 2 - z) := fun z => by
      simp [TF23] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 3 _) (W.c_mean _) (W.mean 3 _) _ _

def TF31 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 6 → G) : ℝ :=
  (w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * c (x 2 - x 3) * c (x 1 - x 4) * c (x 4 - x 5)

theorem WK.TF31_bm (W : WK ν c w B) : BM (TF31 c w) :=
  (((((W.pw 0 1 0).mul (W.pc 0 2)).sub (W.pw 1 1 2)).mul (W.pc 2 3)).mul (W.pc 1 4)).mul (W.pc 4 5)

omit [MeasurableSub₂ G] in
theorem WK.TF31_bd (W : WK ν c w B) (x : Fin 6 → G) : |TF31 c w x| ≤ 2 * B ^ 5 :=
  brB3 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _) (W.c_bound _) (W.c_bound _) (W.c_bound _)

theorem WK.TF31_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({0, 3, 5} : Finset (Fin 6)), ∀ x, ∫ z, TF31 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF31 c w (Function.update x 0 z)
        = (w 0 (x 1 - z) * c (z - x 2) - w (0 + 1) (x 1 - x 2)) * (c (x 2 - x 3) * c (x 1 - x 4) * c (x 4 - x 5)) := fun z => by
      simp [TF31] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 0 _ _ _
  · have e : ∀ z, TF31 c w (Function.update x 3 z)
        = ((w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * (c (x 1 - x 4) * c (x 4 - x 5))) * c (x 2 - z) + 0 * c (x 2 - z) := fun z => by
      simp [TF31] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _
  · have e : ∀ z, TF31 c w (Function.update x 5 z)
        = ((w 0 (x 1 - x 0) * c (x 0 - x 2) - w 1 (x 1 - x 2)) * (c (x 2 - x 3) * c (x 1 - x 4))) * c (x 4 - z) + 0 * c (x 4 - z) := fun z => by
      simp [TF31] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def TF32 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 6 → G) : ℝ :=
  (w 1 (x 1 - x 2) * c (x 2 - x 3) - w 2 (x 1 - x 3)) * c (x 1 - x 4) * c (x 4 - x 5)

theorem WK.TF32_bm (W : WK ν c w B) : BM (TF32 c w) :=
  ((((W.pw 1 1 2).mul (W.pc 2 3)).sub (W.pw 2 1 3)).mul (W.pc 1 4)).mul (W.pc 4 5)

omit [MeasurableSub₂ G] in
theorem WK.TF32_bd (W : WK ν c w B) (x : Fin 6 → G) : |TF32 c w x| ≤ 2 * B ^ 5 :=
  brB2 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _) (W.c_bound _) (W.c_bound _)

theorem WK.TF32_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({2, 3, 5} : Finset (Fin 6)), ∀ x, ∫ z, TF32 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF32 c w (Function.update x 2 z)
        = (w 1 (x 1 - z) * c (z - x 3) - w (1 + 1) (x 1 - x 3)) * (c (x 1 - x 4) * c (x 4 - x 5)) := fun z => by
      simp [TF32] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 1 _ _ _
  · have e : ∀ z, TF32 c w (Function.update x 3 z)
        = (w 1 (x 1 - x 2) * (c (x 1 - x 4) * c (x 4 - x 5))) * c (x 2 - z) + (-(c (x 1 - x 4) * c (x 4 - x 5))) * w 2 (x 1 - z) := fun z => by
      simp [TF32] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 2 _) (W.c_mean _) (W.mean 2 _) _ _
  · have e : ∀ z, TF32 c w (Function.update x 5 z)
        = ((w 1 (x 1 - x 2) * c (x 2 - x 3) - w 2 (x 1 - x 3)) * (c (x 1 - x 4))) * c (x 4 - z) + 0 * c (x 4 - z) := fun z => by
      simp [TF32] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def TF33 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 6 → G) : ℝ :=
  (w 2 (x 3 - x 1) * c (x 1 - x 4) - w 3 (x 3 - x 4)) * c (x 4 - x 5)

theorem WK.TF33_bm (W : WK ν c w B) : BM (TF33 c w) :=
  (((W.pw 2 3 1).mul (W.pc 1 4)).sub (W.pw 3 3 4)).mul (W.pc 4 5)

omit [MeasurableSub₂ G] in
theorem WK.TF33_bd (W : WK ν c w B) (x : Fin 6 → G) : |TF33 c w x| ≤ 2 * B ^ 5 :=
  brB1 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _) (W.c_bound _)

theorem WK.TF33_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({1, 3, 5} : Finset (Fin 6)), ∀ x, ∫ z, TF33 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF33 c w (Function.update x 1 z)
        = (w 2 (x 3 - z) * c (z - x 4) - w (2 + 1) (x 3 - x 4)) * (c (x 4 - x 5)) := fun z => by
      simp [TF33] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 2 _ _ _
  · have e : ∀ z, TF33 c w (Function.update x 3 z)
        = (c (x 1 - x 4) * (c (x 4 - x 5))) * w 2 (z - x 1) + (-(c (x 4 - x 5))) * w 3 (z - x 4) := fun z => by
      simp [TF33] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 2 _) (W.wL 3 _) (W.mean' 2 _) (W.mean' 3 _) _ _
  · have e : ∀ z, TF33 c w (Function.update x 5 z)
        = ((w 2 (x 3 - x 1) * c (x 1 - x 4) - w 3 (x 3 - x 4)) * (1)) * c (x 4 - z) + 0 * c (x 4 - z) := fun z => by
      simp [TF33] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def TF34 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 6 → G) : ℝ :=
  (w 3 (x 3 - x 4) * c (x 4 - x 5) - w 4 (x 3 - x 5))

theorem WK.TF34_bm (W : WK ν c w B) : BM (TF34 c w) :=
  ((W.pw 3 3 4).mul (W.pc 4 5)).sub (W.pw 4 3 5)

omit [MeasurableSub₂ G] in
theorem WK.TF34_bd (W : WK ν c w B) (x : Fin 6 → G) : |TF34 c w x| ≤ 2 * B ^ 5 :=
  brB0 W.B_one (W.bound _ _) (W.c_bound _) (W.bound _ _)

theorem WK.TF34_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({4, 3, 5} : Finset (Fin 6)), ∀ x, ∫ z, TF34 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, TF34 c w (Function.update x 4 z)
        = (w 3 (x 3 - z) * c (z - x 5) - w (3 + 1) (x 3 - x 5)) * (1) := fun z => by
      simp [TF34] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact W.deg_conv 3 _ _ _
  · have e : ∀ z, TF34 c w (Function.update x 3 z)
        = (c (x 4 - x 5) * (1)) * w 3 (z - x 4) + (-(1)) * w 4 (z - x 5) := fun z => by
      simp [TF34] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wL 3 _) (W.wL 4 _) (W.mean' 3 _) (W.mean' 4 _) _ _
  · have e : ∀ z, TF34 c w (Function.update x 5 z)
        = (w 3 (x 3 - x 4) * (1)) * c (x 4 - z) + (-(1)) * w 4 (x 3 - z) := fun z => by
      simp [TF34] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.wR 4 _) (W.c_mean _) (W.mean 4 _) _ _

def PE1 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 4 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 0 - x 3)

theorem WK.PE1_bm (W : WK ν c w B) : BM (PE1 c w) :=
  (((W.pw 0 0 1)).mul (W.pc 0 2)).mul (W.pc 0 3)

omit [MeasurableSub₂ G] in
theorem WK.PE1_bd (W : WK ν c w B) (x : Fin 4 → G) : |PE1 c w x| ≤ 2 * B ^ 5 :=
  prB3 W.B_one (W.bound _ _) (W.c_bound _) (W.c_bound _)

theorem WK.PE1_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)), ∀ x, ∫ z, PE1 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, PE1 c w (Function.update x 1 z)
        = (c (x 0 - x 2) * c (x 0 - x 3)) * w 0 (x 0 - z) + 0 * w 0 (x 0 - z) := fun z => by
      simp [PE1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wR 0 _) (W.wR 0 _) (W.mean 0 _) (W.mean 0 _) _ _
  · have e : ∀ z, PE1 c w (Function.update x 2 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 3)) * c (x 0 - z) + 0 * c (x 0 - z) := fun z => by
      simp [PE1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _
  · have e : ∀ z, PE1 c w (Function.update x 3 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 2)) * c (x 0 - z) + 0 * c (x 0 - z) := fun z => by
      simp [PE1] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def PE2 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 5 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 0 - x 3) * c (x 3 - x 4)

theorem WK.PE2_bm (W : WK ν c w B) : BM (PE2 c w) :=
  ((((W.pw 0 0 1)).mul (W.pc 0 2)).mul (W.pc 0 3)).mul (W.pc 3 4)

omit [MeasurableSub₂ G] in
theorem WK.PE2_bd (W : WK ν c w B) (x : Fin 5 → G) : |PE2 c w x| ≤ 2 * B ^ 5 :=
  prB4 W.B_one (W.bound _ _) (W.c_bound _) (W.c_bound _) (W.c_bound _)

theorem WK.PE2_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({1, 2, 4} : Finset (Fin 5)), ∀ x, ∫ z, PE2 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, PE2 c w (Function.update x 1 z)
        = (c (x 0 - x 2) * c (x 0 - x 3) * c (x 3 - x 4)) * w 0 (x 0 - z) + 0 * w 0 (x 0 - z) := fun z => by
      simp [PE2] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wR 0 _) (W.wR 0 _) (W.mean 0 _) (W.mean 0 _) _ _
  · have e : ∀ z, PE2 c w (Function.update x 2 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 3) * c (x 3 - x 4)) * c (x 0 - z) + 0 * c (x 0 - z) := fun z => by
      simp [PE2] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _
  · have e : ∀ z, PE2 c w (Function.update x 4 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 0 - x 3)) * c (x 3 - z) + 0 * c (x 3 - z) := fun z => by
      simp [PE2] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def PE3 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 6 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 2 - x 3) * c (x 0 - x 4) * c (x 4 - x 5)

theorem WK.PE3_bm (W : WK ν c w B) : BM (PE3 c w) :=
  (((((W.pw 0 0 1)).mul (W.pc 0 2)).mul (W.pc 2 3)).mul (W.pc 0 4)).mul (W.pc 4 5)

omit [MeasurableSub₂ G] in
theorem WK.PE3_bd (W : WK ν c w B) (x : Fin 6 → G) : |PE3 c w x| ≤ 2 * B ^ 5 :=
  prB5 W.B_one (W.bound _ _) (W.c_bound _) (W.c_bound _) (W.c_bound _) (W.c_bound _)

theorem WK.PE3_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({1, 3, 5} : Finset (Fin 6)), ∀ x, ∫ z, PE3 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, PE3 c w (Function.update x 1 z)
        = (c (x 0 - x 2) * c (x 2 - x 3) * c (x 0 - x 4) * c (x 4 - x 5)) * w 0 (x 0 - z) + 0 * w 0 (x 0 - z) := fun z => by
      simp [PE3] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wR 0 _) (W.wR 0 _) (W.mean 0 _) (W.mean 0 _) _ _
  · have e : ∀ z, PE3 c w (Function.update x 3 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 0 - x 4) * c (x 4 - x 5)) * c (x 2 - z) + 0 * c (x 2 - z) := fun z => by
      simp [PE3] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _
  · have e : ∀ z, PE3 c w (Function.update x 5 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 2 - x 3) * c (x 0 - x 4)) * c (x 4 - z) + 0 * c (x 4 - z) := fun z => by
      simp [PE3] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

def PE4 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 5 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 2 - x 3) * c (x 2 - x 4)

theorem WK.PE4_bm (W : WK ν c w B) : BM (PE4 c w) :=
  ((((W.pw 0 0 1)).mul (W.pc 0 2)).mul (W.pc 2 3)).mul (W.pc 2 4)

omit [MeasurableSub₂ G] in
theorem WK.PE4_bd (W : WK ν c w B) (x : Fin 5 → G) : |PE4 c w x| ≤ 2 * B ^ 5 :=
  prB4 W.B_one (W.bound _ _) (W.c_bound _) (W.c_bound _) (W.c_bound _)

theorem WK.PE4_deg [IsProbabilityMeasure ν] (W : WK ν c w B) :
    ∀ v ∈ ({1, 3, 4} : Finset (Fin 5)), ∀ x, ∫ z, PE4 c w (Function.update x v z) ∂ν = 0 := by
  intro v hv x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · have e : ∀ z, PE4 c w (Function.update x 1 z)
        = (c (x 0 - x 2) * c (x 2 - x 3) * c (x 2 - x 4)) * w 0 (x 0 - z) + 0 * w 0 (x 0 - z) := fun z => by
      simp [PE4] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.wR 0 _) (W.wR 0 _) (W.mean 0 _) (W.mean 0 _) _ _
  · have e : ∀ z, PE4 c w (Function.update x 3 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 2 - x 4)) * c (x 2 - z) + 0 * c (x 2 - z) := fun z => by
      simp [PE4] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _
  · have e : ∀ z, PE4 c w (Function.update x 4 z)
        = (w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 2 - x 3)) * c (x 2 - z) + 0 * c (x 2 - z) := fun z => by
      simp [PE4] <;> first | ring1 | (ring_nf; simp) | simp
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact deg_mean2 (W.cR _) (W.cR _) (W.c_mean _) (W.c_mean _) _ _

theorem unif6 {n : ℕ} (hn : n ≤ 6) {x B N : ℝ} (hN : 0 < N)
    (h : x ≤ 10 * (n : ℝ) ^ 6 * (2 * B ^ 5) ^ 2 / N ^ 3) : x ≤ 1866240 * B ^ 10 / N ^ 3 := by
  have h1 : (n : ℝ) ^ 6 ≤ (6 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast hn) 6
  have h2 : 10 * (n : ℝ) ^ 6 * (2 * B ^ 5) ^ 2 ≤ 1866240 * B ^ 10 := by
    have hb : 0 ≤ (2 * B ^ 5) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right h1 hb
    nlinarith only [this]
  exact h.trans (div_le_div_of_nonneg_right h2 (by positivity))

end Pieces

section PieceVar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G}
  {c : G → ℝ} {w : ℕ → G → ℝ} {B : ℝ}

theorem WK.TA1_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 3 * sAll X N (TA1 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 3 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TA1 c w) W.TA1_bm W.TA1_bd
      ({0, 1, 2} : Finset (Fin _)) (by decide) W.TA1_deg))

theorem WK.TW1_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 4 * sAll X N (TW1 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 4 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TW1 c w) W.TW1_bm W.TW1_bd
      ({0, 1, 3} : Finset (Fin _)) (by decide) W.TW1_deg))

theorem WK.TW2_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 4 * sAll X N (TW2 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 4 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TW2 c w) W.TW2_bm W.TW2_bd
      ({2, 1, 3} : Finset (Fin _)) (by decide) W.TW2_deg))

theorem WK.TF11_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 4 * sAll X N (TF11 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 4 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF11 c w) W.TF11_bm W.TF11_bd
      ({0, 2, 3} : Finset (Fin _)) (by decide) W.TF11_deg))

theorem WK.TF12_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 4 * sAll X N (TF12 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 4 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF12 c w) W.TF12_bm W.TF12_bd
      ({1, 2, 3} : Finset (Fin _)) (by decide) W.TF12_deg))

theorem WK.TF21_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 5 * sAll X N (TF21 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 5 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF21 c w) W.TF21_bm W.TF21_bd
      ({0, 2, 4} : Finset (Fin _)) (by decide) W.TF21_deg))

theorem WK.TF22_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 5 * sAll X N (TF22 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 5 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF22 c w) W.TF22_bm W.TF22_bd
      ({1, 2, 4} : Finset (Fin _)) (by decide) W.TF22_deg))

theorem WK.TF23_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 5 * sAll X N (TF23 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 5 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF23 c w) W.TF23_bm W.TF23_bd
      ({3, 2, 4} : Finset (Fin _)) (by decide) W.TF23_deg))

theorem WK.TF31_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 6 * sAll X N (TF31 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 6 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF31 c w) W.TF31_bm W.TF31_bd
      ({0, 3, 5} : Finset (Fin _)) (by decide) W.TF31_deg))

theorem WK.TF32_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 6 * sAll X N (TF32 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 6 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF32 c w) W.TF32_bm W.TF32_bd
      ({2, 3, 5} : Finset (Fin _)) (by decide) W.TF32_deg))

theorem WK.TF33_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 6 * sAll X N (TF33 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 6 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF33 c w) W.TF33_bm W.TF33_bd
      ({1, 3, 5} : Finset (Fin _)) (by decide) W.TF33_deg))

theorem WK.TF34_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 6 * sAll X N (TF34 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 6 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (TF34 c w) W.TF34_bm W.TF34_bd
      ({4, 3, 5} : Finset (Fin _)) (by decide) W.TF34_deg))

theorem WK.PE1_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 4 * sAll X N (PE1 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 4 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (PE1 c w) W.PE1_bm W.PE1_bd
      ({1, 2, 3} : Finset (Fin _)) (by decide) W.PE1_deg))

theorem WK.PE2_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 5 * sAll X N (PE2 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 5 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (PE2 c w) W.PE2_bm W.PE2_bd
      ({1, 2, 4} : Finset (Fin _)) (by decide) W.PE2_deg))

theorem WK.PE3_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 6 * sAll X N (PE3 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 6 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (PE3 c w) W.PE3_bm W.PE3_bd
      ({1, 3, 5} : Finset (Fin _)) (by decide) W.PE3_deg))

theorem WK.PE4_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    cv μ (fun ω => 1 / (N : ℝ) ^ 5 * sAll X N (PE4 c w) ω) ≤ 1866240 * B ^ 10 / (N : ℝ) ^ 3 :=
  unif6 (by norm_num : 5 ≤ 6) (by exact_mod_cast hN)
    (by simpa using (tstat_var H hN (by norm_num) (PE4 c w) W.PE4_bm W.PE4_bd
      ({1, 3, 4} : Finset (Fin _)) (by decide) W.PE4_deg))

end PieceVar


/-! ## Part 4: the path statistics with one `w̃`-edge, their pair projections, and the remainder -/

section Paths2

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G}
  {c : G → ℝ} {w : ℕ → G → ℝ} {B : ℝ}

/-- `w̃(x₀ - x₁)`. -/
def PZ (w : ℕ → G → ℝ) (x : Fin 2 → G) : ℝ := w 0 (x 0 - x 1)
/-- path `1 - 0 - 2` (`w̃, c`). -/
def PA (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 3 → G) : ℝ := w 0 (x 0 - x 1) * c (x 0 - x 2)
/-- path `1 - 0 - 2 - 3` (`w̃, c, c`). -/
def PW (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 4 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 2 - x 3)
/-- path `2 - 0 - 1 - 3` (`c, w̃, c`). -/
def PF1 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 4 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 1 - x 3)
/-- path `2 - 0 - 1 - 3 - 4` (`c, w̃, c, c`). -/
def PF2 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 5 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 1 - x 3) * c (x 3 - x 4)
/-- path `3 - 2 - 0 - 1 - 4 - 5` (`c, c, w̃, c, c`). -/
def PF3 (c : G → ℝ) (w : ℕ → G → ℝ) (x : Fin 6 → G) : ℝ :=
  w 0 (x 0 - x 1) * c (x 0 - x 2) * c (x 2 - x 3) * c (x 1 - x 4) * c (x 4 - x 5)

omit [MeasurableSub₂ G] in
theorem WK.PA_split (W : WK ν c w B) (x : Fin 3 → G) :
    PA c w x = w 1 (x 1 - x 2) + TA1 c w x := by
  unfold PA TA1; rw [W.wsym 0 (x 0) (x 1)]; ring

omit [MeasurableSub₂ G] in
theorem WK.PW_split (W : WK ν c w B) (x : Fin 4 → G) :
    PW c w x = w 2 (x 1 - x 3) + (TW1 c w x + TW2 c w x) := by
  unfold PW TW1 TW2; rw [W.wsym 0 (x 0) (x 1)]; ring

omit [MeasurableSub₂ G] in
theorem WK.PF1_split (W : WK ν c w B) (x : Fin 4 → G) :
    PF1 c w x = w 2 (x 2 - x 3) + (TF11 c w x + TF12 c w x) := by
  unfold PF1 TF11 TF12; rw [W.wsym 0 (x 0) (x 1), W.wsym 1 (x 2) (x 1)]; ring

omit [MeasurableSub₂ G] in
theorem WK.PF2_split (W : WK ν c w B) (x : Fin 5 → G) :
    PF2 c w x = w 3 (x 2 - x 4) + (TF21 c w x + TF22 c w x + TF23 c w x) := by
  unfold PF2 TF21 TF22 TF23; rw [W.wsym 0 (x 0) (x 1), W.wsym 1 (x 2) (x 1)]; ring

omit [MeasurableSub₂ G] in
theorem WK.PF3_split (W : WK ν c w B) (x : Fin 6 → G) :
    PF3 c w x = w 4 (x 3 - x 5) + (TF31 c w x + TF32 c w x + TF33 c w x + TF34 c w x) := by
  unfold PF3 TF31 TF32 TF33 TF34; rw [W.wsym 0 (x 0) (x 1), W.wsym 2 (x 3) (x 1)]; ring

end Paths2

section Stat2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G}
  {c : G → ℝ} {w : ℕ → G → ℝ} {B : ℝ}

theorem sum_fin6 {α : Type*} [Fintype α] (g : (Fin 6 → α) → ℝ) :
    ∑ ι : Fin 6 → α, g ι
      = ∑ i : α, ∑ j : α, ∑ q : α, ∑ a : α, ∑ e : α, ∑ f : α, g ![i, j, q, a, e, f] := by
  rw [sum_cons]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_cons]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_cons]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [sum_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_cons]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_cons]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact sum_fin0 _ ![]

/-- `∑_{i,j < N} f(X_i - X_j)`. -/
noncomputable def prS (X : ℕ → Ω → G) (N : ℕ) (f : G → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, f (X i ω - X j ω)

omit [MeasurableSub₂ G] in
/-- The pair projection of the path statistic `PA`. -/
theorem WK.PA_stat (W : WK ν c w B) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    1 / (N : ℝ) ^ 3 * sAll X N (PA c w) ω
      = 1 / (N : ℝ) ^ 2 * prS X N (w 1) ω + (1 / (N : ℝ) ^ 3 * sAll X N (TA1 c w) ω) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hE : sAll X N (fun x : Fin 3 → G => w 1 (x 1 - x 2)) ω = (N : ℝ) ^ 1 * prS X N (w 1) ω := by
    unfold sAll prS; rw [sum_fin3]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hs : sAll X N (PA c w) ω = sAll X N (fun x : Fin 3 → G => w 1 (x 1 - x 2)) ω
      + (sAll X N (TA1 c w) ω) := by
    unfold sAll
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ι _ => by rw [W.PA_split]
  rw [hs, hE]
  field_simp

omit [MeasurableSub₂ G] in
/-- The pair projection of the path statistic `PW`. -/
theorem WK.PW_stat (W : WK ν c w B) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    1 / (N : ℝ) ^ 4 * sAll X N (PW c w) ω
      = 1 / (N : ℝ) ^ 2 * prS X N (w 2) ω + (1 / (N : ℝ) ^ 4 * sAll X N (TW1 c w) ω + 1 / (N : ℝ) ^ 4 * sAll X N (TW2 c w) ω) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hE : sAll X N (fun x : Fin 4 → G => w 2 (x 1 - x 3)) ω = (N : ℝ) ^ 2 * prS X N (w 2) ω := by
    unfold sAll prS; rw [sum_fin4]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hs : sAll X N (PW c w) ω = sAll X N (fun x : Fin 4 → G => w 2 (x 1 - x 3)) ω
      + (sAll X N (TW1 c w) ω + sAll X N (TW2 c w) ω) := by
    unfold sAll
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ι _ => by rw [W.PW_split]
  rw [hs, hE]
  field_simp

omit [MeasurableSub₂ G] in
/-- The pair projection of the path statistic `PF1`. -/
theorem WK.PF1_stat (W : WK ν c w B) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    1 / (N : ℝ) ^ 4 * sAll X N (PF1 c w) ω
      = 1 / (N : ℝ) ^ 2 * prS X N (w 2) ω + (1 / (N : ℝ) ^ 4 * sAll X N (TF11 c w) ω + 1 / (N : ℝ) ^ 4 * sAll X N (TF12 c w) ω) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hE : sAll X N (fun x : Fin 4 → G => w 2 (x 2 - x 3)) ω = (N : ℝ) ^ 2 * prS X N (w 2) ω := by
    unfold sAll prS; rw [sum_fin4]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hs : sAll X N (PF1 c w) ω = sAll X N (fun x : Fin 4 → G => w 2 (x 2 - x 3)) ω
      + (sAll X N (TF11 c w) ω + sAll X N (TF12 c w) ω) := by
    unfold sAll
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ι _ => by rw [W.PF1_split]
  rw [hs, hE]
  field_simp

omit [MeasurableSub₂ G] in
/-- The pair projection of the path statistic `PF2`. -/
theorem WK.PF2_stat (W : WK ν c w B) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    1 / (N : ℝ) ^ 5 * sAll X N (PF2 c w) ω
      = 1 / (N : ℝ) ^ 2 * prS X N (w 3) ω + (1 / (N : ℝ) ^ 5 * sAll X N (TF21 c w) ω + 1 / (N : ℝ) ^ 5 * sAll X N (TF22 c w) ω + 1 / (N : ℝ) ^ 5 * sAll X N (TF23 c w) ω) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hE : sAll X N (fun x : Fin 5 → G => w 3 (x 2 - x 4)) ω = (N : ℝ) ^ 3 * prS X N (w 3) ω := by
    unfold sAll prS; rw [sum_fin5]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hs : sAll X N (PF2 c w) ω = sAll X N (fun x : Fin 5 → G => w 3 (x 2 - x 4)) ω
      + (sAll X N (TF21 c w) ω + sAll X N (TF22 c w) ω + sAll X N (TF23 c w) ω) := by
    unfold sAll
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ι _ => by rw [W.PF2_split]
  rw [hs, hE]
  field_simp

omit [MeasurableSub₂ G] in
/-- The pair projection of the path statistic `PF3`. -/
theorem WK.PF3_stat (W : WK ν c w B) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    1 / (N : ℝ) ^ 6 * sAll X N (PF3 c w) ω
      = 1 / (N : ℝ) ^ 2 * prS X N (w 4) ω + (1 / (N : ℝ) ^ 6 * sAll X N (TF31 c w) ω + 1 / (N : ℝ) ^ 6 * sAll X N (TF32 c w) ω + 1 / (N : ℝ) ^ 6 * sAll X N (TF33 c w) ω + 1 / (N : ℝ) ^ 6 * sAll X N (TF34 c w) ω) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hE : sAll X N (fun x : Fin 6 → G => w 4 (x 3 - x 5)) ω = (N : ℝ) ^ 4 * prS X N (w 4) ω := by
    unfold sAll prS; rw [sum_fin6]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hs : sAll X N (PF3 c w) ω = sAll X N (fun x : Fin 6 → G => w 4 (x 3 - x 5)) ω
      + (sAll X N (TF31 c w) ω + sAll X N (TF32 c w) ω + sAll X N (TF33 c w) ω + sAll X N (TF34 c w) ω) := by
    unfold sAll
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ι _ => by rw [W.PF3_split]
  rw [hs, hE]
  field_simp

/-- The sixteen remainder terms (each degenerate in three coordinates), with their coefficients. -/
noncomputable def rem2 (c : G → ℝ) (w : ℕ → G → ℝ) (X : ℕ → Ω → G) (N : ℕ) : ℕ → Ω → ℝ
  | 0 => fun ω => (-4) * (1 / (N : ℝ) ^ 3 * sAll X N (TA1 c w) ω)
  | 1 => fun ω => (2) * (1 / (N : ℝ) ^ 4 * sAll X N (TW1 c w) ω)
  | 2 => fun ω => (2) * (1 / (N : ℝ) ^ 4 * sAll X N (TW2 c w) ω)
  | 3 => fun ω => (6) * (1 / (N : ℝ) ^ 4 * sAll X N (PE1 c w) ω)
  | 4 => fun ω => (-6) * (1 / (N : ℝ) ^ 5 * sAll X N (PE2 c w) ω)
  | 5 => fun ω => (2) * (1 / (N : ℝ) ^ 6 * sAll X N (PE3 c w) ω)
  | 6 => fun ω => (-2) * (1 / (N : ℝ) ^ 5 * sAll X N (PE4 c w) ω)
  | 7 => fun ω => (4) * (1 / (N : ℝ) ^ 4 * sAll X N (TF11 c w) ω)
  | 8 => fun ω => (4) * (1 / (N : ℝ) ^ 4 * sAll X N (TF12 c w) ω)
  | 9 => fun ω => (-4) * (1 / (N : ℝ) ^ 5 * sAll X N (TF21 c w) ω)
  | 10 => fun ω => (-4) * (1 / (N : ℝ) ^ 5 * sAll X N (TF22 c w) ω)
  | 11 => fun ω => (-4) * (1 / (N : ℝ) ^ 5 * sAll X N (TF23 c w) ω)
  | 12 => fun ω => (1) * (1 / (N : ℝ) ^ 6 * sAll X N (TF31 c w) ω)
  | 13 => fun ω => (1) * (1 / (N : ℝ) ^ 6 * sAll X N (TF32 c w) ω)
  | 14 => fun ω => (1) * (1 / (N : ℝ) ^ 6 * sAll X N (TF33 c w) ω)
  | 15 => fun ω => (1) * (1 / (N : ℝ) ^ 6 * sAll X N (TF34 c w) ω)
  | _ + 16 => fun _ => 0

theorem coef_le [IsProbabilityMeasure μ] {a K0 : ℝ} {f : Ω → ℝ} (ha : a ^ 2 ≤ 36) (hK : 0 ≤ K0)
    (h : cv μ f ≤ K0) : cv μ (fun ω => a * f ω) ≤ 36 * K0 := by
  rw [cv_const_mul]
  calc a ^ 2 * cv μ f ≤ a ^ 2 * K0 := mul_le_mul_of_nonneg_left h (sq_nonneg a)
    _ ≤ 36 * K0 := mul_le_mul_of_nonneg_right ha hK

theorem rem2_bm (H : SP μ ν X) (W : WK ν c w B) (N : ℕ) : ∀ i, BM (rem2 c w X N i)
  | 0 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TA1_bm))
  | 1 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TW1_bm))
  | 2 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TW2_bm))
  | 3 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.PE1_bm))
  | 4 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.PE2_bm))
  | 5 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.PE3_bm))
  | 6 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.PE4_bm))
  | 7 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF11_bm))
  | 8 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF12_bm))
  | 9 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF21_bm))
  | 10 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF22_bm))
  | 11 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF23_bm))
  | 12 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF31_bm))
  | 13 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF32_bm))
  | 14 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF33_bm))
  | 15 => BM.const_mul _ (BM.const_mul _ (H.sAll_bm N W.TF34_bm))
  | _ + 16 => BM.const 0

theorem rem2_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    ∀ i, cv μ (rem2 c w X N i) ≤ 36 * (1866240 * B ^ 10 / (N : ℝ) ^ 3)
  | 0 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TA1_var H hN)
  | 1 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TW1_var H hN)
  | 2 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TW2_var H hN)
  | 3 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.PE1_var H hN)
  | 4 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.PE2_var H hN)
  | 5 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.PE3_var H hN)
  | 6 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.PE4_var H hN)
  | 7 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF11_var H hN)
  | 8 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF12_var H hN)
  | 9 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF21_var H hN)
  | 10 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF22_var H hN)
  | 11 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF23_var H hN)
  | 12 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF31_var H hN)
  | 13 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF32_var H hN)
  | 14 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF33_var H hN)
  | 15 => coef_le (by norm_num) (by have := W.B_one; positivity) (W.TF34_var H hN)
  | _ + 16 => by
    have h0 : cv μ (fun _ : Ω => (0 : ℝ)) = 0 := by unfold cv; simp
    show cv μ (fun _ : Ω => (0 : ℝ)) ≤ _
    rw [h0]; have := W.B_one; positivity

/-- The remainder of the `w̃`-part: the sum of the sixteen terms. -/
noncomputable def Rem2 (c : G → ℝ) (w : ℕ → G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range 16, rem2 c w X N i ω

/-- **`Var(Rem2) ≤ 16 · 16 · 36 · 1866240 B¹⁰/N³`.** -/
theorem Rem2_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (W : WK ν c w B) {N : ℕ} (hN : 0 < N) :
    BM (Rem2 c w X N) ∧ cv μ (Rem2 c w X N) ≤ 17199267840 * B ^ 10 / (N : ℝ) ^ 3 := by
  refine ⟨BM.sum _ _ fun i _ => rem2_bm H W N i, ?_⟩
  have h := cv_sum_le (μ := μ) (Finset.range 16) (rem2 c w X N) (rem2_bm H W N)
  have h2 : ∑ i ∈ Finset.range 16, cv μ (rem2 c w X N i)
      ≤ ∑ _i ∈ Finset.range 16, 36 * (1866240 * B ^ 10 / (N : ℝ) ^ 3) :=
    Finset.sum_le_sum fun i _ => rem2_var H W hN i
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  rw [Finset.card_range] at h
  have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ ((16 : ℕ) : ℝ))
  have e : ((16 : ℕ) : ℝ) * (((16 : ℕ) : ℝ) * (36 * (1866240 * B ^ 10 / (N : ℝ) ^ 3)))
      = 17199267840 * B ^ 10 / (N : ℝ) ^ 3 := by push_cast; ring
  rw [e] at h3
  exact h.trans h3

/-- The linear `w̃`-statistic `q₀ + 2⟨φᶜ⟩ + [φ¹ᶜ, φ¹ᶜ]` as a combination of tuple statistics. -/
noncomputable def LinW (c : G → ℝ) (w : ℕ → G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) : ℝ :=
  1 / (N : ℝ) ^ 2 * sAll X N (PZ w) ω
    + (-4) * (1 / (N : ℝ) ^ 3 * sAll X N (PA c w) ω)
    + 2 * (1 / (N : ℝ) ^ 4 * sAll X N (PW c w) ω)
    + 6 * (1 / (N : ℝ) ^ 4 * sAll X N (PE1 c w) ω)
    + (-6) * (1 / (N : ℝ) ^ 5 * sAll X N (PE2 c w) ω)
    + 2 * (1 / (N : ℝ) ^ 6 * sAll X N (PE3 c w) ω)
    + (-2) * (1 / (N : ℝ) ^ 5 * sAll X N (PE4 c w) ω)
    + 4 * (1 / (N : ℝ) ^ 4 * sAll X N (PF1 c w) ω)
    + (-4) * (1 / (N : ℝ) ^ 5 * sAll X N (PF2 c w) ω)
    + 1 / (N : ℝ) ^ 6 * sAll X N (PF3 c w) ω

/-- `Φ = w̃ - 4 w₁ + 6 w₂ - 4 w₃ + w₄ = (1 - 𝒫)⁴ w̃`. -/
def phiW (w : ℕ → G → ℝ) (u : G) : ℝ := w 0 u - 4 * w 1 u + 6 * w 2 u - 4 * w 3 u + w 4 u

omit [MeasurableSub₂ G] in
/-- **`LinW = N⁻² ∑_{i,j} Φ(X_i - X_j) + Rem2`** (pointwise). -/
theorem WK.LinW_decomp (W : WK ν c w B) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    LinW c w X N ω = 1 / (N : ℝ) ^ 2 * prS X N (phiW w) ω + Rem2 c w X N ω := by
  have hZ : sAll X N (PZ w) ω = prS X N (w 0) ω := by
    unfold sAll PZ prS; rw [sum_fin2]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one]
  have hΦ : prS X N (phiW w) ω = prS X N (w 0) ω - 4 * prS X N (w 1) ω + 6 * prS X N (w 2) ω
      - 4 * prS X N (w 3) ω + prS X N (w 4) ω := by
    unfold prS phiW
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  unfold LinW Rem2
  rw [W.PA_stat hN ω, W.PW_stat hN ω, W.PF1_stat hN ω, W.PF2_stat hN ω, W.PF3_stat hN ω, hZ, hΦ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rem2]
  ring

end Stat2


/-! ## Part 5: algebra: the polynomial of `trace_two_expansion` as linear part plus products -/

section Algebra2

theorem alg1_final {n m2 s1 s2 s3 s4 e3 Sφ Sψ D0 T0 T1 T2 T3 : ℝ} (hn0 : n ≠ 0)
    (hφ : Sφ = n * (-s1 + 3 * s2 - 3 * s3 + s4 - 2 * s1 ^ 2 + 2 * s1 * s2 - e3))
    (hψ : Sψ = n * (s2 - s1))
    (hD : D0 = T0 + (2 * s1 + 3 * s1 ^ 2 - 2 * s2) * T1 + (-10 * s1) * T2 + (6 * s1) * T3) :
    m2 / n ^ 2 * (n ^ 2 + 2 * n * Sφ + Sψ ^ 2) + 1 / n ^ 2 * D0
      = m2 * (1 + 2 * (-s1 + 3 * s2 - 3 * s3 + s4)) + 1 / n ^ 2 * T0
        + (m2 * (-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2)
          + (2 * s1 + 3 * s1 ^ 2 - 2 * s2) * (1 / n ^ 2 * T1)
          + s1 * (-10 * (1 / n ^ 2 * T2) + 6 * (1 / n ^ 2 * T3))) := by
  rw [hφ, hψ, hD]
  field_simp
  ring

/-- **The polynomial of `trace_two_expansion`, vector level.**  With `K_ij K_ji/n² = (m₂ + w̃_ij)/n²`,
    `(1/n) ∑_l K_il ε_l = s₁ + a_i`, `(1/n) ∑_l K_il ε_l² = s₂ + d_i` and the averages
    `s₁ … s₄, e₃`: the sum is `m₂ (1 + 2(-s₁ + 3s₂ - 3s₃ + s₄))` plus the `w̃`-sum of the connected
    parts plus products. -/
theorem alg1 {α : Type*} [Fintype α] (n m2 : ℝ) (hn : (Fintype.card α : ℝ) = n) (hn0 : n ≠ 0)
    (K wt : α → α → ℝ) (hwt : ∀ i j, wt i j = wt j i)
    (hW : ∀ i j, K i j / n * (K j i / n) = (m2 + wt i j) / n ^ 2)
    (ε a dd : α → ℝ) (s1 s2 s3 s4 e3 : ℝ)
    (hb : ∀ i, 1 / n * ∑ l, K i l * ε l = s1 + a i)
    (hd : ∀ i, 1 / n * ∑ l, K i l * ε l ^ 2 = s2 + dd i)
    (hSε : ∑ i, ε i = n * s1) (hSa : ∑ i, a i = n * s2) (hSε2 : ∑ i, ε i ^ 2 = n * s2)
    (hSεa : ∑ i, ε i * a i = n * s3) (hSa2 : ∑ i, a i ^ 2 = n * s4)
    (hSd : ∑ i, dd i = n * e3) :
    ∑ i, ∑ j, K i j / n * (K j i / n)
          * (1 + ((-2 * ε i + 1 / n * ∑ l, K i l * ε l)
                + (3 * ε i ^ 2 - 3 * ε i * (1 / n * ∑ l, K i l * ε l)
                  + (1 / n * ∑ l, K i l * ε l) ^ 2 - 1 / n * ∑ l, K i l * ε l ^ 2))
              + ((-2 * ε j + 1 / n * ∑ l, K j l * ε l)
                + (3 * ε j ^ 2 - 3 * ε j * (1 / n * ∑ l, K j l * ε l)
                  + (1 / n * ∑ l, K j l * ε l) ^ 2 - 1 / n * ∑ l, K j l * ε l ^ 2))
              + (-2 * ε i + 1 / n * ∑ l, K i l * ε l)
                * (-2 * ε j + 1 / n * ∑ l, K j l * ε l))
      = m2 * (1 + 2 * (-s1 + 3 * s2 - 3 * s3 + s4))
        + 1 / n ^ 2 * ∑ i, ∑ j, wt i j
            * (1 + 2 * (-2 * ε i + a i + 3 * ε i ^ 2 - 3 * ε i * a i + a i ^ 2 - dd i)
              + (-2 * ε i + a i) * (-2 * ε j + a j))
        + (m2 * (-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2)
          + (2 * s1 + 3 * s1 ^ 2 - 2 * s2) * (1 / n ^ 2 * ∑ i, ∑ j, wt i j)
          + s1 * (-10 * (1 / n ^ 2 * ∑ i, ∑ j, wt i j * ε i)
            + 6 * (1 / n ^ 2 * ∑ i, ∑ j, wt i j * a i))) := by
  simp_rw [hb, hd, hW]
  obtain ⟨φ, hφd⟩ : ∃ φ : α → ℝ, φ = fun i => (-2 * ε i + (s1 + a i))
      + (3 * ε i ^ 2 - 3 * ε i * (s1 + a i) + (s1 + a i) ^ 2 - (s2 + dd i)) := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ : α → ℝ, ψ = fun i => -2 * ε i + a i := ⟨_, rfl⟩
  -- sums of φ and of ψ + s₁
  have hSφ : ∑ i, φ i
      = n * (-s1 + 3 * s2 - 3 * s3 + s4 - 2 * s1 ^ 2 + 2 * s1 * s2 - e3) := by
    have e : ∀ i, φ i = (-2 - 3 * s1) * ε i + (1 + 2 * s1) * a i + 3 * ε i ^ 2
        - 3 * (ε i * a i) + a i ^ 2 - dd i + (s1 + s1 ^ 2 - s2) := fun i => by
      rw [hφd]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn, hSε, hSa, hSε2, hSεa, hSa2, hSd]
    ring
  have hSψ : ∑ i, (ψ i + s1) = n * (s2 - s1) := by
    have e : ∀ i, ψ i + s1 = -2 * ε i + a i + s1 := fun i => by rw [hψd]
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn, hSε, hSa]
    ring
  -- the double sum without weight
  have hG : ∑ i, ∑ j, (1 + φ i + φ j + (ψ i + s1) * (ψ j + s1))
      = n ^ 2 + 2 * n * (∑ i, φ i) + (∑ i, (ψ i + s1)) ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul, hn]
    ring
  -- the weighted double sum
  have hD := alg_core wt hwt φ ψ (fun _ => s1)
  have hD2 : ∑ i, ∑ j, wt i j * (1 + 2 * φ i + ψ i * ψ j + 2 * (ψ i * s1) + s1 * s1)
      = ∑ i, ∑ j, wt i j
            * (1 + 2 * (-2 * ε i + a i + 3 * ε i ^ 2 - 3 * ε i * a i + a i ^ 2 - dd i)
              + (-2 * ε i + a i) * (-2 * ε j + a j))
        + (2 * s1 + 3 * s1 ^ 2 - 2 * s2) * (∑ i, ∑ j, wt i j)
        + (-10 * s1) * (∑ i, ∑ j, wt i j * ε i) + (6 * s1) * (∑ i, ∑ j, wt i j * a i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hφd, hψd]; ring
  -- split the weight
  have hsplit : ∑ i, ∑ j, (m2 + wt i j) / n ^ 2
        * (1 + ((-2 * ε i + (s1 + a i))
              + (3 * ε i ^ 2 - 3 * ε i * (s1 + a i) + (s1 + a i) ^ 2 - (s2 + dd i)))
            + ((-2 * ε j + (s1 + a j))
              + (3 * ε j ^ 2 - 3 * ε j * (s1 + a j) + (s1 + a j) ^ 2 - (s2 + dd j)))
            + (-2 * ε i + (s1 + a i)) * (-2 * ε j + (s1 + a j)))
      = m2 / n ^ 2 * (∑ i, ∑ j, (1 + φ i + φ j + (ψ i + s1) * (ψ j + s1)))
        + 1 / n ^ 2 * (∑ i, ∑ j, wt i j * (1 + φ i + φ j + (ψ i + s1) * (ψ j + s1))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hφd, hψd]; ring
  rw [hsplit, hG, hD, hD2]
  exact alg1_final hn0 hSφ hSψ rfl

/-- **Tuple level**: the `w̃`-sum of the connected parts as a combination of the ten nested sums;
    `ε_i = H_i/n`, `a_i = (1/n) ∑_q c_iq ε_q`, `d_i = (1/n) ∑_q c_iq ε_q²`, `H_i = ∑_v c_iv`. -/
theorem alg2 {α : Type*} [Fintype α] (n : ℝ) (hn0 : n ≠ 0) (c wt : α → α → ℝ)
    (hwt : ∀ i j, wt i j = wt j i) :
    1 / n ^ 2 * ∑ i, ∑ j, wt i j
        * (1 + 2 * (-2 * (1 / n * ∑ v, c i v) + 1 / n * ∑ q, c i q * (1 / n * ∑ v, c q v)
              + 3 * (1 / n * ∑ v, c i v) ^ 2
              - 3 * (1 / n * ∑ v, c i v) * (1 / n * ∑ q, c i q * (1 / n * ∑ v, c q v))
              + (1 / n * ∑ q, c i q * (1 / n * ∑ v, c q v)) ^ 2
              - 1 / n * ∑ q, c i q * (1 / n * ∑ v, c q v) ^ 2)
          + (-2 * (1 / n * ∑ v, c i v) + 1 / n * ∑ q, c i q * (1 / n * ∑ v, c q v))
            * (-2 * (1 / n * ∑ v, c j v) + 1 / n * ∑ q, c j q * (1 / n * ∑ v, c q v)))
      = 1 / n ^ 2 * ∑ i, ∑ j, wt i j
        + (-4) * (1 / n ^ 3 * ∑ i, ∑ j, ∑ v, wt i j * c i v)
        + 2 * (1 / n ^ 4 * ∑ i, ∑ j, ∑ q, ∑ v, wt i j * c i q * c q v)
        + 6 * (1 / n ^ 4 * ∑ i, ∑ j, ∑ v, ∑ v', wt i j * c i v * c i v')
        + (-6) * (1 / n ^ 5 * ∑ i, ∑ j, ∑ v, ∑ q, ∑ v', wt i j * c i v * c i q * c q v')
        + 2 * (1 / n ^ 6 * ∑ i, ∑ j, ∑ q, ∑ v, ∑ q', ∑ v',
            wt i j * c i q * c q v * c i q' * c q' v')
        + (-2) * (1 / n ^ 5 * ∑ i, ∑ j, ∑ q, ∑ v, ∑ v', wt i j * c i q * c q v * c q v')
        + 4 * (1 / n ^ 4 * ∑ i, ∑ j, ∑ v, ∑ v', wt i j * c i v * c j v')
        + (-4) * (1 / n ^ 5 * ∑ i, ∑ j, ∑ v, ∑ q, ∑ v', wt i j * c i v * c j q * c q v')
        + 1 / n ^ 6 * ∑ i, ∑ j, ∑ q, ∑ v, ∑ q', ∑ v',
            wt i j * c i q * c q v * c j q' * c q' v' := by
  obtain ⟨Hf, hH⟩ : ∃ Hf : α → ℝ, Hf = fun i => ∑ v, c i v := ⟨_, rfl⟩
  obtain ⟨Af, hA⟩ : ∃ Af : α → ℝ, Af = fun i => ∑ q, c i q * Hf q := ⟨_, rfl⟩
  obtain ⟨Df, hDf⟩ : ∃ Df : α → ℝ, Df = fun i => ∑ q, c i q * (Hf q * Hf q) := ⟨_, rfl⟩
  have hHv : ∀ i, ∑ v, c i v = Hf i := fun i => by rw [hH]
  have ea : ∀ i, ∑ q, c i q * (1 / n * Hf q) = 1 / n * Af i := fun i => by
    rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
  have ed : ∀ i, ∑ q, c i q * (1 / n * Hf q) ^ 2 = 1 / n ^ 2 * Df i := fun i => by
    rw [hDf, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
  -- the nested sums
  have cq : ∀ (x : ℝ) (q : α), ∑ v, x * c q v = x * Hf q := fun x q => by rw [hH, Finset.mul_sum]
  have rA : ∀ i j, ∑ v, wt i j * c i v = wt i j * Hf i := fun i j => cq _ _
  have rW : ∀ i j, ∑ q, ∑ v, wt i j * c i q * c q v = wt i j * Af i := fun i j => by
    simp only [cq]; rw [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have rE1 : ∀ i j, ∑ v, ∑ v', wt i j * c i v * c i v' = wt i j * (Hf i * Hf i) := fun i j => by
    simp only [cq]; rw [← Finset.sum_mul, rA]; ring
  have rE2 : ∀ i j, ∑ v, ∑ q, ∑ v', wt i j * c i v * c i q * c q v'
      = wt i j * (Hf i * Af i) := fun i j => by
    simp only [cq]
    have e : ∀ v, ∑ q, wt i j * c i v * c i q * Hf q = wt i j * c i v * Af i := fun v => by
      rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    simp only [e]; rw [← Finset.sum_mul, rA]; ring
  have rE4 : ∀ i j, ∑ q, ∑ v, ∑ v', wt i j * c i q * c q v * c q v' = wt i j * Df i :=
    fun i j => by
      simp only [cq]
      rw [hDf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.sum_mul, cq]; ring
  have rF1 : ∀ i j, ∑ v, ∑ v', wt i j * c i v * c j v' = wt i j * (Hf i * Hf j) := fun i j => by
    simp only [cq]; rw [← Finset.sum_mul, rA]; ring
  have rF2 : ∀ i j, ∑ v, ∑ q, ∑ v', wt i j * c i v * c j q * c q v'
      = wt i j * (Hf i * Af j) := fun i j => by
    simp only [cq]
    have e : ∀ v, ∑ q, wt i j * c i v * c j q * Hf q = wt i j * c i v * Af j := fun v => by
      rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    simp only [e]; rw [← Finset.sum_mul, rA]; ring
  have rr : ∀ (x : ℝ) (i' : α), ∑ q', ∑ v', x * c i' q' * c q' v' = x * Af i' := fun x i' => by
    simp only [cq]; rw [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have rE3 : ∀ i j, ∑ q, ∑ v, ∑ q', ∑ v', wt i j * c i q * c q v * c i q' * c q' v'
      = wt i j * (Af i * Af i) := fun i j => by
    simp only [rr]
    have e : ∀ q, ∑ v, wt i j * c i q * c q v * Af i = wt i j * c i q * Hf q * Af i := fun q => by
      rw [← Finset.sum_mul, cq]
    simp only [e]
    rw [← Finset.sum_mul]
    have e2 : ∑ q, wt i j * c i q * Hf q = wt i j * Af i := by
      rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    rw [e2]; ring
  have rF3 : ∀ i j, ∑ q, ∑ v, ∑ q', ∑ v', wt i j * c i q * c q v * c j q' * c q' v'
      = wt i j * (Af i * Af j) := fun i j => by
    simp only [rr]
    have e : ∀ q, ∑ v, wt i j * c i q * c q v * Af j = wt i j * c i q * Hf q * Af j := fun q => by
      rw [← Finset.sum_mul, cq]
    simp only [e]
    rw [← Finset.sum_mul]
    have e2 : ∑ q, wt i j * c i q * Hf q = wt i j * Af i := by
      rw [hA, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    rw [e2]; ring
  simp only [rA, rW, rE1, rE2, rE3, rE4, rF1, rF2, rF3, hHv, ea, ed]
  -- symmetrise the mixed term
  have hswap : ∑ i, ∑ j, wt i j * (Af i * Hf j) = ∑ i, ∑ j, wt i j * (Hf i * Af j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hwt j i, mul_comm (Af j)]
  have e1 : ∀ i j, wt i j
        * (1 + 2 * (-2 * (1 / n * Hf i) + 1 / n * (1 / n * Af i) + 3 * (1 / n * Hf i) ^ 2
              - 3 * (1 / n * Hf i) * (1 / n * (1 / n * Af i)) + (1 / n * (1 / n * Af i)) ^ 2
              - 1 / n * (1 / n ^ 2 * Df i))
          + (-2 * (1 / n * Hf i) + 1 / n * (1 / n * Af i))
            * (-2 * (1 / n * Hf j) + 1 / n * (1 / n * Af j)))
      = (wt i j + (-4 / n) * (wt i j * Hf i) + (2 / n ^ 2) * (wt i j * Af i)
          + (6 / n ^ 2) * (wt i j * (Hf i * Hf i)) + (-6 / n ^ 3) * (wt i j * (Hf i * Af i))
          + (2 / n ^ 4) * (wt i j * (Af i * Af i)) + (-2 / n ^ 3) * (wt i j * Df i)
          + (4 / n ^ 2) * (wt i j * (Hf i * Hf j)) + (-2 / n ^ 3) * (wt i j * (Hf i * Af j))
          + (1 / n ^ 4) * (wt i j * (Af i * Af j)))
        + (-2 / n ^ 3) * (wt i j * (Af i * Hf j)) := fun i j => by
    field_simp; ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, hswap]
  field_simp
  ring

end Algebra2


/-! ## Part 6: the pair kernel `H₂`, the statistic `U₂` and the linear statistic for `k = 2` -/

section Abstract2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G}
  {k : ℕ → G → ℝ} {w : ℕ → G → ℝ} {B : ℝ}

omit [MeasurableSub₂ G] in
theorem VK.mono {B' : ℝ} (V : VK ν k B) (h : B ≤ B') : VK ν k B' :=
  { meas := V.meas
    B_one := V.B_one.trans h
    bound := fun j u => (V.bound j u).trans h
    even := V.even
    mean := V.mean
    conv := V.conv
    inv := V.inv }

/-- `Ψ₂ = 2 m₂ ψ + (1 - 𝒫)⁴ w̃`; the pair kernel of the proposition for `k = 2` is
    `H₂ = 2 Ψ₂ = 2 (1 - 𝒫)⁴ Γ₂ - 4 μ₂ (1 - 𝒫)³ p`. -/
def psi2 (m2 : ℝ) (k w : ℕ → G → ℝ) (u : G) : ℝ := 2 * m2 * VarianceOne.psiK k u + phiW w u

omit [MeasurableSub₂ G] in
theorem phi_bound {c : G → ℝ} (W : WK ν c w B) (u : G) : |phiW w u| ≤ 16 * B := by
  unfold phiW
  have h0 := abs_le.mp (W.bound 0 u)
  have h1 := abs_le.mp (W.bound 1 u)
  have h2 := abs_le.mp (W.bound 2 u)
  have h3 := abs_le.mp (W.bound 3 u)
  have h4 := abs_le.mp (W.bound 4 u)
  rw [abs_le]
  constructor <;>
    linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

omit [MeasurableSub₂ G] in
theorem phi_meas {c : G → ℝ} (W : WK ν c w B) : Measurable (phiW w) :=
  (((((W.meas 0).sub ((W.meas 1).const_mul 4)).add ((W.meas 2).const_mul 6)).sub
    ((W.meas 3).const_mul 4)).add (W.meas 4))

/-- `Ψ₂` gives the hypotheses `Deg2`. -/
theorem psi2_deg2 [IsProbabilityMeasure ν] (H : SP μ ν X) (V : VK ν k B)
    (W : WK ν (k 0) w B) {m2 : ℝ} (hm0 : 0 ≤ m2) (hmB : m2 ≤ B) :
    Deg2 μ ν X (psi2 m2 k w) (16 * B ^ 2 + 16 * B) ((16 * B ^ 2 + 16 * B) ^ 2) := by
  have hB0 : 0 ≤ B := zero_le_one.trans V.B_one
  refine deg2_of H ((V.psi_meas.const_mul (2 * m2)).add (phi_meas W)) (fun u => ?_)
    (fun u => ?_) (fun x => ?_)
  · unfold psi2
    have h1 := psi_bound V.bound u
    have h2 := phi_bound W u
    have h3 : |2 * m2 * VarianceOne.psiK k u| ≤ 2 * B * (8 * B) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m2)]
      exact mul_le_mul (by linarith only [hmB]) h1 (abs_nonneg _) (by positivity)
    calc |2 * m2 * VarianceOne.psiK k u + phiW w u| ≤ |2 * m2 * VarianceOne.psiK k u| + |phiW w u| := abs_add_le _ _
      _ ≤ 16 * B ^ 2 + 16 * B := by nlinarith only [h3, h2]
  · unfold psi2 VarianceOne.psiK phiW
    rw [V.even 0, V.even 1, V.even 2, V.even 3, W.even 0, W.even 1, W.even 2, W.even 3,
      W.even 4]
  · have bψ : BM (fun z : G => VarianceOne.psiK k (x - z)) :=
      ⟨V.psi_meas.comp (measurable_const.sub measurable_id), 8 * B, fun _ => psi_bound V.bound _⟩
    have bφ : BM (fun z : G => phiW w (x - z)) :=
      ⟨(phi_meas W).comp (measurable_const.sub measurable_id), 16 * B, fun _ => phi_bound W _⟩
    have m1 : ∫ z, VarianceOne.psiK k (x - z) ∂ν = 0 := (V.psi_deg2 H).mean x
    have m2' : ∫ z, phiW w (x - z) ∂ν = 0 := by
      unfold phiW
      have i0 : Integrable (fun z => w 0 (x - z)) ν := (W.wR 0 x).integrable
      have i1 : Integrable (fun z => 4 * w 1 (x - z)) ν := (BM.const_mul 4 (W.wR 1 x)).integrable
      have i2 : Integrable (fun z => 6 * w 2 (x - z)) ν := (BM.const_mul 6 (W.wR 2 x)).integrable
      have i3 : Integrable (fun z => 4 * w 3 (x - z)) ν := (BM.const_mul 4 (W.wR 3 x)).integrable
      have i4 : Integrable (fun z => w 4 (x - z)) ν := (W.wR 4 x).integrable
      have i01 : Integrable (fun z => w 0 (x - z) - 4 * w 1 (x - z)) ν := i0.sub i1
      have i012 : Integrable (fun z => w 0 (x - z) - 4 * w 1 (x - z) + 6 * w 2 (x - z)) ν :=
        i01.add i2
      have i0123 : Integrable (fun z => w 0 (x - z) - 4 * w 1 (x - z) + 6 * w 2 (x - z)
          - 4 * w 3 (x - z)) ν := i012.sub i3
      rw [integral_add i0123 i4, integral_sub i012 i3, integral_add i01 i2, integral_sub i0 i1,
        integral_const_mul, integral_const_mul, integral_const_mul, W.mean 0, W.mean 1,
        W.mean 2, W.mean 3, W.mean 4]
      ring
    unfold psi2
    have j1 : Integrable (fun z => 2 * m2 * VarianceOne.psiK k (x - z)) ν := (BM.const_mul _ bψ).integrable
    rw [integral_add j1 bφ.integrable, integral_const_mul, m1, m2']
    ring

omit [MeasurableSub₂ G] in
theorem Soff_lin (a : ℝ) (f g : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Soff (fun u => a * f u + g u) X N ω = a * Soff f X N ω + Soff g X N ω := by
  unfold Soff
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aT
  split_ifs <;> ring

/-- `U₂ = N⁻² ∑_{i≠j} Ψ₂(X_i - X_j) = (1/(2N²)) ∑_{i≠j} H₂(X_i - X_j)`. -/
noncomputable def U2 (m2 : ℝ) (k w : ℕ → G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) : ℝ :=
  1 / (N : ℝ) ^ 2 * Soff (psi2 m2 k w) X N ω

/-- The linear statistic for `k = 2`: `m₂ (1 + 2L) + LinW`, `L = -s₁ + 3s₂ - 3s₃ + s₄`. -/
noncomputable def Qlin2 (m2 : ℝ) (k w : ℕ → G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) : ℝ :=
  Qlin (2 * m2) k X N ω - m2 + LinW (k 0) w X N ω

omit [MeasurableSub₂ G] in
/-- **`Q_lin,2 = const + U₂ + (2 m₂ Rem + Rem2)`** (pointwise). -/
theorem Qlin2_decomp (W : WK ν (k 0) w B) (m2 : ℝ) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    Qlin2 m2 k w X N ω
      = (2 * m2 * (1 + VarianceOne.psiK k 0 / N) - m2 + 1 / (N : ℝ) ^ 2 * (N * phiW w 0))
        + U2 m2 k w X N ω + (2 * m2 * Rem k X N ω + Rem2 (k 0) w X N ω) := by
  have hpr : prS X N (phiW w) ω = N * phiW w 0 + Soff (phiW w) X N ω := pair_eq_soff _ X N ω
  have hS : Soff (psi2 m2 k w) X N ω
      = 2 * m2 * Soff (VarianceOne.psiK k) X N ω + Soff (phiW w) X N ω :=
    Soff_lin (2 * m2) (VarianceOne.psiK k) (phiW w) X N ω
  unfold Qlin2 U2
  rw [Qlin_decomp (2 * m2) k X hN ω, W.LinW_decomp hN ω, hpr, hS]
  unfold Ustat
  ring

/-- `Var(2 m₂ Rem + Rem2) ≤ 34629061120 B¹⁰/N³`. -/
theorem Rem_total_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (V : VK ν k B) (W : WK ν (k 0) w B) {m2 : ℝ} (hm0 : 0 ≤ m2) (hmB : m2 ≤ B) {N : ℕ}
    (hN : 0 < N) :
    BM (fun ω => 2 * m2 * Rem k X N ω + Rem2 (k 0) w X N ω)
      ∧ cv μ (fun ω => 2 * m2 * Rem k X N ω + Rem2 (k 0) w X N ω)
        ≤ 34629061120 * B ^ 10 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hB1 := V.B_one
  obtain ⟨b1, h1⟩ := Rem_var (μ := μ) H V hN
  obtain ⟨b2, h2⟩ := Rem2_var (μ := μ) H W hN
  have b1' := BM.const_mul (2 * m2) b1
  refine ⟨b1'.add b2, ?_⟩
  have h3 := cv_add_le (μ := μ) b1' b2
  rw [cv_const_mul] at h3
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have hm2 : (2 * m2) ^ 2 ≤ 4 * B ^ 2 := by nlinarith only [hm0, hmB]
  have hc0 : 0 ≤ cv μ (Rem k X N) := cv_nonneg _ _
  have h4 : (2 * m2) ^ 2 * cv μ (Rem k X N) ≤ 4 * B ^ 2 * (28815680 * B ^ 8 / (N : ℝ) ^ 3) :=
    mul_le_mul hm2 h1 hc0 (by positivity)
  have e : 34629061120 * B ^ 10 / (N : ℝ) ^ 3
      = 2 * (4 * B ^ 2 * (28815680 * B ^ 8 / (N : ℝ) ^ 3))
        + 2 * (17199267840 * B ^ 10 / (N : ℝ) ^ 3) := by ring
  rw [e]
  linarith only [h3, h4, h2]

/-- **Second moment of a pair sum**: `E (N⁻² ∑_{i,j} f(X_i - X_j))² ≤ 3 C²/N²` for an even
    kernel of mean zero bounded by `C`. -/
theorem pair_sq_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    (V : VK ν k B) {f : G → ℝ} {C : ℝ} (hm : Measurable f) (hb : ∀ u, |f u| ≤ C)
    (he : ∀ u, f (-u) = f u) (h0 : ∀ x, ∫ z, f (x - z) ∂ν = 0) {N : ℕ} (hN : 1 ≤ N) :
    BM (fun ω => 1 / (N : ℝ) ^ 2 * prS X N f ω)
      ∧ ∫ ω, (1 / (N : ℝ) ^ 2 * prS X N f ω) ^ 2 ∂μ ≤ 3 * C ^ 2 / (N : ℝ) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have D0 := deg2_of H hm hb he h0
  obtain ⟨V0, hV0d⟩ : ∃ V0 : ℝ, V0 = ∫ u, f u ^ 2 ∂ν := ⟨_, rfl⟩
  have hV0 : ∀ x, ∫ z, f (x - z) ^ 2 ∂ν = V0 := fun x => by
    rw [hV0d]; exact V.inv (fun u => f u ^ 2) (hm.pow_const 2) x
  have hV0n : 0 ≤ V0 := by rw [hV0d]; exact integral_nonneg fun _ => _root_.sq_nonneg _
  have hV0le : V0 ≤ C ^ 2 := by rw [← hV0 0]; exact D0.var 0
  have sm := deg_second_moment D0 hV0 N
  have mz := deg_mean D0 N
  have bS : BM (Soff f X N) := ⟨OracleTwo.Soff_meas D0 N, _, OracleTwo.Soff_bound D0 N⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = f 0 := ⟨_, rfl⟩
  have hc0b : c0 ^ 2 ≤ C ^ 2 := by
    have := abs_le.mp (hb 0)
    rw [← hc0] at this
    nlinarith only [this.1, this.2]
  have hs1 : ∀ ω, 1 / (N : ℝ) ^ 2 * prS X N f ω
      = 1 / (N : ℝ) ^ 2 * (N * c0 + Soff f X N ω) := by
    intro ω; rw [hc0, ← pair_eq_soff]; rfl
  have bm : BM (fun ω => 1 / (N : ℝ) ^ 2 * prS X N f ω) := by
    have : (fun ω => 1 / (N : ℝ) ^ 2 * prS X N f ω)
        = fun ω => 1 / (N : ℝ) ^ 2 * (N * c0 + Soff f X N ω) := funext hs1
    rw [this]; exact BM.const_mul _ ((BM.const _).add bS)
  refine ⟨bm, ?_⟩
  have e : ∀ ω, (1 / (N : ℝ) ^ 2 * prS X N f ω) ^ 2
      = 1 / (N : ℝ) ^ 4 * ((N : ℝ) ^ 2 * c0 ^ 2)
        + (2 * c0 / (N : ℝ) ^ 3 * Soff f X N ω + 1 / (N : ℝ) ^ 4 * Soff f X N ω ^ 2) := by
    intro ω; rw [hs1 ω]; field_simp; ring
  simp_rw [e]
  rw [integral_add (integrable_const _)
      ((BM.const_mul _ bS).add (BM.const_mul _ bS.sqr)).integrable,
    integral_add (BM.const_mul _ bS).integrable (BM.const_mul _ bS.sqr).integrable,
    integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul, mz, sm,
    mul_zero, zero_add]
  exact s1_arith hN1 hc0b hV0n hV0le

end Abstract2

section TorusW

/-- `w̃ = p² - m₂` on the flat torus. -/
noncomputable def wt0 (d : ℕ) (σ : ℝ) (u : FlatTorus d) : ℝ := pker d σ u ^ 2 - torusM d σ 2

/-- `w_j = 𝒫ʲ w̃` (iterated convolution with `c = p - 1`; on functions of mean zero this is the
    convolution with `p`). -/
noncomputable def wT (d : ℕ) (σ : ℝ) : ℕ → FlatTorus d → ℝ :=
  wIter (flatTorusMeasure d) (kT d σ 0) (wt0 d σ)

theorem m2_bounds {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    1 ≤ torusM d σ 2 ∧ torusM d σ 2 ≤ torusM d σ 1 ∧ torusM d σ 1 ≤ torusM d σ 1 ^ 2 := by
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  refine ⟨torusM_ge_one hσ d (a := 2) (by norm_num),
    torusM_anti hσ d (k := 1) (s := 2) le_rfl (by norm_num), ?_⟩
  nlinarith only [hM1]

/-- The hypotheses `WK` hold on the flat torus with `B = m₁²`. -/
theorem torus_wk {d : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    WK (flatTorusMeasure d) (kT d σ 0) (wT d σ) (torusM d σ 1 ^ 2) := by
  obtain ⟨hm1, hm2, hMM⟩ := m2_bounds (d := d) hσ
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  have V := torus_vk (d := d) hσ
  have hp : ∀ u : FlatTorus d, 0 ≤ pker d σ u ∧ pker d σ u ≤ torusM d σ 1 := fun u => by
    have := pker_bounds hσ d u
    rw [torusM_one]; exact this
  refine wk_of V (fun u => ?_) hMM
    (((pker_continuous hσ d).measurable.pow_const 2).sub measurable_const) (fun u => ?_)
    (fun u => ?_) (fun x => ?_)
  · rw [kT_zero]; unfold cK; linarith only [(hp u).1]
  · unfold wt0
    have h1 : pker d σ u ^ 2 ≤ torusM d σ 1 ^ 2 := pow_le_pow_left₀ (hp u).1 (hp u).2 2
    have h0 : 0 ≤ pker d σ u ^ 2 := _root_.sq_nonneg _
    rw [abs_le]; constructor <;> linarith only [h1, h0, hm1, hm2, hMM]
  · unfold wt0
    rw [show pker d σ (-u) = pker d σ u from heatTorus_even d _ u]
  · unfold wt0
    have hc : Continuous fun z : FlatTorus d => pker d σ (x - z) ^ 2 :=
      ((pker_continuous hσ d).comp (continuous_const.sub continuous_id)).pow 2
    rw [integral_sub (flat_integrable d _ hc) (integrable_const _), integral_const,
      probReal_univ, one_smul,
      V.inv (fun u => pker d σ u ^ 2) ((pker_continuous hσ d).measurable.pow_const 2) x,
      pker_sq_int hσ d, sub_self]

/-- **`v₂ = ½ ∫ H₂²`**, `H₂ = 2 Ψ₂ = 2 (1 - 𝒫)⁴ Γ₂ - 4 μ₂ (1 - 𝒫)³ p`, `Γ₂ = p²`, `μ₂ = m₂`
    (`prop:variance`, `k = 2`): `v₂ = 2 ∫ Ψ₂²`. -/
noncomputable def v2 (d : ℕ) (σ : ℝ) : ℝ :=
  2 * ∫ u, psi2 (torusM d σ 2) (kT d σ) (wT d σ) u ^ 2 ∂flatTorusMeasure d

end TorusW


/-! ## Part 7: `Tr P²` against the linear statistic (pointwise) -/

section Arith2

theorem inner_bound {D s1 s2 e3 : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 1 / 8) (hs1 : |s1| ≤ D)
    (hs20 : 0 ≤ s2) (hs2 : s2 ≤ D ^ 2) (he3 : |e3| ≤ D * s2) :
    |-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2| ≤ D * (13 / 2 * |s1| + 9 / 4 * s2) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = |s1| := ⟨_, rfl⟩
  rw [← ha] at hs1 ⊢
  have ha0 : 0 ≤ a := by rw [ha]; exact abs_nonneg _
  have hsq : s1 ^ 2 = a ^ 2 := by rw [ha, sq_abs]
  have f1 : a ^ 2 ≤ D * a := by nlinarith only [ha0, hs1]
  have hDD : D ^ 2 ≤ D / 8 := by nlinarith only [hD0, hD]
  have f2 : |s1 * s2| ≤ D / 8 * a := by
    rw [abs_mul, ← ha, abs_of_nonneg hs20]
    calc a * s2 ≤ a * (D / 8) := mul_le_mul_of_nonneg_left (hs2.trans hDD) ha0
      _ = D / 8 * a := by ring
  have f3 : s2 ^ 2 ≤ D / 8 * s2 := by
    have := mul_le_mul_of_nonneg_right (hs2.trans hDD) hs20
    calc s2 ^ 2 = s2 * s2 := by ring
      _ ≤ D / 8 * s2 := this
  have f0 : 0 ≤ s2 ^ 2 := _root_.sq_nonneg _
  have fa : 0 ≤ a ^ 2 := _root_.sq_nonneg _
  obtain ⟨p1, p2⟩ := abs_le.mp f2
  obtain ⟨q1, q2⟩ := abs_le.mp he3
  have hDa : 0 ≤ D * a := mul_nonneg hD0 ha0
  have hDs : 0 ≤ D * s2 := mul_nonneg hD0 hs20
  have e : -4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2
      = -3 * a ^ 2 + 2 * (s1 * s2) - 2 * e3 + s2 ^ 2 := by rw [← hsq]; ring
  rw [e, abs_le]
  constructor <;> nlinarith only [f1, p1, p2, q1, q2, f3, f0, fa, hDa, hDs]

/-- On the normalisation event with parameter `D ≤ 1/8`:
    `|T - Q_lin| ≤ D (23 B² |s₁| + 583 B² s₂ + 3 |q₀|)`. -/
theorem arith2_good {T S Ql m2 B M D s1 s2 e3 q0 tA tW : ℝ} (hm0 : 0 ≤ m2) (hmB : m2 ≤ B)
    (hM1 : 1 ≤ M) (hMB : M ≤ B) (hD0 : 0 ≤ D) (hD : D ≤ 1 / 8)
    (hT : |T - S| ≤ 580 * D * M * s2)
    (hS : S = Ql + (m2 * (-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2)
      + (2 * s1 + 3 * s1 ^ 2 - 2 * s2) * q0 + s1 * (-10 * tA + 6 * tW)))
    (hs1 : |s1| ≤ D) (hs20 : 0 ≤ s2) (hs2 : s2 ≤ D ^ 2) (he3 : |e3| ≤ D * s2)
    (htA : |tA| ≤ B * D) (htW : |tW| ≤ B * (M * D)) :
    |T - Ql| ≤ D * (23 * B ^ 2 * |s1| + 583 * B ^ 2 * s2 + 3 * |q0|) := by
  have hB1 : 1 ≤ B := hM1.trans hMB
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hBB : B ≤ B ^ 2 := by nlinarith only [hB1]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = |s1| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact abs_nonneg _
  have hX := inner_bound hD0 hD hs1 hs20 hs2 he3
  rw [← ha] at hX hs1 ⊢
  have hDa : 0 ≤ D * a := mul_nonneg hD0 ha0
  have hDs : 0 ≤ D * s2 := mul_nonneg hD0 hs20
  have b1 : |m2 * (-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2)|
      ≤ B * (D * (13 / 2 * a + 9 / 4 * s2)) := by
    rw [abs_mul, abs_of_nonneg hm0]
    exact mul_le_mul hmB hX (abs_nonneg _) hB0
  have hc1 : |2 * s1 + 3 * s1 ^ 2 - 2 * s2| ≤ 3 * D := by
    obtain ⟨u1, u2⟩ := abs_le.mp (hs1.trans_eq' (by rw [ha]))
    have hsq : s1 ^ 2 ≤ D ^ 2 := by
      rw [← sq_abs s1]; exact pow_le_pow_left₀ (abs_nonneg _) (by rw [← ha]; exact hs1) 2
    have hDD : D ^ 2 ≤ D / 8 := by nlinarith only [hD0, hD]
    have h0 : 0 ≤ s1 ^ 2 := _root_.sq_nonneg _
    rw [abs_le]; constructor <;> linarith only [u1, u2, hsq, hDD, h0, hs20, hs2]
  have b2 : |(2 * s1 + 3 * s1 ^ 2 - 2 * s2) * q0| ≤ 3 * D * |q0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hc1 (abs_nonneg _)
  have h6 : |-10 * tA + 6 * tW| ≤ 16 * B ^ 2 * D := by
    obtain ⟨u1, u2⟩ := abs_le.mp htA
    obtain ⟨v1, v2⟩ := abs_le.mp htW
    have k1 : B * D ≤ B ^ 2 * D := mul_le_mul_of_nonneg_right hBB hD0
    have k2 : B * (M * D) ≤ B ^ 2 * D := by
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMB hD0) hB0
      calc B * (M * D) ≤ B * (B * D) := this
        _ = B ^ 2 * D := by ring
    rw [abs_le]; constructor <;> linarith only [u1, u2, v1, v2, k1, k2]
  have b3 : |s1 * (-10 * tA + 6 * tW)| ≤ a * (16 * B ^ 2 * D) := by
    rw [abs_mul, ← ha]; exact mul_le_mul_of_nonneg_left h6 ha0
  have e : T - Ql = (T - S) + m2 * (-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2)
      + (2 * s1 + 3 * s1 ^ 2 - 2 * s2) * q0 + s1 * (-10 * tA + 6 * tW) := by rw [hS]; ring
  have htri : |T - Ql| ≤ |T - S|
      + |m2 * (-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2)|
      + |(2 * s1 + 3 * s1 ^ 2 - 2 * s2) * q0| + |s1 * (-10 * tA + 6 * tW)| := by
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
      (add_le_add_left (abs_add_le _ _) _)) _)
  have k1 : B * (D * a) ≤ B ^ 2 * (D * a) := mul_le_mul_of_nonneg_right hBB hDa
  have k2 : B * (D * s2) ≤ B ^ 2 * (D * s2) := mul_le_mul_of_nonneg_right hBB hDs
  have k3 : M * (D * s2) ≤ B ^ 2 * (D * s2) := mul_le_mul_of_nonneg_right (hMB.trans hBB) hDs
  have k4 : 0 ≤ B ^ 2 * (D * a) := mul_nonneg (_root_.sq_nonneg B) hDa
  have k5 : 0 ≤ B ^ 2 * (D * s2) := mul_nonneg (_root_.sq_nonneg B) hDs
  nlinarith only [htri, hT, b1, b2, b3, k1, k2, k3, k4, k5]

theorem arith2_sq {x D α β s1 s2 q : ℝ} (hD0 : 0 ≤ D)
    (h : |x| ≤ D * (α * |s1| + β * s2 + 3 * |q|)) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs20 : 0 ≤ s2)
    (hs2 : s2 ≤ D ^ 2) :
    x ^ 2 ≤ 3 * D ^ 2 * (α ^ 2 * s1 ^ 2 + β ^ 2 * D ^ 2 * s2 + 9 * q ^ 2) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = α * |s1| := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = β * s2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 3 * |q| := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg hα (abs_nonneg _)
  have hv0 : 0 ≤ v := by rw [hv]; exact mul_nonneg hβ hs20
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  rw [← hu, ← hv, ← hz] at h
  have h1 : x ^ 2 ≤ (D * (u + v + z)) ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) h 2
  have h2 : (u + v + z) ^ 2 ≤ 3 * (u ^ 2 + v ^ 2 + z ^ 2) := by
    nlinarith only [_root_.sq_nonneg (u - v), _root_.sq_nonneg (u - z), _root_.sq_nonneg (v - z)]
  have eu : u ^ 2 = α ^ 2 * s1 ^ 2 := by rw [hu, mul_pow, sq_abs]
  have ez : z ^ 2 = 9 * q ^ 2 := by rw [hz, mul_pow, sq_abs]; ring
  have ev : v ^ 2 ≤ β ^ 2 * D ^ 2 * s2 := by
    rw [hv]
    have := mul_le_mul_of_nonneg_left hs2 (mul_nonneg (_root_.sq_nonneg β) hs20)
    calc (β * s2) ^ 2 = β ^ 2 * s2 * s2 := by ring
      _ ≤ β ^ 2 * s2 * D ^ 2 := this
      _ = β ^ 2 * D ^ 2 * s2 := by ring
  have h3 := mul_le_mul_of_nonneg_left h2 (_root_.sq_nonneg D)
  have h4 : (D * (u + v + z)) ^ 2 = D ^ 2 * (u + v + z) ^ 2 := by ring
  have h5 : D ^ 2 * (3 * (u ^ 2 + v ^ 2 + z ^ 2))
      ≤ 3 * D ^ 2 * (α ^ 2 * s1 ^ 2 + β ^ 2 * D ^ 2 * s2 + 9 * q ^ 2) := by
    rw [eu, ez]
    have := mul_le_mul_of_nonneg_left ev (by positivity : (0 : ℝ) ≤ 3 * D ^ 2)
    linarith only [this]
  linarith only [h1, h3, h4, h5]

theorem prB1 {a B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) : |a| ≤ 2 * B ^ 5 := by
  have := pow_le_pow_right₀ hB (by norm_num : 1 ≤ 5)
  have h0 : 0 ≤ B ^ 5 := by positivity
  rw [pow_one] at this; linarith only [ha, this, h0]

theorem prB2 {a b B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B) : |a * b| ≤ 2 * B ^ 5 := by
  have h := abs_mul_le' ha hb
  have := pow_le_pow_right₀ hB (by norm_num : 2 ≤ 5)
  have h0 : 0 ≤ B ^ 5 := by positivity
  have e : B * B = B ^ 2 := by ring
  rw [e] at h; linarith only [h, this, h0]

/-- `|(1/n²) ∑_{i,j} W_ij u_i| ≤ ‖W‖ ‖u‖`. -/
theorem wsum_abs {N : ℕ} (hN : 0 < N) (wt : Fin N → Fin N → ℝ) (u : Fin N → ℝ) {Bw U : ℝ}
    (hw : ∀ i j, |wt i j| ≤ Bw) (hu : ∀ i, |u i| ≤ U) :
    |1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, wt i j * u i| ≤ Bw * U := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ((Finset.univ : Finset (Fin N)).card : ℝ) = N := by simp
  have h1 : ∀ i, |∑ j, wt i j * u i| ≤ N * (Bw * U) := fun i => by
    have := abs_sum_le_univ (fun j => wt i j * u i) (C := Bw * U)
      (fun j => abs_mul_le' (hw i j) (hu i))
    rwa [hc] at this
  have h2 := abs_sum_le_univ (fun i => ∑ j, wt i j * u i) h1
  rw [hc] at h2
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2)]
  calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j, wt i j * u i| ≤ 1 / (N : ℝ) ^ 2 * (N * (N * (Bw * U))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Bw * U := by field_simp

end Arith2

section Point2

variable {Ω : Type*} [MeasurableSpace Ω]

theorem wT_zero (d : ℕ) (σ : ℝ) : wT d σ 0 = wt0 d σ := rfl

omit [MeasurableSpace Ω] in
theorem Qlin_scale {G : Type*} [AddCommGroup G] (a : ℝ) (k : ℕ → G → ℝ) (X : ℕ → Ω → G)
    (N : ℕ) (ω : Ω) : Qlin a k X N ω = a * Qlin 1 k X N ω := by
  unfold Qlin; ring

/-- `q₀ = N⁻² ∑_{i,j} w̃(X_i - X_j)`. -/
noncomputable def q0T (d : ℕ) (σ : ℝ) (N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) : ℝ :=
  1 / (N : ℝ) ^ 2 * sAll X N (PZ (wT d σ)) ω

/-- **The pointwise bounds for `Tr P² - Q_lin,2`** (`B = m₁²`). -/
theorem trace2_bounds {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 0 < N)
    (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    (∀ D : ℝ, 0 ≤ D → D ≤ 1 / 8 →
      (∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ D) →
      |((torusWalk d σ N (fun j => X j ω)) ^ 2).trace
          - Qlin2 (torusM d σ 2) (kT d σ) (wT d σ) X N ω|
        ≤ D * (23 * (torusM d σ 1 ^ 2) ^ 2 * |s1T d σ N X ω|
          + 583 * (torusM d σ 1 ^ 2) ^ 2 * s2T d σ N X ω + 3 * |q0T d σ N X ω|)
      ∧ 0 ≤ s2T d σ N X ω ∧ s2T d σ N X ω ≤ D ^ 2 ∧ |s1T d σ N X ω| ≤ D)
    ∧ |((torusWalk d σ N (fun j => X j ω)) ^ 2).trace
          - Qlin2 (torusM d σ 2) (kT d σ) (wT d σ) X N ω| ≤ N + 83 * (torusM d σ 1 ^ 2) ^ 5
    ∧ |q0T d σ N X ω| ≤ torusM d σ 1 ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  obtain ⟨hm1, hm2M, hMM⟩ := m2_bounds (d := d) hσ
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  obtain ⟨m2, hm2d⟩ : ∃ m2 : ℝ, m2 = torusM d σ 2 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have V := VK.mono (torus_vk (d := d) hσ) hMM
  have W := torus_wk (d := d) hσ
  rw [← hMd] at hm2M hMM V W ⊢
  rw [← hm2d] at hm1 hm2M ⊢
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = M ^ 2 := ⟨_, rfl⟩
  rw [← hBd] at hMM V W ⊢
  have hB1 : 1 ≤ B := hM1.trans hMM
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hm0 : 0 ≤ m2 := zero_le_one.trans hm1
  have hmB : m2 ≤ B := hm2M.trans hMM
  -- the matrices and vectors of the configuration
  obtain ⟨c, hcd⟩ : ∃ c : Fin N → Fin N → ℝ, c = fun (i j : Fin N) => cK d σ (X i ω - X j ω) := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K : Fin N → Fin N → ℝ, K = torusK d σ N (fun j => X j ω) := ⟨_, rfl⟩
  obtain ⟨wtm, hwd⟩ : ∃ wtm : Fin N → Fin N → ℝ,
      wtm = fun (i j : Fin N) => wt0 d σ (X i ω - X j ω) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε : Fin N → ℝ,
      ε = fun (a : Fin N) => heatRho d σ N (fun j => X j ω) a - 1 := ⟨_, rfl⟩
  obtain ⟨av, had⟩ : ∃ av : Fin N → ℝ, av = fun i => 1 / (N : ℝ) * ∑ q, c i q * ε q := ⟨_, rfl⟩
  obtain ⟨dd, hddd⟩ : ∃ dd : Fin N → ℝ,
      dd = fun i => 1 / (N : ℝ) * ∑ q, c i q * ε q ^ 2 := ⟨_, rfl⟩
  have hεc : ∀ a, ε a = 1 / (N : ℝ) * ∑ v, c a v := fun a => by
    rw [hεd, hcd]; exact eps_fin σ N hN X ω a
  have hcs : ∀ i j, c i j = c j i := fun i j => by
    rw [hcd]; simp only; rw [← neg_sub (X j ω) (X i ω), cK_even]
  have hK : ∀ i l, K i l = 1 + c i l := fun i l => by
    rw [hKd, hcd]; unfold torusK cK pker; ring
  have hKs : ∀ i j, K i j = K j i := fun i j => by rw [hK, hK, hcs]
  have hcb : ∀ i j, |c i j| ≤ M := fun i j => by
    rw [hcd, hMd]; exact (cK_facts hσ d _).1
  have hwK : ∀ i j, wtm i j = K i j ^ 2 - m2 := fun i j => by
    rw [hwd, hKd, hm2d]; rfl
  have hwts : ∀ i j, wtm i j = wtm j i := fun i j => by rw [hwK, hwK, hKs]
  have hwb : ∀ i j, |wtm i j| ≤ B := fun i j => by
    rw [hwd]; exact W.bound 0 _
  obtain ⟨e1, e2, _⟩ := s_eps σ N hN X ω
  obtain ⟨s1, hs1d⟩ : ∃ s1 : ℝ, s1 = s1T d σ N X ω := ⟨_, rfl⟩
  obtain ⟨s2, hs2d⟩ : ∃ s2 : ℝ, s2 = s2T d σ N X ω := ⟨_, rfl⟩
  rw [← hs1d] at e1 ⊢
  rw [← hs2d] at e2 ⊢
  have e1' : s1 = 1 / (N : ℝ) * ∑ a, ε a := by rw [e1, hεd]
  have e2' : s2 = 1 / (N : ℝ) * ∑ a, ε a ^ 2 := by rw [e2, hεd]
  obtain ⟨s3, hs3⟩ : ∃ s3 : ℝ, s3 = 1 / (N : ℝ) * ∑ i, ε i * av i := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ s4 : ℝ, s4 = 1 / (N : ℝ) * ∑ i, av i ^ 2 := ⟨_, rfl⟩
  obtain ⟨e3, he3⟩ : ∃ e3 : ℝ, e3 = 1 / (N : ℝ) * ∑ i, ε i ^ 3 := ⟨_, rfl⟩
  have hSε : ∑ i, ε i = N * s1 := by rw [e1']; field_simp
  have hSε2 : ∑ i, ε i ^ 2 = N * s2 := by rw [e2']; field_simp
  have hSεa : ∑ i, ε i * av i = N * s3 := by rw [hs3]; field_simp
  have hSa2 : ∑ i, av i ^ 2 = N * s4 := by rw [hs4]; field_simp
  have hcol : ∀ q, ∑ i, c i q = N * ε q := fun q => by
    rw [hεc q]
    have : ∑ i, c i q = ∑ v, c q v := Finset.sum_congr rfl fun i _ => hcs i q
    rw [this]; field_simp
  have hSa : ∑ i, av i = N * s2 := by
    rw [had]; simp only
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∀ q, ∑ i, c i q * ε q = N * ε q ^ 2 := fun q => by
      rw [← Finset.sum_mul, hcol]; ring
    simp only [this]
    rw [← Finset.mul_sum, hSε2]; field_simp
  have hSd : ∑ i, dd i = N * e3 := by
    rw [hddd]; simp only
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∀ q, ∑ i, c i q * ε q ^ 2 = N * ε q ^ 3 := fun q => by
      rw [← Finset.sum_mul, hcol]; ring
    simp only [this]
    rw [← Finset.mul_sum, he3]; field_simp
  have hb : ∀ i, 1 / (N : ℝ) * ∑ l, K i l * ε l = s1 + av i := fun i => by
    have : ∑ l, K i l * ε l = ∑ l, ε l + ∑ l, c i l * ε l := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by rw [hK]; ring
    rw [this, had, e1']; ring
  have hd : ∀ i, 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2 = s2 + dd i := fun i => by
    have : ∑ l, K i l * ε l ^ 2 = ∑ l, ε l ^ 2 + ∑ l, c i l * ε l ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by rw [hK]; ring
    rw [this, hddd, e2']; ring
  have hW : ∀ i j, K i j / (N : ℝ) * (K j i / (N : ℝ)) = (m2 + wtm i j) / (N : ℝ) ^ 2 :=
    fun i j => by rw [hwK, ← hKs i j]; field_simp; ring
  have halg := alg1 (α := Fin N) (N : ℝ) m2 (by simp) hN0 K wtm hwts hW ε av dd s1 s2 s3 s4 e3
    hb hd hSε hSa hSε2 hSεa hSa2 hSd
  -- the w̃-sum is `LinW`
  have hLin : 1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, wtm i j
        * (1 + 2 * (-2 * ε i + av i + 3 * ε i ^ 2 - 3 * ε i * av i + av i ^ 2 - dd i)
          + (-2 * ε i + av i) * (-2 * ε j + av j))
      = LinW (kT d σ 0) (wT d σ) X N ω := by
    rw [had, hddd]
    simp only [hεc]
    refine (alg2 (α := Fin N) (N : ℝ) hN0 c wtm hwts).trans ?_
    unfold LinW sAll PZ PA PW PE1 PE2 PE3 PE4 PF1 PF2 PF3
    simp only [sum_fin2, sum_fin3, sum_fin4, sum_fin5, sum_fin6, kT_zero, wT_zero, hcd, hwd,
      Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one]
  -- `Q_lin` in terms of the vectors
  have hQ1 : Qlin 1 (kT d σ) X N ω = 1 + (-s1 + 3 * s2 - 3 * s3 + s4) := by
    have h1 := Q1_Qlin σ N hN X ω
    rw [← hMd, ← hs1d, ← hs2d, Qlin_scale M] at h1
    have h2 := (Q1_eq σ N hN X ω).symm
    rw [← hMd, ← hKd] at h2
    have h3 : ∀ i : Fin N, heatRho d σ N (fun j => X j ω) i - 1 = ε i := fun i => by rw [hεd]
    simp only [h3, hb] at h2
    have e : ∀ i, 3 * ε i ^ 2 - 3 * ε i * (s1 + av i) + (s1 + av i) ^ 2
        = 3 * ε i ^ 2 + (-3 * s1) * ε i - 3 * (ε i * av i) + s1 ^ 2 + (2 * s1) * av i
          + av i ^ 2 := fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hSε, hSa, hSε2, hSεa,
      hSa2] at h2
    have hM0' : M ≠ 0 := by linarith only [hM1]
    have h4 : M * Qlin 1 (kT d σ) X N ω = M * (1 + (-s1 + 3 * s2 - 3 * s3 + s4)) := by
      have h5 : Q1 d σ N X ω = M * (1 + (-s1 + 3 * s2 - 3 * s3 + s4))
          + M * (-2 * s1 ^ 2 + 2 * s1 * s2) := by
        rw [h2]; field_simp; ring
      linarith only [h1, h5]
    exact mul_left_cancel₀ hM0' h4
  obtain ⟨Ql, hQl⟩ : ∃ Ql : ℝ, Ql = Qlin2 m2 (kT d σ) (wT d σ) X N ω := ⟨_, rfl⟩
  have hQl2 : Ql = m2 * (1 + 2 * (-s1 + 3 * s2 - 3 * s3 + s4))
      + LinW (kT d σ 0) (wT d σ) X N ω := by
    rw [hQl]; unfold Qlin2; rw [Qlin_scale (2 * m2), hQ1]; ring
  rw [hLin] at halg
  rw [← hQl]
  -- the q₀, t_A, t_W of the products
  have hq0 : 1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, wtm i j = q0T d σ N X ω := by
    unfold q0T sAll PZ; rw [sum_fin2, wT_zero, hwd]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one]
  obtain ⟨q0, hq0d⟩ : ∃ q0 : ℝ, q0 = q0T d σ N X ω := ⟨_, rfl⟩
  rw [← hq0d] at hq0 ⊢
  have hq0b : |q0| ≤ B := by
    rw [← hq0]
    have := wsum_abs hN wtm (fun _ => (1 : ℝ)) (Bw := B) (U := 1) hwb (fun _ => by simp)
    simpa using this
  have hT0 : |((torusWalk d σ N (fun j => X j ω)) ^ 2).trace| ≤ N := by
    have := walk_pow_trace_le (torusK d σ N (fun j => X j ω)) (torusRho d σ N (fun j => X j ω))
      (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) 2
    exact this
  refine ⟨?_, ?_, hq0b⟩
  · intro D hD0 hD hρ
    have hεD : ∀ i, |ε i| ≤ D := fun i => by rw [hεd]; exact hρ i
    obtain ⟨a1, a2, a3⟩ := avg_bounds hN ε hεD
    rw [← e1'] at a1
    rw [← e2'] at a2 a3
    have htr := BiasVariance2.trace_two_expansion hN K (torusRho d σ N (fun j => X j ω)) ε
      (M := M) (δ := D)
      (fun i j => by rw [hKd]; exact heatTorus_nonneg hc d _)
      (fun i j => by
        rw [hKd, hMd]
        show heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω) ≤ torusM d σ 1
        rw [torusM_one]; exact heatTorus_le_zero hc d _)
      hKs
      (fun i => by
        rw [hKd]
        show ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)
          = N * heatRho d σ N (fun j => X j ω) i
        rw [Fin.sum_univ_eq_sum_range
          (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) N]
        unfold heatRho
        field_simp)
      (fun i => by rw [hεd]; rfl) hD hεD
    rw [← e2'] at htr
    have hwalk : walkMatrix K (torusRho d σ N (fun j => X j ω))
        = torusWalk d σ N (fun j => X j ω) := by rw [hKd]; rfl
    rw [hwalk] at htr
    have hav : ∀ i, |av i| ≤ M * D := fun i => by
      rw [had]; simp only
      have h1 := abs_sum_le_univ (fun q => c i q * ε q) (C := M * D)
        (fun q => abs_mul_le' (hcb i q) (hεD q))
      have hcN : ((Finset.univ : Finset (Fin N)).card : ℝ) = N := by simp
      rw [hcN] at h1
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
      calc 1 / (N : ℝ) * |∑ q, c i q * ε q| ≤ 1 / (N : ℝ) * (N * (M * D)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = M * D := by field_simp
    have htA := wsum_abs hN wtm ε hwb hεD
    have htW := wsum_abs hN wtm av hwb hav
    have he3b : |e3| ≤ D * s2 := by
      rw [he3, e2', abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
      have h1 : |∑ i, ε i ^ 3| ≤ ∑ i, D * ε i ^ 2 :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          have e : ε i ^ 3 = ε i * ε i ^ 2 := by ring
          rw [e, abs_mul, abs_of_nonneg (_root_.sq_nonneg (ε i))]
          exact mul_le_mul_of_nonneg_right (hεD i) (_root_.sq_nonneg _))
      rw [← Finset.mul_sum] at h1
      calc 1 / (N : ℝ) * |∑ i, ε i ^ 3| ≤ 1 / (N : ℝ) * (D * ∑ i, ε i ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = D * (1 / (N : ℝ) * ∑ i, ε i ^ 2) := by ring
    rw [hq0] at halg
    have hS := halg.trans (by rw [hQl2] : _ = Ql
      + (m2 * (-4 * s1 ^ 2 + 4 * s1 * s2 - 2 * e3 + (s2 - s1) ^ 2)
        + (2 * s1 + 3 * s1 ^ 2 - 2 * s2) * q0
        + s1 * (-10 * (1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, wtm i j * ε i)
          + 6 * (1 / (N : ℝ) ^ 2 * ∑ i, ∑ j, wtm i j * av i))))
    exact ⟨arith2_good hm0 hmB hM1 hMM hD0 hD htr hS a1 a2 a3 he3b htA htW, a2, a3, a1⟩
  · -- crude bound
    have b1 : |1 / (N : ℝ) ^ 2 * sAll X N (P1 (kT d σ)) ω| ≤ B :=
      tstat_abs X hN _ (fun y => V.bound 0 _) ω
    have b2 : |1 / (N : ℝ) ^ 3 * sAll X N (P2 (kT d σ)) ω| ≤ B * B :=
      tstat_abs X hN _ (fun y => abs_mul_le' (V.bound 0 _) (V.bound 0 _)) ω
    have b3 : |1 / (N : ℝ) ^ 4 * sAll X N (P3 (kT d σ)) ω| ≤ B * B * B :=
      tstat_abs X hN _
        (fun y => abs_mul_le' (abs_mul_le' (V.bound 0 _) (V.bound 0 _)) (V.bound 0 _)) ω
    have b4 : |1 / (N : ℝ) ^ 5 * sAll X N (P4 (kT d σ)) ω| ≤ B * B * B * B :=
      tstat_abs X hN _ (fun y => abs_mul_le' (abs_mul_le' (abs_mul_le' (V.bound 0 _)
        (V.bound 0 _)) (V.bound 0 _)) (V.bound 0 _)) ω
    have z0 : |1 / (N : ℝ) ^ 2 * sAll X N (PZ (wT d σ)) ω| ≤ 2 * B ^ 5 :=
      tstat_abs X hN _ (fun y => prB1 hB1 (W.bound 0 _)) ω
    have zA : |1 / (N : ℝ) ^ 3 * sAll X N (PA (kT d σ 0) (wT d σ)) ω| ≤ 2 * B ^ 5 :=
      tstat_abs X hN _ (fun y => prB2 hB1 (W.bound 0 _) (W.c_bound _)) ω
    have zW : |1 / (N : ℝ) ^ 4 * sAll X N (PW (kT d σ 0) (wT d σ)) ω| ≤ 2 * B ^ 5 :=
      tstat_abs X hN _ (fun y => prB3 hB1 (W.bound 0 _) (W.c_bound _) (W.c_bound _)) ω
    have zE1 := tstat_abs X hN (PE1 (kT d σ 0) (wT d σ)) W.PE1_bd ω
    have zE2 := tstat_abs X hN (PE2 (kT d σ 0) (wT d σ)) W.PE2_bd ω
    have zE3 := tstat_abs X hN (PE3 (kT d σ 0) (wT d σ)) W.PE3_bd ω
    have zE4 := tstat_abs X hN (PE4 (kT d σ 0) (wT d σ)) W.PE4_bd ω
    have zF1 : |1 / (N : ℝ) ^ 4 * sAll X N (PF1 (kT d σ 0) (wT d σ)) ω| ≤ 2 * B ^ 5 :=
      tstat_abs X hN _ (fun y => prB3 hB1 (W.bound 0 _) (W.c_bound _) (W.c_bound _)) ω
    have zF2 : |1 / (N : ℝ) ^ 5 * sAll X N (PF2 (kT d σ 0) (wT d σ)) ω| ≤ 2 * B ^ 5 :=
      tstat_abs X hN _
        (fun y => prB4 hB1 (W.bound 0 _) (W.c_bound _) (W.c_bound _) (W.c_bound _)) ω
    have zF3 : |1 / (N : ℝ) ^ 6 * sAll X N (PF3 (kT d σ 0) (wT d σ)) ω| ≤ 2 * B ^ 5 :=
      tstat_abs X hN _ (fun y => prB5 hB1 (W.bound 0 _) (W.c_bound _) (W.c_bound _)
        (W.c_bound _) (W.c_bound _)) ω
    have hQe : Ql = 2 * m2 * (1 - 1 / (N : ℝ) ^ 2 * sAll X N (P1 (kT d σ)) ω
          + 3 * (1 / (N : ℝ) ^ 3 * sAll X N (P2 (kT d σ)) ω)
          - 3 * (1 / (N : ℝ) ^ 4 * sAll X N (P3 (kT d σ)) ω)
          + 1 / (N : ℝ) ^ 5 * sAll X N (P4 (kT d σ)) ω) - m2
        + LinW (kT d σ 0) (wT d σ) X N ω := by rw [hQl]; rfl
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 - 1 / (N : ℝ) ^ 2 * sAll X N (P1 (kT d σ)) ω
          + 3 * (1 / (N : ℝ) ^ 3 * sAll X N (P2 (kT d σ)) ω)
          - 3 * (1 / (N : ℝ) ^ 4 * sAll X N (P3 (kT d σ)) ω)
          + 1 / (N : ℝ) ^ 5 * sAll X N (P4 (kT d σ)) ω := ⟨_, rfl⟩
    have p2 : B * B ≤ B ^ 4 := by
      have := pow_le_pow_right₀ hB1 (by norm_num : 2 ≤ 4); nlinarith only [this]
    have p3 : B * B * B ≤ B ^ 4 := by
      have := pow_le_pow_right₀ hB1 (by norm_num : 3 ≤ 4); nlinarith only [this]
    have p4 : B * B * B * B = B ^ 4 := by ring
    have p1 : B ≤ B ^ 4 := by
      have := pow_le_pow_right₀ hB1 (by norm_num : 1 ≤ 4); rwa [pow_one] at this
    have p0 : (1 : ℝ) ≤ B ^ 4 := one_le_pow₀ hB1
    have hLb : |L| ≤ 9 * B ^ 4 := by
      obtain ⟨u1, u2⟩ := abs_le.mp b1
      obtain ⟨v1, v2⟩ := abs_le.mp b2
      obtain ⟨w1, w2⟩ := abs_le.mp b3
      obtain ⟨x1, x2⟩ := abs_le.mp b4
      rw [hL, abs_le]
      constructor <;> linarith only [u1, u2, v1, v2, w1, w2, x1, x2, p0, p1, p2, p3, p4]
    have hmL : |2 * m2 * L| ≤ 18 * B ^ 5 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * m2)]
      have := mul_le_mul (by linarith only [hmB] : 2 * m2 ≤ 2 * B) hLb (abs_nonneg _)
        (by positivity)
      calc 2 * m2 * |L| ≤ 2 * B * (9 * B ^ 4) := this
        _ = 18 * B ^ 5 := by ring
    have hLW : |LinW (kT d σ 0) (wT d σ) X N ω| ≤ 64 * B ^ 5 := by
      unfold LinW
      obtain ⟨a1, a2⟩ := abs_le.mp z0
      obtain ⟨b1', b2'⟩ := abs_le.mp zA
      obtain ⟨c1, c2⟩ := abs_le.mp zW
      obtain ⟨d1, d2⟩ := abs_le.mp zE1
      obtain ⟨f1, f2⟩ := abs_le.mp zE2
      obtain ⟨g1, g2⟩ := abs_le.mp zE3
      obtain ⟨h1, h2⟩ := abs_le.mp zE4
      obtain ⟨i1, i2⟩ := abs_le.mp zF1
      obtain ⟨j1, j2⟩ := abs_le.mp zF2
      obtain ⟨k1, k2⟩ := abs_le.mp zF3
      rw [abs_le]
      constructor <;> linarith only [a1, a2, b1', b2', c1, c2, d1, d2, f1, f2, g1, g2, h1, h2,
        i1, i2, j1, j2, k1, k2]
    have p5 : B ≤ B ^ 5 := by
      have := pow_le_pow_right₀ hB1 (by norm_num : 1 ≤ 5); rwa [pow_one] at this
    rw [← hL] at hQe
    obtain ⟨t1, t2⟩ := abs_le.mp hT0
    obtain ⟨u1, u2⟩ := abs_le.mp hmL
    obtain ⟨v1, v2⟩ := abs_le.mp hLW
    rw [hQe, abs_le]
    constructor <;> linarith only [t1, t2, u1, u2, v1, v2, hm0, hmB, p5]

end Point2


/-! ## Part 8: the second moment of `Tr P² - Q_lin,2` and the variance of `Tr P²` -/

section Final2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `Tr P²` of the normalised walk (self-loops) at the sample. -/
noncomputable def trP2 (d : ℕ) (σ : ℝ) (N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) : ℝ :=
  ((torusWalk d σ N (fun j => X j ω)) ^ 2).trace

/-- `E q₀² ≤ 3 (m₁²)²/N²` for `q₀ = N⁻² ∑_{i,j} w̃(X_i - X_j)`. -/
theorem q0_moments [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N) :
    BM (q0T d σ N X)
      ∧ ∫ ω, q0T d σ N X ω ^ 2 ∂μ ≤ 3 * (torusM d σ 1 ^ 2) ^ 2 / (N : ℝ) ^ 2 := by
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  obtain ⟨_, _, hMM⟩ := m2_bounds (d := d) hσ
  have V := VK.mono (torus_vk (d := d) hσ) hMM
  have W := torus_wk (d := d) hσ
  have hq : q0T d σ N X = fun ω => 1 / (N : ℝ) ^ 2 * prS X N (wT d σ 0) ω := by
    funext ω
    unfold q0T sAll PZ prS; rw [sum_fin2]
    simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val, cons_val_fin_one]
  rw [hq]
  exact pair_sq_le H V (W.meas 0) (W.bound 0) (W.even 0) (W.mean 0) hN

/-- Squared pointwise bound on the good event, with `s₂² ≤ D² s₂`. -/
theorem good_sq {x D B s1 s2 q : ℝ} (hD0 : 0 ≤ D) (hB : 0 ≤ B)
    (h : |x| ≤ D * (23 * B ^ 2 * |s1| + 583 * B ^ 2 * s2 + 3 * |q|)) (hs20 : 0 ≤ s2)
    (hs2 : s2 ≤ D ^ 2) :
    x ^ 2 ≤ 3 * D ^ 2 * (23 * B ^ 2) ^ 2 * s1 ^ 2 + 3 * D ^ 4 * (583 * B ^ 2) ^ 2 * s2
      + 27 * D ^ 2 * q ^ 2 := by
  have := arith2_sq hD0 h (by positivity) (by positivity) hs20 hs2
  have e : 3 * D ^ 2 * ((23 * B ^ 2) ^ 2 * s1 ^ 2 + (583 * B ^ 2) ^ 2 * D ^ 2 * s2 + 9 * q ^ 2)
      = 3 * D ^ 2 * (23 * B ^ 2) ^ 2 * s1 ^ 2 + 3 * D ^ 4 * (583 * B ^ 2) ^ 2 * s2
        + 27 * D ^ 2 * q ^ 2 := by ring
  linarith only [this, e]

/-- The bound on the intermediate event (`max|ε| ≤ 1/8`). -/
theorem mid_bound {x B s1 s2 q : ℝ} (hB : 1 ≤ B)
    (h : |x| ≤ 1 / 8 * (23 * B ^ 2 * |s1| + 583 * B ^ 2 * s2 + 3 * |q|))
    (hs2 : s2 ≤ (1 / 8) ^ 2) (hs1 : |s1| ≤ 1 / 8) (hq : |q| ≤ B) : x ^ 2 ≤ 4 * B ^ 4 := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hBB : B ≤ B ^ 2 := by nlinarith only [hB]
  have t1 : 23 * B ^ 2 * |s1| ≤ 23 * B ^ 2 * (1 / 8) :=
    mul_le_mul_of_nonneg_left hs1 (by positivity)
  have t2 : 583 * B ^ 2 * s2 ≤ 583 * B ^ 2 * (1 / 8) ^ 2 :=
    mul_le_mul_of_nonneg_left hs2 (by positivity)
  have hle : |x| ≤ 2 * B ^ 2 := by
    have : 1 / 8 * (23 * B ^ 2 * |s1| + 583 * B ^ 2 * s2 + 3 * |q|)
        ≤ 1 / 8 * (23 * B ^ 2 * (1 / 8) + 583 * B ^ 2 * (1 / 8) ^ 2 + 3 * B ^ 2) := by
      have : 3 * |q| ≤ 3 * B ^ 2 := by linarith only [hq, hBB]
      linarith only [t1, t2, this]
    nlinarith only [h, this, _root_.sq_nonneg B]
  have h2 : x ^ 2 ≤ (2 * B ^ 2) ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hle 2
  linarith only [h2, show (2 * B ^ 2) ^ 2 = 4 * B ^ 4 by ring]

/-- **`E (Tr P² - Q_lin,2)²`**: for `0 ≤ δ ≤ 1/8`, `B = m₁²`,
    `≤ 3δ²(23B²)² · 3m₁²/N² + 3δ⁴(583B²)² · 2m₁²/N + 27δ² · 3B²/N²
        + 4B⁴ P(max|ε| > δ) + (N + 83 B⁵)² P(max|ε| > 1/8)`. -/
theorem trace2_sq [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) :
    BM (trP2 d σ N X)
      ∧ ∫ ω, (trP2 d σ N X ω - Qlin2 (torusM d σ 2) (kT d σ) (wT d σ) X N ω) ^ 2 ∂μ
        ≤ 3 * δ ^ 2 * (23 * (torusM d σ 1 ^ 2) ^ 2) ^ 2 * (3 * torusM d σ 1 ^ 2 / (N : ℝ) ^ 2)
          + 3 * δ ^ 4 * (583 * (torusM d σ 1 ^ 2) ^ 2) ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + 27 * δ ^ 2 * (3 * (torusM d σ 1 ^ 2) ^ 2 / (N : ℝ) ^ 2)
          + 4 * (torusM d σ 1 ^ 2) ^ 4
            * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ}
          + (N + 83 * (torusM d σ 1 ^ 2) ^ 5) ^ 2
            * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8} := by
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  have hN' : 0 < N := hN
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  obtain ⟨b1, b2, m2e, m1e⟩ := s_moments X h_indep hX hlaw hσ N hN
  obtain ⟨bq, mq⟩ := q0_moments X h_indep hX hlaw hσ N hN
  obtain ⟨hm1, hm2M, hMM⟩ := m2_bounds (d := d) hσ
  have V := VK.mono (torus_vk (d := d) hσ) hMM
  have W := torus_wk (d := d) hσ
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  obtain ⟨m2, hm2d⟩ : ∃ m2 : ℝ, m2 = torusM d σ 2 := ⟨_, rfl⟩
  rw [← hMd] at hm2M hMM m1e m2e mq V W ⊢
  rw [← hm2d] at hm1 hm2M ⊢
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = M ^ 2 := ⟨_, rfl⟩
  rw [← hBd] at hMM mq m1e m2e V W ⊢
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hB1 : 1 ≤ B := hM1.trans hMM
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hm0 : 0 ≤ m2 := zero_le_one.trans hm1
  have hmB : m2 ≤ B := hm2M.trans hMM
  -- measurability
  have mT' : Measurable (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ 2).trace) :=
    Finset.measurable_sum _ fun a _ => walk_pow_entry_measurable hσ d X hX N 2 a a
  have mT : Measurable (trP2 d σ N X) := mT'
  have hTb : ∀ ω, |trP2 d σ N X ω| ≤ N := fun ω =>
    walk_pow_trace_le (torusK d σ N (fun j => X j ω)) (torusRho d σ N (fun j => X j ω))
      (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) 2
  have bT : BM (trP2 d σ N X) := ⟨mT, N, hTb⟩
  refine ⟨bT, ?_⟩
  -- `Q_lin,2` is bounded and measurable: from the decomposition
  have Dψ := psi2_deg2 H V W hm0 hmB
  have bS : BM (Soff (psi2 m2 (kT d σ) (wT d σ)) X N) :=
    ⟨OracleTwo.Soff_meas Dψ N, _, OracleTwo.Soff_bound Dψ N⟩
  obtain ⟨bR, _⟩ := Rem_total_var (μ := μ) H V W hm0 hmB hN'
  have bU : BM (U2 m2 (kT d σ) (wT d σ) X N) := BM.const_mul _ bS
  have bQ : BM (Qlin2 m2 (kT d σ) (wT d σ) X N) := by
    have e : Qlin2 m2 (kT d σ) (wT d σ) X N = fun ω =>
        (2 * m2 * (1 + VarianceOne.psiK (kT d σ) 0 / N) - m2
            + 1 / (N : ℝ) ^ 2 * (N * phiW (wT d σ) 0))
          + U2 m2 (kT d σ) (wT d σ) X N ω
          + (2 * m2 * Rem (kT d σ) X N ω + Rem2 (kT d σ 0) (wT d σ) X N ω) := by
      funext ω; rw [Qlin2_decomp W m2 hN' ω]
    rw [e]; exact ((BM.const _).add bU).add bR
  -- the events
  have hGm : ∀ D : ℝ,
      MeasurableSet {ω | ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ D} := by
    intro D
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => measurableSet_le
      (continuous_abs.measurable.comp
        ((heatRho_sample_measurable hσ d X hX N a).sub measurable_const)) measurable_const
  obtain ⟨Bd, hBdd⟩ : ∃ Bd : Set Ω,
      Bd = {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  obtain ⟨B8, hB8⟩ : ∃ B8 : Set Ω,
      B8 = {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8} := ⟨_, rfl⟩
  have hBdm : MeasurableSet Bd := by rw [hBdd]; exact (hGm δ).compl
  have hB8m : MeasurableSet B8 := by rw [hB8]; exact (hGm (1 / 8)).compl
  rw [← hBdd, ← hB8]
  obtain ⟨g1, hg1⟩ : ∃ g1 : Ω → ℝ, g1 = fun ω =>
      3 * δ ^ 2 * (23 * B ^ 2) ^ 2 * s1T d σ N X ω ^ 2
        + 3 * δ ^ 4 * (583 * B ^ 2) ^ 2 * s2T d σ N X ω + 27 * δ ^ 2 * q0T d σ N X ω ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g2 : Ω → ℝ,
      g2 = fun ω => 4 * B ^ 4 * Bd.indicator (fun _ => (1 : ℝ)) ω := ⟨_, rfl⟩
  obtain ⟨g3, hg3⟩ : ∃ g3 : Ω → ℝ,
      g3 = fun ω => (N + 83 * B ^ 5) ^ 2 * B8.indicator (fun _ => (1 : ℝ)) ω := ⟨_, rfl⟩
  have bg1 : BM g1 := by
    rw [hg1]
    exact ((BM.const_mul _ b1.sqr).add (BM.const_mul _ b2)).add (BM.const_mul _ bq.sqr)
  have ig2 : Integrable g2 μ := by
    rw [hg2]; exact ((integrable_const (1 : ℝ)).indicator hBdm).const_mul _
  have ig3 : Integrable g3 μ := by
    rw [hg3]; exact ((integrable_const (1 : ℝ)).indicator hB8m).const_mul _
  have hs2n : ∀ ω, 0 ≤ s2T d σ N X ω := fun ω => by
    rw [(s_eps σ N hN' X ω).2.1]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => _root_.sq_nonneg _)
  have hg1n : ∀ ω, 0 ≤ g1 ω := fun ω => by
    rw [hg1]
    have := hs2n ω
    positivity
  have hpt : ∀ ω, (trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω) ^ 2
      ≤ g1 ω + g2 ω + g3 ω := by
    intro ω
    obtain ⟨hgood, hcrude, hq0b⟩ := trace2_bounds hσ N hN' X ω
    rw [← hMd, ← hm2d, ← hBd] at hgood hcrude
    rw [← hMd, ← hBd] at hq0b
    have hg1ω := hg1n ω
    by_cases h8 : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8
    · have hn8 : ω ∉ B8 := by rw [hB8]; exact fun h => h h8
      have e3 : g3 ω = 0 := by rw [hg3]; simp only; rw [Set.indicator_of_notMem hn8, mul_zero]
      by_cases hd : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ
      · have hnd : ω ∉ Bd := by rw [hBdd]; exact fun h => h hd
        have e2 : g2 ω = 0 := by rw [hg2]; simp only; rw [Set.indicator_of_notMem hnd, mul_zero]
        obtain ⟨hb, s20, s2le, _⟩ := hgood δ hδ0 hδ hd
        have := good_sq hδ0 hB0 hb s20 s2le
        rw [e2, e3, add_zero, add_zero, hg1]
        exact this
      · have hind : ω ∈ Bd := by rw [hBdd]; exact hd
        have e2 : g2 ω = 4 * B ^ 4 := by
          rw [hg2]; simp only; rw [Set.indicator_of_mem hind, mul_one]
        obtain ⟨hb, _, s2le, s1le⟩ := hgood (1 / 8) (by norm_num) le_rfl h8
        have hsq : (trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω) ^ 2 ≤ 4 * B ^ 4 :=
          mid_bound hB1 hb s2le s1le hq0b
        rw [e2, e3, add_zero]
        linarith only [hsq, hg1ω]
    · have hin8 : ω ∈ B8 := by rw [hB8]; exact h8
      have e3 : g3 ω = (N + 83 * B ^ 5) ^ 2 := by
        rw [hg3]; simp only; rw [Set.indicator_of_mem hin8, mul_one]
      have hg2n : 0 ≤ g2 ω := by
        rw [hg2]
        exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
      have hsq : (trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω) ^ 2
          ≤ (N + 83 * B ^ 5) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hcrude 2
      rw [e3]
      linarith only [hsq, hg1ω, hg2n]
  have hint : ∫ ω, (trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω) ^ 2 ∂μ
      ≤ ∫ ω, (g1 ω + g2 ω + g3 ω) ∂μ :=
    integral_mono (bT.sub bQ).sqr.integrable
      (((bg1.integrable.add ig2 : Integrable (fun ω => g1 ω + g2 ω) μ).add ig3 :
        Integrable (fun ω => g1 ω + g2 ω + g3 ω) μ)) hpt
  have hval : ∫ ω, (g1 ω + g2 ω + g3 ω) ∂μ
      = (3 * δ ^ 2 * (23 * B ^ 2) ^ 2 * ∫ ω, s1T d σ N X ω ^ 2 ∂μ
          + 3 * δ ^ 4 * (583 * B ^ 2) ^ 2 * ∫ ω, s2T d σ N X ω ∂μ
          + 27 * δ ^ 2 * ∫ ω, q0T d σ N X ω ^ 2 ∂μ)
        + 4 * B ^ 4 * μ.real Bd + (N + 83 * B ^ 5) ^ 2 * μ.real B8 := by
    have i12 : Integrable (fun ω => g1 ω + g2 ω) μ := bg1.integrable.add ig2
    have j1 : Integrable (fun ω => 3 * δ ^ 2 * (23 * B ^ 2) ^ 2 * s1T d σ N X ω ^ 2) μ :=
      (BM.const_mul _ b1.sqr).integrable
    have j2 : Integrable (fun ω => 3 * δ ^ 4 * (583 * B ^ 2) ^ 2 * s2T d σ N X ω) μ :=
      (BM.const_mul _ b2).integrable
    have j3 : Integrable (fun ω => 27 * δ ^ 2 * q0T d σ N X ω ^ 2) μ :=
      (BM.const_mul _ bq.sqr).integrable
    have j12 : Integrable (fun ω => 3 * δ ^ 2 * (23 * B ^ 2) ^ 2 * s1T d σ N X ω ^ 2
        + 3 * δ ^ 4 * (583 * B ^ 2) ^ 2 * s2T d σ N X ω) μ := j1.add j2
    rw [integral_add i12 ig3, integral_add bg1.integrable ig2, hg1, hg2,
      hg3, integral_add j12 j3, integral_add j1 j2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul,
      integral_indicator_const (1 : ℝ) hBdm, integral_indicator_const (1 : ℝ) hB8m,
      smul_eq_mul, mul_one, smul_eq_mul, mul_one]
  rw [hval] at hint
  have k1 := mul_le_mul_of_nonneg_left m1e
    (by positivity : (0 : ℝ) ≤ 3 * δ ^ 2 * (23 * B ^ 2) ^ 2)
  have k2 := mul_le_mul_of_nonneg_left m2e
    (by positivity : (0 : ℝ) ≤ 3 * δ ^ 4 * (583 * B ^ 2) ^ 2)
  have k3 := mul_le_mul_of_nonneg_left mq (by positivity : (0 : ℝ) ≤ 27 * δ ^ 2)
  linarith only [hint, k1, k2, k3]

/-- The remainder of `variance_two_general` (`B = m₁²`). -/
noncomputable def varRem2 (M δ p1 p2 : ℝ) (N : ℕ) : ℝ :=
  2 * (3 * δ ^ 2 * (23 * (M ^ 2) ^ 2) ^ 2 * (3 * M ^ 2 / (N : ℝ) ^ 2)
      + 3 * δ ^ 4 * (583 * (M ^ 2) ^ 2) ^ 2 * (2 * M ^ 2 / N)
      + 27 * δ ^ 2 * (3 * (M ^ 2) ^ 2 / (N : ℝ) ^ 2)
      + 4 * (M ^ 2) ^ 4 * p1 + (N + 83 * (M ^ 2) ^ 5) ^ 2 * p2)
    + 2 * (34629061120 * (M ^ 2) ^ 10 / (N : ℝ) ^ 3)

/-- **`prop:variance` for `k = 2`, with self-loops, on the flat torus with the heat kernel;
    general normalisation event.**  For independent uniform points, `N ≥ 1`, `0 ≤ δ ≤ 1/8` and
    every `θ > 0`, with `U₂ = (1/(2N²)) ∑_{i≠j} H₂(X_i - X_j)` (`U2`), `H₂ = 2 psi2 =
    2(1 - 𝒫)⁴ p² - 4 m₂ (1 - 𝒫)³ p` and `v₂ = ½ ∫ H₂²` (`v2`):
    (1) `Var U₂ = v₂ (N-1)/N³` exactly; (2) `Var(Tr P² - U₂) ≤ R`;
    (3) `|Var Tr P² - v₂ (N-1)/N³| ≤ θ v₂ (N-1)/N³ + (1 + 1/θ) R`,
    `R = varRem2 m₁ δ P(max|ε| > δ) P(max|ε| > 1/8) N`. -/
theorem variance_two_general [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) {θ : ℝ} (hθ : 0 < θ) :
    cv μ (U2 (torusM d σ 2) (kT d σ) (wT d σ) X N) = v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3
    ∧ cv μ (fun ω => trP2 d σ N X ω - U2 (torusM d σ 2) (kT d σ) (wT d σ) X N ω)
        ≤ varRem2 (torusM d σ 1) δ
          (μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ})
          (μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8}) N
    ∧ |cv μ (trP2 d σ N X) - v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * varRem2 (torusM d σ 1) δ
          (μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ})
          (μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8}) N := by
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  have hN' : 0 < N := hN
  obtain ⟨bT, hsq⟩ := trace2_sq X h_indep hX hlaw hσ N hN hδ0 hδ
  obtain ⟨p1, hp1⟩ : ∃ p1 : ℝ, p1
      = μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p2 : ℝ, p2
      = μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8} := ⟨_, rfl⟩
  rw [← hp1, ← hp2] at hsq ⊢
  obtain ⟨hm1, hm2M, hMM⟩ := m2_bounds (d := d) hσ
  have V := VK.mono (torus_vk (d := d) hσ) hMM
  have W := torus_wk (d := d) hσ
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  obtain ⟨m2, hm2d⟩ : ∃ m2 : ℝ, m2 = torusM d σ 2 := ⟨_, rfl⟩
  have hv2 : v2 d σ = 2 * ∫ u, psi2 m2 (kT d σ) (wT d σ) u ^ 2 ∂flatTorusMeasure d := by
    rw [hm2d]; rfl
  rw [← hMd] at hm2M hMM hsq V W ⊢
  rw [← hm2d] at hm1 hm2M hsq ⊢
  have hm0 : 0 ≤ m2 := zero_le_one.trans hm1
  have hmB : m2 ≤ M ^ 2 := hm2M.trans hMM
  -- the two-point statistic
  have Dψ := psi2_deg2 H V W hm0 hmB
  obtain ⟨Wv, hWd⟩ : ∃ Wv : ℝ, Wv = ∫ u, psi2 m2 (kT d σ) (wT d σ) u ^ 2 ∂flatTorusMeasure d :=
    ⟨_, rfl⟩
  have hmeas : Measurable (psi2 m2 (kT d σ) (wT d σ)) :=
    (V.psi_meas.const_mul (2 * m2)).add (phi_meas W)
  have hW : ∀ x, ∫ z, psi2 m2 (kT d σ) (wT d σ) (x - z) ^ 2 ∂flatTorusMeasure d = Wv :=
    fun x => by
      rw [hWd]; exact V.inv (fun u => psi2 m2 (kT d σ) (wT d σ) u ^ 2) (hmeas.pow_const 2) x
  have sm := deg_second_moment Dψ hW N
  have mz := deg_mean Dψ N
  have bS : BM (Soff (psi2 m2 (kT d σ) (wT d σ)) X N) :=
    ⟨OracleTwo.Soff_meas Dψ N, _, OracleTwo.Soff_bound Dψ N⟩
  have bU : BM (U2 m2 (kT d σ) (wT d σ) X N) := BM.const_mul _ bS
  have hU0 : ∫ ω, U2 m2 (kT d σ) (wT d σ) X N ω ∂μ = 0 := by
    unfold U2; rw [integral_const_mul, mz, mul_zero]
  have hcvU : cv μ (U2 m2 (kT d σ) (wT d σ) X N) = v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3 := by
    rw [cv_of_mean_zero bU hU0, hv2, ← hWd]
    have e : ∀ ω, U2 m2 (kT d σ) (wT d σ) X N ω ^ 2
        = (1 / (N : ℝ) ^ 2) ^ 2 * Soff (psi2 m2 (kT d σ) (wT d σ)) X N ω ^ 2 := fun ω => by
      unfold U2; ring
    simp_rw [e]
    rw [integral_const_mul, sm]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN'.ne'
    field_simp
  -- the difference `Q_lin,2 - U₂`
  obtain ⟨bR, hR⟩ := Rem_total_var (μ := μ) H V W hm0 hmB hN'
  have hQU : cv μ (fun ω => Qlin2 m2 (kT d σ) (wT d σ) X N ω - U2 m2 (kT d σ) (wT d σ) X N ω)
      ≤ 34629061120 * (M ^ 2) ^ 10 / (N : ℝ) ^ 3 := by
    have e : (fun ω => Qlin2 m2 (kT d σ) (wT d σ) X N ω - U2 m2 (kT d σ) (wT d σ) X N ω)
        = fun ω => (2 * m2 * Rem (kT d σ) X N ω + Rem2 (kT d σ 0) (wT d σ) X N ω)
          + (2 * m2 * (1 + VarianceOne.psiK (kT d σ) 0 / N) - m2
            + 1 / (N : ℝ) ^ 2 * (N * phiW (wT d σ) 0)) := by
      funext ω; rw [Qlin2_decomp W m2 hN' ω]; ring
    rw [e, cv_add_const bR]
    exact hR
  have bQ : BM (Qlin2 m2 (kT d σ) (wT d σ) X N) := by
    have e : Qlin2 m2 (kT d σ) (wT d σ) X N = fun ω =>
        (2 * m2 * (1 + VarianceOne.psiK (kT d σ) 0 / N) - m2
            + 1 / (N : ℝ) ^ 2 * (N * phiW (wT d σ) 0))
          + U2 m2 (kT d σ) (wT d σ) X N ω
          + (2 * m2 * Rem (kT d σ) X N ω + Rem2 (kT d σ 0) (wT d σ) X N ω) := by
      funext ω; rw [Qlin2_decomp W m2 hN' ω]
    rw [e]; exact ((BM.const _).add bU).add bR
  have bTQ : BM (fun ω => trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω) := bT.sub bQ
  have bQU : BM (fun ω => Qlin2 m2 (kT d σ) (wT d σ) X N ω - U2 m2 (kT d σ) (wT d σ) X N ω) :=
    bQ.sub bU
  have hTQ : cv μ (fun ω => trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω)
      ≤ ∫ ω, (trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω) ^ 2 ∂μ := cv_le_sq bTQ
  have hg : cv μ (fun ω => trP2 d σ N X ω - U2 m2 (kT d σ) (wT d σ) X N ω)
      ≤ varRem2 M δ p1 p2 N := by
    have e : (fun ω => trP2 d σ N X ω - U2 m2 (kT d σ) (wT d σ) X N ω)
        = fun ω => (trP2 d σ N X ω - Qlin2 m2 (kT d σ) (wT d σ) X N ω)
          + (Qlin2 m2 (kT d σ) (wT d σ) X N ω - U2 m2 (kT d σ) (wT d σ) X N ω) := by
      funext ω; ring
    rw [e]
    have := cv_add_le (μ := μ) bTQ bQU
    unfold varRem2
    linarith only [this, hTQ, hsq, hQU]
  refine ⟨hcvU, hg, ?_⟩
  have hper := cv_perturb (μ := μ) bU (bT.sub bU) hθ
  have e : (fun ω => U2 m2 (kT d σ) (wT d σ) X N ω
      + (trP2 d σ N X ω - U2 m2 (kT d σ) (wT d σ) X N ω)) = trP2 d σ N X := by
    funext ω; ring
  rw [e, hcvU] at hper
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left hg hθ'
  linarith only [hper, this]

theorem varRem2_mono {M δ p1 p1' p2 : ℝ} (N : ℕ) (h : p1 ≤ p1') :
    varRem2 M δ p1 p2 N ≤ varRem2 M δ p1' p2 N := by
  unfold varRem2
  have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 * (M ^ 2) ^ 4)
  linarith only [this]

/-- **`prop:variance` for `k = 2` with self-loops, heat kernel on the flat torus.**  Under the
    hypotheses of `norm_sample` (`σ ≤ 1`, `d ≥ 1`, `N ≥ 2`, `kernelC1 d · δ' ≤ 1` with
    `δ' = √(m₁ log N / N)`), for every `θ > 0`:
    `|Var Tr P² - v₂ (N-1)/N³| ≤ θ v₂ (N-1)/N³ + (1 + 1/θ) · varRem2 m₁ (normC δ') N⁻³ p₈ N`,
    `p₈ = P(max_a |ρ_a - 1| > 1/8)` (bounded in `VarianceOne.p8_le`). -/
theorem variance_two [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1)
    {θ : ℝ} (hθ : 0 < θ) :
    |cv μ (trP2 d σ N X) - v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * varRem2 (torusM d σ 1) (TorusReductionL1.normC d * δp)
          (1 / (N : ℝ) ^ 3)
          (μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8}) N := by
  have hr : kernelC1 d * δp * Real.sqrt ((1 : ℕ) : ℝ) ≤ 1 := by
    rw [Nat.cast_one, Real.sqrt_one, mul_one]; exact hrange
  obtain ⟨h8, hp⟩ := TorusReductionL1.norm_sample hσ hσ1 d hd X h_indep hX hlaw N 1 hN2
    Nat.one_pos hMp hδp hr
  have hδ0 : 0 ≤ TorusReductionL1.normC d * δp := by
    rw [hδp]; exact mul_nonneg (TorusReductionL1.normC_nonneg d) (Real.sqrt_nonneg _)
  have h := (variance_two_general X h_indep hX hlaw hσ N (by omega) hδ0 h8 hθ).2.2
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left (varRem2_mono (M := torusM d σ 1)
    (δ := TorusReductionL1.normC d * δp)
    (p2 := μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8}) N hp) hθ'
  linarith only [h, this]

end Final2

section Final3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`variance_two` with `θ = N^{-1/2}`**:
    `|Var Tr P² - v₂ (N-1)/N³| ≤ v₂ (N-1)/N^{7/2} + (1 + √N) · varRem2 m₁ (normC δ') N⁻³ p₈ N`. -/
theorem variance_two_sqrt [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1) :
    |cv μ (trP2 d σ N X) - v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ 1 / Real.sqrt N * (v2 d σ * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + Real.sqrt N) * varRem2 (torusM d σ 1) (TorusReductionL1.normC d * δp)
          (1 / (N : ℝ) ^ 3)
          (μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8}) N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have h := variance_two hσ hσ1 d hd X h_indep hX hlaw N hN2 hMp hδp hrange
    (θ := 1 / Real.sqrt N) (by positivity)
  rwa [one_div_one_div] at h

end Final3

end VarianceTwo

/-! ## Lemma "degenerate", part (b), for three indices (A95)

General tools: the whole sample as a point `x : ℕ → G`, and the integration of one free
coordinate. -/

namespace DegenerateB

open PiBound

section IO

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [MeasurableSpace G]

/-- The sample as a point of `ℕ → G`. -/
def smp (X : ℕ → Ω → G) (ω : Ω) : ℕ → G := fun k => X k ω

theorem smp_meas {X : ℕ → Ω → G} (hX : ∀ j, Measurable (X j)) : Measurable (smp X) :=
  measurable_pi_lambda _ hX

/-- **Integrating one coordinate out.** `Φ` bounded measurable, depending only on the
    coordinates in the finite set `T`: `E Φ(X) = E ∫ Φ(X with the coordinate j replaced by z) dν(z)`;
    the inner function is integrable. -/
theorem integrate_out_core [IsProbabilityMeasure μ] (ν : Measure G) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (j : ℕ) (T : Finset ℕ)
    (Φ : (ℕ → G) → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ x, |Φ x| ≤ B)
    (hdep : ∀ x y : ℕ → G, (∀ k ∈ T, x k = y k) → Φ x = Φ y) :
    ∫ ω, Φ (smp X ω) ∂μ = ∫ ω, (∫ z, Φ (Function.update (smp X ω) j z) ∂ν) ∂μ ∧
    Integrable (fun ω => ∫ z, Φ (Function.update (smp X ω) j z) ∂ν) μ := by
  classical
  set S : Finset ℕ := T.erase j with hS
  have hj : j ∉ S := by rw [hS]; exact Finset.notMem_erase j T
  let emb : G × (S → G) → (ℕ → G) := fun p k =>
    if k = j then p.1 else if h : k ∈ S then p.2 ⟨k, h⟩ else p.1
  have hemb : Measurable emb := by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k = j
    · have e : (fun p : G × (S → G) => emb p k) = fun p => p.1 := by
        funext p; simp [emb, hk]
      rw [e]; exact measurable_fst
    · by_cases hkS : k ∈ S
      · have e : (fun p : G × (S → G) => emb p k) = fun p => p.2 ⟨k, hkS⟩ := by
          funext p; simp [emb, hk, hkS]
        rw [e]; exact (measurable_pi_apply _).comp measurable_snd
      · have e : (fun p : G × (S → G) => emb p k) = fun p => p.1 := by
          funext p; simp [emb, hk, hkS]
        rw [e]; exact measurable_fst
  let Gf : G × (S → G) → ℝ := fun p => Φ (emb p)
  have hGf : Measurable Gf := hΦ.comp hemb
  have hY : Measurable (fun ω (t : S) => X t ω) := measurable_pi_lambda _ fun t => hX t
  have hind0 := h_indep.indepFun_finset {j} S (Finset.disjoint_singleton_left.mpr hj) hX
  have hind : IndepFun (X j) (fun ω (t : S) => X t ω) μ :=
    hind0.comp (φ := fun u : (({j} : Finset ℕ) → G) => u ⟨j, Finset.mem_singleton_self j⟩)
      (ψ := id) (measurable_pi_apply _) measurable_id
  have e1 : ∀ ω, Φ (smp X ω) = Gf (X j ω, fun t : S => X t ω) := by
    intro ω
    apply hdep
    intro k hk
    by_cases hkj : k = j
    · subst hkj; simp [Gf, emb, smp]
    · have hkS : k ∈ S := by rw [hS]; exact Finset.mem_erase.mpr ⟨hkj, hk⟩
      simp [Gf, emb, smp, hkj, hkS]
  have e2 : ∀ ω z, Φ (Function.update (smp X ω) j z) = Gf (z, fun t : S => X t ω) := by
    intro ω z
    apply hdep
    intro k hk
    by_cases hkj : k = j
    · subst hkj; simp [Gf, emb]
    · have hkS : k ∈ S := by rw [hS]; exact Finset.mem_erase.mpr ⟨hkj, hk⟩
      simp [Gf, emb, smp, hkj, hkS, Function.update_apply]
  have hinner : Measurable (fun y : S → G => ∫ z, Gf (z, y) ∂ν) :=
    (hGf.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable
  have hbd : ∀ y : S → G, |∫ z, Gf (z, y) ∂ν| ≤ B := by
    intro y
    have h := norm_integral_le_of_norm_le_const (μ := ν) (C := B) (f := fun z => Gf (z, y))
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _)
    simpa using h
  refine ⟨?_, ?_⟩
  · simp_rw [e1, e2]
    rw [indep_integral_eq ν (X j) _ (hX j) hY hind (hlaw j) Gf hGf (fun p => hB (emb p))]
    exact integral_map hY.aemeasurable hinner.aestronglyMeasurable
  · simp_rw [e2]
    exact Integrable.of_bound (hinner.comp hY).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd _)

/-- Equality form: if the inner integral equals `Φ'(x)` for every `x`, then `E Φ = E Φ'`. -/
theorem integrate_out [IsProbabilityMeasure μ] (ν : Measure G) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (j : ℕ) (T : Finset ℕ)
    (Φ : (ℕ → G) → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ x, |Φ x| ≤ B)
    (hdep : ∀ x y : ℕ → G, (∀ k ∈ T, x k = y k) → Φ x = Φ y)
    (Φ' : (ℕ → G) → ℝ) (hin : ∀ x, ∫ z, Φ (Function.update x j z) ∂ν = Φ' x) :
    ∫ ω, Φ (smp X ω) ∂μ = ∫ ω, Φ' (smp X ω) ∂μ := by
  rw [(integrate_out_core ν X h_indep hX hlaw j T Φ hΦ hB hdep).1]
  simp_rw [hin]

/-- Upper-bound form. -/
theorem integrate_out_le [IsProbabilityMeasure μ] (ν : Measure G) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (j : ℕ) (T : Finset ℕ)
    (Φ : (ℕ → G) → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ x, |Φ x| ≤ B)
    (hdep : ∀ x y : ℕ → G, (∀ k ∈ T, x k = y k) → Φ x = Φ y)
    (Ψ : (ℕ → G) → ℝ) (hΨ : Integrable (fun ω => Ψ (smp X ω)) μ)
    (hin : ∀ x, ∫ z, Φ (Function.update x j z) ∂ν ≤ Ψ x) :
    ∫ ω, Φ (smp X ω) ∂μ ≤ ∫ ω, Ψ (smp X ω) ∂μ := by
  obtain ⟨h1, h2⟩ := integrate_out_core ν X h_indep hX hlaw j T Φ hΦ hB hdep
  rw [h1]
  exact integral_mono h2 hΨ (fun ω => hin _)

end IO

/-- Indicator of a proposition. -/
noncomputable def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

theorem ind_nonneg (P : Prop) [Decidable P] : 0 ≤ ind P := by unfold ind; split_ifs <;> norm_num

theorem ind_le_one (P : Prop) [Decidable P] : ind P ≤ 1 := by unfold ind; split_ifs <;> norm_num

theorem ind_true {P : Prop} [Decidable P] (h : P) : ind P = 1 := by unfold ind; rw [if_pos h]

theorem ind_false {P : Prop} [Decidable P] (h : ¬P) : ind P = 0 := by unfold ind; rw [if_neg h]

/-- Membership of an index in a triple, resp. a quadruple, of indices. -/
def m3 (x i j l : ℕ) : Prop := x = i ∨ x = j ∨ x = l
def m4 (x i j l v : ℕ) : Prop := x = i ∨ x = j ∨ x = l ∨ x = v

instance (x i j l : ℕ) : Decidable (m3 x i j l) := by unfold m3; infer_instance
instance (x i j l v : ℕ) : Decidable (m4 x i j l v) := by unfold m4; infer_instance

/-- Three, resp. four, distinct indices. -/
def dist3 (i j l : ℕ) : Prop := i ≠ j ∧ i ≠ l ∧ j ≠ l
def dist4 (i j l v : ℕ) : Prop := i ≠ j ∧ i ≠ l ∧ i ≠ v ∧ j ≠ l ∧ j ≠ v ∧ l ≠ v

instance (i j l : ℕ) : Decidable (dist3 i j l) := by unfold dist3; infer_instance
instance (i j l v : ℕ) : Decidable (dist4 i j l v) := by unfold dist4; infer_instance

/-- Hypotheses of Lemma "degenerate"(b) for `n = 3` and `a = 3`. Independent points with law `ν`;
    `F` bounded (`B`) and measurable; `c` measurable with the properties of `c = p - 1` used in the
    proof (`|c| ≤ M`, mean zero in either argument, `∫|c| ≤ 2`, `∫ c² ≤ M`,
    `|∫ c(x - z) c(y - z) dz| ≤ M`). `Fm` is the (constant) conditional mean of `F` given its last
    point. The norms are upper bounds: `L ≥ ‖F‖₁` (both as the marginals given one point and in
    sample form), `V ≥ ‖F‖₂²`, `ρ ≥ ϱ(F)` (sample form, as in `DegA3`). -/
structure DegB3 {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) {G : Type*}
    [AddCommGroup G] [MeasurableSpace G] (ν : Measure G) (X : ℕ → Ω → G) (F : G → G → G → ℝ)
    (c : G → ℝ) (B M L V ρ Fm : ℝ) : Prop where
  indep : iIndepFun X μ
  meas : ∀ j, Measurable (X j)
  law : ∀ j, μ.map (X j) = ν
  F_meas : Measurable (fun p : G × G × G => F p.1 p.2.1 p.2.2)
  bound : ∀ a b c, |F a b c| ≤ B
  c_meas : Measurable c
  c_bound : ∀ u, |c u| ≤ M
  c_mean1 : ∀ x, ∫ z, c (x - z) ∂ν = 0
  c_mean2 : ∀ x, ∫ z, c (z - x) ∂ν = 0
  c_abs : ∀ x, ∫ z, |c (x - z)| ∂ν ≤ 2
  c_sq : ∀ x, ∫ z, c (x - z) ^ 2 ∂ν ≤ M
  c_cov : ∀ x y, |∫ z, c (x - z) * c (y - z) ∂ν| ≤ M
  mean12 : ∀ y, ∫ b, (∫ a, F a b y ∂ν) ∂ν = Fm
  marg1 : ∀ y, ∫ b, (∫ a, |F y a b| ∂ν) ∂ν ≤ L
  marg2 : ∀ y, ∫ b, (∫ a, |F a y b| ∂ν) ∂ν ≤ L
  marg3 : ∀ y, ∫ b, (∫ a, |F a b y| ∂ν) ∂ν ≤ L
  l1 : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, |F (X i ω) (X j ω) (X l ω)| ∂μ ≤ L
  var : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, F (X i ω) (X j ω) (X l ω) ^ 2 ∂μ ≤ V
  rho12 : ∀ i l : ℕ, i ≠ l → ∫ ω, |F (X i ω) (X i ω) (X l ω)| ∂μ ≤ ρ
  rho13 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X i ω)| ∂μ ≤ ρ
  rho23 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X j ω)| ∂μ ≤ ρ
  L_nonneg : 0 ≤ L
  V_nonneg : 0 ≤ V
  rho_nonneg : 0 ≤ ρ

/-- The summand `F(x_i,x_j,x_l) c(x_l - x_v)` as a function of the whole sample. -/
def wv {G : Type*} [AddCommGroup G] (F : G → G → G → ℝ) (c : G → ℝ) (i j l v : ℕ)
    (x : ℕ → G) : ℝ :=
  F (x i) (x j) (x l) * c (x l - x v)

/-- `F(x_i,x_j,x_l)` as a function of the whole sample. -/
def fv {G : Type*} (F : G → G → G → ℝ) (i j l : ℕ) (x : ℕ → G) : ℝ := F (x i) (x j) (x l)

namespace DegB3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G]
  {ν : Measure G} {X : ℕ → Ω → G} {F : G → G → G → ℝ} {c : G → ℝ} {B M L V ρ Fm : ℝ}

theorem B_nonneg (H : DegB3 μ ν X F c B M L V ρ Fm) (x : G) : 0 ≤ B :=
  (abs_nonneg (F x x x)).trans (H.bound x x x)

theorem M_nonneg (H : DegB3 μ ν X F c B M L V ρ Fm) (x : G) : 0 ≤ M :=
  (abs_nonneg (c x)).trans (H.c_bound x)

theorem fv_meas (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l : ℕ) : Measurable (fv F i j l) := by
  have hm : Measurable (fun x : ℕ → G => (x i, x j, x l)) := by fun_prop
  exact H.F_meas.comp hm

theorem cv_meas (H : DegB3 μ ν X F c B M L V ρ Fm) (l v : ℕ) :
    Measurable (fun x : ℕ → G => c (x l - x v)) := by
  have hm : Measurable (fun x : ℕ → G => x l - x v) := by fun_prop
  exact H.c_meas.comp hm

theorem wv_meas (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) : Measurable (wv F c i j l v) :=
  (H.fv_meas i j l).mul (H.cv_meas l v)

theorem wv_bound (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) (x : ℕ → G) :
    |wv F c i j l v x| ≤ B * M := by
  unfold wv; rw [abs_mul]
  exact mul_le_mul (H.bound _ _ _) (H.c_bound _) (abs_nonneg _) (H.B_nonneg (x 0))

theorem fv_bound (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l : ℕ) (x : ℕ → G) :
    |fv F i j l x| ≤ B := H.bound _ _ _

theorem BM_fv (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l : ℕ) :
    BM (fun ω => fv F i j l (smp X ω)) :=
  ⟨(H.fv_meas i j l).comp (smp_meas H.meas), B, fun _ => H.fv_bound _ _ _ _⟩

theorem BM_wv (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) :
    BM (fun ω => wv F c i j l v (smp X ω)) :=
  ⟨(H.wv_meas i j l v).comp (smp_meas H.meas), B * M, fun _ => H.wv_bound _ _ _ _ _⟩

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem io (H : DegB3 μ ν X F c B M L V ρ Fm) (j : ℕ) (T : Finset ℕ)
    (Φ : (ℕ → G) → ℝ) (hΦ : Measurable Φ) {B' : ℝ} (hB : ∀ x, |Φ x| ≤ B')
    (hdep : ∀ x y : ℕ → G, (∀ k ∈ T, x k = y k) → Φ x = Φ y)
    (Φ' : (ℕ → G) → ℝ) (hin : ∀ x, ∫ z, Φ (Function.update x j z) ∂ν = Φ' x) :
    ∫ ω, Φ (smp X ω) ∂μ = ∫ ω, Φ' (smp X ω) ∂μ :=
  integrate_out ν X H.indep H.meas H.law j T Φ hΦ hB hdep Φ' hin

theorem io_le (H : DegB3 μ ν X F c B M L V ρ Fm) (j : ℕ) (T : Finset ℕ)
    (Φ : (ℕ → G) → ℝ) (hΦ : Measurable Φ) {B' : ℝ} (hB : ∀ x, |Φ x| ≤ B')
    (hdep : ∀ x y : ℕ → G, (∀ k ∈ T, x k = y k) → Φ x = Φ y)
    (Ψ : (ℕ → G) → ℝ) (hΨ : Integrable (fun ω => Ψ (smp X ω)) μ)
    (hin : ∀ x, ∫ z, Φ (Function.update x j z) ∂ν ≤ Ψ x) :
    ∫ ω, Φ (smp X ω) ∂μ ≤ ∫ ω, Ψ (smp X ω) ∂μ :=
  integrate_out_le ν X H.indep H.meas H.law j T Φ hΦ hB hdep Ψ hΨ hin

/-- **(A)** The index `v` of the first summand occurs nowhere else: the mean of the product
    vanishes (integrate `x_v`; `∫ c(y - z) dz = 0`). -/
theorem vanish_v (H : DegB3 μ ν X F c B M L V ρ Fm) {i j l v i' j' l' v' : ℕ}
    (a1 : i ≠ v) (a2 : j ≠ v) (a3 : l ≠ v) (a4 : i' ≠ v) (a5 : j' ≠ v) (a6 : l' ≠ v)
    (a7 : v' ≠ v) :
    ∫ ω, wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω) ∂μ = 0 := by
  have h := H.io v {i, j, l, v, i', j', l', v'}
    (fun x => wv F c i j l v x * wv F c i' j' l' v' x)
    ((H.wv_meas i j l v).mul (H.wv_meas i' j' l' v')) (B' := (B * M) * (B * M))
    (fun x => by
      rw [abs_mul]
      exact mul_le_mul (H.wv_bound _ _ _ _ _) (H.wv_bound _ _ _ _ _) (abs_nonneg _)
        (mul_nonneg (H.B_nonneg (x 0)) (H.M_nonneg (x 0))))
    (fun x y hxy => by
      simp only [wv, hxy i (by simp), hxy j (by simp), hxy l (by simp), hxy v (by simp),
        hxy i' (by simp), hxy j' (by simp), hxy l' (by simp), hxy v' (by simp)])
    (fun _ => 0) (fun x => by
      have e : ∀ z, wv F c i j l v (Function.update x v z) * wv F c i' j' l' v' (Function.update x v z)
          = (F (x i) (x j) (x l) * wv F c i' j' l' v' x) * c (x l - z) := by
        intro z
        simp only [wv, Function.update_self, Function.update_of_ne a1, Function.update_of_ne a2,
          Function.update_of_ne a3, Function.update_of_ne a4, Function.update_of_ne a5,
          Function.update_of_ne a6, Function.update_of_ne a7]
        ring
      show ∫ z, wv F c i j l v (Function.update x v z) * wv F c i' j' l' v' (Function.update x v z) ∂ν = 0
      simp_rw [e]
      rw [integral_const_mul, H.c_mean1, mul_zero])
  rw [show (fun ω => wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω))
      = fun ω => (fun x => wv F c i j l v x * wv F c i' j' l' v' x) (smp X ω) from rfl, h]
  simp

end DegB3


/-- Partial integral in the first argument: `(b, y) ↦ ∫ g(a, b, y) dν(a)`. -/
noncomputable def pint {G : Type*} [MeasurableSpace G] (ν : Measure G) (g : G → G → G → ℝ)
    (q : G × G) : ℝ :=
  ∫ a, g a q.1 q.2 ∂ν

theorem pint_meas {G : Type*} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    {g : G → G → G → ℝ} (hg : Measurable (fun p : G × G × G => g p.1 p.2.1 p.2.2)) :
    Measurable (pint ν g) :=
  (hg.stronglyMeasurable.integral_prod_left' (μ := ν)).measurable

theorem pint_bound {G : Type*} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    {g : G → G → G → ℝ} {Bg : ℝ} (hgB : ∀ a b y, |g a b y| ≤ Bg) (q : G × G) :
    |pint ν g q| ≤ Bg := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (C := Bg) (f := fun a => g a q.1 q.2)
    (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hgB _ _ _)
  simpa [pint] using h

namespace DegB3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G]
  {ν : Measure G} {X : ℕ → Ω → G} {F : G → G → G → ℝ} {c : G → ℝ} {B M L V ρ Fm : ℝ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Integrating two points of a nonnegative factor.** `g ≥ 0` bounded measurable with
    `∫∫ g(a, b, y) da db ≤ L'` for every `y`; `Ψ ≥ 0` bounded measurable, not depending on the
    points `a1, a2`: `E [g(x_{a1}, x_{a2}, x_{a3}) Ψ] ≤ L' E Ψ`. -/
theorem two_out (H : DegB3 μ ν X F c B M L V ρ Fm) (g : G → G → G → ℝ)
    (hg : Measurable (fun p : G × G × G => g p.1 p.2.1 p.2.2)) {Bg : ℝ}
    (hg0 : ∀ a b y, 0 ≤ g a b y) (hgB : ∀ a b y, g a b y ≤ Bg)
    {L' : ℝ} (hmarg : ∀ y, ∫ b, (∫ a, g a b y ∂ν) ∂ν ≤ L')
    {a1 a2 a3 : ℕ} (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3)
    (Ψ : (ℕ → G) → ℝ) (hΨ : Measurable Ψ) {BΨ : ℝ} (hΨ0 : ∀ x, 0 ≤ Ψ x) (hΨB : ∀ x, Ψ x ≤ BΨ)
    (T : Finset ℕ) (hT1 : a1 ∉ T) (hT2 : a2 ∉ T)
    (hdep : ∀ x y : ℕ → G, (∀ k ∈ T, x k = y k) → Ψ x = Ψ y) :
    ∫ ω, g (X a1 ω) (X a2 ω) (X a3 ω) * Ψ (smp X ω) ∂μ ≤ L' * ∫ ω, Ψ (smp X ω) ∂μ := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hBg : 0 ≤ Bg := (hg0 (X 0 ω0) (X 0 ω0) (X 0 ω0)).trans (hgB _ _ _)
  have hBΨ : 0 ≤ BΨ := (hΨ0 (smp X ω0)).trans (hΨB _)
  have hgA : ∀ a b y, |g a b y| ≤ Bg := fun a b y => by rw [abs_of_nonneg (hg0 a b y)]; exact hgB a b y
  have hu1 : ∀ x z, Ψ (Function.update x a1 z) = Ψ x := fun x z =>
    hdep _ _ (fun k hk => Function.update_of_ne (by rintro rfl; exact hT1 hk) _ _)
  have hu2 : ∀ x z, Ψ (Function.update x a2 z) = Ψ x := fun x z =>
    hdep _ _ (fun k hk => Function.update_of_ne (by rintro rfl; exact hT2 hk) _ _)
  have m0 : Measurable (fun x : ℕ → G => g (x a1) (x a2) (x a3) * Ψ x) := by
    have hm : Measurable (fun x : ℕ → G => (x a1, x a2, x a3)) := by fun_prop
    exact (hg.comp hm).mul hΨ
  have m1 : Measurable (fun x : ℕ → G => pint ν g (x a2, x a3) * Ψ x) := by
    have hm : Measurable (fun x : ℕ → G => (x a2, x a3)) := by fun_prop
    exact ((pint_meas ν hg).comp hm).mul hΨ
  have s1 := H.io a1 (insert a1 (insert a2 (insert a3 T)))
    (fun x => g (x a1) (x a2) (x a3) * Ψ x) m0 (B' := Bg * BΨ)
    (fun x => by
      rw [abs_mul, abs_of_nonneg (hΨ0 x)]
      exact mul_le_mul (hgA _ _ _) (hΨB x) (hΨ0 x) hBg)
    (fun x y hxy => by
      simp only [hxy a1 (by simp), hxy a2 (by simp), hxy a3 (by simp),
        hdep x y (fun k hk => hxy k (by simp [hk]))])
    (fun x => pint ν g (x a2, x a3) * Ψ x)
    (fun x => by
      simp only [Function.update_self, Function.update_of_ne h12.symm,
        Function.update_of_ne h13.symm, hu1]
      rw [integral_mul_const]
      rfl)
  have s2 := H.io_le a2 (insert a2 (insert a3 T))
    (fun x => pint ν g (x a2, x a3) * Ψ x) m1 (B' := Bg * BΨ)
    (fun x => by
      rw [abs_mul, abs_of_nonneg (hΨ0 x)]
      exact mul_le_mul (pint_bound ν hgA _) (hΨB x) (hΨ0 x) hBg)
    (fun x y hxy => by
      simp only [hxy a2 (by simp), hxy a3 (by simp),
        hdep x y (fun k hk => hxy k (by simp [hk]))])
    (fun x => L' * Ψ x)
    (BM.const_mul L' (f := fun ω => Ψ (smp X ω)) ⟨hΨ.comp (smp_meas H.meas), BΨ, fun ω => by
      show |Ψ (smp X ω)| ≤ BΨ
      rw [abs_of_nonneg (hΨ0 _)]; exact hΨB _⟩).integrable
    (fun x => by
      simp only [Function.update_self, Function.update_of_ne h23.symm, hu2]
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (hmarg (x a3)) (hΨ0 x))
  calc ∫ ω, g (X a1 ω) (X a2 ω) (X a3 ω) * Ψ (smp X ω) ∂μ
      = ∫ ω, pint ν g (smp X ω a2, smp X ω a3) * Ψ (smp X ω) ∂μ := s1
    _ ≤ ∫ ω, L' * Ψ (smp X ω) ∂μ := s2
    _ = L' * ∫ ω, Ψ (smp X ω) ∂μ := integral_const_mul _ _

/-- `E [|F(x_i,x_j,x_l)| |F(x_{i'},x_{j'},x_{l'})|] ≤ L²` when two points of the first triple do
    not occur in the second (both triples injective). -/
theorem FF_le (H : DegB3 μ ν X F c B M L V ρ Fm) {i j l i' j' l' : ℕ}
    (hd : dist3 i j l) (hd' : dist3 i' j' l')
    (hfree : (¬ m3 i i' j' l' ∧ ¬ m3 j i' j' l') ∨ (¬ m3 j i' j' l' ∧ ¬ m3 l i' j' l')
      ∨ (¬ m3 i i' j' l' ∧ ¬ m3 l i' j' l')) :
    ∫ ω, |fv F i j l (smp X ω)| * |fv F i' j' l' (smp X ω)| ∂μ ≤ L * L := by
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨d1', d2', d3'⟩ := hd'
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := H.B_nonneg (X 0 ω0)
  have hΨm : Measurable (fun x : ℕ → G => |fv F i' j' l' x|) :=
    continuous_abs.measurable.comp (H.fv_meas i' j' l')
  have hΨdep : ∀ x y : ℕ → G, (∀ k ∈ ({i', j', l'} : Finset ℕ), x k = y k) →
      |fv F i' j' l' x| = |fv F i' j' l' y| := fun x y hxy => by
    simp only [fv, hxy i' (by simp), hxy j' (by simp), hxy l' (by simp)]
  have hE : ∫ ω, |fv F i' j' l' (smp X ω)| ∂μ ≤ L := H.l1 i' j' l' d1' d2' d3'
  have hfin : ∀ {L'' : ℝ}, L'' ≤ L → 0 ≤ L'' →
      L'' * ∫ ω, |fv F i' j' l' (smp X ω)| ∂μ ≤ L * L := fun h1 h2 =>
    mul_le_mul h1 hE (integral_nonneg fun _ => abs_nonneg _) H.L_nonneg
  have hm3 : ∀ x, ¬ m3 x i' j' l' → x ∉ ({i', j', l'} : Finset ℕ) := fun x hx hx' => by
    apply hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx'; unfold m3; tauto
  rcases hfree with ⟨f1, f2⟩ | ⟨f1, f2⟩ | ⟨f1, f2⟩
  · -- `i, j` free: integrate them, `g = |F|`
    have hg : Measurable (fun p : G × G × G => |F p.1 p.2.1 p.2.2|) :=
      continuous_abs.measurable.comp H.F_meas
    have h := H.two_out (fun a b y => |F a b y|) hg (Bg := B) (fun _ _ _ => abs_nonneg _)
      (fun _ _ _ => H.bound _ _ _) H.marg3 d1 d2 d3 (fun x => |fv F i' j' l' x|) hΨm (BΨ := B)
      (fun _ => abs_nonneg _) (fun _ => H.bound _ _ _) {i', j', l'} (hm3 i f1) (hm3 j f2) hΨdep
    exact h.trans (hfin le_rfl H.L_nonneg)
  · -- `j, l` free: `g(a, b, y) = |F y a b|`
    have hg : Measurable (fun p : G × G × G => |F p.2.2 p.1 p.2.1|) := by
      have hm : Measurable (fun p : G × G × G => (p.2.2, p.1, p.2.1)) := by fun_prop
      exact continuous_abs.measurable.comp (H.F_meas.comp hm)
    have h := H.two_out (fun a b y => |F y a b|) hg (Bg := B) (fun _ _ _ => abs_nonneg _)
      (fun _ _ _ => H.bound _ _ _) H.marg1 d3 (Ne.symm d1) (Ne.symm d2)
      (fun x => |fv F i' j' l' x|) hΨm (BΨ := B)
      (fun _ => abs_nonneg _) (fun _ => H.bound _ _ _) {i', j', l'} (hm3 j f1) (hm3 l f2) hΨdep
    exact h.trans (hfin le_rfl H.L_nonneg)
  · -- `i, l` free: `g(a, b, y) = |F a y b|`
    have hg : Measurable (fun p : G × G × G => |F p.1 p.2.2 p.2.1|) := by
      have hm : Measurable (fun p : G × G × G => (p.1, p.2.2, p.2.1)) := by fun_prop
      exact continuous_abs.measurable.comp (H.F_meas.comp hm)
    have h := H.two_out (fun a b y => |F a y b|) hg (Bg := B) (fun _ _ _ => abs_nonneg _)
      (fun _ _ _ => H.bound _ _ _) H.marg2 d2 d1 (Ne.symm d3)
      (fun x => |fv F i' j' l' x|) hΨm (BΨ := B)
      (fun _ => abs_nonneg _) (fun _ => H.bound _ _ _) {i', j', l'} (hm3 i f1) (hm3 l f2) hΨdep
    exact h.trans (hfin le_rfl H.L_nonneg)

end DegB3

namespace DegB3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G]
  {ν : Measure G} {X : ℕ → Ω → G} {F : G → G → G → ℝ} {c : G → ℝ} {B M L V ρ Fm : ℝ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem wwB (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v i' j' l' v' : ℕ) (x : ℕ → G) :
    |wv F c i j l v x * wv F c i' j' l' v' x| ≤ (B * M) * (B * M) := by
  rw [abs_mul]
  exact mul_le_mul (H.wv_bound _ _ _ _ _) (H.wv_bound _ _ _ _ _) (abs_nonneg _)
    (mul_nonneg (H.B_nonneg (x 0)) (H.M_nonneg (x 0)))

/-- **(B)** `v = v'` and the triples are disjoint: the mean of the product vanishes (integrate
    `x_i`, then `x_j`, which gives the constant `Fm`, then `x_l`, which gives `∫ c(z - x_v) dz = 0`). -/
theorem vanish_B (H : DegB3 μ ν X F c B M L V ρ Fm) {i j l v i' j' l' : ℕ}
    (d1 : i ≠ j) (d2 : i ≠ l) (d3 : i ≠ v) (d4 : j ≠ l) (d5 : j ≠ v) (d6 : l ≠ v)
    (e1 : i ≠ i') (e2 : i ≠ j') (e3 : i ≠ l') (e4 : j ≠ i') (e5 : j ≠ j') (e6 : j ≠ l')
    (e7 : l ≠ i') (e8 : l ≠ j') (e9 : l ≠ l') :
    ∫ ω, wv F c i j l v (smp X ω) * wv F c i' j' l' v (smp X ω) ∂μ = 0 := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := H.B_nonneg (X 0 ω0)
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have hF1m : Measurable (pint ν F) := pint_meas ν H.F_meas
  -- step 1: the point `i`
  have s1 := H.io i {i, j, l, v, i', j', l'}
    (fun x => wv F c i j l v x * wv F c i' j' l' v x)
    ((H.wv_meas i j l v).mul (H.wv_meas i' j' l' v)) (H.wwB i j l v i' j' l' v)
    (fun x y hxy => by
      simp only [wv, hxy i (by simp), hxy j (by simp), hxy l (by simp), hxy v (by simp),
        hxy i' (by simp), hxy j' (by simp), hxy l' (by simp)])
    (fun x => pint ν F (x j, x l) * (c (x l - x v) * wv F c i' j' l' v x))
    (fun x => by
      have e : ∀ z, wv F c i j l v (Function.update x i z)
            * wv F c i' j' l' v (Function.update x i z)
          = F z (x j) (x l) * (c (x l - x v) * wv F c i' j' l' v x) := by
        intro z
        simp only [wv, Function.update_self, Function.update_of_ne d1.symm,
          Function.update_of_ne d2.symm, Function.update_of_ne d3.symm,
          Function.update_of_ne e1.symm, Function.update_of_ne e2.symm,
          Function.update_of_ne e3.symm]
        ring
      show ∫ z, wv F c i j l v (Function.update x i z)
          * wv F c i' j' l' v (Function.update x i z) ∂ν = _
      simp_rw [e]
      rw [integral_mul_const]
      rfl)
  -- step 2: the point `j`
  have m1 : Measurable (fun x : ℕ → G => pint ν F (x j, x l) * (c (x l - x v) * wv F c i' j' l' v x)) := by
    have hm : Measurable (fun x : ℕ → G => (x j, x l)) := by fun_prop
    exact (hF1m.comp hm).mul ((H.cv_meas l v).mul (H.wv_meas i' j' l' v))
  have s2 := H.io j {j, l, v, i', j', l'}
    (fun x => pint ν F (x j, x l) * (c (x l - x v) * wv F c i' j' l' v x)) m1
    (B' := B * (M * (B * M)))
    (fun x => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (pint_bound ν H.bound _)
        (mul_le_mul (H.c_bound _) (H.wv_bound _ _ _ _ _) (abs_nonneg _) hM0)
        (by positivity) hB0)
    (fun x y hxy => by
      simp only [wv, hxy j (by simp), hxy l (by simp), hxy v (by simp),
        hxy i' (by simp), hxy j' (by simp), hxy l' (by simp)])
    (fun x => Fm * (c (x l - x v) * wv F c i' j' l' v x))
    (fun x => by
      simp only [wv, Function.update_self, Function.update_of_ne d4.symm,
        Function.update_of_ne d5.symm, Function.update_of_ne e4.symm,
        Function.update_of_ne e5.symm, Function.update_of_ne e6.symm]
      rw [integral_mul_const]
      congr 1
      exact H.mean12 (x l))
  -- step 3: the point `l`
  have m2 : Measurable (fun x : ℕ → G => Fm * (c (x l - x v) * wv F c i' j' l' v x)) :=
    measurable_const.mul ((H.cv_meas l v).mul (H.wv_meas i' j' l' v))
  have s3 := H.io l {l, v, i', j', l'}
    (fun x => Fm * (c (x l - x v) * wv F c i' j' l' v x)) m2
    (B' := |Fm| * (M * (B * M)))
    (fun x => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (H.c_bound _) (H.wv_bound _ _ _ _ _) (abs_nonneg _) hM0) (abs_nonneg _))
    (fun x y hxy => by
      simp only [wv, hxy l (by simp), hxy v (by simp),
        hxy i' (by simp), hxy j' (by simp), hxy l' (by simp)])
    (fun _ => 0)
    (fun x => by
      have e : ∀ z, Fm * (c (Function.update x l z l - Function.update x l z v)
            * wv F c i' j' l' v (Function.update x l z))
          = (Fm * wv F c i' j' l' v x) * c (z - x v) := by
        intro z
        simp only [wv, Function.update_self, Function.update_of_ne d6.symm,
          Function.update_of_ne e7.symm, Function.update_of_ne e8.symm,
          Function.update_of_ne e9.symm]
        ring
      show ∫ z, Fm * (c (Function.update x l z l - Function.update x l z v)
            * wv F c i' j' l' v (Function.update x l z)) ∂ν = 0
      simp_rw [e]
      rw [integral_const_mul, H.c_mean2, mul_zero])
  have h0 : ∫ ω, wv F c i j l v (smp X ω) * wv F c i' j' l' v (smp X ω) ∂μ
      = ∫ ω, (fun _ => (0 : ℝ)) (smp X ω) ∂μ := s1.trans (s2.trans s3)
  rw [h0]; simp

/-- `E w² ≤ M V` for an injective quadruple (integrate `x_v`). -/
theorem wsq_le (H : DegB3 μ ν X F c B M L V ρ Fm) {i j l v : ℕ} (hd : dist4 i j l v) :
    ∫ ω, wv F c i j l v (smp X ω) ^ 2 ∂μ ≤ M * V := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := H.B_nonneg (X 0 ω0)
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have h := H.io_le v {i, j, l, v} (fun x => wv F c i j l v x ^ 2)
    ((H.wv_meas i j l v).pow_const 2) (B' := (B * M) ^ 2)
    (fun x => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (H.wv_bound _ _ _ _ _) 2)
    (fun x y hxy => by
      simp only [wv, hxy i (by simp), hxy j (by simp), hxy l (by simp), hxy v (by simp)])
    (fun x => M * fv F i j l x ^ 2)
    ((BM_fv H i j l).sqr.const_mul M).integrable
    (fun x => by
      have e : ∀ z, wv F c i j l v (Function.update x v z) ^ 2
          = fv F i j l x ^ 2 * c (x l - z) ^ 2 := by
        intro z
        simp only [wv, fv, Function.update_self, Function.update_of_ne d3,
          Function.update_of_ne d5, Function.update_of_ne d6]
        ring
      show ∫ z, wv F c i j l v (Function.update x v z) ^ 2 ∂ν ≤ _
      simp_rw [e]
      rw [integral_const_mul]
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (H.c_sq _) (_root_.sq_nonneg _))
  refine h.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (H.var i j l d1 d2 d4) hM0

/-- **(E)** Cauchy–Schwarz: `E [w w'] ≤ M V` for injective quadruples. -/
theorem cs_le (H : DegB3 μ ν X F c B M L V ρ Fm) {i j l v i' j' l' v' : ℕ}
    (hd : dist4 i j l v) (hd' : dist4 i' j' l' v') :
    ∫ ω, wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω) ∂μ ≤ M * V := by
  have b1 := H.BM_wv i j l v
  have b2 := H.BM_wv i' j' l' v'
  have i1 : Integrable (fun ω => wv F c i j l v (smp X ω) ^ 2) μ := b1.sqr.integrable
  have i2 : Integrable (fun ω => wv F c i' j' l' v' (smp X ω) ^ 2) μ := b2.sqr.integrable
  have i3 := (b1.mul b2).integrable (μ := μ)
  have j1 : Integrable (fun ω => 1 / 2 * wv F c i j l v (smp X ω) ^ 2) μ := i1.const_mul _
  have j2 : Integrable (fun ω => 1 / 2 * wv F c i' j' l' v' (smp X ω) ^ 2) μ := i2.const_mul _
  have v1 := H.wsq_le hd
  have v2 := H.wsq_le hd'
  calc ∫ ω, wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω) ∂μ
      ≤ ∫ ω, (1 / 2 * wv F c i j l v (smp X ω) ^ 2
          + 1 / 2 * wv F c i' j' l' v' (smp X ω) ^ 2) ∂μ :=
        integral_mono i3 (j1.add j2) (fun ω => by
          nlinarith [_root_.sq_nonneg
            (wv F c i j l v (smp X ω) - wv F c i' j' l' v' (smp X ω))])
    _ = 1 / 2 * ∫ ω, wv F c i j l v (smp X ω) ^ 2 ∂μ
          + 1 / 2 * ∫ ω, wv F c i' j' l' v' (smp X ω) ^ 2 ∂μ := by
        rw [integral_add j1 j2, integral_const_mul, integral_const_mul]
    _ ≤ M * V := by linarith

/-- **(C)** `v = v'`, `v` not in either triple: integrate `x_v`;
    `|∫ c(y - z) c(y' - z) dz| ≤ M`. -/
theorem boundC (H : DegB3 μ ν X F c B M L V ρ Fm) {i j l v i' j' l' : ℕ}
    (a1 : i ≠ v) (a2 : j ≠ v) (a3 : l ≠ v) (a4 : i' ≠ v) (a5 : j' ≠ v) (a6 : l' ≠ v) :
    ∫ ω, wv F c i j l v (smp X ω) * wv F c i' j' l' v (smp X ω) ∂μ
      ≤ M * ∫ ω, |fv F i j l (smp X ω)| * |fv F i' j' l' (smp X ω)| ∂μ := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have hint : Integrable (fun ω => M * (|fv F i j l (smp X ω)| * |fv F i' j' l' (smp X ω)|)) μ :=
    (((H.BM_fv i j l).absv.mul (H.BM_fv i' j' l').absv).const_mul M).integrable
  have h := H.io_le v {i, j, l, v, i', j', l'}
    (fun x => wv F c i j l v x * wv F c i' j' l' v x)
    ((H.wv_meas i j l v).mul (H.wv_meas i' j' l' v)) (H.wwB i j l v i' j' l' v)
    (fun x y hxy => by
      simp only [wv, hxy i (by simp), hxy j (by simp), hxy l (by simp), hxy v (by simp),
        hxy i' (by simp), hxy j' (by simp), hxy l' (by simp)])
    (fun x => M * (|fv F i j l x| * |fv F i' j' l' x|)) hint
    (fun x => by
      have e : ∀ z, wv F c i j l v (Function.update x v z)
            * wv F c i' j' l' v (Function.update x v z)
          = (fv F i j l x * fv F i' j' l' x) * (c (x l - z) * c (x l' - z)) := by
        intro z
        simp only [wv, fv, Function.update_self, Function.update_of_ne a1,
          Function.update_of_ne a2, Function.update_of_ne a3, Function.update_of_ne a4,
          Function.update_of_ne a5, Function.update_of_ne a6]
        ring
      show ∫ z, wv F c i j l v (Function.update x v z)
          * wv F c i' j' l' v (Function.update x v z) ∂ν ≤ _
      simp_rw [e]
      rw [integral_const_mul]
      calc fv F i j l x * fv F i' j' l' x * ∫ z, c (x l - z) * c (x l' - z) ∂ν
          ≤ |fv F i j l x * fv F i' j' l' x * ∫ z, c (x l - z) * c (x l' - z) ∂ν| :=
            le_abs_self _
        _ = (|fv F i j l x| * |fv F i' j' l' x|) * |∫ z, c (x l - z) * c (x l' - z) ∂ν| := by
            rw [abs_mul, abs_mul]
        _ ≤ (|fv F i j l x| * |fv F i' j' l' x|) * M :=
            mul_le_mul_of_nonneg_left (H.c_cov _ _) (by positivity)
        _ = M * (|fv F i j l x| * |fv F i' j' l' x|) := by ring)
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul]

/-- **(D)** the pointwise bound `w w' ≤ M² |F| |F'|`. -/
theorem boundD (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v i' j' l' v' : ℕ) :
    ∫ ω, wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω) ∂μ
      ≤ M ^ 2 * ∫ ω, |fv F i j l (smp X ω)| * |fv F i' j' l' (smp X ω)| ∂μ := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have i3 := ((H.BM_wv i j l v).mul (H.BM_wv i' j' l' v')).integrable (μ := μ)
  have i4 := ((((H.BM_fv i j l).absv.mul (H.BM_fv i' j' l').absv)).const_mul (M ^ 2)).integrable
    (μ := μ)
  rw [← integral_const_mul]
  refine integral_mono i3 i4 (fun ω => ?_)
  show wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω)
    ≤ M ^ 2 * (|fv F i j l (smp X ω)| * |fv F i' j' l' (smp X ω)|)
  have k1 : |c (smp X ω l - smp X ω v)| ≤ M := H.c_bound _
  have k2 : |c (smp X ω l' - smp X ω v')| ≤ M := H.c_bound _
  calc wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω)
      ≤ |wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω)| := le_abs_self _
    _ = (|fv F i j l (smp X ω)| * |c (smp X ω l - smp X ω v)|)
          * (|fv F i' j' l' (smp X ω)| * |c (smp X ω l' - smp X ω v')|) := by
        simp only [wv, fv, abs_mul]
    _ ≤ (|fv F i j l (smp X ω)| * M) * (|fv F i' j' l' (smp X ω)| * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_left k1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left k2 (abs_nonneg _)) (by positivity) (by positivity)
    _ = M ^ 2 * (|fv F i j l (smp X ω)| * |fv F i' j' l' (smp X ω)|) := by ring

end DegB3

/-- The summand of an injective quadruple (zero otherwise). -/
noncomputable def aW {G : Type*} [AddCommGroup G] (F : G → G → G → ℝ) (c : G → ℝ) (i j l v : ℕ)
    (x : ℕ → G) : ℝ :=
  if dist4 i j l v then wv F c i j l v x else 0

/-- Indicator weights of the three kinds of nonvanishing pairs (paper: `v = v'` with one common
    point; `v ≠ v'` with `v`, `v'` in the other triple; at least three common indices). -/
noncomputable def X1 (i j l v i' j' l' v' : ℕ) : ℝ :=
  ind (v' = v) * (ind (m3 i' i j l) + ind (m3 j' i j l) + ind (m3 l' i j l))

noncomputable def X2 (i j l v i' j' l' v' : ℕ) : ℝ :=
  ind (m3 v' i j l) * (ind (i' = v) + ind (j' = v) + ind (l' = v))

noncomputable def X3 (i j l v i' j' l' v' : ℕ) : ℝ :=
  ind (m4 i' i j l v) * ind (m4 j' i j l v) * ind (m4 l' i j l v)
    + ind (m4 i' i j l v) * ind (m4 j' i j l v) * ind (m4 v' i j l v)
    + ind (m4 i' i j l v) * ind (m4 l' i j l v) * ind (m4 v' i j l v)
    + ind (m4 j' i j l v) * ind (m4 l' i j l v) * ind (m4 v' i j l v)

theorem X1_nonneg (i j l v i' j' l' v' : ℕ) : 0 ≤ X1 i j l v i' j' l' v' := by
  unfold X1
  have := ind_nonneg (v' = v); have := ind_nonneg (m3 i' i j l)
  have := ind_nonneg (m3 j' i j l); have := ind_nonneg (m3 l' i j l)
  positivity

theorem X2_nonneg (i j l v i' j' l' v' : ℕ) : 0 ≤ X2 i j l v i' j' l' v' := by
  unfold X2
  have := ind_nonneg (m3 v' i j l); have := ind_nonneg (i' = v)
  have := ind_nonneg (j' = v); have := ind_nonneg (l' = v)
  positivity

theorem X3_nonneg (i j l v i' j' l' v' : ℕ) : 0 ≤ X3 i j l v i' j' l' v' := by
  unfold X3
  have := ind_nonneg (m4 i' i j l v); have := ind_nonneg (m4 j' i j l v)
  have := ind_nonneg (m4 l' i j l v); have := ind_nonneg (m4 v' i j l v)
  positivity

theorem rhs_t1 {M L V a b e : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) : M * (L * L) ≤ M * L ^ 2 * a + M ^ 2 * L ^ 2 * b + M * V * e := by
  have h1 : M * L ^ 2 * 1 ≤ M * L ^ 2 * a :=
    mul_le_mul_of_nonneg_left ha (mul_nonneg hM (_root_.sq_nonneg L))
  have h2 : 0 ≤ M ^ 2 * L ^ 2 * b := by positivity
  have h3 : 0 ≤ M * V * e := by positivity
  nlinarith

theorem rhs_t2 {M L V a b e : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (ha : 0 ≤ a) (hb : 1 ≤ b)
    (he : 0 ≤ e) : M ^ 2 * (L * L) ≤ M * L ^ 2 * a + M ^ 2 * L ^ 2 * b + M * V * e := by
  have h1 : M ^ 2 * L ^ 2 * 1 ≤ M ^ 2 * L ^ 2 * b :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h2 : 0 ≤ M * L ^ 2 * a := by positivity
  have h3 : 0 ≤ M * V * e := by positivity
  nlinarith

theorem rhs_t3 {M L V a b e : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 1 ≤ e) : M * V ≤ M * L ^ 2 * a + M ^ 2 * L ^ 2 * b + M * V * e := by
  have h1 : M * V * 1 ≤ M * V * e := mul_le_mul_of_nonneg_left he (by positivity)
  have h2 : 0 ≤ M * L ^ 2 * a := by positivity
  have h3 : 0 ≤ M ^ 2 * L ^ 2 * b := by positivity
  nlinarith

theorem one_le3 {a b e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (h : a = 1 ∨ b = 1 ∨ e = 1) :
    1 ≤ a + b + e := by
  rcases h with h | h | h <;> linarith

/-- Case (C): `v = v'`, fewer than three common indices: two points of the first triple are not in
    the second. -/
theorem free_C {i j l v i' j' l' : ℕ} (d1 : i ≠ j) (d2 : i ≠ l) (d4 : j ≠ l)
    (hP : ¬ ((m4 i' i j l v ∧ m4 j' i j l v ∧ m4 l' i j l v)
      ∨ (m4 i' i j l v ∧ m4 j' i j l v ∧ m4 v i j l v)
      ∨ (m4 i' i j l v ∧ m4 l' i j l v ∧ m4 v i j l v)
      ∨ (m4 j' i j l v ∧ m4 l' i j l v ∧ m4 v i j l v))) :
    (¬ m3 i i' j' l' ∧ ¬ m3 j i' j' l') ∨ (¬ m3 j i' j' l' ∧ ¬ m3 l i' j' l')
      ∨ (¬ m3 i i' j' l' ∧ ¬ m3 l i' j' l') := by
  by_cases hi : m3 i i' j' l'
  · refine Or.inr (Or.inl ⟨fun hj => ?_, fun hl => ?_⟩)
    · unfold m3 at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp_all [m4]
    · unfold m3 at hi hl
      rcases hi with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;> simp_all [m4]
  · by_cases hj : m3 j i' j' l'
    · refine Or.inr (Or.inr ⟨hi, fun hl => ?_⟩)
      unfold m3 at hj hl
      rcases hj with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;> simp_all [m4]
    · exact Or.inl ⟨hi, hj⟩

/-- Case (D): `v ≠ v'`, `v` in the second and `v'` in the first quadruple, fewer than three common
    indices: `i, j` are not in the second triple. -/
theorem free_D {i j l v i' j' l' v' : ℕ} (d3 : i ≠ v) (d5 : j ≠ v) (d6 : l ≠ v)
    (hvv : v' ≠ v) (A : m4 v i' j' l' v') (A' : m4 v' i j l v)
    (hP : ¬ ((m4 i' i j l v ∧ m4 j' i j l v ∧ m4 l' i j l v)
      ∨ (m4 i' i j l v ∧ m4 j' i j l v ∧ m4 v' i j l v)
      ∨ (m4 i' i j l v ∧ m4 l' i j l v ∧ m4 v' i j l v)
      ∨ (m4 j' i j l v ∧ m4 l' i j l v ∧ m4 v' i j l v))) :
    (¬ m3 i i' j' l' ∧ ¬ m3 j i' j' l') ∨ (¬ m3 j i' j' l' ∧ ¬ m3 l i' j' l')
      ∨ (¬ m3 i i' j' l' ∧ ¬ m3 l i' j' l') := by
  have hv' : m4 v' i j l v := A'
  have hA : v = i' ∨ v = j' ∨ v = l' := by
    unfold m4 at A
    rcases A with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h.symm hvv
  refine Or.inl ⟨fun hi => ?_, fun hj => ?_⟩
  · unfold m3 at hi
    apply hP
    rcases hA with rfl | rfl | rfl <;> rcases hi with rfl | rfl | rfl <;> simp_all [m4]
  · unfold m3 at hj
    apply hP
    rcases hA with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp_all [m4]

namespace DegB3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G]
  {ν : Measure G} {X : ℕ → Ω → G} {F : G → G → G → ℝ} {c : G → ℝ} {B M L V ρ Fm : ℝ}

theorem aW_meas (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) : Measurable (aW F c i j l v) := by
  unfold aW
  by_cases h : dist4 i j l v
  · simp only [if_pos h]; exact H.wv_meas i j l v
  · simp only [if_neg h]; exact measurable_const

theorem aW_bound (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) (x : ℕ → G) :
    |aW F c i j l v x| ≤ B * M := by
  unfold aW
  by_cases h : dist4 i j l v
  · simp only [if_pos h]; exact H.wv_bound _ _ _ _ _
  · simp only [if_neg h, abs_zero]; exact mul_nonneg (H.B_nonneg (x 0)) (H.M_nonneg (x 0))

theorem BM_aW (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) :
    BM (fun ω => aW F c i j l v (smp X ω)) :=
  ⟨(H.aW_meas i j l v).comp (smp_meas H.meas), B * M, fun _ => H.aW_bound _ _ _ _ _⟩

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **The mean of a product of two summands of the main part**, bounded by the weights of the
    three nonvanishing kinds of pairs. -/
theorem pair_le (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v i' j' l' v' : ℕ) :
    ∫ ω, aW F c i j l v (smp X ω) * aW F c i' j' l' v' (smp X ω) ∂μ
      ≤ M * L ^ 2 * X1 i j l v i' j' l' v' + M ^ 2 * L ^ 2 * X2 i j l v i' j' l' v'
        + M * V * X3 i j l v i' j' l' v' := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have hL0 := H.L_nonneg
  have hV0 := H.V_nonneg
  have x1 := X1_nonneg i j l v i' j' l' v'
  have x2 := X2_nonneg i j l v i' j' l' v'
  have x3 := X3_nonneg i j l v i' j' l' v'
  have hR : 0 ≤ M * L ^ 2 * X1 i j l v i' j' l' v' + M ^ 2 * L ^ 2 * X2 i j l v i' j' l' v'
        + M * V * X3 i j l v i' j' l' v' := by positivity
  by_cases hd : dist4 i j l v
  swap
  · have hz : (fun ω => aW F c i j l v (smp X ω) * aW F c i' j' l' v' (smp X ω))
        = fun _ => (0 : ℝ) := by
      funext ω; simp only [aW, if_neg hd, zero_mul]
    rw [hz, integral_zero]; exact hR
  by_cases hd' : dist4 i' j' l' v'
  swap
  · have hz : (fun ω => aW F c i j l v (smp X ω) * aW F c i' j' l' v' (smp X ω))
        = fun _ => (0 : ℝ) := by
      funext ω; simp only [aW, if_neg hd', mul_zero]
    rw [hz, integral_zero]; exact hR
  have hA : (fun ω => aW F c i j l v (smp X ω) * aW F c i' j' l' v' (smp X ω))
      = fun ω => wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω) := by
    funext ω; simp only [aW, if_pos hd, if_pos hd']
  rw [hA]
  have hd0 := hd
  have hd0' := hd'
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  obtain ⟨d1', d2', d3', d4', d5', d6'⟩ := hd'
  -- (A) `v` occurs only once
  by_cases A : m4 v i' j' l' v'
  swap
  · unfold m4 at A
    rw [H.vanish_v d3 d5 d6 (by omega) (by omega) (by omega) (by omega)]; exact hR
  by_cases A' : m4 v' i j l v
  swap
  · unfold m4 at A'
    have hc : (fun ω => wv F c i j l v (smp X ω) * wv F c i' j' l' v' (smp X ω))
        = fun ω => wv F c i' j' l' v' (smp X ω) * wv F c i j l v (smp X ω) :=
      funext fun ω => mul_comm _ _
    rw [hc, H.vanish_v d3' d5' d6' (by omega) (by omega) (by omega) (by omega)]; exact hR
  -- (E) at least three common indices
  by_cases P3 : (m4 i' i j l v ∧ m4 j' i j l v ∧ m4 l' i j l v)
      ∨ (m4 i' i j l v ∧ m4 j' i j l v ∧ m4 v' i j l v)
      ∨ (m4 i' i j l v ∧ m4 l' i j l v ∧ m4 v' i j l v)
      ∨ (m4 j' i j l v ∧ m4 l' i j l v ∧ m4 v' i j l v)
  · refine (H.cs_le hd0 hd0').trans (rhs_t3 hM0 hV0 x1 x2 ?_)
    unfold X3
    have := ind_nonneg (m4 i' i j l v); have := ind_nonneg (m4 j' i j l v)
    have := ind_nonneg (m4 l' i j l v); have := ind_nonneg (m4 v' i j l v)
    have p1 : 0 ≤ ind (m4 i' i j l v) * ind (m4 j' i j l v) * ind (m4 l' i j l v) := by positivity
    have p2 : 0 ≤ ind (m4 i' i j l v) * ind (m4 j' i j l v) * ind (m4 v' i j l v) := by positivity
    have p3 : 0 ≤ ind (m4 i' i j l v) * ind (m4 l' i j l v) * ind (m4 v' i j l v) := by positivity
    have p4 : 0 ≤ ind (m4 j' i j l v) * ind (m4 l' i j l v) * ind (m4 v' i j l v) := by positivity
    rcases P3 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [ind_true h1, ind_true h2, ind_true h3] at *; linarith
    · rw [ind_true h1, ind_true h2, ind_true h3] at *; linarith
    · rw [ind_true h1, ind_true h2, ind_true h3] at *; linarith
    · rw [ind_true h1, ind_true h2, ind_true h3] at *; linarith
  by_cases hvv : v' = v
  · subst hvv
    by_cases hI : m3 i' i j l ∨ m3 j' i j l ∨ m3 l' i j l
    · -- (C) one common point
      have hfree := free_C d1 d2 d4 P3
      have hb := (H.boundC d3 d5 d6 d3' d5' d6').trans
        (mul_le_mul_of_nonneg_left (H.FF_le ⟨d1, d2, d4⟩ ⟨d1', d2', d4'⟩ hfree) hM0)
      refine hb.trans (rhs_t1 hM0 hV0 ?_ x2 x3)
      unfold X1
      rw [ind_true rfl, one_mul]
      exact one_le3 (ind_nonneg _) (ind_nonneg _) (ind_nonneg _)
        (by rcases hI with h | h | h
            · exact Or.inl (ind_true h)
            · exact Or.inr (Or.inl (ind_true h))
            · exact Or.inr (Or.inr (ind_true h)))
    · -- (B) disjoint triples
      unfold m3 at hI
      rw [H.vanish_B d1 d2 d3 d4 d5 d6 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]
      exact hR
  · -- (D) `v ≠ v'`, each in the other triple
    have hfree := free_D d3 d5 d6 hvv A A' P3
    have hb := (H.boundD i j l v i' j' l' v').trans
      (mul_le_mul_of_nonneg_left (H.FF_le ⟨d1, d2, d4⟩ ⟨d1', d2', d4'⟩ hfree)
        (_root_.sq_nonneg M))
    refine hb.trans (rhs_t2 hM0 hV0 x1 ?_ x3)
    unfold X2
    have hv3 : m3 v' i j l := by
      unfold m4 at A'
      rcases A' with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h hvv
    rw [ind_true hv3, one_mul]
    have hw : i' = v ∨ j' = v ∨ l' = v := by
      unfold m4 at A
      rcases A with h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h.symm)
      · exact absurd h.symm hvv
    exact one_le3 (ind_nonneg _) (ind_nonneg _) (ind_nonneg _)
      (by rcases hw with h | h | h
          · exact Or.inl (ind_true h)
          · exact Or.inr (Or.inl (ind_true h))
          · exact Or.inr (Or.inr (ind_true h)))

end DegB3

/-! ### Counting -/

/-- The index set of quadruples. -/
def R4 (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.range N ×ˢ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N))

theorem sum_R4 (N : ℕ) (f : ℕ × ℕ × ℕ × ℕ → ℝ) :
    ∑ t ∈ R4 N, f t = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ e ∈ Finset.range N,
      ∑ g ∈ Finset.range N, f (a, b, e, g) := by
  unfold R4
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_product]

theorem sum4_prod (N : ℕ) (f1 f2 f3 f4 : ℕ → ℝ) :
    ∑ t ∈ R4 N, f1 t.1 * f2 t.2.1 * f3 t.2.2.1 * f4 t.2.2.2
      = (∑ a ∈ Finset.range N, f1 a) * (∑ a ∈ Finset.range N, f2 a)
        * (∑ a ∈ Finset.range N, f3 a) * (∑ a ∈ Finset.range N, f4 a) := by
  rw [sum_R4]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem prod4_le {a b e g A B E G' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (hg : 0 ≤ g)
    (hA : a ≤ A) (hB : b ≤ B) (hE : e ≤ E) (hG : g ≤ G') : a * b * e * g ≤ A * B * E * G' := by
  have h1 : a * b ≤ A * B := mul_le_mul hA hB hb (ha.trans hA)
  have h2 : a * b * e ≤ A * B * E := mul_le_mul h1 hE he ((mul_nonneg ha hb).trans h1)
  exact mul_le_mul h2 hG hg ((mul_nonneg (mul_nonneg ha hb) he).trans h2)

theorem s_one (N : ℕ) : ∑ _a ∈ Finset.range N, (1 : ℝ) = N := by simp

theorem s_eq (N v : ℕ) : ∑ a ∈ Finset.range N, ind (a = v) ≤ 1 := by
  unfold ind
  rw [Finset.sum_ite_eq']
  split_ifs <;> norm_num

theorem s_nonneg (N : ℕ) (f : ℕ → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ ∑ a ∈ Finset.range N, f a :=
  Finset.sum_nonneg fun a _ => hf a

theorem ind_m3_le (x i j l : ℕ) : ind (m3 x i j l) ≤ ind (x = i) + ind (x = j) + ind (x = l) := by
  have a := ind_nonneg (x = i); have b := ind_nonneg (x = j); have e := ind_nonneg (x = l)
  by_cases h : m3 x i j l
  · rw [ind_true h]
    rcases h with h | h | h
    · rw [ind_true h]; linarith
    · rw [ind_true h]; linarith
    · rw [ind_true h]; linarith
  · rw [ind_false h]; linarith

theorem ind_m4_le (x i j l v : ℕ) :
    ind (m4 x i j l v) ≤ ind (x = i) + ind (x = j) + ind (x = l) + ind (x = v) := by
  have a := ind_nonneg (x = i); have b := ind_nonneg (x = j); have e := ind_nonneg (x = l)
  have f := ind_nonneg (x = v)
  by_cases h : m4 x i j l v
  · rw [ind_true h]
    rcases h with h | h | h | h
    · rw [ind_true h]; linarith
    · rw [ind_true h]; linarith
    · rw [ind_true h]; linarith
    · rw [ind_true h]; linarith
  · rw [ind_false h]; linarith

theorem s_m3 (N i j l : ℕ) : ∑ a ∈ Finset.range N, ind (m3 a i j l) ≤ 3 := by
  calc ∑ a ∈ Finset.range N, ind (m3 a i j l)
      ≤ ∑ a ∈ Finset.range N, (ind (a = i) + ind (a = j) + ind (a = l)) :=
        Finset.sum_le_sum fun a _ => ind_m3_le a i j l
    _ = ∑ a ∈ Finset.range N, ind (a = i) + ∑ a ∈ Finset.range N, ind (a = j)
        + ∑ a ∈ Finset.range N, ind (a = l) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 3 := by linarith [s_eq N i, s_eq N j, s_eq N l]

theorem s_m4 (N i j l v : ℕ) : ∑ a ∈ Finset.range N, ind (m4 a i j l v) ≤ 4 := by
  calc ∑ a ∈ Finset.range N, ind (m4 a i j l v)
      ≤ ∑ a ∈ Finset.range N, (ind (a = i) + ind (a = j) + ind (a = l) + ind (a = v)) :=
        Finset.sum_le_sum fun a _ => ind_m4_le a i j l v
    _ = ∑ a ∈ Finset.range N, ind (a = i) + ∑ a ∈ Finset.range N, ind (a = j)
        + ∑ a ∈ Finset.range N, ind (a = l) + ∑ a ∈ Finset.range N, ind (a = v) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ 4 := by linarith [s_eq N i, s_eq N j, s_eq N l, s_eq N v]

/-- A product-form term with the given bounds on the four one-dimensional sums. -/
theorem sum4_le (N : ℕ) (f1 f2 f3 f4 : ℕ → ℝ) (h1 : ∀ a, 0 ≤ f1 a) (h2 : ∀ a, 0 ≤ f2 a)
    (h3 : ∀ a, 0 ≤ f3 a) (h4 : ∀ a, 0 ≤ f4 a) {C1 C2 C3 C4 : ℝ}
    (k1 : ∑ a ∈ Finset.range N, f1 a ≤ C1) (k2 : ∑ a ∈ Finset.range N, f2 a ≤ C2)
    (k3 : ∑ a ∈ Finset.range N, f3 a ≤ C3) (k4 : ∑ a ∈ Finset.range N, f4 a ≤ C4) :
    ∑ t ∈ R4 N, f1 t.1 * f2 t.2.1 * f3 t.2.2.1 * f4 t.2.2.2 ≤ C1 * C2 * C3 * C4 := by
  rw [sum4_prod]
  exact prod4_le (s_nonneg N f1 h1) (s_nonneg N f2 h2) (s_nonneg N f3 h3) (s_nonneg N f4 h4)
    k1 k2 k3 k4

theorem one_nn : ∀ _a : ℕ, (0 : ℝ) ≤ 1 := fun _ => zero_le_one

theorem sumX1 (N i j l v : ℕ) :
    ∑ t ∈ R4 N, X1 i j l v t.1 t.2.1 t.2.2.1 t.2.2.2 ≤ 9 * (N : ℝ) ^ 2 := by
  have e : ∀ t : ℕ × ℕ × ℕ × ℕ, X1 i j l v t.1 t.2.1 t.2.2.1 t.2.2.2
      = (fun a => ind (m3 a i j l)) t.1 * (fun _ => (1 : ℝ)) t.2.1 * (fun _ => (1 : ℝ)) t.2.2.1
          * (fun a => ind (a = v)) t.2.2.2
        + (fun _ => (1 : ℝ)) t.1 * (fun a => ind (m3 a i j l)) t.2.1 * (fun _ => (1 : ℝ)) t.2.2.1
          * (fun a => ind (a = v)) t.2.2.2
        + (fun _ => (1 : ℝ)) t.1 * (fun _ => (1 : ℝ)) t.2.1 * (fun a => ind (m3 a i j l)) t.2.2.1
          * (fun a => ind (a = v)) t.2.2.2 := by
    intro t; unfold X1; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have a1 := sum4_le N _ _ _ _ (fun a => ind_nonneg (m3 a i j l)) one_nn one_nn
    (fun a => ind_nonneg (a = v)) (s_m3 N i j l) (s_one N).le (s_one N).le (s_eq N v)
  have a2 := sum4_le N _ _ _ _ one_nn (fun a => ind_nonneg (m3 a i j l)) one_nn
    (fun a => ind_nonneg (a = v)) (s_one N).le (s_m3 N i j l) (s_one N).le (s_eq N v)
  have a3 := sum4_le N _ _ _ _ one_nn one_nn (fun a => ind_nonneg (m3 a i j l))
    (fun a => ind_nonneg (a = v)) (s_one N).le (s_one N).le (s_m3 N i j l) (s_eq N v)
  linarith

theorem sumX2 (N i j l v : ℕ) :
    ∑ t ∈ R4 N, X2 i j l v t.1 t.2.1 t.2.2.1 t.2.2.2 ≤ 9 * (N : ℝ) ^ 2 := by
  have e : ∀ t : ℕ × ℕ × ℕ × ℕ, X2 i j l v t.1 t.2.1 t.2.2.1 t.2.2.2
      = (fun a => ind (a = v)) t.1 * (fun _ => (1 : ℝ)) t.2.1 * (fun _ => (1 : ℝ)) t.2.2.1
          * (fun a => ind (m3 a i j l)) t.2.2.2
        + (fun _ => (1 : ℝ)) t.1 * (fun a => ind (a = v)) t.2.1 * (fun _ => (1 : ℝ)) t.2.2.1
          * (fun a => ind (m3 a i j l)) t.2.2.2
        + (fun _ => (1 : ℝ)) t.1 * (fun _ => (1 : ℝ)) t.2.1 * (fun a => ind (a = v)) t.2.2.1
          * (fun a => ind (m3 a i j l)) t.2.2.2 := by
    intro t; unfold X2; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have a1 := sum4_le N _ _ _ _ (fun a => ind_nonneg (a = v)) one_nn one_nn
    (fun a => ind_nonneg (m3 a i j l)) (s_eq N v) (s_one N).le (s_one N).le (s_m3 N i j l)
  have a2 := sum4_le N _ _ _ _ one_nn (fun a => ind_nonneg (a = v)) one_nn
    (fun a => ind_nonneg (m3 a i j l)) (s_one N).le (s_eq N v) (s_one N).le (s_m3 N i j l)
  have a3 := sum4_le N _ _ _ _ one_nn one_nn (fun a => ind_nonneg (a = v))
    (fun a => ind_nonneg (m3 a i j l)) (s_one N).le (s_one N).le (s_eq N v) (s_m3 N i j l)
  linarith

theorem sumX3 (N i j l v : ℕ) :
    ∑ t ∈ R4 N, X3 i j l v t.1 t.2.1 t.2.2.1 t.2.2.2 ≤ 256 * (N : ℝ) := by
  set g : ℕ → ℝ := fun a => ind (m4 a i j l v) with hg
  have g0 : ∀ a, 0 ≤ g a := fun a => ind_nonneg _
  have gs : ∑ a ∈ Finset.range N, g a ≤ 4 := s_m4 N i j l v
  have e : ∀ t : ℕ × ℕ × ℕ × ℕ, X3 i j l v t.1 t.2.1 t.2.2.1 t.2.2.2
      = g t.1 * g t.2.1 * g t.2.2.1 * (fun _ => (1 : ℝ)) t.2.2.2
        + g t.1 * g t.2.1 * (fun _ => (1 : ℝ)) t.2.2.1 * g t.2.2.2
        + g t.1 * (fun _ => (1 : ℝ)) t.2.1 * g t.2.2.1 * g t.2.2.2
        + (fun _ => (1 : ℝ)) t.1 * g t.2.1 * g t.2.2.1 * g t.2.2.2 := by
    intro t; unfold X3; rw [hg]; ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have a1 := sum4_le N _ _ _ _ g0 g0 g0 one_nn gs gs gs (s_one N).le
  have a2 := sum4_le N _ _ _ _ g0 g0 one_nn g0 gs gs (s_one N).le gs
  have a3 := sum4_le N _ _ _ _ g0 one_nn g0 g0 gs (s_one N).le gs gs
  have a4 := sum4_le N _ _ _ _ one_nn g0 g0 g0 (s_one N).le gs gs gs
  linarith

/-- The main part `V` (injective quadruples) as a function of the sample. -/
noncomputable def Vm {G : Type*} [AddCommGroup G] (F : G → G → G → ℝ) (c : G → ℝ) (N : ℕ)
    (x : ℕ → G) : ℝ :=
  ∑ t ∈ R4 N, aW F c t.1 t.2.1 t.2.2.1 t.2.2.2 x

/-- The summand of an injective triple with `v` in the triple. -/
noncomputable def r1 {G : Type*} [AddCommGroup G] (F : G → G → G → ℝ) (c : G → ℝ)
    (i j l v : ℕ) (x : ℕ → G) : ℝ :=
  if dist3 i j l ∧ m3 v i j l then wv F c i j l v x else 0

/-- The summand of a triple that is not injective. -/
noncomputable def r2 {G : Type*} [AddCommGroup G] (F : G → G → G → ℝ) (c : G → ℝ)
    (i j l v : ℕ) (x : ℕ → G) : ℝ :=
  if dist3 i j l then 0 else wv F c i j l v x

/-- `F` at a triple that is not injective (zero otherwise). -/
noncomputable def dF {G : Type*} (F : G → G → G → ℝ) (i j l : ℕ) (x : ℕ → G) : ℝ :=
  if dist3 i j l then 0 else F (x i) (x j) (x l)

theorem wv_split {G : Type*} [AddCommGroup G] (F : G → G → G → ℝ) (c : G → ℝ) (i j l v : ℕ)
    (x : ℕ → G) : wv F c i j l v x = aW F c i j l v x + r1 F c i j l v x + r2 F c i j l v x := by
  unfold aW r1 r2
  by_cases hd : dist3 i j l
  · by_cases hm : m3 v i j l
    · have h4 : ¬ dist4 i j l v := by unfold dist4 m3 at *; omega
      simp [hd, hm, h4]
    · have h4 : dist4 i j l v := by unfold dist4 dist3 m3 at *; omega
      simp [hd, hm, h4]
  · have h4 : ¬ dist4 i j l v := by unfold dist4 dist3 at *; omega
    simp [hd, h4]

namespace DegB3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G]
  {ν : Measure G} {X : ℕ → Ω → G} {F : G → G → G → ℝ} {c : G → ℝ} {B M L V ρ Fm : ℝ}

theorem BM_Vm (H : DegB3 μ ν X F c B M L V ρ Fm) (N : ℕ) :
    BM (fun ω => Vm F c N (smp X ω)) := by
  unfold Vm
  exact BM.sum (R4 N) (fun (t : ℕ × ℕ × ℕ × ℕ) ω => aW F c t.1 t.2.1 t.2.2.1 t.2.2.2 (smp X ω))
    fun t _ => H.BM_aW _ _ _ _

theorem BM_r1 (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) :
    BM (fun ω => r1 F c i j l v (smp X ω)) := by
  unfold r1
  by_cases h : dist3 i j l ∧ m3 v i j l
  · simp only [if_pos h]; exact H.BM_wv i j l v
  · simp only [if_neg h]; exact BM.const 0

theorem BM_r2 (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) :
    BM (fun ω => r2 F c i j l v (smp X ω)) := by
  unfold r2
  by_cases h : dist3 i j l
  · simp only [if_pos h]; exact BM.const 0
  · simp only [if_neg h]; exact H.BM_wv i j l v

theorem BM_dF (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l : ℕ) :
    BM (fun ω => dF F i j l (smp X ω)) := by
  unfold dF
  by_cases h : dist3 i j l
  · simp only [if_pos h]; exact BM.const 0
  · simp only [if_neg h]; exact H.BM_fv i j l

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Second moment of the main part:**
    `E V² ≤ N⁴ (9 N² M L² + 9 N² M² L² + 256 N M V)`. -/
theorem Vm_sq (H : DegB3 μ ν X F c B M L V ρ Fm) (N : ℕ) :
    ∫ ω, Vm F c N (smp X ω) ^ 2 ∂μ
      ≤ (N : ℝ) ^ 4 * (M * L ^ 2 * (9 * (N : ℝ) ^ 2) + M ^ 2 * L ^ 2 * (9 * (N : ℝ) ^ 2)
        + M * V * (256 * (N : ℝ))) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have hL0 := H.L_nonneg
  have hV0 := H.V_nonneg
  have hS2 : ∀ ω, Vm F c N (smp X ω) ^ 2
      = ∑ t ∈ R4 N, ∑ t' ∈ R4 N, aW F c t.1 t.2.1 t.2.2.1 t.2.2.2 (smp X ω)
          * aW F c t'.1 t'.2.1 t'.2.2.1 t'.2.2.2 (smp X ω) := by
    intro ω
    unfold Vm
    rw [pow_two, Finset.sum_mul_sum]
  simp_rw [hS2]
  rw [integral_finset_sum _ (fun t _ => integrable_finset_sum _ fun t' _ =>
    ((H.BM_aW _ _ _ _).mul (H.BM_aW _ _ _ _)).integrable)]
  have h1 : ∀ t ∈ R4 N, ∫ ω, ∑ t' ∈ R4 N, aW F c t.1 t.2.1 t.2.2.1 t.2.2.2 (smp X ω)
          * aW F c t'.1 t'.2.1 t'.2.2.1 t'.2.2.2 (smp X ω) ∂μ
        ≤ M * L ^ 2 * (9 * (N : ℝ) ^ 2) + M ^ 2 * L ^ 2 * (9 * (N : ℝ) ^ 2)
          + M * V * (256 * (N : ℝ)) := by
    intro t _
    rw [integral_finset_sum _ (fun t' _ => ((H.BM_aW _ _ _ _).mul (H.BM_aW _ _ _ _)).integrable)]
    refine (Finset.sum_le_sum fun t' _ => H.pair_le t.1 t.2.1 t.2.2.1 t.2.2.2
      t'.1 t'.2.1 t'.2.2.1 t'.2.2.2).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have k1 := sumX1 N t.1 t.2.1 t.2.2.1 t.2.2.2
    have k2 := sumX2 N t.1 t.2.1 t.2.2.1 t.2.2.2
    have k3 := sumX3 N t.1 t.2.1 t.2.2.1 t.2.2.2
    have c1 : 0 ≤ M * L ^ 2 := by positivity
    have c2 : 0 ≤ M ^ 2 * L ^ 2 := by positivity
    have c3 : 0 ≤ M * V := by positivity
    have := mul_le_mul_of_nonneg_left k1 c1
    have := mul_le_mul_of_nonneg_left k2 c2
    have := mul_le_mul_of_nonneg_left k3 c3
    linarith
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  simp only [Finset.sum_const, R4, Finset.card_product, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The mean of `|F|` at a triple that is not injective. -/
theorem dF_le (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l : ℕ) :
    ∫ ω, |dF F i j l (smp X ω)| ∂μ
      ≤ ρ * ((if i = j then (1 : ℝ) else 0) + (if j = l then (1 : ℝ) else 0)
          + (if i = l then (1 : ℝ) else 0)) + B * (if j = i ∧ l = i then (1 : ℝ) else 0) := by
  have hρ := H.rho_nonneg
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := H.B_nonneg (X 0 ω0)
  have t1 : (0 : ℝ) ≤ (if i = j then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t2 : (0 : ℝ) ≤ (if j = l then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t3 : (0 : ℝ) ≤ (if i = l then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have t4 : (0 : ℝ) ≤ (if j = i ∧ l = i then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have p1 := mul_nonneg hρ t1
  have p2 := mul_nonneg hρ t2
  have p3 := mul_nonneg hρ t3
  have p4 := mul_nonneg hB0 t4
  by_cases hd : dist3 i j l
  · have e : (fun ω => |dF F i j l (smp X ω)|) = fun _ => (0 : ℝ) := by
      funext ω; unfold dF; rw [if_pos hd, abs_zero]
    rw [e, integral_zero]; nlinarith
  · have e : (fun ω => |dF F i j l (smp X ω)|) = fun ω => |F (X i ω) (X j ω) (X l ω)| := by
      funext ω; unfold dF; rw [if_neg hd]; rfl
    rw [e]
    have hint : Integrable (fun ω => |F (X i ω) (X j ω) (X l ω)|) μ :=
      (H.BM_fv i j l).absv.integrable
    by_cases a : i = j
    · by_cases b : j = l
      · have e4 : (if j = i ∧ l = i then (1 : ℝ) else 0) = 1 := if_pos ⟨a.symm, by omega⟩
        have hle : ∫ ω, |F (X i ω) (X j ω) (X l ω)| ∂μ ≤ B := by
          calc ∫ ω, |F (X i ω) (X j ω) (X l ω)| ∂μ ≤ ∫ _ω, B ∂μ :=
                integral_mono hint (integrable_const _) (fun ω => H.bound _ _ _)
            _ = B := by simp
        rw [e4]; nlinarith
      · have e1 : (if i = j then (1 : ℝ) else 0) = 1 := if_pos a
        subst a
        have hle := H.rho12 i l b
        rw [e1]; nlinarith
    · by_cases b : j = l
      · have e2 : (if j = l then (1 : ℝ) else 0) = 1 := if_pos b
        subst b
        have hle := H.rho23 i j a
        rw [e2]; nlinarith
      · have cc : i = l := by unfold dist3 at hd; tauto
        have e3 : (if i = l then (1 : ℝ) else 0) = 1 := if_pos cc
        subst cc
        have hle := H.rho13 i j a
        rw [e3]; nlinarith

/-- The pairs with `ι` injective and `v` in its image. -/
theorem r1_le (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) :
    ∫ ω, |r1 F c i j l v (smp X ω)| ∂μ
      ≤ M * L * (ind (v = i) + ind (v = j) + ind (v = l)) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have hML : 0 ≤ M * L := mul_nonneg hM0 H.L_nonneg
  have hs : 0 ≤ ind (v = i) + ind (v = j) + ind (v = l) := by
    have := ind_nonneg (v = i); have := ind_nonneg (v = j); have := ind_nonneg (v = l)
    linarith
  by_cases h : dist3 i j l ∧ m3 v i j l
  · have e : (fun ω => |r1 F c i j l v (smp X ω)|) = fun ω => |wv F c i j l v (smp X ω)| := by
      funext ω; unfold r1; rw [if_pos h]
    rw [e]
    obtain ⟨⟨d1, d2, d3⟩, hm⟩ := h
    have hge : 1 ≤ ind (v = i) + ind (v = j) + ind (v = l) :=
      one_le3 (ind_nonneg _) (ind_nonneg _) (ind_nonneg _)
        (by rcases hm with h | h | h
            · exact Or.inl (ind_true h)
            · exact Or.inr (Or.inl (ind_true h))
            · exact Or.inr (Or.inr (ind_true h)))
    have hpt : ∀ ω, |wv F c i j l v (smp X ω)| ≤ M * |fv F i j l (smp X ω)| := fun ω => by
      unfold wv fv; rw [abs_mul, mul_comm M]
      exact mul_le_mul_of_nonneg_left (H.c_bound _) (abs_nonneg _)
    have h1 : ∫ ω, |wv F c i j l v (smp X ω)| ∂μ ≤ ∫ ω, M * |fv F i j l (smp X ω)| ∂μ :=
      integral_mono (H.BM_wv i j l v).absv.integrable
        ((H.BM_fv i j l).absv.const_mul M).integrable hpt
    rw [integral_const_mul] at h1
    have h2 : M * ∫ ω, |fv F i j l (smp X ω)| ∂μ ≤ M * L :=
      mul_le_mul_of_nonneg_left (H.l1 i j l d1 d2 d3) hM0
    nlinarith
  · have e : (fun ω => |r1 F c i j l v (smp X ω)|) = fun _ => (0 : ℝ) := by
      funext ω; unfold r1; rw [if_neg h, abs_zero]
    rw [e, integral_zero]; positivity

/-- The pairs with `ι` not injective. -/
theorem r2_le (H : DegB3 μ ν X F c B M L V ρ Fm) (i j l v : ℕ) :
    ∫ ω, |r2 F c i j l v (smp X ω)| ∂μ
      ≤ (2 + M * (ind (v = i) + ind (v = j) + ind (v = l))) * ∫ ω, |dF F i j l (smp X ω)| ∂μ := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have hs : 0 ≤ ind (v = i) + ind (v = j) + ind (v = l) := by
    have := ind_nonneg (v = i); have := ind_nonneg (v = j); have := ind_nonneg (v = l)
    linarith
  have hE : 0 ≤ ∫ ω, |dF F i j l (smp X ω)| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have e : ∀ x, |r2 F c i j l v x| = |dF F i j l x| * |c (x l - x v)| := fun x => by
    unfold r2 dF wv
    by_cases hd : dist3 i j l
    · simp [hd]
    · simp only [if_neg hd, abs_mul]
  simp_rw [e]
  by_cases hm : m3 v i j l
  · have hge : 1 ≤ ind (v = i) + ind (v = j) + ind (v = l) :=
      one_le3 (ind_nonneg _) (ind_nonneg _) (ind_nonneg _)
        (by rcases hm with h | h | h
            · exact Or.inl (ind_true h)
            · exact Or.inr (Or.inl (ind_true h))
            · exact Or.inr (Or.inr (ind_true h)))
    have h1 : ∫ ω, |dF F i j l (smp X ω)| * |c (smp X ω l - smp X ω v)| ∂μ
        ≤ ∫ ω, M * |dF F i j l (smp X ω)| ∂μ :=
      integral_mono ((H.BM_dF i j l).absv.mul
          (⟨(H.cv_meas l v).comp (smp_meas H.meas), M, fun _ => H.c_bound _⟩ : BM _).absv).integrable
        ((H.BM_dF i j l).absv.const_mul M).integrable
        (fun ω => by
          rw [mul_comm M]
          exact mul_le_mul_of_nonneg_left (H.c_bound _) (abs_nonneg _))
    rw [integral_const_mul] at h1
    refine h1.trans ?_
    have : M ≤ 2 + M * (ind (v = i) + ind (v = j) + ind (v = l)) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hE
  · unfold m3 at hm
    have a1 : i ≠ v := fun h => hm (Or.inl h.symm)
    have a2 : j ≠ v := fun h => hm (Or.inr (Or.inl h.symm))
    have a3 : l ≠ v := fun h => hm (Or.inr (Or.inr h.symm))
    have hdm : Measurable (fun x : ℕ → G => dF F i j l x) := by
      unfold dF
      by_cases hd : dist3 i j l
      · simp only [if_pos hd]; exact measurable_const
      · simp only [if_neg hd]; exact H.fv_meas i j l
    have hdb : ∀ x : ℕ → G, |dF F i j l x| ≤ B := fun x => by
      unfold dF
      by_cases hd : dist3 i j l
      · simp only [if_pos hd, abs_zero]; exact H.B_nonneg (x 0)
      · simp only [if_neg hd]; exact H.bound _ _ _
    have h := H.io_le v {i, j, l, v} (fun x => |dF F i j l x| * |c (x l - x v)|)
      ((continuous_abs.measurable.comp hdm).mul (continuous_abs.measurable.comp (H.cv_meas l v)))
      (B' := B * M)
      (fun x => by
        rw [abs_mul, abs_abs, abs_abs]
        exact mul_le_mul (hdb x) (H.c_bound _) (abs_nonneg _) (H.B_nonneg (x 0)))
      (fun x y hxy => by
        simp only [dF, hxy i (by simp), hxy j (by simp), hxy l (by simp), hxy v (by simp)])
      (fun x => 2 * |dF F i j l x|) (((H.BM_dF i j l).absv.const_mul 2).integrable)
      (fun x => by
        have ee : ∀ z, |dF F i j l (Function.update x v z)|
              * |c (Function.update x v z l - Function.update x v z v)|
            = |dF F i j l x| * |c (x l - z)| := by
          intro z
          simp only [dF, Function.update_self, Function.update_of_ne a1,
            Function.update_of_ne a2, Function.update_of_ne a3]
        show ∫ z, |dF F i j l (Function.update x v z)|
            * |c (Function.update x v z l - Function.update x v z v)| ∂ν ≤ _
        simp_rw [ee]
        rw [integral_const_mul, mul_comm 2]
        exact mul_le_mul_of_nonneg_left (H.c_abs _) (abs_nonneg _))
    refine h.trans ?_
    rw [integral_const_mul]
    have : (2 : ℝ) ≤ 2 + M * (ind (v = i) + ind (v = j) + ind (v = l)) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hE

end DegB3

/-- The final arithmetic. -/
theorem final_alg {N M L V ρ B : ℝ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hMN : M ≤ N) (hL : 0 ≤ L)
    (hV : 0 ≤ V) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) :
    1 / N ^ 4 * (Real.sqrt (N ^ 4 * (M * L ^ 2 * (9 * N ^ 2) + M ^ 2 * L ^ 2 * (9 * N ^ 2)
        + M * V * (256 * N))) + 3 * M * L * N ^ 3 + (2 * N + 3 * M) * (3 * N ^ 2 * ρ + N * B))
      ≤ 16 * ((M * L + ρ) / N + Real.sqrt (M * V / N) / N + B / N ^ 2) := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 ≤ M := by linarith
  set q := Real.sqrt (M * V / N) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = M * V / N := Real.sq_sqrt (by positivity)
  have hNq : N * q ^ 2 = M * V := by rw [hq2]; field_simp
  have hML : M * L ^ 2 ≤ M ^ 2 * L ^ 2 := by
    have : M * L ^ 2 * 1 ≤ M * L ^ 2 * M := mul_le_mul_of_nonneg_left hM1 (by positivity)
    nlinarith
  have hK : N ^ 4 * (M * L ^ 2 * (9 * N ^ 2) + M ^ 2 * L ^ 2 * (9 * N ^ 2) + M * V * (256 * N))
      ≤ (N ^ 2 * (5 * N * M * L + 16 * N * q)) ^ 2 := by
    have e : (N ^ 2 * (5 * N * M * L + 16 * N * q)) ^ 2
        = N ^ 4 * (25 * N ^ 2 * M ^ 2 * L ^ 2 + 160 * N ^ 2 * M * L * q + 256 * N * (N * q ^ 2)) := by
      ring
    rw [e, hNq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : 0 ≤ 160 * N ^ 2 * M * L * q := by positivity
    have h2 : M * L ^ 2 * (9 * N ^ 2) ≤ M ^ 2 * L ^ 2 * (9 * N ^ 2) :=
      mul_le_mul_of_nonneg_right hML (by positivity)
    have h3 : 0 ≤ N ^ 2 * M ^ 2 * L ^ 2 := by positivity
    have e5 : M ^ 2 * L ^ 2 * (9 * N ^ 2) = 9 * (N ^ 2 * M ^ 2 * L ^ 2) := by ring
    have e6 : 25 * N ^ 2 * M ^ 2 * L ^ 2 = 25 * (N ^ 2 * M ^ 2 * L ^ 2) := by ring
    have e7 : M * V * (256 * N) = 256 * N * (M * V) := by ring
    rw [e6, e7]
    rw [e5] at h2
    linarith
  have hs : Real.sqrt (N ^ 4 * (M * L ^ 2 * (9 * N ^ 2) + M ^ 2 * L ^ 2 * (9 * N ^ 2)
        + M * V * (256 * N))) ≤ N ^ 2 * (5 * N * M * L + 16 * N * q) := by
    calc _ ≤ Real.sqrt ((N ^ 2 * (5 * N * M * L + 16 * N * q)) ^ 2) := Real.sqrt_le_sqrt hK
      _ = N ^ 2 * (5 * N * M * L + 16 * N * q) := Real.sqrt_sq (by positivity)
  have h23 : (2 * N + 3 * M) * (3 * N ^ 2 * ρ + N * B) ≤ 5 * N * (3 * N ^ 2 * ρ + N * B) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hR : 16 * ((M * L + ρ) / N + q / N + B / N ^ 2)
      = 1 / N ^ 4 * (16 * (N ^ 3 * (M * L + ρ) + N ^ 3 * q + N ^ 2 * B)) := by
    field_simp
  rw [hR]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hb1 : 0 ≤ N ^ 3 * (M * L) := by positivity
  have hb2 : 0 ≤ N ^ 2 * B := by positivity
  have hb3 : 0 ≤ N ^ 3 * ρ := by positivity
  have e1 : N ^ 2 * (5 * N * M * L + 16 * N * q) = 5 * (N ^ 3 * (M * L)) + 16 * (N ^ 3 * q) := by
    ring
  have e2 : 5 * N * (3 * N ^ 2 * ρ + N * B) = 15 * (N ^ 3 * ρ) + 5 * (N ^ 2 * B) := by ring
  have e3 : 3 * M * L * N ^ 3 = 3 * (N ^ 3 * (M * L)) := by ring
  have e4 : 16 * (N ^ 3 * (M * L + ρ) + N ^ 3 * q + N ^ 2 * B)
      = 16 * (N ^ 3 * (M * L)) + 16 * (N ^ 3 * ρ) + 16 * (N ^ 3 * q) + 16 * (N ^ 2 * B) := by ring
  rw [e4]
  linarith

theorem cnt3_ind (N i j l : ℕ) :
    ∑ v ∈ Finset.range N, (ind (v = i) + ind (v = j) + ind (v = l)) ≤ 3 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [s_eq N i, s_eq N j, s_eq N l]

namespace DegB3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G]
  {ν : Measure G} {X : ℕ → Ω → G} {F : G → G → G → ℝ} {c : G → ℝ} {B M L V ρ Fm : ℝ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem BM_sum4 (f : ℕ → ℕ → ℕ → ℕ → Ω → ℝ) (h : ∀ i j l v, BM (f i j l v)) (N : ℕ) :
    BM (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      ∑ v ∈ Finset.range N, f i j l v ω) :=
  BM.sum _ _ fun i _ => BM.sum _ _ fun j _ => BM.sum _ _ fun l _ => BM.sum _ _ fun v _ =>
    h i j l v

/-- **Lemma "degenerate"(b) for `n = 3`, `a = 3`, undivided form.** -/
theorem Z1_three_sum (H : DegB3 μ ν X F c B M L V ρ Fm) (N : ℕ) :
    ∫ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ∑ v ∈ Finset.range N, wv F c i j l v (smp X ω)| ∂μ
      ≤ Real.sqrt ((N : ℝ) ^ 4 * (M * L ^ 2 * (9 * (N : ℝ) ^ 2)
          + M ^ 2 * L ^ 2 * (9 * (N : ℝ) ^ 2) + M * V * (256 * (N : ℝ))))
        + 3 * M * L * (N : ℝ) ^ 3 + (2 * (N : ℝ) + 3 * M) * (3 * (N : ℝ) ^ 2 * ρ + N * B) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := H.M_nonneg (X 0 ω0)
  have hsplit : ∀ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ∑ v ∈ Finset.range N, wv F c i j l v (smp X ω)
      = Vm F c N (smp X ω)
        + ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
            ∑ v ∈ Finset.range N, r1 F c i j l v (smp X ω)
        + ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
            ∑ v ∈ Finset.range N, r2 F c i j l v (smp X ω) := by
    intro ω
    unfold Vm
    rw [sum_R4 N (fun t => aW F c t.1 t.2.1 t.2.2.1 t.2.2.2 (smp X ω))]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun v _ => ?_
    exact wv_split F c i j l v _
  have b1 := H.BM_Vm N
  have b2 : BM (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      ∑ v ∈ Finset.range N, |r1 F c i j l v (smp X ω)|) :=
    BM_sum4 _ (fun i j l v => (H.BM_r1 i j l v).absv) N
  have b3 : BM (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      ∑ v ∈ Finset.range N, |r2 F c i j l v (smp X ω)|) :=
    BM_sum4 _ (fun i j l v => (H.BM_r2 i j l v).absv) N
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ∑ v ∈ Finset.range N, wv F c i j l v (smp X ω)|
      ≤ |Vm F c N (smp X ω)|
        + ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
            ∑ v ∈ Finset.range N, |r1 F c i j l v (smp X ω)|
        + ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
            ∑ v ∈ Finset.range N, |r2 F c i j l v (smp X ω)| := by
    intro ω
    rw [hsplit ω]
    have a4 : ∀ (g : ℕ → ℕ → ℕ → ℕ → ℝ),
        |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          ∑ v ∈ Finset.range N, g i j l v|
        ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          ∑ v ∈ Finset.range N, |g i j l v| := by
      intro g
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      exact Finset.abs_sum_le_sum_abs _ _
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add le_rfl (a4 _))) (a4 _))
  have hint := ((b1.absv.add b2).add b3).integrable (μ := μ)
  have hmono := integral_mono_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun ω => abs_nonneg _) hint (Filter.Eventually.of_forall hpt)
  refine hmono.trans ?_
  rw [integral_add (b1.absv.add b2).integrable b3.integrable,
    integral_add b1.absv.integrable b2.integrable]
  have hV1 : ∫ ω, |Vm F c N (smp X ω)| ∂μ ≤ Real.sqrt ((N : ℝ) ^ 4 * (M * L ^ 2 * (9 * (N : ℝ) ^ 2)
          + M ^ 2 * L ^ 2 * (9 * (N : ℝ) ^ 2) + M * V * (256 * (N : ℝ)))) :=
    b1.abs_le_sqrt (H.Vm_sq N)
  have hR1 : ∫ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      ∑ v ∈ Finset.range N, |r1 F c i j l v (smp X ω)| ∂μ ≤ 3 * M * L * (N : ℝ) ^ 3 := by
    rw [integral_sum4 (Finset.range N) (fun i j l v ω => |r1 F c i j l v (smp X ω)|)
      (fun i j l v => (H.BM_r1 i j l v).absv.integrable)]
    have hML : 0 ≤ M * L := mul_nonneg hM0 H.L_nonneg
    calc _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          ∑ v ∈ Finset.range N, M * L * (ind (v = i) + ind (v = j) + ind (v = l)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ =>
            Finset.sum_le_sum fun v _ => H.r1_le i j l v
      _ ≤ ∑ _i ∈ Finset.range N, ∑ _j ∈ Finset.range N, ∑ _l ∈ Finset.range N, M * L * 3 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            Finset.sum_le_sum fun l _ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (cnt3_ind N i j l) hML
      _ = 3 * M * L * (N : ℝ) ^ 3 := by simp; ring
  have hR2 : ∫ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      ∑ v ∈ Finset.range N, |r2 F c i j l v (smp X ω)| ∂μ
        ≤ (2 * (N : ℝ) + 3 * M) * (3 * (N : ℝ) ^ 2 * ρ + N * B) := by
    rw [integral_sum4 (Finset.range N) (fun i j l v ω => |r2 F c i j l v (smp X ω)|)
      (fun i j l v => (H.BM_r2 i j l v).absv.integrable)]
    have hE : ∀ i j l, 0 ≤ ∫ ω, |dF F i j l (smp X ω)| ∂μ := fun i j l =>
      integral_nonneg fun _ => abs_nonneg _
    have hc : 0 ≤ 2 * (N : ℝ) + 3 * M := by positivity
    calc _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          ∑ v ∈ Finset.range N, (2 + M * (ind (v = i) + ind (v = j) + ind (v = l)))
            * ∫ ω, |dF F i j l (smp X ω)| ∂μ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ =>
            Finset.sum_le_sum fun v _ => H.r2_le i j l v
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          (2 * (N : ℝ) + 3 * M) * ∫ ω, |dF F i j l (smp X ω)| ∂μ := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            Finset.sum_le_sum fun l _ => ?_
          rw [← Finset.sum_mul]
          refine mul_le_mul_of_nonneg_right ?_ (hE i j l)
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          have := mul_le_mul_of_nonneg_left (cnt3_ind N i j l) hM0
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          linarith
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
          (2 * (N : ℝ) + 3 * M) * (ρ * ((if i = j then (1 : ℝ) else 0)
            + (if j = l then (1 : ℝ) else 0) + (if i = l then (1 : ℝ) else 0))
            + B * (if j = i ∧ l = i then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (H.dF_le i j l) hc
      _ = (2 * (N : ℝ) + 3 * M) * (3 * (N : ℝ) ^ 2 * ρ + N * B) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
          rw [SmallGaps.cnt_ij, SmallGaps.cnt_jl, SmallGaps.cnt_il, SmallGaps.cnt_all]
          ring
  linarith

/-- **Lemma "degenerate"(b) for `n = 3`, `a = 3`.** With `1 ≤ M ≤ N`:
    `E |N⁻⁴ ∑_{i,j,l,v} F(X_i,X_j,X_l) c(X_l - X_v)|
       ≤ 16 [(M L + ρ)/N + (M V/N)^{1/2}/N + B/N²]`,
    `L ≥ ‖F‖₁`, `V ≥ ‖F‖₂²`, `ρ ≥ ϱ(F)`, `B ≥ ‖F‖_∞`. -/
theorem Z1_three (H : DegB3 μ ν X F c B M L V ρ Fm) (N : ℕ) (hN : 1 ≤ N) (hM1 : 1 ≤ M)
    (hMN : M ≤ N) :
    ∫ ω, |1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ∑ v ∈ Finset.range N, F (X i ω) (X j ω) (X l ω) * c (X l ω - X v ω)| ∂μ
      ≤ 16 * ((M * L + ρ) / N + Real.sqrt (M * V / N) / N + B / (N : ℝ) ^ 2) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := H.Z1_three_sum N
  have e : ∀ ω, |1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ∑ l ∈ Finset.range N, ∑ v ∈ Finset.range N, F (X i ω) (X j ω) (X l ω) * c (X l ω - X v ω)|
      = 1 / (N : ℝ) ^ 4 * |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ∑ l ∈ Finset.range N, ∑ v ∈ Finset.range N, wv F c i j l v (smp X ω)| := fun ω => by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 4)]
    rfl
  simp_rw [e]
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  exact final_alg hNr hM1 hMN H.L_nonneg H.V_nonneg H.rho_nonneg (H.B_nonneg (X 0 ω0))

end DegB3

/-! ### The flat torus with the heat kernel -/

section Torus

open CTG.Reals.TorusReduction BiasVariance

/-- For a function invariant under simultaneous translations, `y ↦ ∫∫ f(a, b, y) da db` is
    constant. -/
theorem shift_const {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant]
    {f : G → G → G → ℝ} (hinv : ∀ a b c t, f (a + t) (b + t) (c + t) = f a b c) (y : G) :
    ∫ b, (∫ a, f a b y ∂ν) ∂ν = ∫ b, (∫ a, f a b 0 ∂ν) ∂ν := by
  have e1 : ∀ b, ∫ a, f a b y ∂ν = ∫ a, f a (b - y) 0 ∂ν := by
    intro b
    have e : ∀ a, f a b y = f (a - y) (b - y) 0 := fun a => by
      have h := hinv (a - y) (b - y) 0 y
      rw [sub_add_cancel, sub_add_cancel, zero_add] at h
      exact h
    simp_rw [e]
    exact integral_sub_right_eq_self (μ := ν) (fun a => f a (b - y) 0) y
  simp_rw [e1]
  exact integral_sub_right_eq_self (μ := ν) (fun b => ∫ a, f a b 0 ∂ν) y

/-- `E g(X_{a1}, X_{a2}, X_{a3}) = K` if `∫∫ g(a, b, y) da db = K` for every `y`. -/
theorem nested_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G : Type*} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (g : G → G → G → ℝ)
    (hg : Measurable (fun p : G × G × G => g p.1 p.2.1 p.2.2)) {Bg : ℝ}
    (hgB : ∀ a b y, |g a b y| ≤ Bg) {K : ℝ} (hK : ∀ y, ∫ b, (∫ a, g a b y ∂ν) ∂ν = K)
    {a1 a2 a3 : ℕ} (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h23 : a2 ≠ a3) :
    ∫ ω, g (X a1 ω) (X a2 ω) (X a3 ω) ∂μ = K := by
  have m0 : Measurable (fun x : ℕ → G => g (x a1) (x a2) (x a3)) := by
    have hm : Measurable (fun x : ℕ → G => (x a1, x a2, x a3)) := by fun_prop
    exact hg.comp hm
  have m1 : Measurable (fun x : ℕ → G => pint ν g (x a2, x a3)) := by
    have hm : Measurable (fun x : ℕ → G => (x a2, x a3)) := by fun_prop
    exact (pint_meas ν hg).comp hm
  have s1 := integrate_out ν X h_indep hX hlaw a1 {a1, a2, a3}
    (fun x => g (x a1) (x a2) (x a3)) m0 (fun x => hgB _ _ _)
    (fun x y hxy => by simp only [hxy a1 (by simp), hxy a2 (by simp), hxy a3 (by simp)])
    (fun x => pint ν g (x a2, x a3))
    (fun x => by
      simp only [Function.update_self, Function.update_of_ne h12.symm,
        Function.update_of_ne h13.symm]
      rfl)
  have s2 := integrate_out ν X h_indep hX hlaw a2 {a2, a3}
    (fun x => pint ν g (x a2, x a3)) m1 (fun x => pint_bound ν hgB _)
    (fun x y hxy => by simp only [hxy a2 (by simp), hxy a3 (by simp)])
    (fun _ => K)
    (fun x => by
      simp only [Function.update_self, Function.update_of_ne h23.symm]
      exact hK (x a3))
  calc ∫ ω, g (X a1 ω) (X a2 ω) (X a3 ω) ∂μ
      = ∫ ω, pint ν g (smp X ω a2, smp X ω a3) ∂μ := s1
    _ = ∫ _ω, K ∂μ := s2
    _ = K := by simp

/-- The hypotheses `DegB3` hold on the flat torus for `c = p - 1`, `p` the heat kernel `p_σ`,
    `M = p(0)`, for every measurable bounded `F` invariant under simultaneous translations, with
    the norms in sample form as hypotheses (`L ≥ ‖F‖₁`, `V ≥ ‖F‖₂²`, `ρ ≥ ϱ(F)`). -/
theorem torus_degB3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ)
    {F : FlatTorus d → FlatTorus d → FlatTorus d → ℝ} {B L V ρ : ℝ}
    (hF : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => F p.1 p.2.1 p.2.2))
    (hB : ∀ a b c, |F a b c| ≤ B)
    (hinv : ∀ a b c t, F (a + t) (b + t) (c + t) = F a b c)
    (hl1 : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, |F (X i ω) (X j ω) (X l ω)| ∂μ ≤ L)
    (hvar : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, F (X i ω) (X j ω) (X l ω) ^ 2 ∂μ ≤ V)
    (h12 : ∀ i l : ℕ, i ≠ l → ∫ ω, |F (X i ω) (X i ω) (X l ω)| ∂μ ≤ ρ)
    (h13 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X i ω)| ∂μ ≤ ρ)
    (h23 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X j ω)| ∂μ ≤ ρ) :
    DegB3 μ (flatTorusMeasure d) X F (fun u => pker d σ u - 1) B (torusM d σ 1) L V ρ
      (∫ b, (∫ a, F a b 0 ∂flatTorusMeasure d) ∂flatTorusMeasure d) := by
  set ν := flatTorusMeasure d with hν
  set M := torusM d σ 1 with hMdef
  have hM1 : 1 ≤ M := torusM_one_ge hσ d
  have hp : ∀ u, 0 ≤ pker d σ u ∧ pker d σ u ≤ M := fun u => by
    rw [hMdef, torusM_one]; exact pker_bounds hσ d u
  have hpm : Measurable (pker d σ) := (pker_continuous hσ d).measurable
  have hpx : ∀ x : FlatTorus d, Measurable (fun z : FlatTorus d => pker d σ (x - z)) :=
    fun x => hpm.comp (measurable_const.sub measurable_id)
  have hpi : ∀ x : FlatTorus d, Integrable (fun z => pker d σ (x - z)) ν := fun x =>
    Integrable.of_bound (hpx x).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hp _).1]; exact (hp _).2)
  have hmass : ∀ x : FlatTorus d, ∫ z, pker d σ (x - z) ∂ν = 1 := fun x => pker_mass hσ d x
  have hL : 0 ≤ L := (integral_nonneg fun ω => abs_nonneg _).trans
    (hl1 0 1 2 (by norm_num) (by norm_num) (by norm_num))
  have hV : 0 ≤ V := (integral_nonneg fun ω => _root_.sq_nonneg _).trans
    (hvar 0 1 2 (by norm_num) (by norm_num) (by norm_num))
  have hρ : 0 ≤ ρ := (integral_nonneg fun ω => abs_nonneg _).trans (h12 0 1 (by norm_num))
  have hFa : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => |F p.1 p.2.1 p.2.2|) :=
    continuous_abs.measurable.comp hF
  have hBa : ∀ a b c, |(|F a b c|)| ≤ B := fun a b c => by rw [abs_abs]; exact hB a b c
  refine
    { indep := h_indep
      meas := hX
      law := hlaw
      F_meas := hF
      bound := hB
      c_meas := hpm.sub measurable_const
      c_bound := fun u => by
        rw [abs_le]; constructor <;> linarith [(hp u).1, (hp u).2]
      c_mean1 := fun x => by
        rw [integral_sub (hpi x) (integrable_const 1), hmass x]; simp
      c_mean2 := fun x => by
        have e : ∀ z, pker d σ (z - x) - 1 = pker d σ (x - z) - 1 := fun z => by
          rw [pker_even']
        simp_rw [e]
        rw [integral_sub (hpi x) (integrable_const 1), hmass x]; simp
      c_abs := fun x => by
        calc ∫ z, |pker d σ (x - z) - 1| ∂ν ≤ ∫ z, (pker d σ (x - z) + 1) ∂ν :=
              integral_mono ((hpi x).sub (integrable_const 1)).abs
                ((hpi x).add (integrable_const 1))
                (fun z => by rw [abs_le]; constructor <;> linarith [(hp (x - z)).1])
          _ = 2 := by rw [integral_add (hpi x) (integrable_const 1), hmass x]; simp; norm_num
      c_sq := fun x => by
        have hi2 : Integrable (fun z => (pker d σ (x - z) - 1) ^ 2) ν :=
          Integrable.of_bound (((hpx x).sub measurable_const).pow_const 2).aestronglyMeasurable
            ((M + 1) ^ 2) (Filter.Eventually.of_forall fun z => by
              rw [Real.norm_eq_abs, abs_pow]
              apply pow_le_pow_left₀ (abs_nonneg _)
              rw [abs_le]; constructor <;> linarith [(hp (x - z)).1, (hp (x - z)).2])
        calc ∫ z, (pker d σ (x - z) - 1) ^ 2 ∂ν
            ≤ ∫ z, (M * pker d σ (x - z) - 2 * pker d σ (x - z) + 1) ∂ν :=
              integral_mono hi2
                ((((hpi x).const_mul M).sub ((hpi x).const_mul 2)).add (integrable_const 1))
                (fun z => by
                  have h1 := (hp (x - z)).1
                  have h2 := (hp (x - z)).2
                  nlinarith)
          _ = M - 1 := by
              have i1 : Integrable (fun z => M * pker d σ (x - z) - 2 * pker d σ (x - z)) ν :=
                ((hpi x).const_mul M).sub ((hpi x).const_mul 2)
              rw [integral_add i1
                (integrable_const 1), integral_sub ((hpi x).const_mul M) ((hpi x).const_mul 2),
                integral_const_mul, integral_const_mul, hmass x]
              simp; ring
          _ ≤ M := by linarith
      c_cov := fun x y => by
        have hprod : Integrable (fun z => pker d σ (x - z) * pker d σ (y - z)) ν :=
          Integrable.of_bound ((hpx x).mul (hpx y)).aestronglyMeasurable (M * M)
            (Filter.Eventually.of_forall fun z => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp _).1, abs_of_nonneg (hp _).1]
              exact mul_le_mul (hp _).2 (hp _).2 (hp _).1 (by linarith))
        have e : ∀ z, (pker d σ (x - z) - 1) * (pker d σ (y - z) - 1)
            = pker d σ (x - z) * pker d σ (y - z) - pker d σ (x - z) - pker d σ (y - z) + 1 :=
          fun z => by ring
        simp_rw [e]
        have i1 : Integrable (fun z => pker d σ (x - z) * pker d σ (y - z) - pker d σ (x - z)) ν :=
          hprod.sub (hpi x)
        have i2 : Integrable (fun z => pker d σ (x - z) * pker d σ (y - z) - pker d σ (x - z)
            - pker d σ (y - z)) ν := i1.sub (hpi y)
        rw [integral_add i2 (integrable_const 1),
          integral_sub i1 (hpi y), integral_sub hprod (hpi x), hmass x, hmass y]
        have hI0 : 0 ≤ ∫ z, pker d σ (x - z) * pker d σ (y - z) ∂ν :=
          integral_nonneg fun z => mul_nonneg (hp _).1 (hp _).1
        have hIM : ∫ z, pker d σ (x - z) * pker d σ (y - z) ∂ν ≤ M := by
          calc ∫ z, pker d σ (x - z) * pker d σ (y - z) ∂ν ≤ ∫ z, M * pker d σ (y - z) ∂ν :=
                integral_mono hprod ((hpi y).const_mul M)
                  (fun z => mul_le_mul_of_nonneg_right (hp _).2 (hp _).1)
            _ = M := by rw [integral_const_mul, hmass y, mul_one]
        simp
        rw [abs_le]; constructor <;> linarith
      mean12 := fun y => shift_const ν hinv y
      marg1 := fun y => by
        have hinv' : ∀ a b c t, |F (c + t) (a + t) (b + t)| = |F c a b| := fun a b c t => by
          rw [hinv]
        rw [shift_const ν (f := fun a b y => |F y a b|) hinv' y]
        have hm : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
            |F p.2.2 p.1 p.2.1|) := by
          have hm' : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
              (p.2.2, p.1, p.2.1)) := by fun_prop
          exact continuous_abs.measurable.comp (hF.comp hm')
        have h := nested_eq ν X h_indep hX hlaw (fun a b y => |F y a b|) hm
          (fun a b y => hBa y a b) (fun y => shift_const ν (f := fun a b y => |F y a b|) hinv' y)
          (a1 := 1) (a2 := 2) (a3 := 0) (by norm_num) (by norm_num) (by norm_num)
        rw [← h]
        exact hl1 0 1 2 (by norm_num) (by norm_num) (by norm_num)
      marg2 := fun y => by
        have hinv' : ∀ a b c t, |F (a + t) (c + t) (b + t)| = |F a c b| := fun a b c t => by
          rw [hinv]
        rw [shift_const ν (f := fun a b y => |F a y b|) hinv' y]
        have hm : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
            |F p.1 p.2.2 p.2.1|) := by
          have hm' : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
              (p.1, p.2.2, p.2.1)) := by fun_prop
          exact continuous_abs.measurable.comp (hF.comp hm')
        have h := nested_eq ν X h_indep hX hlaw (fun a b y => |F a y b|) hm
          (fun a b y => hBa a y b) (fun y => shift_const ν (f := fun a b y => |F a y b|) hinv' y)
          (a1 := 0) (a2 := 2) (a3 := 1) (by norm_num) (by norm_num) (by norm_num)
        rw [← h]
        exact hl1 0 1 2 (by norm_num) (by norm_num) (by norm_num)
      marg3 := fun y => by
        have hinv' : ∀ a b c t, |F (a + t) (b + t) (c + t)| = |F a b c| := fun a b c t => by
          rw [hinv]
        rw [shift_const ν (f := fun a b y => |F a b y|) hinv' y]
        have h := nested_eq ν X h_indep hX hlaw (fun a b y => |F a b y|) hFa
          (fun a b y => hBa a b y) (fun y => shift_const ν (f := fun a b y => |F a b y|) hinv' y)
          (a1 := 0) (a2 := 1) (a3 := 2) (by norm_num) (by norm_num) (by norm_num)
        rw [← h]
        exact hl1 0 1 2 (by norm_num) (by norm_num) (by norm_num)
      l1 := hl1
      var := hvar
      rho12 := h12
      rho13 := h13
      rho23 := h23
      L_nonneg := hL
      V_nonneg := hV
      rho_nonneg := hρ }

/-- **Lemma "degenerate"(b) for `n = 3`, `a = 3`, on the flat torus with the heat kernel.**
    Independent uniform points; `p = p_σ`, `M = p(0)`, `c_{jv} = p(x_j - x_v) - 1`; `F` bounded
    (`B`), measurable, invariant under simultaneous translations; `L ≥ ‖F‖₁`, `V ≥ ‖F‖₂²`,
    `ρ ≥ ϱ(F)` in sample form. For `M ≤ N`:
    `E |N⁻⁴ ∑_{i,j,l,v} F(X_i,X_j,X_l) c_{lv}| ≤ 16 [(M L + ρ)/N + (M V/N)^{1/2}/N + B/N²]`. -/
theorem degenerate_b_three_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ)
    {F : FlatTorus d → FlatTorus d → FlatTorus d → ℝ} {B L V ρ : ℝ}
    (hF : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => F p.1 p.2.1 p.2.2))
    (hB : ∀ a b c, |F a b c| ≤ B)
    (hinv : ∀ a b c t, F (a + t) (b + t) (c + t) = F a b c)
    (hl1 : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, |F (X i ω) (X j ω) (X l ω)| ∂μ ≤ L)
    (hvar : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, F (X i ω) (X j ω) (X l ω) ^ 2 ∂μ ≤ V)
    (h12 : ∀ i l : ℕ, i ≠ l → ∫ ω, |F (X i ω) (X i ω) (X l ω)| ∂μ ≤ ρ)
    (h13 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X i ω)| ∂μ ≤ ρ)
    (h23 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X j ω)| ∂μ ≤ ρ)
    (N : ℕ) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ∑ v ∈ Finset.range N, F (X i ω) (X j ω) (X l ω) * (pker d σ (X l ω - X v ω) - 1)| ∂μ
      ≤ 16 * ((torusM d σ 1 * L + ρ) / N + Real.sqrt (torusM d σ 1 * V / N) / N
        + B / (N : ℝ) ^ 2) := by
  have H := torus_degB3 X h_indep hX hlaw hσ hF hB hinv hl1 hvar h12 h13 h23
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := hM1.trans hMN
    exact_mod_cast this
  exact H.Z1_three N hN hM1 hMN

end Torus

/-! ### The positions `a = 1` and `a = 2`, by permuting the arguments of `F` -/

section OtherPositions

open CTG.Reals.TorusReduction

theorem sum3_rev (N : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, f i j l
      = ∑ l ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, f i j l := by
  calc ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, f i j l
      = ∑ i ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j l :=
        Finset.sum_comm
    _ = ∑ l ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range N, f i j l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum3_swap23 (N : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, f i j l
      = ∑ i ∈ Finset.range N, ∑ l ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j l :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **Lemma "degenerate"(b) for `n = 3`, `a = 1`, on the flat torus.** Same hypotheses as
    `degenerate_b_three_torus`; the factor is `c_{ι(1) v}`. -/
theorem degenerate_b_three_torus_a1 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ)
    {F : FlatTorus d → FlatTorus d → FlatTorus d → ℝ} {B L V ρ : ℝ}
    (hF : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => F p.1 p.2.1 p.2.2))
    (hB : ∀ a b c, |F a b c| ≤ B)
    (hinv : ∀ a b c t, F (a + t) (b + t) (c + t) = F a b c)
    (hl1 : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, |F (X i ω) (X j ω) (X l ω)| ∂μ ≤ L)
    (hvar : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, F (X i ω) (X j ω) (X l ω) ^ 2 ∂μ ≤ V)
    (h12 : ∀ i l : ℕ, i ≠ l → ∫ ω, |F (X i ω) (X i ω) (X l ω)| ∂μ ≤ ρ)
    (h13 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X i ω)| ∂μ ≤ ρ)
    (h23 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X j ω)| ∂μ ≤ ρ)
    (N : ℕ) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ∑ v ∈ Finset.range N, F (X i ω) (X j ω) (X l ω) * (pker d σ (X i ω - X v ω) - 1)| ∂μ
      ≤ 16 * ((torusM d σ 1 * L + ρ) / N + Real.sqrt (torusM d σ 1 * V / N) / N
        + B / (N : ℝ) ^ 2) := by
  have hF' : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => F p.2.2 p.2.1 p.1) := by
    have hm : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => (p.2.2, p.2.1, p.1)) :=
      by fun_prop
    exact hF.comp hm
  have h := degenerate_b_three_torus X h_indep hX hlaw hσ (F := fun a b c => F c b a) hF'
    (fun a b c => hB c b a) (fun a b c t => hinv c b a t)
    (fun i j l a b e => hl1 l j i (Ne.symm e) (Ne.symm b) (Ne.symm a))
    (fun i j l a b e => hvar l j i (Ne.symm e) (Ne.symm b) (Ne.symm a))
    (fun i l a => h23 l i (Ne.symm a)) (fun i j a => h13 i j a) (fun i j a => h12 j i (Ne.symm a))
    N hMN
  refine Eq.trans_le ?_ h
  congr 1
  funext ω
  congr 2
  exact sum3_rev N (fun i j l => ∑ v ∈ Finset.range N,
    F (X i ω) (X j ω) (X l ω) * (pker d σ (X i ω - X v ω) - 1))

/-- **Lemma "degenerate"(b) for `n = 3`, `a = 2`, on the flat torus.** -/
theorem degenerate_b_three_torus_a2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ)
    {F : FlatTorus d → FlatTorus d → FlatTorus d → ℝ} {B L V ρ : ℝ}
    (hF : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => F p.1 p.2.1 p.2.2))
    (hB : ∀ a b c, |F a b c| ≤ B)
    (hinv : ∀ a b c t, F (a + t) (b + t) (c + t) = F a b c)
    (hl1 : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, |F (X i ω) (X j ω) (X l ω)| ∂μ ≤ L)
    (hvar : ∀ i j l : ℕ, i ≠ j → i ≠ l → j ≠ l → ∫ ω, F (X i ω) (X j ω) (X l ω) ^ 2 ∂μ ≤ V)
    (h12 : ∀ i l : ℕ, i ≠ l → ∫ ω, |F (X i ω) (X i ω) (X l ω)| ∂μ ≤ ρ)
    (h13 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X i ω)| ∂μ ≤ ρ)
    (h23 : ∀ i j : ℕ, i ≠ j → ∫ ω, |F (X i ω) (X j ω) (X j ω)| ∂μ ≤ ρ)
    (N : ℕ) (hMN : torusM d σ 1 ≤ N) :
    ∫ ω, |1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
        ∑ v ∈ Finset.range N, F (X i ω) (X j ω) (X l ω) * (pker d σ (X j ω - X v ω) - 1)| ∂μ
      ≤ 16 * ((torusM d σ 1 * L + ρ) / N + Real.sqrt (torusM d σ 1 * V / N) / N
        + B / (N : ℝ) ^ 2) := by
  have hF' : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => F p.1 p.2.2 p.2.1) := by
    have hm : Measurable (fun p : FlatTorus d × FlatTorus d × FlatTorus d => (p.1, p.2.2, p.2.1)) :=
      by fun_prop
    exact hF.comp hm
  have h := degenerate_b_three_torus X h_indep hX hlaw hσ (F := fun a b c => F a c b) hF'
    (fun a b c => hB a c b) (fun a b c t => hinv a c b t)
    (fun i j l a b e => hl1 i l j b a (Ne.symm e))
    (fun i j l a b e => hvar i l j b a (Ne.symm e))
    (fun i l a => h13 i l a) (fun i j a => h12 i j a) (fun i j a => h23 i j a)
    N hMN
  refine Eq.trans_le ?_ h
  congr 1
  funext ω
  congr 2
  exact sum3_swap23 N (fun i j l => ∑ v ∈ Finset.range N,
    F (X i ω) (X j ω) (X l ω) * (pker d σ (X j ω - X v ω) - 1))

end OtherPositions
end DegenerateB

namespace BiasGeneral

/-! # A96: `prop:bias` (Appendix G) for every `k`, Stages 1 and 2

* `sigC`, `sig0`, `betaK`: `β_k` of `prop:bias` for `ρ = p(0)` as a definition for every `k`;
  `betaK_one`, `betaK_two`, `betaK_three`: it agrees with the forms used for `k = 1, 2, 3`
  (`bias_one_general`, `BiasVariance3.beta2`, `BiasVariance4.beta3`).
* `pth`, `cw`, `trace_pow_cw`, `sum_cw_shift`, `sum_cw_pos`, `sum_cw_pos_le`: closed walks as sums
  over vertex tuples, cyclic symmetry, the bound `∑_v cw(v) f(v_t) ≤ (M/N) r^n ∑ f`.
* `gC`, `prod_gamma`: the product of `k` vertex factors to second order (the term `E_3` of the
  paper is in the remainder), with the constant `gC k ≤ 800 · 4^k` (`gC_le`).
* `trace_expansion`, `trace_expansion_paper`: Steps 1–3 of the proof for EVERY `k`
  (deterministic): `|Tr P^k - (Q₀ + Q₁ + Q₂ + Q₃)| ≤ gC(k) k (9/8)^{k-1} (17/8) δ M (1/N) ∑ ε²`.

NOT proved here: the expectations of the polynomial statistics for general `k` (Steps 4–7),
hence no statement `E Tr P^k = m_k + β_k/N + …` for `k ≥ 4`. -/

open PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance3 BiasVariance4

/-- `Σ_c` of `prop:bias` for `ρ = p(0)`: `∑_{l=1}^{k-1} ∫ p_{lσ} p_{(k-l)σ} p_{cσ}`. -/
noncomputable def sigC (d : ℕ) (σ : ℝ) (k c : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ico 1 k, ∫ u, pker d ((l : ℝ) * σ) u * pker d (((k - l : ℕ) : ℝ) * σ) u
      * pker d ((c : ℝ) * σ) u ∂flatTorusMeasure d

/-- `Σ_0` of `prop:bias` for `ρ = p(0)` (`μ_l = m_l`): `∑_{l=1}^{k-1} m_l m_{k-l}`. -/
noncomputable def sig0 (d : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ico 1 k, torusM d σ l * torusM d σ (k - l)

/-- **`β_k` of `prop:bias` for `ρ = p(0)`, every `k`:**
    `β_k = k [Σ₀/2 - 2Σ₁ + 3Σ₂ - 2Σ₃ + Σ₄/2] + k m_k (m₄ - 3m₃ + 3m₂ - m₁)`. -/
noncomputable def betaK (d : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  k * (sig0 d σ k / 2 - 2 * sigC d σ k 1 + 3 * sigC d σ k 2 - 2 * sigC d σ k 3
      + sigC d σ k 4 / 2)
    + k * torusM d σ k
      * (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1)

theorem betaK_one (d : ℕ) (σ : ℝ) :
    betaK d σ 1 = torusM d σ 1
      * (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1) := by
  simp [betaK, sigC, sig0]

theorem betaK_two (d : ℕ) (σ : ℝ) : betaK d σ 2 = beta2 d σ := by
  have e : ∀ c : ℕ, sigC d σ 2 c = Jp d σ ((c : ℝ) * σ) := by
    intro c
    simp only [sigC, Jp]
    rw [show Finset.Ico 1 2 = {1} from rfl, Finset.sum_singleton]
    norm_num
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only; ring)
  simp only [betaK, beta2, sig0, e]
  rw [show Finset.Ico 1 2 = {1} from rfl, Finset.sum_singleton]
  norm_num
  ring

theorem betaK_three (d : ℕ) (σ : ℝ) : betaK d σ 3 = beta3 d σ := by
  have h2 : ((2 : ℕ) : ℝ) * σ = σ + σ := by push_cast; ring
  have e : ∀ c : ℕ, sigC d σ 3 c = 2 * Tp d σ ((c : ℝ) * σ) := by
    intro c
    simp only [sigC, Tp]
    rw [show Finset.Ico 1 3 = {1, 2} from rfl, Finset.sum_pair (by norm_num)]
    norm_num
    rw [show (2 : ℝ) * σ = σ + σ by ring]
    rw [two_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only; ring)
  simp only [betaK, beta3, sig0, e]
  rw [show Finset.Ico 1 3 = {1, 2} from rfl, Finset.sum_pair (by norm_num)]
  norm_num
  ring

/-! ## Stage 2a: closed walks as sums over vertex tuples -/

section Walks

variable {α : Type*} [Fintype α]

/-- The open path `B a w₀ · B w₀ w₁ ⋯ B w_{n-1} b`. -/
def pth (B : α → α → ℝ) : (n : ℕ) → α → (Fin n → α) → α → ℝ
  | 0, a, _, b => B a b
  | n + 1, a, w, b => B a (w 0) * pth B n (w 0) (Fin.tail w) b

/-- The weight of a closed walk through `v₀, …, v_n`: `∏_a B (v a) (v (a+1))`. -/
def cw (B : α → α → ℝ) {n : ℕ} (v : Fin (n + 1) → α) : ℝ := ∏ a : Fin (n + 1), B (v a) (v (a + 1))

theorem pow_apply_pth [DecidableEq α] (B : Matrix α α ℝ) (n : ℕ) (a b : α) :
    (B ^ (n + 1)) a b = ∑ w : Fin n → α, pth B n a w b := by
  induction n generalizing a with
  | zero => simp [pth]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, BiasVariance3.sum_cons]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [pth]

theorem pth_prod (B : α → α → ℝ) : ∀ (n : ℕ) (v : Fin (n + 1) → α) (b : α),
    pth B n (v 0) (Fin.tail v) b
      = (∏ i : Fin n, B (v i.castSucc) (v i.succ)) * B (v (Fin.last n)) b := by
  intro n
  induction n with
  | zero => intro v b; simp [pth]
  | succ n ih =>
    intro v b
    have h := ih (Fin.tail v) b
    simp only [pth]
    rw [Fin.prod_univ_succ]
    have e1 : (Fin.tail v : Fin (n + 1) → α) 0 = v (1 : Fin (n + 2)) := rfl
    rw [show (Fin.tail v : Fin (n + 1) → α) 0 = Fin.tail v 0 from rfl] at h
    rw [h]
    simp only [Fin.tail, Fin.succ_castSucc, Fin.succ_last]
    rw [show (Fin.succ (0 : Fin (n + 1))) = (1 : Fin (n + 2)) from rfl,
      show (Fin.castSucc (0 : Fin (n + 1))) = (0 : Fin (n + 2)) from rfl]
    ring

theorem cw_eq_pth (B : α → α → ℝ) (n : ℕ) (v : Fin (n + 1) → α) :
    cw B v = pth B n (v 0) (Fin.tail v) (v 0) := by
  rw [pth_prod, cw, Fin.prod_univ_castSucc, Fin.last_add_one]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.coeSucc_eq_succ]

theorem trace_pow_cw [DecidableEq α] (B : Matrix α α ℝ) (n : ℕ) :
    (B ^ (n + 1)).trace = ∑ v : Fin (n + 1) → α, cw B v := by
  rw [BiasVariance3.sum_cons, Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, pow_apply_pth]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cw_eq_pth]
  simp

theorem cw_mul_diag (A : α → α → ℝ) (γ : α → ℝ) {n : ℕ} (v : Fin (n + 1) → α) :
    cw (fun i j => A i j * γ j) v = cw A v * ∏ a, γ (v a) := by
  rw [cw, cw, Finset.prod_mul_distrib]
  congr 1
  exact Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun a => rfl)

theorem cw_rot (B : α → α → ℝ) {n : ℕ} (v : Fin (n + 1) → α) :
    cw B (fun a => v (a + 1)) = cw B v := by
  rw [cw, cw]
  exact Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun a => rfl)

/-- A function of the shifted walk has the same sum against the closed walks (cyclic symmetry). -/
theorem sum_cw_shift (B : α → α → ℝ) {n : ℕ} (Φ : (Fin (n + 1) → α) → ℝ) (s : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → α, cw B v * Φ (fun a => v (a + s))
      = ∑ v : Fin (n + 1) → α, cw B v * Φ v := by
  have step : ∀ (Ψ : (Fin (n + 1) → α) → ℝ),
      ∑ v : Fin (n + 1) → α, cw B v * Ψ (fun a => v (a + 1))
        = ∑ v : Fin (n + 1) → α, cw B v * Ψ v := by
    intro Ψ
    let e : (Fin (n + 1) → α) ≃ (Fin (n + 1) → α) :=
      (Equiv.addRight (1 : Fin (n + 1))).symm.arrowCongr (Equiv.refl α)
    have he : ∀ v, e v = fun a => v (a + 1) := fun v => by
      funext a; simp [e, Equiv.arrowCongr_apply]
    symm
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [he, cw_rot]
  have key : ∀ s : Fin (n + 1), ∀ Ψ : (Fin (n + 1) → α) → ℝ,
      ∑ v : Fin (n + 1) → α, cw B v * Ψ (fun a => v (a + s))
        = ∑ v : Fin (n + 1) → α, cw B v * Ψ v := by
    intro s
    induction s using Fin.induction with
    | zero => intro Ψ; simp
    | succ i ih =>
      intro Ψ
      rw [← Fin.coeSucc_eq_succ]
      have h := step (fun w => Ψ (fun a => w (a + i.castSucc)))
      simp only at h
      rw [← ih Ψ, ← h]
      refine Finset.sum_congr rfl fun v _ => ?_
      have e : (fun a => v (a + (i.castSucc + 1))) = (fun a => v (a + i.castSucc + 1)) := by
        funext a; simp only [add_assoc]
      rw [e]
  exact key s Φ

/-- Summing a function of one position against the closed walks does not depend on the
    position. -/
theorem sum_cw_pos (B : α → α → ℝ) {n : ℕ} (f : α → ℝ) (t : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → α, cw B v * f (v t) = ∑ v : Fin (n + 1) → α, cw B v * f (v 0) := by
  have h := sum_cw_shift B (fun w => f (w 0)) t
  simp only [zero_add] at h
  exact h

theorem pth_nonneg (B : α → α → ℝ) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ (n : ℕ) (a : α) (w : Fin n → α) (b : α), 0 ≤ pth B n a w b := by
  intro n
  induction n with
  | zero => intro a w b; exact hB a b
  | succ n ih => intro a w b; exact mul_nonneg (hB _ _) (ih _ _ _)

theorem cw_nonneg (B : α → α → ℝ) (hB : ∀ i j, 0 ≤ B i j) {n : ℕ} (v : Fin (n + 1) → α) :
    0 ≤ cw B v := Finset.prod_nonneg fun a _ => hB _ _

theorem sum_pth_le (B : α → α → ℝ) (hB : ∀ i j, 0 ≤ B i j) {e r : ℝ} (he : ∀ i j, B i j ≤ e)
    (hrow : ∀ i, ∑ j, B i j ≤ r) (he0 : 0 ≤ e) (hr0 : 0 ≤ r) :
    ∀ (n : ℕ) (a b : α), ∑ w : Fin n → α, pth B n a w b ≤ e * r ^ n := by
  intro n
  induction n with
  | zero => intro a b; simp [pth, he]
  | succ n ih =>
    intro a b
    rw [BiasVariance3.sum_cons]
    calc ∑ c : α, ∑ w : Fin n → α, pth B (n + 1) a (Fin.cons c w) b
        = ∑ c : α, B a c * ∑ w : Fin n → α, pth B n c w b := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          simp [pth]
      _ ≤ ∑ c : α, B a c * (e * r ^ n) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (ih c b) (hB a c)
      _ = (∑ c, B a c) * (e * r ^ n) := by rw [Finset.sum_mul]
      _ ≤ r * (e * r ^ n) :=
          mul_le_mul_of_nonneg_right (hrow a) (mul_nonneg he0 (pow_nonneg hr0 n))
      _ = e * r ^ (n + 1) := by ring

/-- `∑_v cw(v) f(v_t) ≤ e r^n ∑ f` for every position `t` and `f ≥ 0`. -/
theorem sum_cw_pos_le (B : α → α → ℝ) (hB : ∀ i j, 0 ≤ B i j) {e r : ℝ} (he : ∀ i j, B i j ≤ e)
    (hrow : ∀ i, ∑ j, B i j ≤ r) (he0 : 0 ≤ e) (hr0 : 0 ≤ r) {n : ℕ} (f : α → ℝ)
    (hf : ∀ i, 0 ≤ f i) (t : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → α, cw B v * f (v t) ≤ e * r ^ n * ∑ i, f i := by
  rw [sum_cw_pos, BiasVariance3.sum_cons, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have e1 : ∑ w : Fin n → α, cw B (Fin.cons a w : Fin (n + 1) → α) * f ((Fin.cons a w : Fin (n + 1) → α) 0)
      = (∑ w : Fin n → α, pth B n a w a) * f a := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [cw_eq_pth]; simp
  rw [e1, mul_comm (e * r ^ n)]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (sum_pth_le B hB he hrow he0 hr0 n a a) (hf a)

end Walks

open BiasVariance

/-- `(∑ f)² ≤ k ∑ f²`. -/
theorem sq_sum_le_fin {k : ℕ} (f : Fin k → ℝ) : (∑ t, f t) ^ 2 ≤ k * ∑ t, f t ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) (fun _ => (1 : ℝ)) f
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  exact h

/-- The constant of `prod_gamma`: `gC 0 = 0`, `gC (k+1) = 2 gC k + 200 (k+1)²`. -/
noncomputable def gC : ℕ → ℝ
  | 0 => 0
  | k + 1 => 2 * gC k + 200 * ((k : ℝ) + 1) ^ 2

theorem gC_nonneg : ∀ k, 0 ≤ gC k
  | 0 => le_refl _
  | k + 1 => by
    have := gC_nonneg k
    simp only [gC]; positivity

theorem gC_le : ∀ k : ℕ, gC k ≤ 800 * 4 ^ k
  | 0 => by simp [gC]
  | k + 1 => by
    have ih := gC_le k
    have h2 : ((k : ℝ) + 1) ≤ 2 ^ k := by
      have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      exact_mod_cast this
    have h3 : ((k : ℝ) + 1) ^ 2 ≤ 4 ^ k := by
      rw [show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      exact pow_le_pow_left₀ (by positivity) h2 2
    simp only [gC, pow_succ]
    nlinarith only [ih, h3]

theorem step_arith {δ k G g0 a0 c0 q0 E C S1 S2 Sq R0 : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hk : 0 ≤ k) (hG : 0 ≤ G) (hq0 : 0 ≤ q0) (hSq0 : 0 ≤ Sq)
    (hE : |E| ≤ G * δ * Sq) (hR0 : |R0| ≤ 44 * δ * q0) (ha0 : |a0| ≤ 4 * δ) (hC : |C| ≤ 5 * Sq)
    (hS2 : |S2| ≤ 4 * (k + 1) * Sq) (hS1 : |S1| ≤ 4 * k * δ + 5 * Sq) (hc0 : |c0| ≤ 5 * q0)
    (hg0 : |g0| ≤ 2) (hSq : Sq ≤ 17 / 64 * k * δ) :
    |g0 * E + R0 + a0 * C + a0 * S2 + (c0 + R0) * (S1 + S2)|
      ≤ (2 * G + 200 * (k + 1) ^ 2) * δ * (q0 + Sq) := by
  have t1 := abs_mul_le' hg0 hE
  have t2 := abs_mul_le' ha0 hC
  have t3 := abs_mul_le' ha0 hS2
  have hcR : |c0 + R0| ≤ 11 * q0 := by
    have : 44 * δ * q0 ≤ 6 * q0 := by nlinarith only [hδ, hq0]
    exact (abs_add_le _ _).trans (by linarith only [hc0, hR0, this])
  have hSS : |S1 + S2| ≤ 4 * k * δ + (4 * k + 9) * (17 / 64 * k * δ) := by
    have h1 := (abs_add_le S1 S2).trans (add_le_add hS1 hS2)
    have h2 : (4 * k + 9) * Sq ≤ (4 * k + 9) * (17 / 64 * k * δ) :=
      mul_le_mul_of_nonneg_left hSq (by linarith)
    linarith only [h1, h2]
  have t4 := abs_mul_le' hcR hSS
  have tot := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add t1 hR0)) t2)) t3)) t4)
  refine tot.trans ?_
  have hX : 0 ≤ δ * q0 := mul_nonneg hδ0 hq0
  have hY : 0 ≤ δ * Sq := mul_nonneg hδ0 hSq0
  have p1 : 0 ≤ k * (δ * q0) := mul_nonneg hk hX
  have p2 : 0 ≤ k * k * (δ * q0) := mul_nonneg (mul_nonneg hk hk) hX
  have p3 : 0 ≤ k * (δ * Sq) := mul_nonneg hk hY
  have p4 : 0 ≤ k * k * (δ * Sq) := mul_nonneg (mul_nonneg hk hk) hY
  nlinarith only [p1, p2, p3, p4, hX, hY, hG, mul_nonneg hG hY]

/-- **The product of `k` vertex factors to second order** (Step 3 of `prop:bias` for one tuple):
    with `|g_t - (1 + a_t + c_t)| ≤ 44 δ q_t`, `|a_t| ≤ 4δ`, `a_t² ≤ 8 q_t`, `|c_t| ≤ 5 q_t`,
    `0 ≤ q_t ≤ 17/8 δ²`, `δ ≤ 1/8`:
    `|∏ g - (1 + ∑ (a + c) + ((∑ a)² - ∑ a²)/2)| ≤ gC k · δ · ∑ q`.  The quadratic term is
    `∑_{s<t} a_s a_t`. -/
theorem prod_gamma {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) :
    ∀ (k : ℕ) (g a c q : Fin k → ℝ), (∀ t, 0 ≤ q t) → (∀ t, q t ≤ 17 / 8 * δ ^ 2) →
      (∀ t, |g t - (1 + a t + c t)| ≤ 44 * δ * q t) → (∀ t, |a t| ≤ 4 * δ) →
      (∀ t, a t ^ 2 ≤ 8 * q t) → (∀ t, |c t| ≤ 5 * q t) →
      |∏ t, g t - (1 + ∑ t, (a t + c t) + ((∑ t, a t) ^ 2 - ∑ t, a t ^ 2) / 2)|
        ≤ gC k * δ * ∑ t, q t := by
  intro k
  induction k with
  | zero => intro g a c q _ _ _ _ _ _; simp [gC]
  | succ k ih =>
    intro g a c q hq hqδ hg ha has hc
    have IH := ih (fun t => g t.succ) (fun t => a t.succ) (fun t => c t.succ) (fun t => q t.succ)
      (fun t => hq _) (fun t => hqδ _) (fun t => hg _) (fun t => ha _) (fun t => has _)
      (fun t => hc _)
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ]
    obtain ⟨P, hP⟩ : ∃ P, P = ∏ t : Fin k, g t.succ := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A, A = ∑ t : Fin k, a t.succ := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, C = ∑ t : Fin k, c t.succ := ⟨_, rfl⟩
    obtain ⟨Q2, hQ2⟩ : ∃ Q2, Q2 = ∑ t : Fin k, a t.succ ^ 2 := ⟨_, rfl⟩
    obtain ⟨Sq, hSq⟩ : ∃ Sq, Sq = ∑ t : Fin k, q t.succ := ⟨_, rfl⟩
    have hS1e : ∑ t : Fin k, (a t.succ + c t.succ) = A + C := by
      rw [hA, hC, Finset.sum_add_distrib]
    rw [← hP, ← hQ2, ← hSq, hS1e, ← hA] at IH
    rw [← hP, ← hA, ← hQ2, ← hSq, hS1e]
    obtain ⟨E, hE⟩ : ∃ E, E = P - (1 + (A + C) + (A ^ 2 - Q2) / 2) := ⟨_, rfl⟩
    obtain ⟨R0, hR0⟩ : ∃ R0, R0 = g 0 - (1 + a 0 + c 0) := ⟨_, rfl⟩
    rw [← hE] at IH
    have e : g 0 * P - (1 + (a 0 + c 0 + (A + C)) + ((a 0 + A) ^ 2 - (a 0 ^ 2 + Q2)) / 2)
        = g 0 * E + R0 + a 0 * C + a 0 * ((A ^ 2 - Q2) / 2)
          + (c 0 + R0) * ((A + C) + (A ^ 2 - Q2) / 2) := by
      rw [hE, hR0]; ring
    rw [e]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hSq0 : 0 ≤ Sq := by rw [hSq]; exact Finset.sum_nonneg fun t _ => hq _
    have hSqδ : Sq ≤ 17 / 64 * k * δ := by
      have h1 : Sq ≤ ∑ _t : Fin k, 17 / 8 * δ ^ 2 := by
        rw [hSq]; exact Finset.sum_le_sum fun t _ => hqδ _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      have h2 : δ ^ 2 ≤ δ / 8 := by nlinarith only [hδ0, hδ]
      nlinarith only [h1, h2, hk0]
    have hCb : |C| ≤ 5 * Sq := by
      rw [hC, hSq, Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hc _)
    have hAb : |A| ≤ 4 * k * δ := by
      rw [hA]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_sum fun (t : Fin k) (_ : t ∈ Finset.univ) => ha t.succ
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith only [this]
    have hQ2b : Q2 ≤ 8 * Sq := by
      rw [hQ2, hSq, Finset.mul_sum]; exact Finset.sum_le_sum fun t _ => has _
    have hQ20 : 0 ≤ Q2 := by rw [hQ2]; exact Finset.sum_nonneg fun t _ => _root_.sq_nonneg _
    have hA2 : A ^ 2 ≤ k * Q2 := by
      rw [hA, hQ2]; exact sq_sum_le_fin (fun t => a t.succ)
    have hS2 : |(A ^ 2 - Q2) / 2| ≤ 4 * (k + 1) * Sq := by
      have h1 : k * Q2 ≤ k * (8 * Sq) := mul_le_mul_of_nonneg_left hQ2b hk0
      rw [abs_le]; constructor <;> nlinarith only [h1, hA2, hQ2b, hQ20, _root_.sq_nonneg A]
    have hS1 : |A + C| ≤ 4 * k * δ + 5 * Sq := (abs_add_le _ _).trans (add_le_add hAb hCb)
    have hg0 : |g 0| ≤ 2 := by
      have h1 := hg 0
      have h2 := ha 0
      have h3 := hc 0
      have h4 := hqδ 0
      have h5 : δ ^ 2 ≤ δ / 8 := by nlinarith only [hδ0, hδ]
      have h6 : δ * q 0 ≤ 1 / 8 * q 0 := mul_le_mul_of_nonneg_right hδ (hq 0)
      obtain ⟨x1, x2⟩ := abs_le.mp h1
      obtain ⟨y1, y2⟩ := abs_le.mp h2
      obtain ⟨z1, z2⟩ := abs_le.mp h3
      rw [abs_le]; constructor <;> nlinarith only [x1, x2, y1, y2, z1, z2, h4, h5, h6, hδ, hδ0, hq 0]
    have hR0b : |R0| ≤ 44 * δ * q 0 := by rw [hR0]; exact hg 0
    have := step_arith hδ0 hδ hk0 (gC_nonneg k) (hq 0) hSq0 IH hR0b (ha 0) hCb hS2 hS1 (hc 0) hg0
      hSqδ
    have e2 : gC (k + 1) * δ * (q 0 + Sq) = (2 * gC k + 200 * ((k : ℝ) + 1) ^ 2) * δ * (q 0 + Sq) := by
      simp only [gC]
    rw [e2]
    exact this

open PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance2

/-! ## Stage 2c: Steps 1–3 of `prop:bias` for every `k`, deterministic -/

/-- **Steps 1–3 of the proof of `prop:bias` for every `k = n + 1`, deterministic.** `K` symmetric
    with values in `[0, M]`, `ρ_i = (1/N) ∑_l K_il = 1 + ε_i`, `|ε_i| ≤ δ ≤ 1/8`, `bv = P̃ε`,
    `sv = P̃ε²`, `φ¹ = -2ε + bv`, `φ² = 3ε² - 3ε bv + bv² - sv`; the sum runs over the closed walks
    `v₀ → v₁ → ⋯ → v_n → v₀` with weight `cw = ∏ P̃_{v_a v_{a+1}}`.  Then
    `|Tr P^{n+1} - ∑_v cw(v) (1 + ∑_t (φ¹+φ²)(v_t) + ∑_{s<t} φ¹(v_s) φ¹(v_t))|
       ≤ gC(n+1) (n+1) (9/8)^n (17/8) δ M (1/N) ∑ ε²`,
    the pair sum written as `((∑ φ¹)² - ∑ (φ¹)²)/2`.  The subtracted sum is `Q_0+Q_1+Q_2+Q_3`
    of the paper (before the cyclic symmetrisation); the products of three or more factors
    `γ - 1` (the term `E_3` of the paper) are in the remainder. -/
theorem trace_expansion {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ) (ρ ε bv sv : Fin N → ℝ)
    {M δ : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hKM : ∀ i j, K i j ≤ M) (hsym : ∀ i j, K i j = K j i)
    (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1)
    (hbv : ∀ i, bv i = 1 / (N : ℝ) * ∑ l, K i l * ε l)
    (hsv : ∀ i, sv i = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    (hδ : δ ≤ 1 / 8) (hεδ : ∀ i, |ε i| ≤ δ) (n : ℕ) :
    |((walkMatrix K ρ) ^ (n + 1)).trace
        - ∑ v : Fin (n + 1) → Fin N, cw (fun i j => K i j / (N : ℝ)) v
          * (1 + ∑ t, ((-2 * ε (v t) + bv (v t))
                + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
              + ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2
                - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2) / 2)|
      ≤ gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * (17 / 8)
          * (δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  have hδ0 : 0 ≤ δ := (abs_nonneg (ε ⟨0, hN⟩)).trans (hεδ _)
  have hM0 : 0 ≤ M := (hK0 ⟨0, hN⟩ ⟨0, hN⟩).trans (hKM _ _)
  have hl : ∀ l, -δ ≤ ε l ∧ ε l ≤ δ := fun l => abs_le.mp (hεδ l)
  have hρe : ∀ l, ρ l = 1 + ε l := fun l => by rw [hε l]; ring
  have hρlo : ∀ l, 7 / 8 ≤ ρ l := fun l => by rw [hρe l]; linarith only [(hl l).1, hδ]
  have hρhi : ∀ l, ρ l ≤ 9 / 8 := fun l => by rw [hρe l]; linarith only [(hl l).2, hδ]
  have hρ0 : ∀ l, ρ l ≠ 0 := fun l => by linarith only [hρlo l]
  obtain ⟨γ, hγd⟩ : ∃ γ : Fin N → ℝ,
      γ = fun i => 1 / ρ i * (1 / (1 / (N : ℝ) * ∑ l, K i l / ρ l)) := ⟨_, rfl⟩
  obtain ⟨qv, hqv⟩ : ∃ qv : Fin N → ℝ, qv = fun i => ε i ^ 2 + sv i := ⟨_, rfl⟩
  have hv : ∀ i, |γ i - (1 + (-2 * ε i + bv i)
        + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))| ≤ 44 * δ * qv i
      ∧ 0 ≤ qv i ∧ qv i ≤ 17 / 8 * δ ^ 2 ∧ |-2 * ε i + bv i| ≤ 4 * δ
      ∧ (-2 * ε i + bv i) ^ 2 ≤ 8 * qv i
      ∧ |3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i| ≤ 5 * qv i := by
    intro i
    have Gv := BiasVariance2.gamma_vertex hN K ρ ε hK0 hρ hε hδ hεδ i
    rw [← hbv i, ← hsv i] at Gv
    obtain ⟨g1, g2, g3, g4, g5⟩ := Gv
    have he2 : ε i ^ 2 ≤ δ ^ 2 := sq_le_sq' (hl i).1 (hl i).2
    obtain ⟨b1, b2⟩ := abs_le.mp g2
    have hqi : qv i = ε i ^ 2 + sv i := by rw [hqv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hγd, hqi]
      have e : 1 + (-2 * ε i + bv i) + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i)
          = 1 - 2 * ε i + bv i + 3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i := by ring
      rw [e]; exact g1
    · rw [hqi]; exact add_nonneg (_root_.sq_nonneg _) g4
    · rw [hqi]; linarith only [he2, g5]
    · rw [abs_le]; constructor <;> linarith only [(hl i).1, (hl i).2, b1, b2, hδ0]
    · rw [hqi]
      nlinarith only [_root_.sq_nonneg (2 * ε i + bv i), g3, g4, _root_.sq_nonneg (ε i)]
    · rw [hqi, abs_le]
      constructor
      · nlinarith only [_root_.sq_nonneg (ε i - bv i), _root_.sq_nonneg (ε i + bv i), g3, g4,
          _root_.sq_nonneg (ε i), _root_.sq_nonneg (bv i)]
      · nlinarith only [_root_.sq_nonneg (ε i - bv i), _root_.sq_nonneg (ε i + bv i), g3, g4,
          _root_.sq_nonneg (ε i), _root_.sq_nonneg (bv i)]
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
  have hcolq : ∑ i, sv i ≤ 9 / 8 * ∑ i, ε i ^ 2 := by
    simp only [hsv]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i, K i l = N * ρ l := by
      rw [← hρ l]; exact Finset.sum_congr rfl fun i _ => hsym i l
    rw [this]
    have h1 := mul_le_mul_of_nonneg_right (hρhi l) (_root_.sq_nonneg (ε l))
    have e : 1 / (N : ℝ) * (N * ρ l * ε l ^ 2) = ρ l * ε l ^ 2 := by field_simp
    rw [e]; exact h1
  have hSq : ∑ i, qv i ≤ 17 / 8 * ∑ i, ε i ^ 2 := by
    rw [hqv, Finset.sum_add_distrib]; linarith only [hcolq]
  have hSe : 0 ≤ ∑ i, ε i ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
  have hterm : ∀ v : Fin (n + 1) → Fin N,
      |cw A v * (∏ t, γ (v t)
          - (1 + ∑ t, ((-2 * ε (v t) + bv (v t))
                + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
              + ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2
                - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2) / 2))|
        ≤ gC (n + 1) * δ * ∑ t, cw A v * qv (v t) := by
    intro v
    have hp := prod_gamma hδ0 hδ (n + 1) (fun t => γ (v t)) (fun t => -2 * ε (v t) + bv (v t))
      (fun t => 3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t))
      (fun t => qv (v t)) (fun t => (hv _).2.1) (fun t => (hv _).2.2.1)
      (fun t => by
        have := (hv (v t)).1
        have e : 1 + (-2 * ε (v t) + bv (v t))
            + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t))
            = 1 + (-2 * ε (v t) + bv (v t))
              + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)) := rfl
        exact this)
      (fun t => (hv _).2.2.2.1) (fun t => (hv _).2.2.2.2.1) (fun t => (hv _).2.2.2.2.2)
    rw [abs_mul, abs_of_nonneg (cw_nonneg A hA0 v), ← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left hp (cw_nonneg A hA0 v)
    exact h.trans (le_of_eq (by ring))
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => hterm v)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hpos : ∀ t : Fin (n + 1), ∑ v : Fin (n + 1) → Fin N, cw A v * qv (v t)
      ≤ M / N * (9 / 8) ^ n * ∑ i, qv i := fun t =>
    sum_cw_pos_le A hA0 hAM hrow (div_nonneg hM0 hNpos.le) (by norm_num) qv (fun i => (hv i).2.1) t
  have hsum := Finset.sum_le_sum fun (t : Fin (n + 1)) (_ : t ∈ Finset.univ) => hpos t
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hG := gC_nonneg (n + 1)
  have hGδ : 0 ≤ gC (n + 1) * δ := mul_nonneg hG hδ0
  have h1 := mul_le_mul_of_nonneg_left hsum hGδ
  have hc : 0 ≤ ((n + 1 : ℕ) : ℝ) * (M / N * (9 / 8) ^ n) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg hM0 hNpos.le) (by positivity))
  have h2 : ((n + 1 : ℕ) : ℝ) * (M / N * (9 / 8) ^ n * ∑ i, qv i)
      ≤ ((n + 1 : ℕ) : ℝ) * (M / N * (9 / 8) ^ n) * (17 / 8 * ∑ i, ε i ^ 2) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hSq hc
  have h3 := mul_le_mul_of_nonneg_left h2 hGδ
  refine h1.trans (h3.trans (le_of_eq ?_))
  push_cast
  field_simp

/-! ## Stage 2d: the cyclic symmetrisation (`Q_1`, `Q_2`, `Q_3` of the paper as sums over walks
    with the factors at positions `0` and `l`) -/

section Sym

variable {α : Type*} [Fintype α]

/-- The pair sum over positions `s < t` of a closed walk, symmetrised:
    `∑_v cw(v) ∑_{s ≠ t} f(v_s) f(v_t) = (n+1) ∑_{l=1}^{n} ∑_v cw(v) f(v_0) f(v_l)`. -/
theorem sum_cw_pairs (B : α → α → ℝ) {n : ℕ} (f : α → ℝ) :
    ∑ v : Fin (n + 1) → α, cw B v * ((∑ t, f (v t)) ^ 2 - ∑ t, f (v t) ^ 2)
      = ((n : ℝ) + 1) * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
          ∑ v : Fin (n + 1) → α, cw B v * (f (v 0) * f (v l)) := by
  have e1 : ∀ v : Fin (n + 1) → α, (∑ t, f (v t)) ^ 2 - ∑ t, f (v t) ^ 2
      = ∑ s : Fin (n + 1), ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), f (v s) * f (v (s + l)) := by
    intro v
    rw [sq, Finset.sum_mul_sum]
    have h : ∀ s : Fin (n + 1), ∑ t, f (v s) * f (v t)
        = f (v s) ^ 2 + ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), f (v s) * f (v (s + l)) := by
      intro s
      rw [← Equiv.sum_comp (Equiv.addLeft s) (fun t => f (v s) * f (v t)),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
      simp [sq]
    simp only [h, Finset.sum_add_distrib]
    ring
  have e2 : ∀ s : Fin (n + 1), ∀ l : Fin (n + 1),
      ∑ v : Fin (n + 1) → α, cw B v * (f (v s) * f (v (s + l)))
        = ∑ v : Fin (n + 1) → α, cw B v * (f (v 0) * f (v l)) := by
    intro s l
    have := sum_cw_shift B (fun w => f (w 0) * f (w l)) s
    simp only [zero_add] at this
    rw [← this]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [add_comm l s]
  have e3 : ∀ s : Fin (n + 1),
      ∑ v : Fin (n + 1) → α, ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
          cw B v * (f (v s) * f (v (s + l)))
        = ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
            ∑ v : Fin (n + 1) → α, cw B v * (f (v 0) * f (v l)) := by
    intro s
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => e2 s l
  simp only [e1]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun s _ => e3 s, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The one-position sums: `∑_v cw(v) ∑_t f(v_t) = (n+1) ∑_v cw(v) f(v_0) = (n+1) ∑_i (B^{n+1})_ii f(i)`. -/
theorem sum_cw_lin [DecidableEq α] (B : Matrix α α ℝ) {n : ℕ} (f : α → ℝ) :
    ∑ v : Fin (n + 1) → α, cw B v * ∑ t, f (v t)
      = ((n : ℝ) + 1) * ∑ i, (B ^ (n + 1)) i i * f i := by
  have e : ∀ t : Fin (n + 1), ∑ v : Fin (n + 1) → α, cw B v * f (v t)
      = ∑ i, (B ^ (n + 1)) i i * f i := by
    intro t
    rw [sum_cw_pos, BiasVariance3.sum_cons]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_apply_pth, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [cw_eq_pth]; simp
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun t _ => e t, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

end Sym

open PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance2

/-- **`eq:bias-trace` of `prop:bias` for every `k = n + 1`, in the form of the paper.** Under the
    hypotheses of `trace_expansion`, with `P̃ = K/N`, `φ¹ = -2ε + bv`, `φ² = 3ε² - 3ε bv + bv² - sv`:
    `|Tr P^k - (Q₀ + Q₁ + Q₂ + Q₃)| ≤ gC(k) k (9/8)^{k-1} (17/8) δ M (1/N) ∑ ε²` with
    `Q₀ = Tr P̃^k`, `Q₁ + Q₂ = k ∑_i (P̃^k)_ii (φ¹_i + φ²_i)` and
    `Q₃ = (k/2) ∑_{l=1}^{k-1} ∑_v cw(v) φ¹(v_0) φ¹(v_l)` (the closed walks `v` with the two
    factors at the positions `0` and `l`; the paper writes the inner sum as
    `∑_{i,j} (P̃^l)_ij (P̃^{k-l})_ji φ¹_i φ¹_j`). -/
theorem trace_expansion_paper {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ) (ρ ε bv sv : Fin N → ℝ)
    {M δ : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hKM : ∀ i j, K i j ≤ M) (hsym : ∀ i j, K i j = K j i)
    (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1)
    (hbv : ∀ i, bv i = 1 / (N : ℝ) * ∑ l, K i l * ε l)
    (hsv : ∀ i, sv i = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    (hδ : δ ≤ 1 / 8) (hεδ : ∀ i, |ε i| ≤ δ) (n : ℕ) :
    |((walkMatrix K ρ) ^ (n + 1)).trace
        - ((Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace
          + ((n : ℝ) + 1) * ∑ i, (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)) i i
              * ((-2 * ε i + bv i) + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))
          + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
              ∑ v : Fin (n + 1) → Fin N, cw (fun i j => K i j / (N : ℝ)) v
                * ((-2 * ε (v 0) + bv (v 0)) * (-2 * ε (v l) + bv (v l))))|
      ≤ gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * (17 / 8)
          * (δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2)) := by
  have h := trace_expansion hN K ρ ε bv sv hK0 hKM hsym hρ hε hbv hsv hδ hεδ n
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

end BiasGeneral

namespace BiasGeneral2

open WalkCount Function
open scoped ENNReal

/-! # A97: `prop:bias` for every `k`, Stage 3, Points 1 and 2

Point 1 (the family of kernels `p_l`, all `l`): this is `WalkCount.RK` (HYPOTHESES: measurable,
nonnegative, bounded, mass one, semigroup, constant diagonal), proved for the periodised Gaussian
kernel on the flat torus in `WalkCount.torusRK` (`q_l(x,y) = heatP d σ l (x - y)`, `m_l = torusM`).

Point 2: closed walks through pairwise different points,
* `cycP_int`: `∫ cycle = m_k` (product measure), `cycle_mean`: the same for sample points;
* `cycP_vertex`, `cycle_vertex`: `E[cycle · f(x_t)] = m_k ∫ f`;
* `torus_chord`, `cycle_chord`: `E[cycle · g(x_0 - x_l)] = ∫ p_l p_{k-l} g` on the torus. -/

section Chains

variable {ι : Type*} {G : Type*}

/-- A chain along the list `v₁, …, v_n` of a tuple as a product. -/
theorem ch_prod (Q : ℕ → G → G → ℝ) (x : ι → G) :
    ∀ (n : ℕ) (v : Fin (n + 1) → ι) (b : ι),
      ch Q x 1 (v 0) (List.ofFn fun i : Fin n => v i.succ) b
        = (∏ i : Fin n, Q 1 (x (v i.castSucc)) (x (v i.succ))) * Q 1 (x (v (Fin.last n))) (x b) := by
  intro n
  induction n with
  | zero => intro v b; simp [ch]
  | succ n ih =>
    intro v b
    have h := ih (fun j => v j.succ) b
    simp only at h
    rw [List.ofFn_succ]
    simp only [ch_cons]
    rw [h, Fin.prod_univ_succ]
    simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
    ring

/-- The weight of the closed walk `y₀ → y₁ → ⋯ → y_n → y₀` (the same product as
    `BiasGeneral.cw`, with the points themselves as vertices). -/
def cycP (B : G → G → ℝ) {n : ℕ} (y : Fin (n + 1) → G) : ℝ := ∏ a : Fin (n + 1), B (y a) (y (a + 1))

/-- The list of the vertices `0, 1, …, n` of the closed walk. -/
def cycL (n : ℕ) : List (Fin (n + 1)) := 0 :: List.ofFn fun i : Fin n => i.succ

theorem cycP_eq (Q : ℕ → G → G → ℝ) {n : ℕ} (y : Fin (n + 1) → G) :
    cycP (Q 1) y = cyc Q y (cycL n) := by
  rw [cycL, cyc_cons]
  have h := ch_prod Q y n id 0
  simp only [id] at h
  rw [h, cycP, Fin.prod_univ_castSucc, Fin.last_add_one]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [Fin.coeSucc_eq_succ]

theorem cycL_nodup (n : ℕ) : (cycL n).Nodup := by
  rw [cycL, List.nodup_cons, List.nodup_ofFn]
  refine ⟨?_, Fin.succ_injective _⟩
  rw [List.mem_ofFn]
  rintro ⟨i, hi⟩
  exact Fin.succ_ne_zero i hi

theorem mem_cycL {n : ℕ} (t : Fin (n + 1)) : t ∈ cycL n := by
  rw [cycL]
  refine Fin.cases ?_ (fun i => ?_) t
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem cycL_length (n : ℕ) : (cycL n).length = n + 1 := by simp [cycL]

end Chains

section ProductMeasure

variable {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
  {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

theorem cycP_meas (S : RK ν q M m) (n : ℕ) :
    Measurable fun y : Fin (n + 1) → G => cycP (q 1) y :=
  Finset.measurable_prod _ fun a _ =>
    meas2 S.meas 1 (measurable_pi_apply a) (measurable_pi_apply (a + 1))

theorem cycP_nonneg (S : RK ν q M m) {n : ℕ} (y : Fin (n + 1) → G) : 0 ≤ cycP (q 1) y :=
  Finset.prod_nonneg fun a _ => S.nonneg 1 _ _

theorem cycP_le (S : RK ν q M m) {n : ℕ} (y : Fin (n + 1) → G) : cycP (q 1) y ≤ M ^ (n + 1) := by
  rw [cycP]
  calc ∏ a : Fin (n + 1), q 1 (y a) (y (a + 1)) ≤ ∏ _a : Fin (n + 1), M :=
        Finset.prod_le_prod (fun a _ => S.nonneg 1 _ _) (fun a _ => S.bound _ _)
    _ = M ^ (n + 1) := by simp

/-- **A closed walk through `k = n + 1` different points has expectation `m_k`.** -/
theorem cycP_int (S : RK ν q M m) (n : ℕ) :
    ∫ y, cycP (q 1) y ∂Measure.pi (fun _ : Fin (n + 1) => ν) = m (n + 1) := by
  simp only [cycP_eq q]
  have h := S.int_nodup (ι := Fin (n + 1)) 0 (List.ofFn fun i : Fin n => i.succ) (cycL_nodup n)
  rw [List.length_ofFn] at h
  exact h

/-- **A closed walk next to a function of one of its points:** `∫ cycle · f(y_t) = m_k ∫ f`
    for measurable `0 ≤ f ≤ C`. -/
theorem cycP_vertex (S : RK ν q M m) (n : ℕ) (t : Fin (n + 1)) (f : G → ℝ) (hf : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) {C : ℝ} (hfC : ∀ z, f z ≤ C) :
    ∫ y, cycP (q 1) y * f (y t) ∂Measure.pi (fun _ : Fin (n + 1) => ν)
      = m (n + 1) * ∫ z, f z ∂ν := by
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hfC z)
  refine integral_eq_of_lintegral_eq (fun y => mul_nonneg (cycP_nonneg S y) (hf0 _))
    ((cycP_meas S n).mul (hf.comp (measurable_pi_apply t)))
    (mul_nonneg (S.m_nonneg _ (by omega)) (integral_nonneg hf0)) ?_
  have e : ∀ y : Fin (n + 1) → G, ENNReal.ofReal (cycP (q 1) y * f (y t))
      = cyc (QE q) y (cycL n) * ENNReal.ofReal (f (y t)) := fun y => by
    rw [ENNReal.ofReal_mul (cycP_nonneg S y), cycP_eq q, ofReal_cyc S.nonneg]
  simp_rw [e]
  rw [cycL]
  simp only [cyc_cons]
  have hh : Measurable fun y : Fin (n + 1) → G => ENNReal.ofReal (f (y t)) :=
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_pi_apply t))
  rw [cyc_integral_spect ν (QE q) S.measE S.semi (fun i => ENNReal.ofReal (m i)) S.diagE hh 0
    (List.ofFn fun i : Fin n => i.succ) (cycL_nodup n) t (mem_cycL t)
    (fun c _ hct x z => by rw [update_of_ne (Ne.symm hct)])]
  rw [List.length_ofFn]
  have h1 : ∫⁻ y, ENNReal.ofReal (f (y t)) ∂Measure.pi (fun _ : Fin (n + 1) => ν)
      = ∫⁻ z, ENNReal.ofReal (f z) ∂ν :=
    (measurePreserving_eval (μ := fun _ : Fin (n + 1) => ν) t).lintegral_comp
      (ENNReal.measurable_ofReal.comp hf)
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
    ← ENNReal.ofReal_mul (S.m_nonneg _ (by omega))]

end ProductMeasure

section Torus

open PiBound CTG.Reals.TorusReduction

/-- **A closed walk with a chord function on the flat torus.** For `1 ≤ l ≤ n` and measurable
    `0 ≤ g ≤ C`: `∫ cycle(y) g(y_0 - y_l) dy = ∫ p_l p_{k-l} g`, `k = n + 1`, `p_s = heatP d σ s`. -/
theorem torus_chord {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) (l : Fin (n + 1)) (hl : l ≠ 0)
    (g : FlatTorus d → ℝ) (hg : Measurable g) (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hgC : ∀ u, g u ≤ C) :
    ∫ y, cycP (fun x z => heatP d σ 1 (x - z)) y * g (y 0 - y l)
        ∂Measure.pi (fun _ : Fin (n + 1) => flatTorusMeasure d)
      = ∫ u, heatP d σ l.val u * heatP d σ (n + 1 - l.val) u * g u ∂flatTorusMeasure d := by
  classical
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have S := torusRK hσ d
  set ν := flatTorusMeasure d with hν
  set q : ℕ → FlatTorus d → FlatTorus d → ℝ := fun i x z => heatP d σ i (x - z) with hq
  set Q := QE q with hQ
  -- the decomposition of the list of vertices at `l`
  have hlmem : l ∈ List.ofFn fun i : Fin n => (i.succ : Fin (n + 1)) := by
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hl
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem hlmem
  have hnd := cycL_nodup n
  rw [cycL, hL] at hnd
  have hlen1 : L1.length + 1 = l.val := by
    have h1 : (L1 ++ l :: L2)[L1.length]? = some l := by simp
    rw [← hL, List.getElem?_ofFn] at h1
    have hlt : L1.length < n := by
      by_contra hc
      simp [hc] at h1
    simp only [hlt, dite_true, Option.some.injEq] at h1
    have := congrArg Fin.val h1
    simp at this
    omega
  have hlen : L1.length + L2.length + 1 = n := by
    have := congrArg List.length hL
    simp at this; omega
  have haL : (0 : Fin (n + 1)) ∉ L1 ++ l :: L2 := (List.nodup_cons.mp hnd).1
  have hLnd : (L1 ++ l :: L2).Nodup := (List.nodup_cons.mp hnd).2
  obtain ⟨hL1, hvL2nd, hdisj⟩ := List.nodup_append.mp hLnd
  have hvL2 : l ∉ L2 := (List.nodup_cons.mp hvL2nd).1
  have hL2 : L2.Nodup := (List.nodup_cons.mp hvL2nd).2
  have hvL1 : l ∉ L1 := fun hm => hdisj l hm l List.mem_cons_self rfl
  have haL1 : (0 : Fin (n + 1)) ∉ L1 := fun hm => haL (List.mem_append_left _ hm)
  have haL2 : (0 : Fin (n + 1)) ∉ L2 :=
    fun hm => haL (List.mem_append_right _ (List.mem_cons_of_mem _ hm))
  have hL21 : ∀ c ∈ L2, c ∉ L1 :=
    fun c hc hm => hdisj c hm c (List.mem_cons_of_mem _ hc) rfl
  have hneL1 : ∀ c ∈ L1, c ≠ l := fun c hc e => hvL1 (by rw [← e]; exact hc)
  have hneL2 : ∀ c ∈ L2, c ≠ l := fun c hc e => hvL2 (by rw [← e]; exact hc)
  have hneaL1 : ∀ c ∈ L1, c ≠ 0 := fun c hc e => haL1 (by rw [← e]; exact hc)
  have hneaL2 : ∀ c ∈ L2, c ≠ 0 := fun c hc e => haL2 (by rw [← e]; exact hc)
  -- the integrand in `ℝ≥0∞`
  obtain ⟨H, hH⟩ : ∃ H : FlatTorus d → ℝ≥0∞, H = fun u => ENNReal.ofReal (g u) := ⟨_, rfl⟩
  have hHm : Measurable H := by rw [hH]; exact ENNReal.measurable_ofReal.comp hg
  have hgi : ∀ i, 1 ≤ i → ∀ u, 0 ≤ heatP d σ i u * heatP d σ (n + 1 - i) u * g u := fun i _ u =>
    mul_nonneg (mul_nonneg (heatP_nonneg hσ d _ _) (heatP_nonneg hσ d _ _)) (hg0 u)
  have hrhs0 : 0 ≤ ∫ u, heatP d σ l.val u * heatP d σ (n + 1 - l.val) u * g u ∂ν :=
    integral_nonneg (hgi l.val (by omega))
  have hcm := cycP_meas S n
  have hm2 : Measurable (heatP d σ (n + 1 - l.val)) := by
    by_cases h0 : n + 1 - l.val = 0
    · have : heatP d σ (n + 1 - l.val) = fun _ => 0 := by funext u; simp [heatP, h0]
      rw [this]; exact measurable_const
    · exact (heatP_cont hσ d (by omega)).measurable
  have hmR : Measurable fun u => heatP d σ l.val u * heatP d σ (n + 1 - l.val) u * g u :=
    ((heatP_cont hσ d (by omega)).measurable.mul hm2).mul hg
  refine integral_eq_of_lintegral_eq (fun y => mul_nonneg (cycP_nonneg S y) (hg0 _))
    (hcm.mul (hg.comp ((measurable_pi_apply 0).sub (measurable_pi_apply l)))) hrhs0 ?_
  have e0 : ∀ y : Fin (n + 1) → FlatTorus d, ENNReal.ofReal (cycP (q 1) y * g (y 0 - y l))
      = ch Q y 1 l L2 0 * (ch Q y 1 0 L1 l * H (y 0 - y l)) := fun y => by
    rw [ENNReal.ofReal_mul (cycP_nonneg S y), cycP_eq q, ofReal_cyc S.nonneg, cycL, hL, cyc_cons,
      ch_append, hH]
    ring
  simp_rw [e0]
  -- step 1: integrate out `L2`
  have hh1 : Measurable fun y : Fin (n + 1) → FlatTorus d => ch Q y 1 0 L1 l * H (y 0 - y l) :=
    (ch_meas S.measE 1 0 L1 l).mul (hHm.comp ((measurable_pi_apply 0).sub (measurable_pi_apply l)))
  rw [ch_integral ν Q S.measE S.semi hh1 L2 hL2 1 le_rfl l 0 hvL2 haL2
    (fun c hc x z => by
      rw [ch_update Q x c z 1 0 L1 l (hneaL2 c hc) (hneL2 c hc) (hL21 c hc),
        update_of_ne (hneaL2 c hc).symm, update_of_ne (hneL2 c hc).symm])]
  -- step 2: integrate out `L1`
  have s2 : ∀ y : Fin (n + 1) → FlatTorus d,
      Q (1 + L2.length) (y l) (y 0) * (ch Q y 1 0 L1 l * H (y 0 - y l))
        = ch Q y 1 0 L1 l * (Q (1 + L2.length) (y l) (y 0) * H (y 0 - y l)) := fun y => by ring
  simp_rw [s2]
  have hh2 : Measurable fun y : Fin (n + 1) → FlatTorus d =>
      Q (1 + L2.length) (y l) (y 0) * H (y 0 - y l) :=
    (meas2 S.measE _ (measurable_pi_apply l) (measurable_pi_apply 0)).mul
      (hHm.comp ((measurable_pi_apply 0).sub (measurable_pi_apply l)))
  rw [ch_integral ν Q S.measE S.semi hh2 L1 hL1 1 le_rfl 0 l haL1 hvL1
    (fun c hc x z => by
      rw [update_of_ne (hneL1 c hc).symm, update_of_ne (hneaL1 c hc).symm])]
  -- step 3: a function of `y_0 - y_l`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FlatTorus d → ℝ≥0∞, Ψ = fun u =>
      ENNReal.ofReal (heatP d σ l.val u * heatP d σ (n + 1 - l.val) u * g u) := ⟨_, rfl⟩
  have e3 : ∀ y : Fin (n + 1) → FlatTorus d,
      Q (1 + L1.length) (y 0) (y l) * (Q (1 + L2.length) (y l) (y 0) * H (y 0 - y l))
        = Ψ (y 0 - y l) := fun y => by
    have i1 : 1 + L1.length = l.val := by omega
    have i2 : 1 + L2.length = n + 1 - l.val := by omega
    rw [hQ, hH, hΨ, i1, i2]
    simp only [QE, hq]
    rw [heatP_flip d σ (n + 1 - l.val) (y l) (y 0),
      ← ENNReal.ofReal_mul (heatP_nonneg hσ d _ _),
      ← ENNReal.ofReal_mul (heatP_nonneg hσ d _ _), mul_assoc]
  simp_rw [e3]
  have hΨm : Measurable Ψ := by rw [hΨ]; exact ENNReal.measurable_ofReal.comp hmR
  have hF : Measurable fun y : Fin (n + 1) → FlatTorus d => Ψ (y 0 - y l) :=
    hΨm.comp ((measurable_pi_apply 0).sub (measurable_pi_apply l))
  rw [lintegral_pi_coord ν l hF]
  have hl0 : (0 : Fin (n + 1)) ≠ l := Ne.symm hl
  have inner : ∀ y : Fin (n + 1) → FlatTorus d,
      ∫⁻ z, Ψ (update y l z 0 - update y l z l) ∂ν = ∫⁻ u, Ψ u ∂ν := fun y => by
    simp only [update_self, update_of_ne hl0]
    exact lintegral_sub_left_eq_self Ψ (y 0)
  simp_rw [inner]
  rw [lintegral_const, measure_univ, mul_one, hΨ]
  have hint : Integrable (fun u => heatP d σ l.val u * heatP d σ (n + 1 - l.val) u * g u) ν := by
    refine Integrable.of_bound ?_ (torusM d σ 1 * torusM d σ 1 * C)
      (Filter.Eventually.of_forall fun u => ?_)
    · exact hmR.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hgi l.val (by omega) u)]
      have a1 : heatP d σ l.val u ≤ torusM d σ 1 :=
        (heatP_le hσ d (by omega) u).trans (torusM_anti hσ d le_rfl (by omega))
      have a2 : heatP d σ (n + 1 - l.val) u ≤ torusM d σ 1 := by
        by_cases h0 : n + 1 - l.val = 0
        · simp [heatP, h0]; exact (torusM_pos hσ d le_rfl).le
        · exact (heatP_le hσ d (by omega) u).trans (torusM_anti hσ d le_rfl (by omega))
      have hC0 : 0 ≤ C := (hg0 u).trans (hgC u)
      have hM0 := (torusM_pos hσ d (le_refl 1)).le
      exact mul_le_mul (mul_le_mul a1 a2 (heatP_nonneg hσ d _ _) hM0) (hgC u) (hg0 u)
              (mul_nonneg hM0 hM0)
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (hgi l.val (by omega)))).symm

end Torus

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G}

/-- For pairwise different indices the sample points are independent with law `ν`. -/
theorem tuple_map (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {n : ℕ} (ι : Fin n → ℕ)
    (hι : Injective ι) :
    μ.map (fun ω (a : Fin n) => X (ι a) ω) = Measure.pi (fun _ : Fin n => ν) := by
  have hi : ProbabilityTheory.iIndepFun (fun a : Fin n => X (ι a)) μ := h_indep.precomp hι
  have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun a : Fin n => (hX (ι a)).aemeasurable)).mp hi
  simp_rw [hlaw] at h
  exact h

theorem tuple_integral (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {n : ℕ} (ι : Fin n → ℕ)
    (hι : Injective ι) (F : (Fin n → G) → ℝ) (hF : Measurable F) :
    ∫ ω, F (fun a => X (ι a) ω) ∂μ = ∫ y, F y ∂Measure.pi (fun _ : Fin n => ν) := by
  rw [← tuple_map X h_indep hX hlaw ι hι,
    integral_map (measurable_pi_lambda _ fun a => hX (ι a)).aemeasurable hF.aestronglyMeasurable]

variable [IsProbabilityMeasure ν] {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

/-- **`E[cycle] = m_k` for pairwise different sample points.** -/
theorem cycle_mean (S : RK ν q M m) (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {n : ℕ} (ι : Fin (n + 1) → ℕ)
    (hι : Injective ι) :
    ∫ ω, cycP (q 1) (fun a => X (ι a) ω) ∂μ = m (n + 1) := by
  rw [tuple_integral X h_indep hX hlaw ι hι _ (cycP_meas S n), cycP_int S n]

/-- **`E[cycle · f(x_t)] = m_k ∫ f` for pairwise different sample points.** -/
theorem cycle_vertex (S : RK ν q M m) (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {n : ℕ} (ι : Fin (n + 1) → ℕ)
    (hι : Injective ι) (t : Fin (n + 1)) (f : G → ℝ) (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    {C : ℝ} (hfC : ∀ z, f z ≤ C) :
    ∫ ω, cycP (q 1) (fun a => X (ι a) ω) * f (X (ι t) ω) ∂μ = m (n + 1) * ∫ z, f z ∂ν := by
  rw [tuple_integral X h_indep hX hlaw ι hι (fun y => cycP (q 1) y * f (y t))
    ((cycP_meas S n).mul (hf.comp (measurable_pi_apply t))), cycP_vertex S n t f hf hf0 hfC]

end Sample

/-- **`E[cycle · g(x_0 - x_l)] = ∫ p_l p_{k-l} g` for pairwise different sample points** on the
    flat torus (`k = n + 1`, `1 ≤ l ≤ n`, measurable `0 ≤ g ≤ C`). -/
theorem cycle_chord {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {n : ℕ} (ι : Fin (n + 1) → ℕ)
    (hι : Injective ι) (l : Fin (n + 1)) (hl : l ≠ 0) (g : FlatTorus d → ℝ) (hg : Measurable g)
    (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hgC : ∀ u, g u ≤ C) :
    ∫ ω, cycP (fun x z => heatP d σ 1 (x - z)) (fun a => X (ι a) ω) * g (X (ι 0) ω - X (ι l) ω) ∂μ
      = ∫ u, heatP d σ l.val u * heatP d σ (n + 1 - l.val) u * g u ∂flatTorusMeasure d := by
  have S := torusRK hσ d
  rw [tuple_integral X h_indep hX hlaw ι hι
    (fun y => cycP (fun x z => heatP d σ 1 (x - z)) y * g (y 0 - y l))
    ((cycP_meas S n).mul (hg.comp ((measurable_pi_apply 0).sub (measurable_pi_apply l)))),
    torus_chord hσ d n l hl g hg hg0 hgC]

end BiasGeneral2

namespace BiasGeneral3

open WalkCount Function BiasGeneral2
open scoped ENNReal

/-! # A98: `prop:bias` for every `k`, Stage 3, Point 3

* (3a) `cycle_pair`: a closed walk whose positions `i < j` carry the same sample point and
  which is otherwise through pairwise different points has expectation `m_{j-i} m_{k-(j-i)}`
  (two cycles with one common point). -/

section Pair

variable {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
  {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

theorem cycP_comp_eq {ι : Type*} (Q : ℕ → G → G → ℝ) (x : ι → G) {n : ℕ}
    (v : Fin (n + 1) → ι) :
    cycP (Q 1) (x ∘ v) = cyc Q x (v 0 :: List.ofFn fun i : Fin n => v i.succ) := by
  rw [cyc_cons]
  have h := ch_prod Q x n v (v 0)
  rw [h, cycP, Fin.prod_univ_castSucc, Fin.last_add_one]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by simp only [Function.comp]; rw [Fin.coeSucc_eq_succ]

theorem cycP_rot (B : G → G → ℝ) {n : ℕ} (y : Fin (n + 1) → G) (s : Fin (n + 1)) :
    cycP B (fun a => y (a + s)) = cycP B y := by
  rw [cycP, cycP]
  exact Fintype.prod_equiv (Equiv.addRight s) _ _ (fun a => by
    simp only [Equiv.coe_addRight]; rw [add_right_comm])

/-- The case `i = 0`, `j = l` on the product space of `N` points. -/
theorem pi_pair0 (S : RK ν q M m) {N n : ℕ} (v : Fin (n + 1) → Fin N) (j : Fin (n + 1))
    (hj : j ≠ 0) (hvj : v j = v 0)
    (hv : ∀ s t, s ≠ t → v s = v t → (s = 0 ∧ t = j) ∨ (s = j ∧ t = 0)) :
    ∫ x, cycP (q 1) (x ∘ v) ∂Measure.pi (fun _ : Fin N => ν)
      = m j.val * m (n + 1 - j.val) := by
  have hl1 : 1 ≤ j.val := by
    rcases Nat.eq_zero_or_pos j.val with h | h
    · exact absurd (Fin.ext h) hj
    · exact h
  have hln : j.val ≤ n := by have := j.isLt; omega
  obtain ⟨L1, hL1⟩ : ∃ L1 : List (Fin N),
      L1 = List.ofFn (fun s : Fin (j.val - 1) => v ⟨s.val + 1, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L2 : List (Fin N),
      L2 = List.ofFn (fun s : Fin (n - j.val) => v ⟨j.val + 1 + s.val, by omega⟩) := ⟨_, rfl⟩
  have hsplit : (List.ofFn fun i : Fin n => v i.succ) = L1 ++ v j :: L2 := by
    apply List.ext_getElem
    · rw [hL1, hL2]; simp only [List.length_ofFn, List.length_append, List.length_cons]; omega
    · intro t h1 h2
      rw [List.getElem_ofFn, List.getElem_append]
      have hlen1 : L1.length = j.val - 1 := by rw [hL1, List.length_ofFn]
      split_ifs with hlt
      · simp only [hL1, List.getElem_ofFn]
        congr 1
        all_goals (ext; simp)
      · rw [List.getElem_cons]
        split_ifs with h0
        · congr 1
          all_goals (ext; simp <;> omega)
        · simp only [hL2, List.getElem_ofFn]
          congr 1
          all_goals (ext; simp <;> omega)
  have hcyc : ∀ x : Fin N → G, cycP (q 1) (x ∘ v)
      = cyc q x (v 0 :: L1) * cyc q x (v 0 :: L2) := by
    intro x
    rw [cycP_comp_eq, hsplit, hvj, cyc_cons, ch_append, cyc_cons, cyc_cons]
  -- membership in the two lists
  have m1 : ∀ c, c ∈ L1 → ∃ s : Fin (n + 1), s ≠ 0 ∧ s ≠ j ∧ s.val < j.val ∧ v s = c := by
    intro c hc
    rw [hL1, List.mem_ofFn] at hc
    obtain ⟨s, rfl⟩ := hc
    refine ⟨⟨s.val + 1, by omega⟩, ?_, ?_, ?_, rfl⟩
    · intro h; have := congrArg Fin.val h; simp at this <;> omega
    · intro h; have := congrArg Fin.val h; simp at this <;> omega
    · simp; omega
  have m2 : ∀ c, c ∈ L2 → ∃ s : Fin (n + 1), s ≠ 0 ∧ s ≠ j ∧ j.val < s.val ∧ v s = c := by
    intro c hc
    rw [hL2, List.mem_ofFn] at hc
    obtain ⟨s, rfl⟩ := hc
    refine ⟨⟨j.val + 1 + s.val, by omega⟩, ?_, ?_, ?_, rfl⟩
    · intro h; have := congrArg Fin.val h; simp at this <;> omega
    · intro h; have := congrArg Fin.val h; simp at this <;> omega
    · simp; omega
  have hne : ∀ s t : Fin (n + 1), s ≠ t → s ≠ 0 → s ≠ j → v s ≠ v t := by
    intro s t hst hs0 hsj e
    rcases hv s t hst e with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hs0 h1
    · exact hsj h1
  have hnd1 : (v 0 :: L1).Nodup := by
    rw [List.nodup_cons]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨s, hs0, hsj, _, hs⟩ := m1 _ h
      exact hne s 0 hs0 hs0 hsj hs
    · rw [hL1, List.nodup_ofFn]
      intro a b hab
      have := hne ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩
      by_contra hne'
      refine this ?_ ?_ ?_ hab
      · intro h; apply hne'; ext; have := congrArg Fin.val h; simp at this <;> omega
      · intro h; have := congrArg Fin.val h; simp at this <;> omega
      · intro h; have := congrArg Fin.val h; simp at this <;> omega
  have hnd2 : (v 0 :: L2).Nodup := by
    rw [List.nodup_cons]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨s, hs0, hsj, _, hs⟩ := m2 _ h
      exact hne s 0 hs0 hs0 hsj hs
    · rw [hL2, List.nodup_ofFn]
      intro a b hab
      have := hne ⟨j.val + 1 + a.val, by omega⟩ ⟨j.val + 1 + b.val, by omega⟩
      by_contra hne'
      refine this ?_ ?_ ?_ hab
      · intro h; apply hne'; ext; have := congrArg Fin.val h; simp at this <;> omega
      · intro h; have := congrArg Fin.val h; simp at this <;> omega
      · intro h; have := congrArg Fin.val h; simp at this <;> omega
  have hcommon : ∀ c ∈ v 0 :: L1, c ∈ v 0 :: L2 → c = v 0 := by
    intro c hc1 hc2
    rcases List.mem_cons.mp hc1 with h | h
    · exact h
    rcases List.mem_cons.mp hc2 with h' | h'
    · exact h'
    obtain ⟨s, hs0, hsj, hsl, rfl⟩ := m1 c h
    obtain ⟨t, -, -, htl, ht⟩ := m2 _ h'
    exact absurd ht.symm (hne s t (fun e => by rw [e] at hsl; omega) hs0 hsj)
  have h := S.pair_eq (ι := Fin N) (v 0) L1 hnd1 (v 0) L2 hnd2 (v 0) List.mem_cons_self hcommon
  have e1 : L1.length + 1 = j.val := by rw [hL1, List.length_ofFn]; omega
  have e2 : L2.length + 1 = n + 1 - j.val := by rw [hL2, List.length_ofFn]; omega
  rw [e1, e2] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall hcyc)

/-- **(3a) on the product space:** positions `i < j` carry the same point, all other positions
    pairwise different points: `∫ cycle = m_{j-i} m_{k-(j-i)}`, `k = n + 1`. -/
theorem pi_pair (S : RK ν q M m) {N n : ℕ} (v : Fin (n + 1) → Fin N) (i j : Fin (n + 1))
    (hij : i < j) (hvj : v j = v i)
    (hv : ∀ s t, s ≠ t → v s = v t → (s = i ∧ t = j) ∨ (s = j ∧ t = i)) :
    ∫ x, cycP (q 1) (x ∘ v) ∂Measure.pi (fun _ : Fin N => ν)
      = m (j.val - i.val) * m (n + 1 - (j.val - i.val)) := by
  have hrot : ∀ x : Fin N → G, cycP (q 1) (x ∘ v) = cycP (q 1) (x ∘ fun a => v (a + i)) := by
    intro x
    exact (cycP_rot (q 1) (x ∘ v) i).symm
  have hval : (j - i).val = j.val - i.val := by
    rw [Fin.sub_val_of_le (le_of_lt hij)]
  have hji : j - i ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; exact absurd h (ne_of_gt hij)
  have h := pi_pair0 S (fun a => v (a + i)) (j - i) hji
    (by simp only [zero_add, sub_add_cancel]; exact hvj)
    (by
      intro s t hst e
      simp only at e
      have hst' : s + i ≠ t + i := fun h => hst (add_right_cancel h)
      rcases hv _ _ hst' e with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        constructor
        · exact add_eq_right.mp h1
        · exact eq_sub_of_add_eq h2
      · right
        constructor
        · exact eq_sub_of_add_eq h1
        · exact add_eq_right.mp h2)
  rw [hval] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall hrot)

end Pair

section SamplePair

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
  {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

/-- The law of the first `N` sample points is the product measure. -/
theorem first_integral (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (N : ℕ)
    (F : (Fin N → G) → ℝ) (hF : Measurable F) :
    ∫ ω, F (fun a => X a ω) ∂μ = ∫ x, F x ∂Measure.pi (fun _ : Fin N => ν) :=
  tuple_integral X h_indep hX hlaw (fun a : Fin N => (a : ℕ)) Fin.val_injective F hF

/-- **(3a) for the sample:** `E[cycle] = m_{j-i} m_{k-(j-i)}` for a closed walk through the
    sample points `X_{v_0}, …, X_{v_n}` with `v_i = v_j` (`i < j`) and otherwise pairwise
    different indices. -/
theorem cycle_pair (S : RK ν q M m) (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {N n : ℕ}
    (v : Fin (n + 1) → Fin N) (i j : Fin (n + 1)) (hij : i < j) (hvj : v j = v i)
    (hv : ∀ s t, s ≠ t → v s = v t → (s = i ∧ t = j) ∨ (s = j ∧ t = i)) :
    ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ = m (j.val - i.val) * m (n + 1 - (j.val - i.val)) := by
  have hF : Measurable fun x : Fin N → G => cycP (q 1) (x ∘ v) :=
    (cycP_meas S n).comp (measurable_pi_lambda _ fun a => measurable_pi_apply (v a))
  rw [← pi_pair S v i j hij hvj hv]
  exact first_integral X h_indep hX hlaw N _ hF

end SamplePair

/-! ## (3b), counting: index tuples with prescribed coincidences -/

section Count

variable {T α : Type*} [Fintype T] [DecidableEq T] [Fintype α] [DecidableEq α]

theorem card_ne (s : T) : Fintype.card {x // x ≠ s} = Fintype.card T - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem split_eval (s : T) (c : α) (w : {x // x ≠ s} → α) :
    (Equiv.funSplitAt s α).symm (c, w) s = c := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem split_eval' (s t : T) (ht : t ≠ s) (c : α) (w : {x // x ≠ s} → α) :
    (Equiv.funSplitAt s α).symm (c, w) t = w ⟨t, ht⟩ := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt, ht]

/-- `#{w : w_s = w_t} = |α|^{|T| - 1}` for `s ≠ t`. -/
theorem count_one (s t : T) (hst : s ≠ t) :
    ∑ w : T → α, (if w s = w t then (1 : ℝ) else 0)
      = (Fintype.card α : ℝ) ^ (Fintype.card T - 1) := by
  have ht : t ≠ s := hst.symm
  rw [← (Equiv.funSplitAt s α).symm.sum_comp, Fintype.sum_prod_type]
  simp only [split_eval, split_eval' s t ht]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, card_ne, nsmul_eq_mul, mul_one, Nat.cast_pow]

/-- `#{w : w_j = w_i, w_s = w_t} = |α|^{|T| - 2}` if `j ∉ {i, s, t}` and `s ≠ t`. -/
theorem count_two (j i s t : T) (hji : j ≠ i) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t) :
    ∑ w : T → α, (if w j = w i then (1 : ℝ) else 0) * (if w s = w t then (1 : ℝ) else 0)
      = (Fintype.card α : ℝ) ^ (Fintype.card T - 2) := by
  rw [← (Equiv.funSplitAt j α).symm.sum_comp, Fintype.sum_prod_type]
  simp only [split_eval, split_eval' j i hji.symm, split_eval' j s hjs.symm,
    split_eval' j t hjt.symm]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
  have hst' : (⟨s, hjs.symm⟩ : {x // x ≠ j}) ≠ ⟨t, hjt.symm⟩ := fun h => hst (congrArg Subtype.val h)
  have := count_one (α := α) (⟨s, hjs.symm⟩ : {x // x ≠ j}) ⟨t, hjt.symm⟩ hst'
  rw [this, card_ne]
  congr 1

end Count

open WalkCount Function BiasGeneral2

/-! ## (3b): `E ∑_v cycle(v)` up to `O(N^{k-2})` -/

section Coincidences

/-- The ordered pairs of positions `s < t`. -/
def Prs (k : ℕ) : Finset (Fin k × Fin k) := Finset.univ.filter fun p => p.1 < p.2

/-- The indicator that the positions of `p` carry the same index. -/
def ind {N k : ℕ} (v : Fin k → Fin N) (p : Fin k × Fin k) : ℝ := if v p.1 = v p.2 then 1 else 0

/-- Only the positions of `p` coincide. -/
def onlyP {N k : ℕ} (v : Fin k → Fin N) (p : Fin k × Fin k) : Prop :=
  ∀ s t, s ≠ t → v s = v t → (s = p.1 ∧ t = p.2) ∨ (s = p.2 ∧ t = p.1)

variable {N k : ℕ}

theorem ind_nonneg (v : Fin k → Fin N) (p : Fin k × Fin k) : 0 ≤ ind v p := by
  unfold ind; split_ifs <;> norm_num

theorem ind_sq (v : Fin k → Fin N) (p : Fin k × Fin k) : ind v p * ind v p = ind v p := by
  unfold ind; split_ifs <;> norm_num

theorem mem_Prs {p : Fin k × Fin k} : p ∈ Prs k ↔ p.1 < p.2 := by simp [Prs]

theorem exists_pair (v : Fin k → Fin N) (s t : Fin k) (hst : s ≠ t) (h : v s = v t) :
    ∃ p ∈ Prs k, ind v p = 1 ∧ ((p.1 = s ∧ p.2 = t) ∨ (p.1 = t ∧ p.2 = s)) := by
  rcases lt_or_gt_of_ne hst with h1 | h1
  · exact ⟨(s, t), mem_Prs.mpr h1, by simp [ind, h], Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨(t, s), mem_Prs.mpr h1, by simp [ind, h.symm], Or.inr ⟨rfl, rfl⟩⟩

theorem ind_inj (v : Fin k → Fin N) (hv : Injective v) (p : Fin k × Fin k) (hp : p ∈ Prs k) :
    ind v p = 0 := by
  have hne : p.1 ≠ p.2 := ne_of_lt (mem_Prs.mp hp)
  have hne' : v p.1 ≠ v p.2 := fun h => hne (hv h)
  simp [ind, hne']

open Classical in
/-- The excess `R(v) = #{coinciding pairs} - 1[v not injective]`. -/
noncomputable def Rx (v : Fin k → Fin N) : ℝ :=
  (∑ p ∈ Prs k, ind v p) - (if Injective v then 0 else 1)

/-- `D(v) = #{ordered pairs of different coinciding pairs}`. -/
def Dx (v : Fin k → Fin N) : ℝ := ∑ p ∈ Prs k, ∑ p' ∈ (Prs k).erase p, ind v p * ind v p'

theorem Dx_eq (v : Fin k → Fin N) :
    Dx v = (∑ p ∈ Prs k, ind v p) ^ 2 - ∑ p ∈ Prs k, ind v p := by
  have e : ∀ p ∈ Prs k, ∑ p' ∈ (Prs k).erase p, ind v p * ind v p'
      = ind v p * (∑ p' ∈ Prs k, ind v p') - ind v p := by
    intro p hp
    rw [← Finset.mul_sum, ← Finset.add_sum_erase _ _ hp, mul_add, ind_sq]
    ring
  rw [Dx, Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]

theorem Dx_nonneg (v : Fin k → Fin N) : 0 ≤ Dx v :=
  Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun p' _ =>
    mul_nonneg (ind_nonneg v p) (ind_nonneg v p')

theorem Rx_bounds (v : Fin k → Fin N) :
    0 ≤ Rx v ∧ Rx v ≤ Dx v ∧ (1 - ∑ p ∈ Prs k, ind v p + Rx v = if Injective v then 1 else 0) := by
  classical
  by_cases hv : Injective v
  · have h0 : ∑ p ∈ Prs k, ind v p = 0 :=
      Finset.sum_eq_zero fun p hp => ind_inj v hv p hp
    have hR : Rx v = 0 := by simp [Rx, h0, hv]
    refine ⟨hR.ge, by rw [hR]; exact Dx_nonneg v, by simp [hR, h0, hv]⟩
  · obtain ⟨s, t, hst, hne⟩ : ∃ s t, v s = v t ∧ s ≠ t := by
      by_contra hc
      push_neg at hc
      exact hv fun s t h => hc s t h
    obtain ⟨p, hp, hp1, -⟩ := exists_pair v s t hne hst
    have hc1 : 1 ≤ ∑ p ∈ Prs k, ind v p :=
      hp1 ▸ Finset.single_le_sum (fun p _ => ind_nonneg v p) hp
    have hR : Rx v = (∑ p ∈ Prs k, ind v p) - 1 := by simp [Rx, hv]
    rw [hR, Dx_eq]
    refine ⟨by linarith, by nlinarith, by simp [hv]⟩

open Classical in
theorem excess_only (v : Fin k → Fin N) (p : Fin k × Fin k) (hp : p ∈ Prs k) :
    ind v p * (1 - (if onlyP v p then 1 else 0)) ≤ ∑ p' ∈ (Prs k).erase p, ind v p * ind v p' := by
  classical
  have hsum0 : 0 ≤ ∑ p' ∈ (Prs k).erase p, ind v p * ind v p' :=
    Finset.sum_nonneg fun p' _ => mul_nonneg (ind_nonneg v p) (ind_nonneg v p')
  by_cases ho : onlyP v p
  · simp [ho, hsum0]
  · by_cases hvp : v p.1 = v p.2
    · have ho' := ho
      simp only [onlyP, not_forall] at ho
      obtain ⟨s, t, hst, hvst, hnot⟩ := ho
      obtain ⟨p', hp', hp'1, hp's⟩ := exists_pair v s t hst hvst
      have hpp : p' ≠ p := by
        intro e
        rw [e] at hp's
        rcases hp's with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hnot (Or.inl ⟨h1.symm, h2.symm⟩)
        · exact hnot (Or.inr ⟨h2.symm, h1.symm⟩)
      have hm : p' ∈ (Prs k).erase p := Finset.mem_erase.mpr ⟨hpp, hp'⟩
      have h1 := Finset.single_le_sum (f := fun p' => ind v p * ind v p')
        (fun p' _ => mul_nonneg (ind_nonneg v p) (ind_nonneg v p')) hm
      have hi : ind v p = 1 := by simp [ind, hvp]
      rw [if_neg ho', hi]
      simp only [hi, hp'1] at h1
      linarith
    · have hi : ind v p = 0 := by simp [ind, hvp]
      have e0 : ind v p * (1 - (if onlyP v p then (1 : ℝ) else 0)) = 0 := by rw [hi, zero_mul]
      rw [e0]; exact hsum0

theorem count_single (p : Fin k × Fin k) (hp : p ∈ Prs k) :
    ∑ v : Fin k → Fin N, ind v p = (N : ℝ) ^ (k - 1) := by
  have h := count_one (α := Fin N) p.1 p.2 (ne_of_lt (mem_Prs.mp hp))
  simp only [Fintype.card_fin] at h
  exact h

theorem count_double (p p' : Fin k × Fin k) (hp : p ∈ Prs k) (hp' : p' ∈ Prs k) (hpp : p ≠ p') :
    ∑ v : Fin k → Fin N, ind v p * ind v p' = (N : ℝ) ^ (k - 2) := by
  have h1 := mem_Prs.mp hp
  have h2 := mem_Prs.mp hp'
  have hst : p'.1 ≠ p'.2 := ne_of_lt h2
  by_cases ha : p.1 ≠ p'.1 ∧ p.1 ≠ p'.2
  · have h := count_two (α := Fin N) p.1 p.2 p'.1 p'.2 (ne_of_lt h1) ha.1 ha.2 hst
    simp only [Fintype.card_fin] at h
    exact h
  · have hb : p.2 ≠ p'.1 ∧ p.2 ≠ p'.2 := by
      push_neg at ha
      constructor
      · intro e
        by_cases hc : p.1 = p'.1
        · rw [hc, e] at h1; exact lt_irrefl _ h1
        · have := ha hc; rw [this, e] at h1; exact absurd (h1.trans h2) (lt_irrefl _)
      · intro e
        by_cases hc : p.1 = p'.1
        · exact hpp (Prod.ext hc e)
        · have := ha hc; rw [this, e] at h1; exact lt_irrefl _ h1
    have h := count_two (α := Fin N) p.2 p.1 p'.1 p'.2 (ne_of_lt h1).symm hb.1 hb.2 hst
    simp only [Fintype.card_fin] at h
    have e : ∀ v : Fin k → Fin N, ind v p * ind v p'
        = (if v p.2 = v p.1 then (1 : ℝ) else 0) * (if v p'.1 = v p'.2 then (1 : ℝ) else 0) := by
      intro v; simp only [ind, eq_comm]
    simp only [e]
    exact h

theorem sum_Dx :
    ∑ v : Fin k → Fin N, Dx v ≤ ((Prs k).card : ℝ) ^ 2 * (N : ℝ) ^ (k - 2) := by
  simp only [Dx]
  rw [Finset.sum_comm]
  have e : ∀ p ∈ Prs k, ∑ v : Fin k → Fin N, ∑ p' ∈ (Prs k).erase p, ind v p * ind v p'
      = (((Prs k).erase p).card : ℝ) * (N : ℝ) ^ (k - 2) := by
    intro p hp
    rw [Finset.sum_comm, Finset.sum_congr rfl fun p' hp' =>
      count_double p p' hp (Finset.mem_of_mem_erase hp') (Finset.ne_of_mem_erase hp').symm]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl e]
  calc ∑ p ∈ Prs k, (((Prs k).erase p).card : ℝ) * (N : ℝ) ^ (k - 2)
      ≤ ∑ p ∈ Prs k, ((Prs k).card : ℝ) * (N : ℝ) ^ (k - 2) :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right
          (by exact_mod_cast Finset.card_erase_le) (by positivity)
    _ = ((Prs k).card : ℝ) ^ 2 * (N : ℝ) ^ (k - 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end Coincidences

open WalkCount Function BiasGeneral2

section SumCycles

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
  {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

/-- `I_p = m_{p₂-p₁} m_{k-(p₂-p₁)}`: the value of a walk whose positions `p₁ < p₂` coincide. -/
def Ip (m : ℕ → ℝ) (k : ℕ) (p : Fin k × Fin k) : ℝ :=
  m (p.2.val - p.1.val) * m (k - (p.2.val - p.1.val))

theorem cycle_bound (S : RK ν q M m) (X : ℕ → Ω → G) (hX : ∀ j, Measurable (X j)) {N n : ℕ}
    (v : Fin (n + 1) → Fin N) :
    0 ≤ ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ
      ∧ ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ ≤ M ^ (n + 1) := by
  have hm : Measurable fun ω => cycP (q 1) (fun a => X (v a) ω) :=
    (cycP_meas S n).comp (measurable_pi_lambda _ fun a => hX (v a))
  have hint : Integrable (fun ω => cycP (q 1) (fun a => X (v a) ω)) μ :=
    Integrable.of_bound hm.aestronglyMeasurable (M ^ (n + 1))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cycP_nonneg S _)]; exact cycP_le S _)
  refine ⟨integral_nonneg fun ω => cycP_nonneg S _, ?_⟩
  calc ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ ≤ ∫ _ω, M ^ (n + 1) ∂μ :=
        integral_mono hint (integrable_const _) fun ω => cycP_le S _
    _ = M ^ (n + 1) := by simp

/-- **(3b), sum form.** With `F(v) = E[cycle through X_{v_0}, …, X_{v_n}]`, `k = n + 1`:
    `|∑_v F(v) - (N^k m_k - #Prs · N^{k-1} m_k + N^{k-1} ∑_{p ∈ Prs} I_p)|
       ≤ (M + M² + 2 M^k) #Prs² N^{k-2}`
    (`Prs` the pairs of positions `p₁ < p₂`, `I_p = m_{p₂-p₁} m_{k-(p₂-p₁)}`). -/
theorem sum_cycle_mean (S : RK ν q M m) (X : ℕ → Ω → G)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (N n : ℕ) :
    |∑ v : Fin (n + 1) → Fin N, ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ
        - ((N : ℝ) ^ (n + 1) * m (n + 1) - ((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ n * m (n + 1)
          + (N : ℝ) ^ n * ∑ p ∈ Prs (n + 1), Ip m (n + 1) p)|
      ≤ (M + M * M + 2 * M ^ (n + 1)) * (((Prs (n + 1)).card : ℝ) ^ 2 * (N : ℝ) ^ (n + 1 - 2)) := by
  classical
  have hM1 := S.M_ge
  have hM0 : 0 ≤ M := by linarith
  have hmk0 : 0 ≤ m (n + 1) := S.m_nonneg _ (by omega)
  have hmkM : m (n + 1) ≤ M := S.m_le _ (by omega)
  have hI : ∀ p ∈ Prs (n + 1), 0 ≤ Ip m (n + 1) p ∧ Ip m (n + 1) p ≤ M * M := by
    intro p hp
    have h := mem_Prs.mp hp
    have h1 : 1 ≤ p.2.val - p.1.val := by
      have : p.1.val < p.2.val := h; omega
    have h2 : 1 ≤ n + 1 - (p.2.val - p.1.val) := by have := p.2.isLt; omega
    exact ⟨mul_nonneg (S.m_nonneg _ h1) (S.m_nonneg _ h2),
      mul_le_mul (S.m_le _ h1) (S.m_le _ h2) (S.m_nonneg _ h2) hM0⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = M + M * M + 2 * M ^ (n + 1) := ⟨_, rfl⟩
  have hMk : 1 ≤ M ^ (n + 1) := one_le_pow₀ hM1
  -- the pointwise bound
  have hpt : ∀ v : Fin (n + 1) → Fin N,
      |∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ
        - (m (n + 1) - m (n + 1) * ∑ p ∈ Prs (n + 1), ind v p
          + ∑ p ∈ Prs (n + 1), ind v p * Ip m (n + 1) p)| ≤ K * Dx v := by
    intro v
    obtain ⟨F, hF⟩ : ∃ F, F = ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ := ⟨_, rfl⟩
    rw [← hF]
    obtain ⟨hF0, hFM⟩ := cycle_bound (μ := μ) S X hX v
    rw [← hF] at hF0 hFM
    obtain ⟨hR0, hRD, hR1⟩ := Rx_bounds v
    set c := ∑ p ∈ Prs (n + 1), ind v p with hc
    -- (a): the injective part
    have hA : (1 - c + Rx v) * F = (1 - c + Rx v) * m (n + 1) := by
      rw [hR1]
      split_ifs with hv
      · rw [one_mul, one_mul, hF]
        exact cycle_mean S X h_indep hX hlaw (fun a => (v a : ℕ))
          (fun a b h => hv (Fin.ext h))
      · simp
    -- (b): the walks with exactly one coinciding pair
    have hB : ∀ p ∈ Prs (n + 1), ind v p * (if onlyP v p then 1 else 0) * F
        = ind v p * (if onlyP v p then 1 else 0) * Ip m (n + 1) p := by
      intro p hp
      by_cases ho : onlyP v p
      · by_cases hvp : v p.1 = v p.2
        · simp only [ho, if_true, mul_one]
          congr 1
          rw [hF, Ip]
          exact cycle_pair S X h_indep hX hlaw v p.1 p.2 (mem_Prs.mp hp) hvp.symm ho
        · simp [ind, hvp]
      · simp [ho]
    have hcF : c * F - ∑ p ∈ Prs (n + 1), ind v p * Ip m (n + 1) p
        = ∑ p ∈ Prs (n + 1), ind v p * (1 - (if onlyP v p then 1 else 0))
            * (F - Ip m (n + 1) p) := by
      rw [hc, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      linear_combination hB p hp
    have hid : F - (m (n + 1) - m (n + 1) * c + ∑ p ∈ Prs (n + 1), ind v p * Ip m (n + 1) p)
        = Rx v * m (n + 1)
          + ∑ p ∈ Prs (n + 1), ind v p * (1 - (if onlyP v p then 1 else 0))
            * (F - Ip m (n + 1) p) - Rx v * F := by
      linear_combination hA + hcF
    rw [hid]
    have he0 : ∀ p, 0 ≤ ind v p * (1 - (if onlyP v p then (1 : ℝ) else 0)) := by
      intro p
      refine mul_nonneg (ind_nonneg v p) ?_
      split_ifs <;> norm_num
    have hesum : ∑ p ∈ Prs (n + 1), ind v p * (1 - (if onlyP v p then 1 else 0)) ≤ Dx v :=
      Finset.sum_le_sum fun p hp => excess_only v p hp
    have hterm : ∀ p ∈ Prs (n + 1), |ind v p * (1 - (if onlyP v p then 1 else 0))
        * (F - Ip m (n + 1) p)| ≤ ind v p * (1 - (if onlyP v p then 1 else 0))
          * (M ^ (n + 1) + M * M) := by
      intro p hp
      rw [abs_mul, abs_of_nonneg (he0 p)]
      refine mul_le_mul_of_nonneg_left ?_ (he0 p)
      obtain ⟨i0, i1⟩ := hI p hp
      rw [abs_le]; constructor <;> linarith
    have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    rw [← Finset.sum_mul] at hsum
    have hs2 := mul_le_mul_of_nonneg_right hesum (by positivity : (0 : ℝ) ≤ M ^ (n + 1) + M * M)
    have hR2 : |Rx v * m (n + 1) - Rx v * F| ≤ Rx v * (M + M ^ (n + 1)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hR0]
      refine mul_le_mul_of_nonneg_left ?_ hR0
      rw [abs_le]; constructor <;> linarith
    have hR3 := mul_le_mul_of_nonneg_right hRD (by positivity : (0 : ℝ) ≤ M + M ^ (n + 1))
    have e : Rx v * m (n + 1) + ∑ p ∈ Prs (n + 1), ind v p * (1 - (if onlyP v p then 1 else 0))
          * (F - Ip m (n + 1) p) - Rx v * F
        = (Rx v * m (n + 1) - Rx v * F) + ∑ p ∈ Prs (n + 1), ind v p
          * (1 - (if onlyP v p then 1 else 0)) * (F - Ip m (n + 1) p) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [hK]
    have hD := Dx_nonneg v
    nlinarith [hR2, hsum, hs2, hR3]
  -- summing over the walks
  have hsumF := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun v (_ : v ∈ (Finset.univ : Finset (Fin (n + 1) → Fin N))) => hpt v)
  rw [← Finset.mul_sum] at hsumF
  have hDsum := sum_Dx (N := N) (k := n + 1)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hmain : ∑ v : Fin (n + 1) → Fin N,
      (∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ
        - (m (n + 1) - m (n + 1) * ∑ p ∈ Prs (n + 1), ind v p
          + ∑ p ∈ Prs (n + 1), ind v p * Ip m (n + 1) p))
      = ∑ v : Fin (n + 1) → Fin N, ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ
        - ((N : ℝ) ^ (n + 1) * m (n + 1) - ((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ n * m (n + 1)
          + (N : ℝ) ^ n * ∑ p ∈ Prs (n + 1), Ip m (n + 1) p) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have h1 : ∑ v : Fin (n + 1) → Fin N, m (n + 1) * ∑ p ∈ Prs (n + 1), ind v p
        = ((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ n * m (n + 1) := by
      rw [← Finset.mul_sum, Finset.sum_comm,
        Finset.sum_congr rfl fun p hp => count_single (N := N) p hp]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.add_sub_cancel]
      ring
    have h2 : ∑ v : Fin (n + 1) → Fin N, ∑ p ∈ Prs (n + 1), ind v p * Ip m (n + 1) p
        = (N : ℝ) ^ n * ∑ p ∈ Prs (n + 1), Ip m (n + 1) p := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← Finset.sum_mul, count_single (N := N) p hp, Nat.add_sub_cancel]
    rw [h1, h2]
    push_cast
    ring
  rw [← hmain]
  refine hsumF.trans ?_
  rw [hK] at hK0 ⊢
  exact mul_le_mul_of_nonneg_left hDsum hK0

end SumCycles

open WalkCount Function BiasGeneral2

section MeanQ0

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
  {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

theorem trace_tilde (q : ℕ → G → G → ℝ) (N n : ℕ) (x : Fin N → G) :
    (Matrix.of (fun a b : Fin N => q 1 (x a) (x b) / N) ^ (n + 1)).trace
      = (∑ v : Fin (n + 1) → Fin N, cycP (q 1) (fun a => x (v a))) / (N : ℝ) ^ (n + 1) := by
  rw [BiasGeneral.trace_pow_cw, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [BiasGeneral.cw, cycP]
  simp only [Matrix.of_apply]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **(3b): `E Q₀ = E Tr P̃^k` up to `O(N⁻²)`, every `k = n + 1 ≥ 2`.**
    `|E Tr P̃^k - (m_k - #Prs · m_k/N + (∑_{p ∈ Prs} I_p)/N)| ≤ (M + M² + 2M^k) #Prs² / N²`.
    In the notation of the paper (`ρ = p(0)`, `μ_l = m_l`): `#Prs = k(k-1)/2` and
    `∑_{p} I_p = ∑_{l=1}^{k-1} (k-l) m_l m_{k-l} = (k/2) Σ₀`; these two identities are not
    part of this statement (see `card_Prs`, `sum_Ip` below if present). -/
theorem mean_Q0 (S : RK ν q M m) (X : ℕ → Ω → G)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) {N n : ℕ} (hN : 0 < N) (hn : 1 ≤ n) :
    |∫ ω, (Matrix.of (fun a b : Fin N => q 1 (X a ω) (X b ω) / N) ^ (n + 1)).trace ∂μ
        - (m (n + 1) - ((Prs (n + 1)).card : ℝ) * m (n + 1) / N
          + (∑ p ∈ Prs (n + 1), Ip m (n + 1) p) / N)|
      ≤ (M + M * M + 2 * M ^ (n + 1)) * ((Prs (n + 1)).card : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := sum_cycle_mean S X h_indep hX hlaw N n
  have hint : ∀ v : Fin (n + 1) → Fin N,
      Integrable (fun ω => cycP (q 1) (fun a => X (v a) ω)) μ := fun v =>
    Integrable.of_bound ((cycP_meas S n).comp
      (measurable_pi_lambda _ fun a => hX (v a))).aestronglyMeasurable (M ^ (n + 1))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cycP_nonneg S _)]; exact cycP_le S _)
  have e : ∫ ω, (Matrix.of (fun a b : Fin N => q 1 (X a ω) (X b ω) / N) ^ (n + 1)).trace ∂μ
      = (∑ v : Fin (n + 1) → Fin N, ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ) / (N : ℝ) ^ (n + 1) := by
    simp only [trace_tilde q N n]
    rw [integral_div, integral_finset_sum _ fun v _ => hint v]
  rw [e]
  have hpow : (N : ℝ) ^ (n + 1) = (N : ℝ) ^ (n + 1 - 2) * (N : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : (N : ℝ) ^ (n + 1) = (N : ℝ) ^ n * N := pow_succ _ _
  have hNk : (0 : ℝ) < (N : ℝ) ^ (n + 1) := by positivity
  obtain ⟨sv, hsv⟩ : ∃ s, s = ∑ v : Fin (n + 1) → Fin N, ∫ ω, cycP (q 1) (fun a => X (v a) ω) ∂μ :=
    ⟨_, rfl⟩
  rw [← hsv] at h ⊢
  have e2 : sv / (N : ℝ) ^ (n + 1) - (m (n + 1) - ((Prs (n + 1)).card : ℝ) * m (n + 1) / N
          + (∑ p ∈ Prs (n + 1), Ip m (n + 1) p) / N)
      = (sv - ((N : ℝ) ^ (n + 1) * m (n + 1) - ((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ n * m (n + 1)
          + (N : ℝ) ^ n * ∑ p ∈ Prs (n + 1), Ip m (n + 1) p)) / (N : ℝ) ^ (n + 1) := by
    field_simp
    rw [hpow2]
    ring
  rw [e2, abs_div, abs_of_pos hNk, div_le_div_iff₀ hNk (by positivity)]
  calc _ ≤ (M + M * M + 2 * M ^ (n + 1)) * (((Prs (n + 1)).card : ℝ) ^ 2 * (N : ℝ) ^ (n + 1 - 2))
        * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by rw [hpow]; ring

end MeanQ0

/-! ## (3b): the coefficients `#Prs = k(k-1)/2` and `∑_p I_p = (k/2) Σ₀` -/

section Coeff

theorem sum_Prs_fin (k : ℕ) (g : Fin k × Fin k → ℝ) :
    ∑ p ∈ Prs k, g p = ∑ i : Fin k, ∑ j : Fin k, if i < j then g (i, j) else 0 := by
  rw [Prs, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

theorem rangeA (f : ℕ → ℝ) : ∀ k : ℕ,
    ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, (if i < j then f (j - i) else 0)
      = ∑ l ∈ Finset.range k, ((k - l : ℕ) : ℝ) * f l - (k : ℝ) * f 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e1 : ∀ i ∈ Finset.range k, ∑ j ∈ Finset.range (k + 1), (if i < j then f (j - i) else 0)
        = ∑ j ∈ Finset.range k, (if i < j then f (j - i) else 0) + f (k - i) := by
      intro i hi
      rw [Finset.sum_range_succ, if_pos (Finset.mem_range.mp hi)]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ih]
    have e2 : ∑ j ∈ Finset.range (k + 1), (if k < j then f (j - k) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have : ¬ k < j := by have := Finset.mem_range.mp hj; omega
      simp [this]
    rw [e2]
    have e3 : ∑ i ∈ Finset.range k, f (k - i) = ∑ l ∈ Finset.range k, f (l + 1) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun l hl => ?_
      have := Finset.mem_range.mp hl
      congr 1; omega
    rw [e3]
    have e4 : ∑ l ∈ Finset.range (k + 1), ((k + 1 - l : ℕ) : ℝ) * f l
        = ∑ l ∈ Finset.range k, ((k - l : ℕ) : ℝ) * f l + ∑ l ∈ Finset.range (k + 1), f l := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun l => f l), ← add_assoc,
        ← Finset.sum_add_distrib]
      have : ∀ l ∈ Finset.range k, ((k + 1 - l : ℕ) : ℝ) * f l = ((k - l : ℕ) : ℝ) * f l + f l := by
        intro l hl
        have := Finset.mem_range.mp hl
        rw [show k + 1 - l = (k - l) + 1 by omega]; push_cast; ring
      rw [Finset.sum_congr rfl this]
      simp
    rw [e4, Finset.sum_range_succ' (f := fun l => f l)]
    push_cast
    ring

/-- `∑_{p₁<p₂} f(p₂ - p₁) = ∑_{l=1}^{k-1} (k - l) f(l)`. -/
theorem sum_Prs_diff (k : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Prs k, f (p.2.val - p.1.val) = ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : ℝ) * f l := by
  rw [sum_Prs_fin]
  have e : ∀ i j : Fin k, (if i < j then f (j.val - i.val) else 0)
      = (if i.val < j.val then f (j.val - i.val) else 0) := fun i j => by
    simp only [Fin.lt_iff_val_lt_val]
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin k, if i < j.val then f (j.val - i) else 0)]
  have e2 : ∀ i, ∑ j : Fin k, (if i < j.val then f (j.val - i) else 0)
      = ∑ j ∈ Finset.range k, (if i < j then f (j - i) else 0) := fun i =>
    Fin.sum_univ_eq_sum_range (fun j => if i < j then f (j - i) else 0) k
  simp only [e2]
  rw [rangeA]
  cases k with
  | zero => simp
  | succ k =>
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp

/-- The reflection `l ↦ k - l`: `2 ∑_{l=1}^{k-1} (k-l) a_l = k ∑_{l=1}^{k-1} a_l` for symmetric `a`. -/
theorem sum_reflect (k : ℕ) (a : ℕ → ℝ) (ha : ∀ l ∈ Finset.Ico 1 k, a (k - l) = a l) :
    (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : ℝ) * a l) * 2 = (k : ℝ) * ∑ l ∈ Finset.Ico 1 k, a l := by
  have h : ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : ℝ) * a l
      = ∑ l ∈ Finset.Ico 1 k, (l : ℝ) * a l := by
    refine Finset.sum_nbij' (fun l => k - l) (fun l => k - l) ?_ ?_ ?_ ?_ ?_
    · intro l hl; simp only [Finset.mem_Ico] at hl ⊢; omega
    · intro l hl; simp only [Finset.mem_Ico] at hl ⊢; omega
    · intro l hl; simp only [Finset.mem_Ico] at hl; show k - (k - l) = l; omega
    · intro l hl; simp only [Finset.mem_Ico] at hl; show k - (k - l) = l; omega
    · intro l hl
      rw [ha l hl]
  have e : ∀ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : ℝ) * a l + (l : ℝ) * a l = (k : ℝ) * a l := by
    intro l hl
    have := Finset.mem_Ico.mp hl
    rw [Nat.cast_sub (by omega)]; ring
  calc (∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : ℝ) * a l) * 2
      = ∑ l ∈ Finset.Ico 1 k, ((k - l : ℕ) : ℝ) * a l + ∑ l ∈ Finset.Ico 1 k, (l : ℝ) * a l := by
        rw [← h]; ring
    _ = ∑ l ∈ Finset.Ico 1 k, (k : ℝ) * a l := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl e
    _ = (k : ℝ) * ∑ l ∈ Finset.Ico 1 k, a l := by rw [Finset.mul_sum]

/-- `#Prs = k(k-1)/2`. -/
theorem card_Prs (k : ℕ) : ((Prs k).card : ℝ) * 2 = (k : ℝ) * ((k : ℝ) - 1) := by
  have h := sum_Prs_diff k (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  have h2 := sum_reflect k (fun _ => 1) (fun _ _ => rfl)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico] at h2
  rw [h, h2]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- `∑_{p ∈ Prs} I_p = ∑_{l=1}^{k-1} (k-l) m_l m_{k-l}`, and twice it is `k Σ₀`. -/
theorem sum_Ip (m : ℕ → ℝ) (k : ℕ) :
    (∑ p ∈ Prs k, Ip m k p) * 2 = (k : ℝ) * ∑ l ∈ Finset.Ico 1 k, m l * m (k - l) := by
  have h := sum_Prs_diff k (fun l => m l * m (k - l))
  simp only [Ip] at h ⊢
  rw [h]
  refine sum_reflect k (fun l => m l * m (k - l)) fun l hl => ?_
  have := Finset.mem_Ico.mp hl
  simp only
  rw [show k - (k - l) = l by omega, mul_comm]

end Coeff

end BiasGeneral3

namespace BiasGeneral4

open WalkCount Function BiasGeneral2 BiasGeneral3 PiBound

/-! # A99: `prop:bias` for every `k`, Point 4

* (4a) `indep_tuple`, `integrate_extra`, `integrate_extra_zero`: a sample point outside an index
  tuple can be integrated first; with a centred factor (`c = p - 1`) the expectation vanishes.
* (4b, generic) `lin_stat_gen`, `quad_stat_gen`: statistics with one or two centred row sums over
  index tuples of any arity, up to `O(N^{n-1})` resp. `O(N^n)`. -/

section Extra

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]

theorem indep_tuple (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) {n : ℕ} (w : Fin n → ℕ) (u : ℕ) (hu : ∀ i, w i ≠ u) :
    ProbabilityTheory.IndepFun (X u) (fun ω i => X (w i) ω) μ := by
  classical
  have hST : Disjoint ({u} : Finset ℕ) (Finset.univ.image w) := by
    rw [Finset.disjoint_singleton_left, Finset.mem_image]
    rintro ⟨i, _, hi⟩; exact hu i hi
  have h := h_indep.indepFun_finset {u} (Finset.univ.image w) hST hX
  have h1 : Measurable fun f : ({u} : Finset ℕ) → G => f ⟨u, Finset.mem_singleton_self u⟩ :=
    measurable_pi_apply _
  have h2 : Measurable fun (g : (Finset.univ.image w) → G) (i : Fin n) =>
      g ⟨w i, Finset.mem_image_of_mem w (Finset.mem_univ i)⟩ :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  exact h.comp h1 h2

/-- **(4a) Integrating a point outside the tuple first.** -/
theorem integrate_extra (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {n : ℕ} (w : Fin n → ℕ) (u : ℕ)
    (hu : ∀ i, w i ≠ u) (Φ : (Fin n → G) × G → ℝ) (hΦ : Measurable Φ) {B : ℝ}
    (hB : ∀ p, |Φ p| ≤ B) :
    ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ = ∫ ω, (∫ z, Φ (fun i => X (w i) ω, z) ∂ν) ∂μ := by
  have hY : Measurable (fun ω i => X (w i) ω) := measurable_pi_lambda _ fun i => hX (w i)
  have h := indep_integral_eq ν (X u) (fun ω i => X (w i) ω) (hX u) hY
    (indep_tuple X h_indep hX w u hu) (hlaw u) (fun p => Φ (p.2, p.1))
    (hΦ.comp (measurable_snd.prodMk measurable_fst)) (B := B) (fun p => hB _)
  simp only at h
  rw [h]
  have hψ : Measurable fun y : Fin n → G => ∫ z, Φ (y, z) ∂ν :=
    (hΦ.stronglyMeasurable.integral_prod_right').measurable
  rw [integral_map hY.aemeasurable hψ.aestronglyMeasurable]

/-- **(4a) A centred factor at a point outside the tuple has expectation zero.** -/
theorem integrate_extra_zero (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {n : ℕ} (w : Fin n → ℕ) (u : ℕ)
    (hu : ∀ i, w i ≠ u) (Φ : (Fin n → G) × G → ℝ) (hΦ : Measurable Φ) {B : ℝ}
    (hB : ∀ p, |Φ p| ≤ B) (hc : ∀ y, ∫ z, Φ (y, z) ∂ν = 0) :
    ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ = 0 := by
  rw [integrate_extra X h_indep hX hlaw w u hu Φ hΦ hB]
  simp [hc]

theorem abs_int_le_B {f : Ω → ℝ} {B : ℝ} (hf : ∀ ω, |f ω| ≤ B) : |∫ ω, f ω ∂μ| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hf ω)
  simpa [Real.norm_eq_abs] using h

end Extra

/-! ## Generic statistics with centred row sums -/

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]

theorem noninj_le {N n : ℕ} (w : Fin n → Fin N) :
    (if Injective w then (0 : ℝ) else 1) ≤ ∑ p ∈ Prs n, ind w p := by
  classical
  obtain ⟨h0, -, h1⟩ := Rx_bounds w
  have e : (if Injective w then (0 : ℝ) else 1) = 1 - (if Injective w then 1 else 0) := by
    split_ifs <;> norm_num
  rw [e, ← h1]
  linarith

theorem sum_noninj_le (N n : ℕ) :
    ∑ w : Fin n → Fin N, (if Injective w then (0 : ℝ) else 1)
      ≤ ((Prs n).card : ℝ) * (N : ℝ) ^ (n - 1) := by
  classical
  calc ∑ w : Fin n → Fin N, (if Injective w then (0 : ℝ) else 1)
      ≤ ∑ w : Fin n → Fin N, ∑ p ∈ Prs n, ind w p := Finset.sum_le_sum fun w _ => noninj_le w
    _ = ∑ p ∈ Prs n, ∑ w : Fin n → Fin N, ind w p := Finset.sum_comm
    _ = ∑ p ∈ Prs n, (N : ℝ) ^ (n - 1) :=
        Finset.sum_congr rfl fun p hp => count_single p hp
    _ = ((Prs n).card : ℝ) * (N : ℝ) ^ (n - 1) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **A statistic with one centred row sum, any arity `n`.** `Φ(y, z)` centred in `z`, `|Φ| ≤ B`;
    on injective tuples `E Φ(X_w, X_{w_r}) = L_r` with `|L_r| ≤ B`. Then
    `|E ∑_w ∑_u Φ(X_w, X_u) - N^n ∑_r L_r| ≤ 2 n B #Prs N^{n-1}`. -/
theorem lin_stat_gen (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (N n : ℕ)
    (Φ : (Fin n → G) × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p, |Φ p| ≤ B)
    (hc : ∀ y, ∫ z, Φ (y, z) ∂ν = 0) (L : Fin n → ℝ) (hLb : ∀ r, |L r| ≤ B)
    (hL : ∀ w : Fin n → Fin N, Injective w → ∀ r,
      ∫ ω, Φ (fun i => X (w i) ω, X (w r) ω) ∂μ = L r) :
    |∑ w : Fin n → Fin N, ∑ u : Fin N, ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ
        - (N : ℝ) ^ n * ∑ r, L r|
      ≤ 2 * n * B * (((Prs n).card : ℝ) * (N : ℝ) ^ (n - 1)) := by
  classical
  have hzero : ∀ (w : Fin n → Fin N) (u : Fin N), u ∉ Finset.univ.image w →
      ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ = 0 := by
    intro w u hu
    refine integrate_extra_zero X h_indep hX hlaw (fun i => (w i : ℕ)) u ?_ Φ hΦ hB hc
    intro i h
    exact hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
  have hT : ∀ w : Fin n → Fin N, ∑ u : Fin N, ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ
      = ∑ u ∈ Finset.univ.image w, ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ := by
    intro w
    exact (Finset.sum_subset (Finset.subset_univ _) fun u _ hu => hzero w u hu).symm
  have hbd : ∀ w : Fin n → Fin N,
      |∑ u : Fin N, ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ - ∑ r, L r|
        ≤ (if Injective w then (0 : ℝ) else 1) * (2 * n * B) := by
    intro w
    rw [hT w]
    split_ifs with hw
    · rw [Finset.sum_image fun a _ b _ h => hw h]
      simp only [hL w hw, sub_self, abs_zero, zero_mul, le_refl]
    · have h1 : |∑ u ∈ Finset.univ.image w, ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ| ≤ n * B := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ u ∈ Finset.univ.image w, |∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ|
            ≤ ∑ _u ∈ Finset.univ.image w, B :=
              Finset.sum_le_sum fun u _ => abs_int_le_B fun ω => hB _
          _ = (Finset.univ.image w).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ n * B := by
              refine mul_le_mul_of_nonneg_right ?_ hB0
              have := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := w)
              simp only [Finset.card_univ, Fintype.card_fin] at this
              exact_mod_cast this
      have h2 : |∑ r, L r| ≤ n * B := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ r, |L r| ≤ ∑ _r : Fin n, B := Finset.sum_le_sum fun r _ => hLb r
          _ = n * B := by simp
      rw [one_mul]
      exact (abs_sub _ _).trans (by linarith)
  have e : ∑ w : Fin n → Fin N, ∑ u : Fin N, ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ
        - (N : ℝ) ^ n * ∑ r, L r
      = ∑ w : Fin n → Fin N, (∑ u : Fin N, ∫ ω, Φ (fun i => X (w i) ω, X u ω) ∂μ - ∑ r, L r) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun w _ => hbd w).trans ?_)
  rw [← Finset.sum_mul]
  have h := sum_noninj_le N n
  have hc0 : 0 ≤ 2 * (n : ℝ) * B := by positivity
  calc (∑ w : Fin n → Fin N, (if Injective w then (0 : ℝ) else 1)) * (2 * n * B)
      ≤ (((Prs n).card : ℝ) * (N : ℝ) ^ (n - 1)) * (2 * n * B) :=
        mul_le_mul_of_nonneg_right h hc0
    _ = _ := by ring

end Generic

open WalkCount Function BiasGeneral2 BiasGeneral3 PiBound

section Generic2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]

/-- Integrating the first of two centred row sums when it sits outside the tuple and differs from
    the second. -/
theorem zero_first (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {N n : ℕ}
    (Φ : (Fin n → G) × G × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ p, |Φ p| ≤ B)
    (hc1 : ∀ y z', ∫ z, Φ (y, z, z') ∂ν = 0) (w : Fin n → Fin N) (u u' : Fin N)
    (hu : u ∉ Finset.univ.image w) (huu : u ≠ u') :
    ∫ ω, Φ (fun i => X (w i) ω, X u ω, X u' ω) ∂μ = 0 := by
  have h := integrate_extra_zero X h_indep hX hlaw
    (Fin.cons (u' : ℕ) (fun i => (w i : ℕ)) : Fin (n + 1) → ℕ) u
    (by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; intro h; exact huu (Fin.ext h.symm)
      · simp only [Fin.cons_succ]; intro h
        exact hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩))
    (fun p => Φ (fun i => p.1 i.succ, p.2, p.1 0))
    (hΦ.comp ((measurable_pi_lambda _ fun i => (measurable_pi_apply i.succ).comp measurable_fst).prodMk
      (measurable_snd.prodMk ((measurable_pi_apply 0).comp measurable_fst))))
    (B := B) (fun p => hB _) (fun y => hc1 (fun i => y i.succ) (y 0))
  simpa only [Fin.cons_succ, Fin.cons_zero] using h

theorem zero_second (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {N n : ℕ}
    (Φ : (Fin n → G) × G × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ p, |Φ p| ≤ B)
    (hc2 : ∀ y z, ∫ z', Φ (y, z, z') ∂ν = 0) (w : Fin n → Fin N) (u u' : Fin N)
    (hu' : u' ∉ Finset.univ.image w) (huu : u ≠ u') :
    ∫ ω, Φ (fun i => X (w i) ω, X u ω, X u' ω) ∂μ = 0 := by
  have h := integrate_extra_zero X h_indep hX hlaw
    (Fin.cons (u : ℕ) (fun i => (w i : ℕ)) : Fin (n + 1) → ℕ) u'
    (by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; intro h; exact huu (Fin.ext h)
      · simp only [Fin.cons_succ]; intro h
        exact hu' (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩))
    (fun p => Φ (fun i => p.1 i.succ, p.1 0, p.2))
    (hΦ.comp ((measurable_pi_lambda _ fun i => (measurable_pi_apply i.succ).comp measurable_fst).prodMk
      (((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd)))
    (B := B) (fun p => hB _) (fun y => hc2 (fun i => y i.succ) (y 0))
  simpa only [Fin.cons_succ, Fin.cons_zero] using h

/-- **A statistic with two centred row sums, any arity `n`.** `Φ(y, z, z')` centred in `z` and in
    `z'`, `|Φ| ≤ B`; on injective tuples and `u` outside, `E Φ(X_w, X_u, X_u) = L` with `|L| ≤ B`.
    Then `|E ∑_w ∑_{u,u'} Φ(X_w, X_u, X_{u'}) - N^{n+1} L|
       ≤ B ((n + n²) N^n + #Prs N^{n-1} (2N + n²))`. -/
theorem quad_stat_gen (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (N n : ℕ)
    (Φ : (Fin n → G) × G × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ p, |Φ p| ≤ B)
    (hc1 : ∀ y z', ∫ z, Φ (y, z, z') ∂ν = 0) (hc2 : ∀ y z, ∫ z', Φ (y, z, z') ∂ν = 0)
    (L : ℝ) (hLb : |L| ≤ B)
    (hL : ∀ w : Fin n → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, Φ (fun i => X (w i) ω, X u ω, X u ω) ∂μ = L) :
    |∑ w : Fin n → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, Φ (fun i => X (w i) ω, X u ω, X u' ω) ∂μ - (N : ℝ) ^ (n + 1) * L|
      ≤ B * (((n : ℝ) + n ^ 2) * (N : ℝ) ^ n
          + ((Prs n).card : ℝ) * (N : ℝ) ^ (n - 1) * (2 * N + (n : ℝ) ^ 2)) := by
  classical
  set E := fun (w : Fin n → Fin N) (u u' : Fin N) =>
    ∫ ω, Φ (fun i => X (w i) ω, X u ω, X u' ω) ∂μ with hEdef
  have hEb : ∀ w u u', |E w u u'| ≤ B := fun w u u' => abs_int_le_B fun ω => hB _
  -- the structure of the inner double sum
  have hT : ∀ w : Fin n → Fin N, ∑ u : Fin N, ∑ u' : Fin N, E w u u'
      = ∑ u ∈ (Finset.univ.image w)ᶜ, E w u u
        + ∑ u ∈ Finset.univ.image w, ∑ u' ∈ Finset.univ.image w, E w u u' := by
    intro w
    rw [← Finset.sum_compl_add_sum (Finset.univ.image w)]
    congr 1
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_compl] at hu
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
      have : ∑ u' ∈ Finset.univ.erase u, E w u u' = 0 :=
        Finset.sum_eq_zero fun u' hu' =>
          zero_first X h_indep hX hlaw Φ hΦ hB hc1 w u u' hu (Finset.ne_of_mem_erase hu').symm
      rw [this, add_zero]
    · refine Finset.sum_congr rfl fun u hu => ?_
      refine (Finset.sum_subset (Finset.subset_univ _) fun u' _ hu' => ?_).symm
      exact zero_second X h_indep hX hlaw Φ hΦ hB hc2 w u u' hu'
        (fun e => hu' (e ▸ hu))
  have hR : ∀ w : Fin n → Fin N,
      |∑ u ∈ Finset.univ.image w, ∑ u' ∈ Finset.univ.image w, E w u u'| ≤ (n : ℝ) ^ 2 * B := by
    intro w
    have hc : ((Finset.univ.image w).card : ℝ) ≤ n := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := w)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u ∈ Finset.univ.image w, |∑ u' ∈ Finset.univ.image w, E w u u'|
        ≤ ∑ _u ∈ Finset.univ.image w, (n : ℝ) * B := by
          refine Finset.sum_le_sum fun u _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ u' ∈ Finset.univ.image w, |E w u u'| ≤ ∑ _u' ∈ Finset.univ.image w, B :=
                Finset.sum_le_sum fun u' _ => hEb w u u'
            _ = (Finset.univ.image w).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ n * B := mul_le_mul_of_nonneg_right hc hB0
      _ = (Finset.univ.image w).card * ((n : ℝ) * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * ((n : ℝ) * B) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (n : ℝ) ^ 2 * B := by ring
  have hbd : ∀ w : Fin n → Fin N, |∑ u : Fin N, ∑ u' : Fin N, E w u u' - N * L|
      ≤ ((n : ℝ) + n ^ 2) * B
        + (if Injective w then (0 : ℝ) else 1) * ((2 * N + (n : ℝ) ^ 2) * B) := by
    intro w
    rw [hT w]
    have hR' := hR w
    split_ifs with hw
    · have h1 : ∑ u ∈ (Finset.univ.image w)ᶜ, E w u u = ((N : ℝ) - n) * L := by
        rw [Finset.sum_congr rfl fun u hu => hL w hw u (Finset.mem_compl.mp hu),
          Finset.sum_const, nsmul_eq_mul, Finset.card_compl,
          Finset.card_image_of_injective _ hw]
        simp only [Finset.card_univ, Fintype.card_fin]
        rw [Nat.cast_sub]
        have := Fintype.card_le_of_injective w hw
        simpa using this
      rw [h1]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnL : |(n : ℝ) * L| ≤ n * B := by
        rw [abs_mul, abs_of_nonneg hn0]; exact mul_le_mul_of_nonneg_left hLb hn0
      have e : ((N : ℝ) - n) * L + ∑ u ∈ Finset.univ.image w, ∑ u' ∈ Finset.univ.image w, E w u u'
          - N * L = -((n : ℝ) * L) + ∑ u ∈ Finset.univ.image w,
            ∑ u' ∈ Finset.univ.image w, E w u u' := by ring
      rw [e, zero_mul, add_zero]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      nlinarith
    · have h1 : |∑ u ∈ (Finset.univ.image w)ᶜ, E w u u| ≤ N * B := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ u ∈ (Finset.univ.image w)ᶜ, |E w u u| ≤ ∑ _u ∈ (Finset.univ.image w)ᶜ, B :=
              Finset.sum_le_sum fun u _ => hEb w u u
          _ = ((Finset.univ.image w)ᶜ).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ N * B := by
              refine mul_le_mul_of_nonneg_right ?_ hB0
              have := Finset.card_le_univ ((Finset.univ.image w)ᶜ)
              simp only [Fintype.card_fin] at this
              exact_mod_cast this
      have hNL : |(N : ℝ) * L| ≤ N * B := by
        rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left hLb (Nat.cast_nonneg N)
      have hnn : (0 : ℝ) ≤ ((n : ℝ) + n ^ 2) * B := by positivity
      calc |∑ u ∈ (Finset.univ.image w)ᶜ, E w u u
            + ∑ u ∈ Finset.univ.image w, ∑ u' ∈ Finset.univ.image w, E w u u' - N * L|
          ≤ N * B + (n : ℝ) ^ 2 * B + N * B :=
            (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 hR')) hNL)
        _ ≤ ((n : ℝ) + n ^ 2) * B + 1 * ((2 * N + (n : ℝ) ^ 2) * B) := by linarith
  have e : ∑ w : Fin n → Fin N, ∑ u : Fin N, ∑ u' : Fin N, E w u u' - (N : ℝ) ^ (n + 1) * L
      = ∑ w : Fin n → Fin N, (∑ u : Fin N, ∑ u' : Fin N, E w u u' - N * L) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  show |∑ w : Fin n → Fin N, ∑ u : Fin N, ∑ u' : Fin N, E w u u' - (N : ℝ) ^ (n + 1) * L| ≤ _
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun w _ => hbd w).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
  have h := sum_noninj_le N n
  have hc0 : 0 ≤ (2 * (N : ℝ) + (n : ℝ) ^ 2) * B := by positivity
  have h2 := mul_le_mul_of_nonneg_right h hc0
  have h3 : ∑ x : Fin n → Fin N, (if Injective x then (0 : ℝ) else 1) * ((2 * (N : ℝ) + (n : ℝ) ^ 2) * B)
      = (∑ x : Fin n → Fin N, if Injective x then (0 : ℝ) else 1) * ((2 * (N : ℝ) + (n : ℝ) ^ 2) * B) := by
    rw [Finset.sum_mul]
  push_cast
  have e : B * (((n : ℝ) + n ^ 2) * (N : ℝ) ^ n
          + ((Prs n).card : ℝ) * (N : ℝ) ^ (n - 1) * (2 * N + (n : ℝ) ^ 2))
      = (N : ℝ) ^ n * ((n : ℝ) + n ^ 2) * B
        + ((Prs n).card : ℝ) * (N : ℝ) ^ (n - 1) * ((2 * N + (n : ℝ) ^ 2) * B) := by ring
  linarith [h2, h3, e]

end Generic2

open WalkCount Function BiasGeneral2 BiasGeneral3 PiBound CTG.Reals.TorusReduction

/-! ## (4b) on the flat torus: the statistic `A = ∑_i (P̃^k)_ii ε_i` for every `k` -/

section TorusA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `Ch d σ k r c = ∫ p_r p_{k-r} p_c` (`p_s = heatP d σ s`). -/
noncomputable def Ch (d : ℕ) (σ : ℝ) (k r c : ℕ) : ℝ :=
  ∫ u, heatP d σ r u * heatP d σ (k - r) u * heatP d σ c u ∂flatTorusMeasure d

/-- The values `L_r` of the statistic `A` (`k = n + 1`). -/
noncomputable def LA (d : ℕ) (σ : ℝ) (n : ℕ) (r : Fin (n + 1)) : ℝ :=
  if r = 0 then (torusM d σ 1 - 1) * torusM d σ (n + 1)
  else Ch d σ (n + 1) r.val 1 - torusM d σ (n + 1)

/-- The cycle weight on the torus. -/
noncomputable def cyT (d : ℕ) (σ : ℝ) {n : ℕ} (y : Fin (n + 1) → FlatTorus d) : ℝ :=
  cycP (fun x z => heatP d σ 1 (x - z)) y

theorem cyT_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) :
    Measurable fun y : Fin (n + 1) → FlatTorus d => cyT d σ y :=
  cycP_meas (torusRK hσ d) n

theorem cyT_bounds {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {n : ℕ} (y : Fin (n + 1) → FlatTorus d) :
    0 ≤ cyT d σ y ∧ cyT d σ y ≤ torusM d σ 1 ^ (n + 1) :=
  ⟨cycP_nonneg (torusRK hσ d) y, cycP_le (torusRK hσ d) y⟩

theorem cK_bound {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (u : FlatTorus d) :
    |heatP d σ 1 u - 1| ≤ torusM d σ 1 := by
  have h0 := heatP_nonneg hσ d 1 u
  have h1 := heatP_le hσ d le_rfl u
  have hM := torusM_one_ge hσ d
  rw [abs_le]; constructor <;> linarith

theorem cyT_int {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (hX : ∀ j, Measurable (X j)) {n : ℕ} (ι : Fin (n + 1) → ℕ) (g : FlatTorus d → FlatTorus d → ℝ)
    (hg : Measurable fun p : FlatTorus d × FlatTorus d => g p.1 p.2) {C : ℝ}
    (hgC : ∀ x z, |g x z| ≤ C) (a b : Fin (n + 1)) :
    Integrable (fun ω => cyT d σ (fun i => X (ι i) ω) * g (X (ι a) ω) (X (ι b) ω)) μ :=
  Integrable.of_bound (((cyT_meas hσ d n).comp (measurable_pi_lambda _ fun i => hX (ι i))).mul
    (hg.comp ((hX (ι a)).prodMk (hX (ι b))))).aestronglyMeasurable
    (torusM d σ 1 ^ (n + 1) * C) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by rw [abs_of_nonneg (cyT_bounds hσ d _).1]; exact (cyT_bounds hσ d _).2)
        (hgC _ _) (abs_nonneg _) (le_trans (cyT_bounds hσ d (fun i => X (ι i) ω)).1 (cyT_bounds hσ d (fun i => X (ι i) ω)).2))

/-- The summand of `A`: `cycle(y) (p(y_0 - z) - 1)`. -/
noncomputable def PhiA (d : ℕ) (σ : ℝ) (n : ℕ) (p : (Fin (n + 1) → FlatTorus d) × FlatTorus d) : ℝ :=
  cyT d σ p.1 * (heatP d σ 1 (p.1 0 - p.2) - 1)

theorem PhiA_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : Measurable (PhiA d σ n) := by
  unfold PhiA
  exact ((cyT_meas hσ d n).comp measurable_fst).mul
    (((heatP_cont hσ d le_rfl).measurable.comp
      (((measurable_pi_apply 0).comp measurable_fst).sub measurable_snd)).sub_const 1)

theorem p1_int {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (x : FlatTorus d) :
    Integrable (fun z => heatP d σ 1 (x - z)) (flatTorusMeasure d) :=
  Integrable.of_bound ((heatP_cont hσ d le_rfl).measurable.comp
    (measurable_const.sub measurable_id)).aestronglyMeasurable (torusM d σ 1)
    (Filter.Eventually.of_forall fun z => by
      show |heatP d σ 1 (x - z)| ≤ _
      rw [abs_of_nonneg (heatP_nonneg hσ d 1 _)]; exact heatP_le hσ d le_rfl _)

/-- **The values of `A` on injective tuples.** -/
theorem LA_value {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {N n : ℕ} (w : Fin (n + 1) → Fin N)
    (hw : Injective w) (r : Fin (n + 1)) :
    ∫ ω, PhiA d σ n (fun i => X (w i) ω, X (w r) ω) ∂μ = LA d σ n r := by
  simp only [PhiA]
  have S := torusRK hσ d
  have hι : Injective fun i => (w i : ℕ) := fun a b h => hw (Fin.ext h)
  have hmean : ∫ ω, cyT d σ (fun i => X (w i) ω) ∂μ = torusM d σ (n + 1) :=
    cycle_mean S X h_indep hX hlaw (fun i => (w i : ℕ)) hι
  have hM := torusM_one_ge hσ d
  have hpm : Measurable fun p : FlatTorus d × FlatTorus d => heatP d σ 1 (p.1 - p.2) :=
    (heatP_cont hσ d le_rfl).measurable.comp (measurable_fst.sub measurable_snd)
  have hI1 := cyT_int (μ := μ) hσ d X hX (fun i => (w i : ℕ)) (fun x z => heatP d σ 1 (x - z)) hpm
    (C := torusM d σ 1) (fun x z => by
      rw [abs_of_nonneg (heatP_nonneg hσ d 1 _)]; exact heatP_le hσ d le_rfl _) 0 r
  have hI0 : Integrable (fun ω => cyT d σ (fun i => X (w i) ω)) μ := by
    have := cyT_int (μ := μ) hσ d X hX (fun i => (w i : ℕ)) (fun _ _ => (1 : ℝ))
      measurable_const (C := 1) (fun _ _ => by norm_num) 0 r
    simpa using this
  have e : ∀ ω, cyT d σ (fun i => X (w i) ω) * (heatP d σ 1 (X (w 0) ω - X (w r) ω) - 1)
      = cyT d σ (fun i => X (w i) ω) * heatP d σ 1 (X (w 0) ω - X (w r) ω)
        - cyT d σ (fun i => X (w i) ω) := fun ω => by ring
  simp_rw [e]
  rw [integral_sub hI1 hI0, hmean, LA]
  split_ifs with hr
  · subst hr
    simp only [sub_self, heatP_zero d σ le_rfl]
    rw [integral_mul_const, hmean]; ring
  · have h := cycle_chord hσ d X h_indep hX hlaw (fun i => (w i : ℕ)) hι r hr (heatP d σ 1)
      (heatP_cont hσ d le_rfl).measurable (heatP_nonneg hσ d 1) (C := torusM d σ 1)
      (heatP_le hσ d le_rfl)
    rw [show (∫ ω, cyT d σ (fun i => X (w i) ω) * heatP d σ 1 (X (w 0) ω - X (w r) ω) ∂μ)
        = ∫ u, heatP d σ r.val u * heatP d σ (n + 1 - r.val) u * heatP d σ 1 u
          ∂flatTorusMeasure d from h, Ch]

/-- **`E A` for every `k = n + 1`** (`A = N^{-k-1} ∑_w ∑_u cycle(X_w) c(X_{w_0} - X_u)`):
    `|E ∑_w ∑_u cycle · c - N^k ∑_r L_r| ≤ 2 k M^{k+1} #Prs N^{k-1}`,
    `∑_r L_r = (m₁ - 1) m_k + ∑_{r=1}^{k-1} (∫ p_r p_{k-r} p - m_k)`. -/
theorem meanA {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) :
    |∑ w : Fin (n + 1) → Fin N, ∑ u : Fin N, ∫ ω, PhiA d σ n (fun i => X (w i) ω, X u ω) ∂μ
        - (N : ℝ) ^ (n + 1) * ∑ r, LA d σ n r|
      ≤ 2 * ((n + 1 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1)
        * (((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ (n + 1 - 1)) := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiA d σ n p| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 := by
    intro p
    unfold PhiA
    rw [abs_mul, abs_of_nonneg (cyT_bounds hσ d p.1).1]
    exact mul_le_mul (cyT_bounds hσ d p.1).2 (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  have hc : ∀ y, ∫ z, PhiA d σ n (y, z) ∂flatTorusMeasure d = 0 := by
    intro y
    simp only [PhiA]
    rw [integral_const_mul]
    have hm := heatP_mass hσ d (le_refl 1) (y 0)
    rw [integral_sub (p1_int hσ d (y 0)) (integrable_const 1), hm]
    simp
  have hLb : ∀ r, |LA d σ n r| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 := by
    intro r
    have hm1 : torusM d σ (n + 1) ≤ torusM d σ 1 := torusM_anti hσ d le_rfl (by omega)
    have hm0 : 0 ≤ torusM d σ (n + 1) := (torusM_pos hσ d (by omega)).le
    have hMk : torusM d σ 1 ≤ torusM d σ 1 ^ (n + 1) := le_self_pow₀ hM (by omega)
    unfold LA
    split_ifs with hr0
    · rw [abs_le]; constructor <;> nlinarith
    · have hr1 : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr (fun h => hr0 (Fin.ext h))
      have hrn : r.val ≤ n := by have := r.isLt; omega
      have hpb : ∀ u, 0 ≤ heatP d σ r.val u * heatP d σ (n + 1 - r.val) u * heatP d σ 1 u
          ∧ heatP d σ r.val u * heatP d σ (n + 1 - r.val) u * heatP d σ 1 u
            ≤ torusM d σ 1 * torusM d σ 1 * torusM d σ 1 := by
        intro u
        have a1 : heatP d σ r.val u ≤ torusM d σ 1 :=
          (heatP_le hσ d hr1 u).trans (torusM_anti hσ d le_rfl hr1)
        have a2 : heatP d σ (n + 1 - r.val) u ≤ torusM d σ 1 :=
          (heatP_le hσ d (by omega) u).trans (torusM_anti hσ d le_rfl (by omega))
        have a3 := heatP_le hσ d (le_refl 1) u
        have b1 := heatP_nonneg hσ d r.val u
        have b2 := heatP_nonneg hσ d (n + 1 - r.val) u
        have b3 := heatP_nonneg hσ d 1 u
        refine ⟨mul_nonneg (mul_nonneg b1 b2) b3, ?_⟩
        exact mul_le_mul (mul_le_mul a1 a2 b2 (by linarith)) a3 b3 (by positivity)
      have hint : Integrable (fun u => heatP d σ r.val u * heatP d σ (n + 1 - r.val) u
          * heatP d σ 1 u) (flatTorusMeasure d) :=
        Integrable.of_bound ((((heatP_cont hσ d hr1).measurable.mul
          (heatP_cont hσ d (by omega)).measurable).mul
          (heatP_cont hσ d le_rfl).measurable).aestronglyMeasurable)
          (torusM d σ 1 * torusM d σ 1 * torusM d σ 1)
          (Filter.Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hpb u).1]; exact (hpb u).2)
      have hc0 : 0 ≤ Ch d σ (n + 1) r.val 1 := integral_nonneg fun u => (hpb u).1
      have hcM : Ch d σ (n + 1) r.val 1 ≤ torusM d σ 1 * torusM d σ 1 * torusM d σ 1 := by
        unfold Ch
        calc ∫ u, heatP d σ r.val u * heatP d σ (n + 1 - r.val) u * heatP d σ 1 u
              ∂flatTorusMeasure d
            ≤ ∫ _u, torusM d σ 1 * torusM d σ 1 * torusM d σ 1 ∂flatTorusMeasure d :=
              integral_mono hint (integrable_const _) fun u => (hpb u).2
          _ = _ := by simp
      have hM2 : torusM d σ 1 ^ 2 ≤ torusM d σ 1 ^ (n + 1) := pow_le_pow_right₀ hM (by omega)
      have hM3 : torusM d σ 1 * torusM d σ 1 * torusM d σ 1
          ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 := by nlinarith
      rw [abs_le]; constructor <;> nlinarith
  exact lin_stat_gen X h_indep hX hlaw N (n + 1) (PhiA d σ n) (PhiA_meas hσ d n) (by positivity)
    hB hc (LA d σ n) hLb (fun w hw r => LA_value hσ d X h_indep hX hlaw w hw r)

end TorusA

open WalkCount Function BiasGeneral2 BiasGeneral3 PiBound CTG.Reals.TorusReduction

/-! ## (4b) on the flat torus: the statistic `B = ∑_i (P̃^k)_ii (P̃ε)_i` for every `k` -/

section TorusB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `E[cycle (p_c(x_0 - x_r) - 1)]` on injective tuples, `c ≥ 1`. -/
theorem chordc_value {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {N n : ℕ} (w : Fin (n + 1) → Fin N)
    (hw : Injective w) (r : Fin (n + 1)) (c : ℕ) (hc : 1 ≤ c) :
    ∫ ω, cyT d σ (fun i => X (w i) ω) * (heatP d σ c (X (w 0) ω - X (w r) ω) - 1) ∂μ
      = if r = 0 then (torusM d σ c - 1) * torusM d σ (n + 1)
        else Ch d σ (n + 1) r.val c - torusM d σ (n + 1) := by
  have S := torusRK hσ d
  have hι : Injective fun i => (w i : ℕ) := fun a b h => hw (Fin.ext h)
  have hmean : ∫ ω, cyT d σ (fun i => X (w i) ω) ∂μ = torusM d σ (n + 1) :=
    cycle_mean S X h_indep hX hlaw (fun i => (w i : ℕ)) hι
  have hpm : Measurable fun p : FlatTorus d × FlatTorus d => heatP d σ c (p.1 - p.2) :=
    (heatP_cont hσ d hc).measurable.comp (measurable_fst.sub measurable_snd)
  have hI1 := cyT_int (μ := μ) hσ d X hX (fun i => (w i : ℕ)) (fun x z => heatP d σ c (x - z)) hpm
    (C := torusM d σ c) (fun x z => by
      rw [abs_of_nonneg (heatP_nonneg hσ d c _)]; exact heatP_le hσ d hc _) 0 r
  have hI0 : Integrable (fun ω => cyT d σ (fun i => X (w i) ω)) μ := by
    have := cyT_int (μ := μ) hσ d X hX (fun i => (w i : ℕ)) (fun _ _ => (1 : ℝ))
      measurable_const (C := 1) (fun _ _ => by norm_num) 0 r
    simpa using this
  have e : ∀ ω, cyT d σ (fun i => X (w i) ω) * (heatP d σ c (X (w 0) ω - X (w r) ω) - 1)
      = cyT d σ (fun i => X (w i) ω) * heatP d σ c (X (w 0) ω - X (w r) ω)
        - cyT d σ (fun i => X (w i) ω) := fun ω => by ring
  simp_rw [e]
  rw [integral_sub hI1 hI0, hmean]
  split_ifs with hr
  · subst hr
    simp only [sub_self, heatP_zero d σ hc]
    rw [integral_mul_const, hmean]; ring
  · have h := cycle_chord hσ d X h_indep hX hlaw (fun i => (w i : ℕ)) hι r hr (heatP d σ c)
      (heatP_cont hσ d hc).measurable (heatP_nonneg hσ d c) (C := torusM d σ c)
      (heatP_le hσ d hc)
    rw [show (∫ ω, cyT d σ (fun i => X (w i) ω) * heatP d σ c (X (w 0) ω - X (w r) ω) ∂μ)
        = ∫ u, heatP d σ r.val u * heatP d σ (n + 1 - r.val) u * heatP d σ c u
          ∂flatTorusMeasure d from h, Ch]

/-- The summand of `B`: `cycle(y_0..y_n) p(y_0 - y_q) (p(y_q - z) - 1)`, `q = n + 1`. -/
noncomputable def PhiB (d : ℕ) (σ : ℝ) (n : ℕ) (p : (Fin (n + 2) → FlatTorus d) × FlatTorus d) :
    ℝ :=
  cyT d σ (fun i : Fin (n + 1) => p.1 i.castSucc) * heatP d σ 1 (p.1 0 - p.1 (Fin.last (n + 1)))
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)) - p.2) - 1)

/-- The values `L_r` of `B`. -/
noncomputable def LB (d : ℕ) (σ : ℝ) (n : ℕ) (r : Fin (n + 2)) : ℝ :=
  if r = Fin.last (n + 1) then (torusM d σ 1 - 1) * torusM d σ (n + 1)
  else if r.val = 0 then (torusM d σ 2 - 1) * torusM d σ (n + 1)
  else Ch d σ (n + 1) r.val 2 - torusM d σ (n + 1)

/-- `∫ p(x - z) (p(z - y) - 1) dz = p_2(x - y) - 1`. -/
theorem tail_conv {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (x y : FlatTorus d) :
    ∫ z, heatP d σ 1 (x - z) * (heatP d σ 1 (z - y) - 1) ∂flatTorusMeasure d
      = heatP d σ 2 (x - y) - 1 := by
  have hint2 : Integrable (fun z => heatP d σ 1 (x - z) * heatP d σ 1 (z - y))
      (flatTorusMeasure d) :=
    Integrable.of_bound (((heatP_cont hσ d le_rfl).measurable.comp
      (measurable_const.sub measurable_id)).mul ((heatP_cont hσ d le_rfl).measurable.comp
      (measurable_id.sub measurable_const))).aestronglyMeasurable (torusM d σ 1 * torusM d σ 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatP_nonneg hσ d 1 _)
          (heatP_nonneg hσ d 1 _))]
        exact mul_le_mul (heatP_le hσ d le_rfl _) (heatP_le hσ d le_rfl _)
          (heatP_nonneg hσ d 1 _) (torusM_pos hσ d le_rfl).le)
  have e : ∀ z, heatP d σ 1 (x - z) * (heatP d σ 1 (z - y) - 1)
      = heatP d σ 1 (x - z) * heatP d σ 1 (z - y) - heatP d σ 1 (x - z) := fun z => by ring
  simp_rw [e]
  rw [integral_sub hint2 (p1_int hσ d x), heatP_semi hσ d le_rfl le_rfl x y,
    heatP_mass hσ d le_rfl x]

theorem LB_value {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {N n : ℕ} (w : Fin (n + 2) → Fin N)
    (hw : Injective w) (r : Fin (n + 2)) :
    ∫ ω, PhiB d σ n (fun i => X (w i) ω, X (w r) ω) ∂μ = LB d σ n r := by
  have hM := torusM_one_ge hσ d
  have hw' : Injective fun i : Fin (n + 1) => w i.castSucc :=
    fun a b h => Fin.castSucc_injective _ (hw h)
  have hu : ∀ i : Fin (n + 1), (w i.castSucc : ℕ) ≠ (w (Fin.last (n + 1)) : ℕ) := by
    intro i h
    exact Fin.castSucc_ne_last i (hw (Fin.ext h))
  have hcm := cyT_meas hσ d n
  have hp1m : Measurable fun p : FlatTorus d × FlatTorus d => heatP d σ 1 (p.1 - p.2) :=
    (heatP_cont hσ d le_rfl).measurable.comp (measurable_fst.sub measurable_snd)
  have hbd : ∀ (y : Fin (n + 1) → FlatTorus d) (a b e : FlatTorus d),
      |cyT d σ y * heatP d σ 1 (a - b) * (heatP d σ 1 (b - e) - 1)|
        ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    intro y a b e
    rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d y).1,
      abs_of_nonneg (heatP_nonneg hσ d 1 _)]
    exact mul_le_mul (mul_le_mul (cyT_bounds hσ d y).2 (heatP_le hσ d le_rfl _)
      (heatP_nonneg hσ d 1 _) (by positivity)) (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  have S := torusRK hσ d
  have hmean : ∫ ω, cyT d σ (fun i => X (w i.castSucc) ω) ∂μ = torusM d σ (n + 1) :=
    cycle_mean S X h_indep hX hlaw (fun i => (w i.castSucc : ℕ)) (fun a b h => hw' (Fin.ext h))
  induction r using Fin.lastCases with
  | last =>
    have e1 : ∀ ω, PhiB d σ n (fun i => X (w i) ω, X (w (Fin.last (n + 1))) ω)
        = (fun p : (Fin (n + 1) → FlatTorus d) × FlatTorus d =>
            cyT d σ p.1 * heatP d σ 1 (p.1 0 - p.2) * (torusM d σ 1 - 1))
          (fun i => X (w i.castSucc) ω, X (w (Fin.last (n + 1))) ω) := fun ω => by
      simp [PhiB, heatP_zero d σ le_rfl]
    simp_rw [e1]
    rw [integrate_extra X h_indep hX hlaw (fun i : Fin (n + 1) => (w i.castSucc : ℕ))
      (w (Fin.last (n + 1)) : ℕ) hu
      (fun p => cyT d σ p.1 * heatP d σ 1 (p.1 0 - p.2) * (torusM d σ 1 - 1))
      (((hcm.comp measurable_fst).mul (hp1m.comp (((measurable_pi_apply 0).comp
        measurable_fst).prodMk measurable_snd))).mul_const _)
      (B := torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1) (fun p => by
        have := hbd p.1 (p.1 0) p.2 p.2
        simpa [heatP_zero d σ le_rfl] using this)]
    have e2 : ∀ y : Fin (n + 1) → FlatTorus d,
        ∫ z, cyT d σ y * heatP d σ 1 (y 0 - z) * (torusM d σ 1 - 1) ∂flatTorusMeasure d
          = cyT d σ y * (torusM d σ 1 - 1) := by
      intro y
      have : ∀ z, cyT d σ y * heatP d σ 1 (y 0 - z) * (torusM d σ 1 - 1)
          = (cyT d σ y * (torusM d σ 1 - 1)) * heatP d σ 1 (y 0 - z) := fun z => by ring
      simp_rw [this]
      rw [integral_const_mul, heatP_mass hσ d le_rfl, mul_one]
    simp only [e2]
    rw [integral_mul_const, hmean, LB, if_pos rfl]
    ring
  | cast s =>
    have e1 : ∀ ω, PhiB d σ n (fun i => X (w i) ω, X (w s.castSucc) ω)
        = (fun p : (Fin (n + 1) → FlatTorus d) × FlatTorus d =>
            cyT d σ p.1 * heatP d σ 1 (p.1 0 - p.2) * (heatP d σ 1 (p.2 - p.1 s) - 1))
          (fun i => X (w i.castSucc) ω, X (w (Fin.last (n + 1))) ω) := fun ω => by
      simp [PhiB]
    simp_rw [e1]
    rw [integrate_extra X h_indep hX hlaw (fun i : Fin (n + 1) => (w i.castSucc : ℕ))
      (w (Fin.last (n + 1)) : ℕ) hu
      (fun p => cyT d σ p.1 * heatP d σ 1 (p.1 0 - p.2) * (heatP d σ 1 (p.2 - p.1 s) - 1))
      (((hcm.comp measurable_fst).mul (hp1m.comp (((measurable_pi_apply 0).comp
        measurable_fst).prodMk measurable_snd))).mul ((hp1m.comp (measurable_snd.prodMk
        ((measurable_pi_apply s).comp measurable_fst))).sub_const 1))
      (B := torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1) (fun p => hbd _ _ _ _)]
    have e2 : ∀ y : Fin (n + 1) → FlatTorus d,
        ∫ z, cyT d σ y * heatP d σ 1 (y 0 - z) * (heatP d σ 1 (z - y s) - 1) ∂flatTorusMeasure d
          = cyT d σ y * (heatP d σ 2 (y 0 - y s) - 1) := by
      intro y
      have : ∀ z, cyT d σ y * heatP d σ 1 (y 0 - z) * (heatP d σ 1 (z - y s) - 1)
          = cyT d σ y * (heatP d σ 1 (y 0 - z) * (heatP d σ 1 (z - y s) - 1)) := fun z => by ring
      simp_rw [this]
      rw [integral_const_mul, tail_conv hσ d]
    simp only [e2]
    have h := chordc_value hσ d X h_indep hX hlaw (fun i => w i.castSucc) hw' s 2 (by norm_num)
    rw [h, LB, if_neg (Fin.castSucc_ne_last s)]
    simp only [Fin.coe_castSucc]
    by_cases hs : s = 0
    · subst hs; simp
    · have hs' : s.val ≠ 0 := fun h => hs (Fin.ext h)
      simp [hs, hs']

end TorusB

open WalkCount Function BiasGeneral2 BiasGeneral3 PiBound CTG.Reals.TorusReduction

section TorusB2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem Ch_bounds {σ : ℝ} (hσ : 0 < σ) (d n r c : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) (hc : 1 ≤ c) :
    0 ≤ Ch d σ (n + 1) r c
      ∧ Ch d σ (n + 1) r c ≤ torusM d σ 1 * torusM d σ 1 * torusM d σ 1 := by
  have hM := torusM_one_ge hσ d
  have hpb : ∀ u, 0 ≤ heatP d σ r u * heatP d σ (n + 1 - r) u * heatP d σ c u
      ∧ heatP d σ r u * heatP d σ (n + 1 - r) u * heatP d σ c u
        ≤ torusM d σ 1 * torusM d σ 1 * torusM d σ 1 := by
    intro u
    have a1 : heatP d σ r u ≤ torusM d σ 1 :=
      (heatP_le hσ d hr1 u).trans (torusM_anti hσ d le_rfl hr1)
    have a2 : heatP d σ (n + 1 - r) u ≤ torusM d σ 1 :=
      (heatP_le hσ d (by omega) u).trans (torusM_anti hσ d le_rfl (by omega))
    have a3 : heatP d σ c u ≤ torusM d σ 1 :=
      (heatP_le hσ d hc u).trans (torusM_anti hσ d le_rfl hc)
    have b1 := heatP_nonneg hσ d r u
    have b2 := heatP_nonneg hσ d (n + 1 - r) u
    have b3 := heatP_nonneg hσ d c u
    exact ⟨mul_nonneg (mul_nonneg b1 b2) b3,
      mul_le_mul (mul_le_mul a1 a2 b2 (by linarith)) a3 b3 (by positivity)⟩
  have hint : Integrable (fun u => heatP d σ r u * heatP d σ (n + 1 - r) u * heatP d σ c u)
      (flatTorusMeasure d) :=
    Integrable.of_bound ((((heatP_cont hσ d hr1).measurable.mul
      (heatP_cont hσ d (by omega)).measurable).mul
      (heatP_cont hσ d hc).measurable).aestronglyMeasurable)
      (torusM d σ 1 * torusM d σ 1 * torusM d σ 1)
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpb u).1]; exact (hpb u).2)
  refine ⟨integral_nonneg fun u => (hpb u).1, ?_⟩
  unfold Ch
  calc ∫ u, heatP d σ r u * heatP d σ (n + 1 - r) u * heatP d σ c u ∂flatTorusMeasure d
      ≤ ∫ _u, torusM d σ 1 * torusM d σ 1 * torusM d σ 1 ∂flatTorusMeasure d :=
        integral_mono hint (integrable_const _) fun u => (hpb u).2
    _ = _ := by simp

theorem PhiB_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : Measurable (PhiB d σ n) := by
  unfold PhiB
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  exact (((cyT_meas hσ d n).comp (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i.castSucc).comp measurable_fst)).mul
    (hp.comp (((measurable_pi_apply 0).comp measurable_fst).sub
      ((measurable_pi_apply (Fin.last (n + 1))).comp measurable_fst)))).mul
    ((hp.comp (((measurable_pi_apply (Fin.last (n + 1))).comp measurable_fst).sub
      measurable_snd)).sub_const 1)

/-- **`E B` for every `k = n + 1`** (`B = N^{-k-2} ∑_{w=(v,q)} ∑_u cycle(X_v) p(X_{v_0} - X_q)
    c(X_q - X_u)`): `|E ∑_w ∑_u PhiB - N^{k+1} ∑_r L^B_r| ≤ 2 (k+1) M^{k+2} #Prs(k+1) N^k`,
    `∑_r L^B_r = (m₁ - 1) m_k + (m₂ - 1) m_k + ∑_{s=1}^{k-1} (∫ p_s p_{k-s} p₂ - m_k)`. -/
theorem meanB {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) :
    |∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∫ ω, PhiB d σ n (fun i => X (w i) ω, X u ω) ∂μ
        - (N : ℝ) ^ (n + 2) * ∑ r, LB d σ n r|
      ≤ 2 * ((n + 2 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1)
        * (((Prs (n + 2)).card : ℝ) * (N : ℝ) ^ (n + 2 - 1)) := by
  have hM := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have hB : ∀ p, |PhiB d σ n p| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    intro p
    unfold PhiB
    rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1,
      abs_of_nonneg (heatP_nonneg hσ d 1 _)]
    exact mul_le_mul (mul_le_mul (cyT_bounds hσ d _).2 (heatP_le hσ d le_rfl _)
      (heatP_nonneg hσ d 1 _) (by positivity)) (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  have hc : ∀ y, ∫ z, PhiB d σ n (y, z) ∂flatTorusMeasure d = 0 := by
    intro y
    simp only [PhiB]
    rw [integral_const_mul, integral_sub (p1_int hσ d _) (integrable_const 1),
      heatP_mass hσ d le_rfl]
    simp
  have hM3 : torusM d σ 1 * torusM d σ 1 * torusM d σ 1
      ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    have : torusM d σ 1 ≤ torusM d σ 1 ^ (n + 1) := le_self_pow₀ hM (by omega)
    have h2 := mul_le_mul_of_nonneg_right this (mul_nonneg hM0 hM0)
    nlinarith
  have hLb : ∀ r, |LB d σ n r| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    intro r
    have hm1 : torusM d σ (n + 1) ≤ torusM d σ 1 := torusM_anti hσ d le_rfl (by omega)
    have hm0 : 0 ≤ torusM d σ (n + 1) := (torusM_pos hσ d (by omega)).le
    have h21 : torusM d σ 2 ≤ torusM d σ 1 := torusM_anti hσ d le_rfl (by omega)
    have h20 : 1 ≤ torusM d σ 2 := torusM_ge_one hσ d (by omega)
    unfold LB
    split_ifs with h1 h2
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_le]; constructor <;> nlinarith
    · have hr1 : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr h2
      have hrn : r.val ≤ n := by
        have := r.isLt
        have : r.val ≠ n + 1 := fun h => h1 (Fin.ext (by simpa using h))
        omega
      obtain ⟨c0, cM⟩ := Ch_bounds hσ d n r.val 2 hr1 hrn (by norm_num)
      rw [abs_le]; constructor <;> nlinarith
  exact lin_stat_gen X h_indep hX hlaw N (n + 2) (PhiB d σ n) (PhiB_meas hσ d n)
    (by positivity) hB hc (LB d σ n) hLb (fun w hw r => LB_value hσ d X h_indep hX hlaw w hw r)

end TorusB2

open WalkCount Function BiasGeneral2 BiasGeneral3 PiBound CTG.Reals.TorusReduction

/-! ## (4b) on the flat torus: the statistic `∑_i (P̃^k)_ii ε_i²` for every `k` (a part of `Q₂`) -/

section TorusEE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The summand: `cycle(y) c(y_0 - z) c(y_0 - z')`. -/
noncomputable def PhiEE (d : ℕ) (σ : ℝ) (n : ℕ)
    (p : (Fin (n + 1) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cyT d σ p.1 * (heatP d σ 1 (p.1 0 - p.2.1) - 1) * (heatP d σ 1 (p.1 0 - p.2.2) - 1)

theorem PhiEE_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : Measurable (PhiEE d σ n) := by
  unfold PhiEE
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  exact (((cyT_meas hσ d n).comp measurable_fst).mul
    ((hp.comp (((measurable_pi_apply 0).comp measurable_fst).sub
      (measurable_fst.comp measurable_snd))).sub_const 1)).mul
    ((hp.comp (((measurable_pi_apply 0).comp measurable_fst).sub
      (measurable_snd.comp measurable_snd))).sub_const 1)

/-- `∫ (p(x - z) - 1)² dz = m₂ - 1`. -/
theorem csq_int {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (x : FlatTorus d) :
    ∫ z, (heatP d σ 1 (x - z) - 1) * (heatP d σ 1 (x - z) - 1) ∂flatTorusMeasure d
      = torusM d σ 2 - 1 := by
  have h := tail_conv hσ d x x
  rw [sub_self, heatP_zero d σ (by norm_num : 1 ≤ 2)] at h
  have e : ∀ z, (heatP d σ 1 (x - z) - 1) * (heatP d σ 1 (x - z) - 1)
      = heatP d σ 1 (x - z) * (heatP d σ 1 (z - x) - 1) - (heatP d σ 1 (x - z) - 1) := by
    intro z; rw [heatP_flip d σ 1 x z]; ring
  simp_rw [e]
  have hi : Integrable (fun z => heatP d σ 1 (x - z) * (heatP d σ 1 (z - x) - 1))
      (flatTorusMeasure d) := by
    refine Integrable.of_bound (((heatP_cont hσ d le_rfl).measurable.comp
      (measurable_const.sub measurable_id)).mul (((heatP_cont hσ d le_rfl).measurable.comp
      (measurable_id.sub measurable_const)).sub_const 1)).aestronglyMeasurable
      (torusM d σ 1 * torusM d σ 1) (Filter.Eventually.of_forall fun z => ?_)
    show |heatP d σ 1 (x - z) * (heatP d σ 1 (z - x) - 1)| ≤ _
    rw [abs_mul, abs_of_nonneg (heatP_nonneg hσ d 1 _)]
    exact mul_le_mul (heatP_le hσ d le_rfl _) (cK_bound hσ d _) (abs_nonneg _)
      (torusM_pos hσ d le_rfl).le
  have hj : Integrable (fun z => heatP d σ 1 (x - z) - 1) (flatTorusMeasure d) :=
    (p1_int hσ d x).sub (integrable_const 1)
  rw [integral_sub hi hj, h,
    integral_sub (p1_int hσ d x) (integrable_const 1), heatP_mass hσ d le_rfl]
  simp

/-- **`E ∑_w ∑_{u,u'} cycle · c · c` for every `k = n + 1`:**
    `|… - N^{k+1} (m₂ - 1) m_k| ≤ B ((k + k²) N^k + #Prs(k) N^{k-1} (2N + k²))`,
    `B = M^{k+2}`. -/
theorem meanEE {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) :
    |∑ w : Fin (n + 1) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiEE d σ n (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 1 + 1) * ((torusM d σ 2 - 1) * torusM d σ (n + 1))|
      ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1
        * ((((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 1)
          + ((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ (n + 1 - 1)
            * (2 * N + ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have hB : ∀ p, |PhiEE d σ n p| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    intro p
    unfold PhiEE
    rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1]
    exact mul_le_mul (mul_le_mul (cyT_bounds hσ d _).2 (cK_bound hσ d _) (abs_nonneg _)
      (by positivity)) (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  have hc1 : ∀ y z', ∫ z, PhiEE d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    simp only [PhiEE]
    have : ∀ z, cyT d σ y * (heatP d σ 1 (y 0 - z) - 1) * (heatP d σ 1 (y 0 - z') - 1)
        = (cyT d σ y * (heatP d σ 1 (y 0 - z') - 1)) * (heatP d σ 1 (y 0 - z) - 1) :=
      fun z => by ring
    simp_rw [this]
    rw [integral_const_mul, integral_sub (p1_int hσ d _) (integrable_const 1),
      heatP_mass hσ d le_rfl]
    simp
  have hc2 : ∀ y z, ∫ z', PhiEE d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    simp only [PhiEE]
    rw [integral_const_mul, integral_sub (p1_int hσ d _) (integrable_const 1),
      heatP_mass hσ d le_rfl]
    simp
  have hm1 : torusM d σ (n + 1) ≤ torusM d σ 1 := torusM_anti hσ d le_rfl (by omega)
  have hm0 : 0 ≤ torusM d σ (n + 1) := (torusM_pos hσ d (by omega)).le
  have h21 : torusM d σ 2 ≤ torusM d σ 1 := torusM_anti hσ d le_rfl (by omega)
  have h20 : 1 ≤ torusM d σ 2 := torusM_ge_one hσ d (by omega)
  have hMk : torusM d σ 1 ≤ torusM d σ 1 ^ (n + 1) := le_self_pow₀ hM (by omega)
  have hLb : |(torusM d σ 2 - 1) * torusM d σ (n + 1)|
      ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    rw [abs_le]; constructor <;> nlinarith [mul_le_mul_of_nonneg_right hMk (mul_nonneg hM0 hM0)]
  have hL : ∀ w : Fin (n + 1) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiEE d σ n (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = (torusM d σ 2 - 1) * torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    have e1 : ∀ ω, PhiEE d σ n (fun i => X (w i) ω, X u ω, X u ω)
        = (fun p : (Fin (n + 1) → FlatTorus d) × FlatTorus d =>
            cyT d σ p.1 * ((heatP d σ 1 (p.1 0 - p.2) - 1) * (heatP d σ 1 (p.1 0 - p.2) - 1)))
          (fun i => X (w i) ω, X u ω) := fun ω => by simp only [PhiEE]; ring
    simp_rw [e1]
    have hp := (heatP_cont hσ d (le_refl 1)).measurable
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => cyT d σ p.1 * ((heatP d σ 1 (p.1 0 - p.2) - 1) * (heatP d σ 1 (p.1 0 - p.2) - 1)))
      (((cyT_meas hσ d n).comp measurable_fst).mul
        (((hp.comp (((measurable_pi_apply 0).comp measurable_fst).sub measurable_snd)).sub_const 1).mul
          ((hp.comp (((measurable_pi_apply 0).comp measurable_fst).sub measurable_snd)).sub_const 1)))
      (B := torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1) (fun p => by
        rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1, ← mul_assoc]
        exact mul_le_mul (mul_le_mul (cyT_bounds hσ d _).2 (cK_bound hσ d _) (abs_nonneg _)
          (by positivity)) (cK_bound hσ d _) (abs_nonneg _) (by positivity))]
    simp only [integral_const_mul, csq_int hσ d]
    rw [integral_mul_const]
    have hmean := cycle_mean (torusRK hσ d) X h_indep hX hlaw (fun i => (w i : ℕ))
      (fun a b h => hw (Fin.ext h))
    rw [show ∫ ω, cyT d σ (fun i => X (w i) ω) ∂μ = torusM d σ (n + 1) from hmean]
    ring
  exact quad_stat_gen X h_indep hX hlaw N (n + 1) (PhiEE d σ n) (PhiEE_meas hσ d n)
    (by positivity) hB hc1 hc2 _ hLb hL

end TorusEE

end BiasGeneral4

namespace BiasGeneral5

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

/-! # A100: `prop:bias` for every `k`, the rest of Point 4 -/

section Tools

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]

theorem snoc_meas {m : ℕ} : Measurable fun p : (Fin m → G) × G => (Fin.snoc p.1 p.2 : Fin (m + 1) → G) := by
  refine measurable_pi_lambda _ fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa [Fin.snoc_last] using measurable_snd
  | cast j => simpa [Fin.snoc_castSucc] using (measurable_pi_apply j).comp measurable_fst

/-- Integrate the last point of an injective tuple first. -/
theorem int_last (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) {N m : ℕ}
    (w : Fin (m + 1) → Fin N) (hw : Injective w) (F : (Fin (m + 1) → G) → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : ∀ y, |F y| ≤ B) :
    ∫ ω, F (fun i => X (w i) ω) ∂μ
      = ∫ ω, (∫ z, F (Fin.snoc (fun i : Fin m => X (w i.castSucc) ω) z) ∂ν) ∂μ := by
  have hu : ∀ i : Fin m, (w i.castSucc : ℕ) ≠ (w (Fin.last m) : ℕ) :=
    fun i h => Fin.castSucc_ne_last i (hw (Fin.ext h))
  have h := integrate_extra X h_indep hX hlaw (fun i : Fin m => (w i.castSucc : ℕ))
    (w (Fin.last m) : ℕ) hu (fun p => F (Fin.snoc p.1 p.2)) (hF.comp snoc_meas) (B := B)
    (fun p => hB _)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show F (fun i => X (w i) ω) = F (Fin.snoc (fun i : Fin m => X (w i.castSucc) ω) (X (w (Fin.last m)) ω))
  congr 1
  exact (Fin.snoc_init_self (fun i => X (w i) ω)).symm

end Tools

section Conv

theorem cont_int {d : ℕ} {f : FlatTorus d → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
    Integrable f (flatTorusMeasure d) :=
  Integrable.of_bound hf.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hC z)

theorem hP_abs {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {k : ℕ} (hk : 1 ≤ k) (u : FlatTorus d) :
    |heatP d σ k u| ≤ torusM d σ 1 := by
  rw [abs_of_nonneg (heatP_nonneg hσ d k u)]
  exact (heatP_le hσ d hk u).trans (torusM_anti hσ d le_rfl hk)

/-- `∫ p(a - z) (p_k(b - z) - 1) dz = p_{k+1}(a - b) - 1`. -/
theorem conv_pk {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {k : ℕ} (hk : 1 ≤ k) (a b : FlatTorus d) :
    ∫ z, heatP d σ 1 (a - z) * (heatP d σ k (b - z) - 1) ∂flatTorusMeasure d
      = heatP d σ (k + 1) (a - b) - 1 := by
  have hM := torusM_one_ge hσ d
  have c1 : Continuous fun z : FlatTorus d => heatP d σ 1 (a - z) :=
    (heatP_cont hσ d le_rfl).comp (continuous_const.sub continuous_id)
  have ck : Continuous fun z : FlatTorus d => heatP d σ k (z - b) :=
    (heatP_cont hσ d hk).comp (continuous_id.sub continuous_const)
  have e : ∀ z, heatP d σ 1 (a - z) * (heatP d σ k (b - z) - 1)
      = heatP d σ 1 (a - z) * heatP d σ k (z - b) - heatP d σ 1 (a - z) := fun z => by
    rw [heatP_flip d σ k b z]; ring
  simp_rw [e]
  have i1 : Integrable (fun z => heatP d σ 1 (a - z) * heatP d σ k (z - b)) (flatTorusMeasure d) :=
    cont_int (c1.mul ck) (C := torusM d σ 1 * torusM d σ 1) fun z => by
      rw [abs_mul]; exact mul_le_mul (hP_abs hσ d le_rfl _) (hP_abs hσ d hk _) (abs_nonneg _)
        (by linarith)
  have i2 : Integrable (fun z => heatP d σ 1 (a - z)) (flatTorusMeasure d) :=
    cont_int c1 (C := torusM d σ 1) fun z => hP_abs hσ d le_rfl _
  rw [integral_sub i1 i2,
    heatP_semi hσ d le_rfl hk a b, heatP_mass hσ d le_rfl a, add_comm]

/-- `∫ (p(a - z) - 1)(p(b - z) - 1) dz = p₂(a - b) - 1`. -/
theorem conv_cc {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (a b : FlatTorus d) :
    ∫ z, (heatP d σ 1 (a - z) - 1) * (heatP d σ 1 (b - z) - 1) ∂flatTorusMeasure d
      = heatP d σ 2 (a - b) - 1 := by
  have hM := torusM_one_ge hσ d
  have c1 : Continuous fun z : FlatTorus d => heatP d σ 1 (a - z) :=
    (heatP_cont hσ d le_rfl).comp (continuous_const.sub continuous_id)
  have cb : Continuous fun z : FlatTorus d => heatP d σ 1 (b - z) :=
    (heatP_cont hσ d le_rfl).comp (continuous_const.sub continuous_id)
  have e : ∀ z, (heatP d σ 1 (a - z) - 1) * (heatP d σ 1 (b - z) - 1)
      = heatP d σ 1 (a - z) * (heatP d σ 1 (b - z) - 1) - (heatP d σ 1 (b - z) - 1) :=
    fun z => by ring
  simp_rw [e]
  have h1 := conv_pk hσ d (le_refl 1) a b
  have i1 : Integrable (fun z => heatP d σ 1 (a - z) * (heatP d σ 1 (b - z) - 1))
      (flatTorusMeasure d) :=
    cont_int (c1.mul (cb.sub continuous_const)) (C := torusM d σ 1 * torusM d σ 1) fun z => by
      rw [abs_mul]; exact mul_le_mul (hP_abs hσ d le_rfl _) (cK_bound hσ d _) (abs_nonneg _)
        (by linarith)
  have i2 : Integrable (fun z => heatP d σ 1 (b - z) - 1) (flatTorusMeasure d) :=
    cont_int (cb.sub continuous_const) (C := torusM d σ 1) fun z => cK_bound hσ d _
  have i3 : Integrable (fun z => heatP d σ 1 (b - z)) (flatTorusMeasure d) :=
    cont_int cb (C := torusM d σ 1) fun z => hP_abs hσ d le_rfl _
  rw [integral_sub i1 i2, h1, integral_sub i3 (integrable_const 1), heatP_mass hσ d le_rfl]
  simp

/-- `∫ p(a - z) dz = 1`, in the `heatP` notation. -/
theorem mass1 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (a : FlatTorus d) :
    ∫ z, heatP d σ 1 (a - z) ∂flatTorusMeasure d = 1 := heatP_mass hσ d le_rfl a

end Conv

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

/-! ## The three remaining parts of `Q₂` for every `k` -/

section Q2rest

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem cent {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (K : ℝ) (a : FlatTorus d) :
    ∫ z, K * (heatP d σ 1 (a - z) - 1) ∂flatTorusMeasure d = 0 := by
  rw [integral_const_mul, integral_sub (p1_int hσ d a) (integrable_const 1), mass1 hσ d]
  simp

theorem bd3 {M C a b e f : ℝ} (hM : 1 ≤ M) (hC0 : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a ≤ C)
    (h1 : |b| ≤ M) (h2 : |e| ≤ M) (h3 : |f| ≤ M) : |a * b * e * f| ≤ C * M ^ 4 := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0]
  have hM0 : 0 ≤ M := by linarith
  have : a * |b| * |e| * |f| ≤ C * M * M * M :=
    mul_le_mul (mul_le_mul (mul_le_mul ha h1 (abs_nonneg _) hC0) h2 (abs_nonneg _)
      (by positivity)) h3 (abs_nonneg _) (by positivity)
  have hM4 : C * M * M * M ≤ C * M ^ 4 := by
    have : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left this hC0]
  linarith

theorem bd4 {M C a b e f g : ℝ} (hM : 1 ≤ M) (hC0 : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a ≤ C)
    (h1 : |b| ≤ M) (h2 : |e| ≤ M) (h3 : |f| ≤ M) (h4 : |g| ≤ M) :
    |a * b * e * f * g| ≤ C * M ^ 4 := by
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0]
  have hM0 : 0 ≤ M := by linarith
  have : a * |b| * |e| * |f| * |g| ≤ C * M * M * M * M :=
    mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul ha h1 (abs_nonneg _) hC0) h2 (abs_nonneg _)
      (by positivity)) h3 (abs_nonneg _) (by positivity)) h4 (abs_nonneg _) (by positivity)
  nlinarith

theorem bd2 {M C a b e : ℝ} (hM : 1 ≤ M) (hC0 : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a ≤ C)
    (h1 : |b| ≤ M) (h2 : |e| ≤ M) : |a * b * e| ≤ C * M ^ 4 := by
  rw [abs_mul, abs_mul, abs_of_nonneg ha0]
  have hM0 : 0 ≤ M := by linarith
  have : a * |b| * |e| ≤ C * M * M :=
    mul_le_mul (mul_le_mul ha h1 (abs_nonneg _) hC0) h2 (abs_nonneg _) (by positivity)
  have hM4 : C * M * M ≤ C * M ^ 4 := by
    have : M ^ 2 ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left this hC0]
  linarith

theorem cKc_bound {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {c : ℕ} (hc : 1 ≤ c) (u : FlatTorus d) :
    |heatP d σ c u - 1| ≤ torusM d σ 1 := by
  have h0 := heatP_nonneg hσ d c u
  have h1 := (heatP_le hσ d hc u).trans (torusM_anti hσ d le_rfl hc)
  have hM := torusM_one_ge hσ d
  rw [abs_le]; constructor <;> linarith

/-- The cycle part of a tuple `(v, q)`. -/
noncomputable def cy2 (d : ℕ) (σ : ℝ) {n : ℕ} (y : Fin (n + 2) → FlatTorus d) : ℝ :=
  cyT d σ (fun a : Fin (n + 1) => y a.castSucc)

theorem cy2_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) :
    Measurable fun y : Fin (n + 2) → FlatTorus d => cy2 d σ y :=
  (cyT_meas hσ d n).comp (measurable_pi_lambda _ fun a => measurable_pi_apply _)

/-- `(P̃ε²)_i`: `cycle · p(x₀ - x_q) c(x_q - z) c(x_q - z')`. -/
noncomputable def PhiS (d : ℕ) (σ : ℝ) (n : ℕ)
    (p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cy2 d σ p.1 * heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc - p.1 (Fin.last (n + 1)))
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)) - p.2.1) - 1)
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)) - p.2.2) - 1)

/-- `ε_i (P̃ε)_i`: `cycle · c(x₀ - z) p(x₀ - x_q) c(x_q - z')`. -/
noncomputable def PhiEB (d : ℕ) (σ : ℝ) (n : ℕ)
    (p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cy2 d σ p.1 * (heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc - p.2.1) - 1)
    * heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc - p.1 (Fin.last (n + 1)))
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)) - p.2.2) - 1)

/-- `E[cycle · p(x₀ - x_q) · g]` after integrating the tail point `q`:
    `E[cy2(X_w) p(x₀ - x_q) (p_c(x₀ - x_q) - 1)] = (m_{c+1} - 1) m_k`; for `c = 0` (no
    factor) the value is `m_k`. -/
theorem tail_mean {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {N n : ℕ} (w : Fin (n + 2) → Fin N)
    (hw : Injective w) (c : ℕ) (hc : 1 ≤ c) :
    ∫ ω, cy2 d σ (fun i => X (w i) ω)
        * heatP d σ 1 (X (w (0 : Fin (n + 1)).castSucc) ω - X (w (Fin.last (n + 1))) ω)
        * (heatP d σ c (X (w (0 : Fin (n + 1)).castSucc) ω - X (w (Fin.last (n + 1))) ω) - 1) ∂μ
      = (torusM d σ (c + 1) - 1) * torusM d σ (n + 1) := by
  have hM := torusM_one_ge hσ d
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have hpc := (heatP_cont hσ d hc).measurable
  have hF : Measurable fun y : Fin (n + 2) → FlatTorus d => cy2 d σ y
      * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
      * (heatP d σ c (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))) - 1) :=
    ((cy2_meas hσ d n).mul (hp.comp ((measurable_pi_apply (0 : Fin (n + 1)).castSucc).sub (measurable_pi_apply (Fin.last (n + 1)))))).mul
      ((hpc.comp ((measurable_pi_apply (0 : Fin (n + 1)).castSucc).sub (measurable_pi_apply (Fin.last (n + 1))))).sub_const 1)
  have h := int_last X h_indep hX hlaw w hw _ hF (B := torusM d σ 1 ^ (n + 1) * torusM d σ 1 ^ 4)
    (fun y => bd2 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2
      (hP_abs hσ d le_rfl _) (cKc_bound hσ d hc _))
  rw [h]
  have e : ∀ (y' : Fin (n + 1) → FlatTorus d), ∫ z, cy2 d σ (Fin.snoc y' z : Fin (n + 2) → _)
      * heatP d σ 1 ((Fin.snoc y' z : Fin (n + 2) → _) (0 : Fin (n + 1)).castSucc
          - (Fin.snoc y' z : Fin (n + 2) → _) (Fin.last (n + 1)))
      * (heatP d σ c ((Fin.snoc y' z : Fin (n + 2) → _) (0 : Fin (n + 1)).castSucc
          - (Fin.snoc y' z : Fin (n + 2) → _) (Fin.last (n + 1))) - 1) ∂flatTorusMeasure d
      = cyT d σ y' * (torusM d σ (c + 1) - 1) := by
    intro y'
    simp only [cy2, Fin.snoc_castSucc, Fin.snoc_last]
    have : ∀ z, cyT d σ y' * heatP d σ 1 (y' 0 - z) * (heatP d σ c (y' 0 - z) - 1)
        = cyT d σ y' * (heatP d σ 1 (y' 0 - z) * (heatP d σ c (y' 0 - z) - 1)) :=
      fun z => by ring
    simp_rw [this]
    rw [integral_const_mul, conv_pk hσ d hc, sub_self, heatP_zero d σ (by omega)]
  simp only [e]
  rw [integral_mul_const]
  have hmean := cycle_mean (torusRK hσ d) X h_indep hX hlaw (fun i : Fin (n + 1) => (w i.castSucc : ℕ))
    (fun a b h => Fin.castSucc_injective _ (hw (Fin.ext h)))
  rw [show ∫ ω, cyT d σ (fun i : Fin (n + 1) => X (w i.castSucc) ω) ∂μ = torusM d σ (n + 1)
    from hmean]
  ring

end Q2rest

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

section Q2stats

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem tail_mean0 {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {N n : ℕ} (w : Fin (n + 2) → Fin N)
    (hw : Injective w) :
    ∫ ω, cy2 d σ (fun i => X (w i) ω)
        * heatP d σ 1 (X (w (0 : Fin (n + 1)).castSucc) ω - X (w (Fin.last (n + 1))) ω) ∂μ
      = torusM d σ (n + 1) := by
  have hM := torusM_one_ge hσ d
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have hF : Measurable fun y : Fin (n + 2) → FlatTorus d => cy2 d σ y
      * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))) :=
    (cy2_meas hσ d n).mul (hp.comp ((measurable_pi_apply (0 : Fin (n + 1)).castSucc).sub (measurable_pi_apply (Fin.last (n + 1)))))
  have h := int_last X h_indep hX hlaw w hw _ hF (B := torusM d σ 1 ^ (n + 1) * torusM d σ 1 ^ 4)
    (fun y => by
      simp only [cy2]
      rw [abs_mul, abs_of_nonneg (cyT_bounds hσ d (fun a : Fin (n + 1) => y a.castSucc)).1]
      have h1 := (cyT_bounds hσ d (fun a : Fin (n + 1) => y a.castSucc)).2
      have h2 := hP_abs hσ d le_rfl (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
      have h4 : torusM d σ 1 ≤ torusM d σ 1 ^ 4 := le_self_pow₀ hM (by norm_num)
      calc _ ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity))
  rw [h]
  have e : ∀ (y' : Fin (n + 1) → FlatTorus d), ∫ z, cy2 d σ (Fin.snoc y' z : Fin (n + 2) → _)
      * heatP d σ 1 ((Fin.snoc y' z : Fin (n + 2) → _) (0 : Fin (n + 1)).castSucc
          - (Fin.snoc y' z : Fin (n + 2) → _) (Fin.last (n + 1))) ∂flatTorusMeasure d
      = cyT d σ y' := by
    intro y'
    simp only [cy2, Fin.snoc_castSucc, Fin.snoc_last]
    rw [integral_const_mul, mass1 hσ d, mul_one]
  simp only [e]
  exact cycle_mean (torusRK hσ d) X h_indep hX hlaw (fun i : Fin (n + 1) => (w i.castSucc : ℕ))
    (fun a b h => Fin.castSucc_injective _ (hw (Fin.ext h)))

theorem PhiS_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : Measurable (PhiS d σ n) := by
  unfold PhiS
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have a0 : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (0 : Fin (n + 1)).castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 1)) := (measurable_pi_apply _).comp measurable_fst
  exact ((((cy2_meas hσ d n).comp measurable_fst).mul (hp.comp (a0.sub aq))).mul
    ((hp.comp (aq.sub (measurable_fst.comp measurable_snd))).sub_const 1)).mul
    ((hp.comp (aq.sub (measurable_snd.comp measurable_snd))).sub_const 1)

theorem PhiEB_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : Measurable (PhiEB d σ n) := by
  unfold PhiEB
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have a0 : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (0 : Fin (n + 1)).castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 1)) := (measurable_pi_apply _).comp measurable_fst
  exact ((((cy2_meas hσ d n).comp measurable_fst).mul ((hp.comp
    (a0.sub (measurable_fst.comp measurable_snd))).sub_const 1)).mul
    (hp.comp (a0.sub aq))).mul
    ((hp.comp (aq.sub (measurable_snd.comp measurable_snd))).sub_const 1)

/-- The common constant of the bounds: `B = M^{k} M^4`. -/
noncomputable def B4 (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ := torusM d σ 1 ^ (n + 1) * torusM d σ 1 ^ 4

theorem B4_nonneg {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : 0 ≤ B4 d σ n := by
  have := torusM_one_ge hσ d; unfold B4; positivity

theorem m_bound {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) {c : ℕ} (hc : 1 ≤ c) :
    |(torusM d σ c - 1) * torusM d σ (n + 1)| ≤ B4 d σ n := by
  have hM := torusM_one_ge hσ d
  have hm1 : torusM d σ (n + 1) ≤ torusM d σ 1 := torusM_anti hσ d le_rfl (by omega)
  have hm0 : 0 ≤ torusM d σ (n + 1) := (torusM_pos hσ d (by omega)).le
  have hc1 : torusM d σ c ≤ torusM d σ 1 := torusM_anti hσ d le_rfl hc
  have hc0 : 1 ≤ torusM d σ c := torusM_ge_one hσ d hc
  have hM2 : torusM d σ 1 * torusM d σ 1 ≤ B4 d σ n := by
    unfold B4
    have h1 : torusM d σ 1 ^ 2 ≤ torusM d σ 1 ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    have h2 : 1 ≤ torusM d σ 1 ^ (n + 1) := one_le_pow₀ hM
    nlinarith
  rw [abs_le]; constructor <;> nlinarith

/-- **`E ∑ (P̃ε²)-statistic` for every `k = n + 1`:** main term `N^{k+2} (m₂ - 1) m_k`. -/
theorem meanS {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) :
    |∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiS d σ n (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 2 + 1) * ((torusM d σ 2 - 1) * torusM d σ (n + 1))|
      ≤ B4 d σ n * ((((n + 2 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 2)
          + ((Prs (n + 2)).card : ℝ) * (N : ℝ) ^ (n + 2 - 1) * (2 * N + ((n + 2 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiS d σ n p| ≤ B4 d σ n := fun p =>
    bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (cK_bound hσ d _)
  have hc1 : ∀ y z', ∫ z, PhiS d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    have e : (fun z => PhiS d σ n (y, z, z')) = fun z => (cy2 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z') - 1))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1) := funext fun z => by simp only [PhiS]; ring
    rw [e, cent hσ d]
  have hc2 : ∀ y z, ∫ z', PhiS d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    have e : (fun z' => PhiS d σ n (y, z, z')) = fun z' => (cy2 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z') - 1) := funext fun z' => by simp only [PhiS]
    rw [e, cent hσ d]
  have hL : ∀ w : Fin (n + 2) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiS d σ n (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = (torusM d σ 2 - 1) * torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => PhiS d σ n (p.1, p.2, p.2))
      ((PhiS_meas hσ d n).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)))
      (B := B4 d σ n) (fun p => hB _)]
    have e : ∀ y : Fin (n + 2) → FlatTorus d, ∫ z, PhiS d σ n (y, z, z) ∂flatTorusMeasure d
        = cy2 d σ y * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
          * (torusM d σ 2 - 1) := by
      intro y
      have e1 : (fun z => PhiS d σ n (y, z, z)) = fun z => (cy2 d σ y
          * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))))
          * ((heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1)
            * (heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1)) := funext fun z => by
        simp only [PhiS]; ring
      rw [e1, integral_const_mul, csq_int hσ d]
    simp only [e]
    rw [integral_mul_const, tail_mean0 hσ d X h_indep hX hlaw w hw]
    ring
  exact quad_stat_gen X h_indep hX hlaw N (n + 2) (PhiS d σ n) (PhiS_meas hσ d n)
    (B4_nonneg hσ d n) hB hc1 hc2 _ (m_bound hσ d n (by norm_num)) hL

/-- **`E ∑ ε(P̃ε)-statistic` for every `k = n + 1`:** main term `N^{k+2} (m₃ - 1) m_k`. -/
theorem meanEB {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) :
    |∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiEB d σ n (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 2 + 1) * ((torusM d σ 3 - 1) * torusM d σ (n + 1))|
      ≤ B4 d σ n * ((((n + 2 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 2)
          + ((Prs (n + 2)).card : ℝ) * (N : ℝ) ^ (n + 2 - 1) * (2 * N + ((n + 2 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiEB d σ n p| ≤ B4 d σ n := fun p =>
    bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (cK_bound hσ d _)
      (hP_abs hσ d le_rfl _) (cK_bound hσ d _)
  have hc1 : ∀ y z', ∫ z, PhiEB d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    have e : (fun z => PhiEB d σ n (y, z, z')) = fun z => (cy2 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z') - 1))
        * (heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - z) - 1) := funext fun z => by
      simp only [PhiEB]; ring
    rw [e, cent hσ d]
  have hc2 : ∀ y z, ∫ z', PhiEB d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    have e : (fun z' => PhiEB d σ n (y, z, z')) = fun z' => (cy2 d σ y
        * (heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - z) - 1)
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z') - 1) := funext fun z' => by simp only [PhiEB]
    rw [e, cent hσ d]
  have hL : ∀ w : Fin (n + 2) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiEB d σ n (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = (torusM d σ 3 - 1) * torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => PhiEB d σ n (p.1, p.2, p.2))
      ((PhiEB_meas hσ d n).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)))
      (B := B4 d σ n) (fun p => hB _)]
    have e : ∀ y : Fin (n + 2) → FlatTorus d, ∫ z, PhiEB d σ n (y, z, z) ∂flatTorusMeasure d
        = cy2 d σ y * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
          * (heatP d σ 2 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))) - 1) := by
      intro y
      have e1 : (fun z => PhiEB d σ n (y, z, z)) = fun z => (cy2 d σ y
          * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))))
          * ((heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - z) - 1)
            * (heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1)) := funext fun z => by
        simp only [PhiEB]; ring
      rw [e1, integral_const_mul, conv_cc hσ d]
    simp only [e]
    exact tail_mean hσ d X h_indep hX hlaw w hw 2 (by norm_num)
  exact quad_stat_gen X h_indep hX hlaw N (n + 2) (PhiEB d σ n) (PhiEB_meas hσ d n)
    (B4_nonneg hσ d n) hB hc1 hc2 _ (m_bound hσ d n (by norm_num)) hL

end Q2stats

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

section Q2BB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The cycle part of a tuple `(v, q, q')`. -/
noncomputable def cy3 (d : ℕ) (σ : ℝ) {n : ℕ} (y : Fin (n + 3) → FlatTorus d) : ℝ :=
  cyT d σ (fun a : Fin (n + 1) => y a.castSucc.castSucc)

theorem cy3_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) :
    Measurable fun y : Fin (n + 3) → FlatTorus d => cy3 d σ y :=
  (cyT_meas hσ d n).comp (measurable_pi_lambda _ fun a => measurable_pi_apply _)

/-- `(P̃ε)_i²`: `cycle · p(x₀ - x_q) c(x_q - z) p(x₀ - x_{q'}) c(x_{q'} - z')`. -/
noncomputable def PhiBB (d : ℕ) (σ : ℝ) (n : ℕ)
    (p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cy3 d σ p.1 * heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc.castSucc - p.1 (Fin.last (n + 1)).castSucc)
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)).castSucc - p.2.1) - 1)
    * heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc.castSucc - p.1 (Fin.last (n + 2)))
    * (heatP d σ 1 (p.1 (Fin.last (n + 2)) - p.2.2) - 1)

theorem PhiBB_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : Measurable (PhiBB d σ n) := by
  unfold PhiBB
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have a0 : Measurable fun p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (0 : Fin (n + 1)).castSucc.castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq : Measurable fun p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 1)).castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq' : Measurable fun p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 2)) := (measurable_pi_apply _).comp measurable_fst
  exact (((((cy3_meas hσ d n).comp measurable_fst).mul (hp.comp (a0.sub aq))).mul
    ((hp.comp (aq.sub (measurable_fst.comp measurable_snd))).sub_const 1)).mul
    (hp.comp (a0.sub aq'))).mul
    ((hp.comp (aq'.sub (measurable_snd.comp measurable_snd))).sub_const 1)

/-- **`E ∑ (P̃ε)²-statistic` for every `k = n + 1`:** main term `N^{k+3} (m₄ - 1) m_k`. -/
theorem meanBB {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) :
    |∑ w : Fin (n + 3) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiBB d σ n (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 3 + 1) * ((torusM d σ 4 - 1) * torusM d σ (n + 1))|
      ≤ B4 d σ n * ((((n + 3 : ℕ) : ℝ) + ((n + 3 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 3)
          + ((Prs (n + 3)).card : ℝ) * (N : ℝ) ^ (n + 3 - 1) * (2 * N + ((n + 3 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have hB : ∀ p, |PhiBB d σ n p| ≤ B4 d σ n := fun p =>
    bd4 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (hP_abs hσ d le_rfl _) (cK_bound hσ d _)
  have hc1 : ∀ y z', ∫ z, PhiBB d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    have e : (fun z => PhiBB d σ n (y, z, z')) = fun z => (cy3 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 2)))
        * (heatP d σ 1 (y (Fin.last (n + 2)) - z') - 1))
        * (heatP d σ 1 (y (Fin.last (n + 1)).castSucc - z) - 1) := funext fun z => by
      simp only [PhiBB]; ring
    rw [e, cent hσ d]
  have hc2 : ∀ y z, ∫ z', PhiBB d σ n (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    have e : (fun z' => PhiBB d σ n (y, z, z')) = fun z' => (cy3 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
        * (heatP d σ 1 (y (Fin.last (n + 1)).castSucc - z) - 1)
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 2))))
        * (heatP d σ 1 (y (Fin.last (n + 2)) - z') - 1) := funext fun z' => by
      simp only [PhiBB]
    rw [e, cent hσ d]
  have hL : ∀ w : Fin (n + 3) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiBB d σ n (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = (torusM d σ 4 - 1) * torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => PhiBB d σ n (p.1, p.2, p.2))
      ((PhiBB_meas hσ d n).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)))
      (B := B4 d σ n) (fun p => hB _)]
    obtain ⟨F, hFd⟩ : ∃ F : (Fin (n + 3) → FlatTorus d) → ℝ, F = fun y => cy3 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 2)))
        * (heatP d σ 2 (y (Fin.last (n + 1)).castSucc - y (Fin.last (n + 2))) - 1) := ⟨_, rfl⟩
    have e : ∀ y : Fin (n + 3) → FlatTorus d, ∫ z, PhiBB d σ n (y, z, z) ∂flatTorusMeasure d
        = F y := by
      intro y
      have e1 : (fun z => PhiBB d σ n (y, z, z)) = fun z => (cy3 d σ y
          * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
          * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 2))))
          * ((heatP d σ 1 (y (Fin.last (n + 1)).castSucc - z) - 1)
            * (heatP d σ 1 (y (Fin.last (n + 2)) - z) - 1)) := funext fun z => by
        simp only [PhiBB]; ring
      rw [e1, integral_const_mul, conv_cc hσ d, hFd]
    simp only [e]
    have hF : Measurable F := by
      rw [hFd]
      have hp2 := (heatP_cont hσ d (by norm_num : 1 ≤ 2)).measurable
      exact (((cy3_meas hσ d n).mul (hp.comp ((measurable_pi_apply _).sub (measurable_pi_apply _)))).mul
        (hp.comp ((measurable_pi_apply _).sub (measurable_pi_apply _)))).mul
        ((hp2.comp ((measurable_pi_apply (Fin.last (n + 1)).castSucc).sub
          (measurable_pi_apply (Fin.last (n + 2))))).sub_const 1)
    rw [int_last X h_indep hX hlaw w hw F hF (B := B4 d σ n) (fun y => by
      rw [hFd]
      exact bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2
        (hP_abs hσ d le_rfl _) (hP_abs hσ d le_rfl _) (cKc_bound hσ d (by norm_num) _))]
    have e2 : ∀ y' : Fin (n + 2) → FlatTorus d,
        ∫ z, F (Fin.snoc y' z) ∂flatTorusMeasure d
          = cy2 d σ y' * heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - y' (Fin.last (n + 1)))
            * (heatP d σ 3 (y' (0 : Fin (n + 1)).castSucc - y' (Fin.last (n + 1))) - 1) := by
      intro y'
      rw [hFd]
      simp only [cy3, cy2, Fin.snoc_castSucc, Fin.snoc_last]
      have : ∀ z, cyT d σ (fun a : Fin (n + 1) => y' a.castSucc)
          * heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - y' (Fin.last (n + 1)))
          * heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - z)
          * (heatP d σ 2 (y' (Fin.last (n + 1)) - z) - 1)
          = (cyT d σ (fun a : Fin (n + 1) => y' a.castSucc)
            * heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - y' (Fin.last (n + 1))))
            * (heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - z)
              * (heatP d σ 2 (y' (Fin.last (n + 1)) - z) - 1)) := fun z => by ring
      simp_rw [this]
      rw [integral_const_mul, conv_pk hσ d (by norm_num : 1 ≤ 2)]
    simp only [e2]
    exact tail_mean hσ d X h_indep hX hlaw (fun i => w i.castSucc)
      (fun a b h => Fin.castSucc_injective _ (hw h)) 3 (by norm_num)
  exact quad_stat_gen X h_indep hX hlaw N (n + 3) (PhiBB d σ n) (PhiBB_meas hσ d n)
    (B4_nonneg hσ d n) hB hc1 hc2 _ (m_bound hσ d n (by norm_num)) hL

end Q2BB

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

/-! ## `Q₃` for every `k`: the statistics with the two row sums at the positions `0` and `l` -/

section Q3stats

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem Ch_bound4 {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) (l : Fin (n + 1)) (hl : l ≠ 0) {c : ℕ}
    (hc : 1 ≤ c) : |Ch d σ (n + 1) l.val c - torusM d σ (n + 1)| ≤ B4 d σ n := by
  have hM := torusM_one_ge hσ d
  have hr1 : 1 ≤ l.val := Nat.one_le_iff_ne_zero.mpr (fun h => hl (Fin.ext h))
  have hrn : l.val ≤ n := by have := l.isLt; omega
  obtain ⟨c0, cM⟩ := Ch_bounds hσ d n l.val c hr1 hrn hc
  have hm1 : torusM d σ (n + 1) ≤ torusM d σ 1 := torusM_anti hσ d le_rfl (by omega)
  have hm0 : 0 ≤ torusM d σ (n + 1) := (torusM_pos hσ d (by omega)).le
  have hM3 : torusM d σ 1 * torusM d σ 1 * torusM d σ 1 ≤ B4 d σ n := by
    unfold B4
    have h1 : torusM d σ 1 ^ 3 ≤ torusM d σ 1 ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    have h2 : 1 ≤ torusM d σ 1 ^ (n + 1) := one_le_pow₀ hM
    nlinarith
  rw [abs_le]; constructor <;> nlinarith

/-- `ε_{v_0} ε_{v_l}`: `cycle · c(x₀ - z) c(x_l - z')`. -/
noncomputable def PhiQee (d : ℕ) (σ : ℝ) (n : ℕ) (l : Fin (n + 1))
    (p : (Fin (n + 1) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cyT d σ p.1 * (heatP d σ 1 (p.1 0 - p.2.1) - 1) * (heatP d σ 1 (p.1 l - p.2.2) - 1)

theorem PhiQee_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) (l : Fin (n + 1)) :
    Measurable (PhiQee d σ n l) := by
  unfold PhiQee
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have a0 : Measurable fun p : (Fin (n + 1) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 0 := (measurable_pi_apply _).comp measurable_fst
  have al : Measurable fun p : (Fin (n + 1) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 l := (measurable_pi_apply _).comp measurable_fst
  exact (((cyT_meas hσ d n).comp measurable_fst).mul
    ((hp.comp (a0.sub (measurable_fst.comp measurable_snd))).sub_const 1)).mul
    ((hp.comp (al.sub (measurable_snd.comp measurable_snd))).sub_const 1)

/-- **`Q₃`, type `εε` at the positions `0, l`, every `k = n + 1`:** main term
    `N^{k+1} (∫ p_l p_{k-l} p₂ - m_k)`. -/
theorem meanQee {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) (l : Fin (n + 1)) (hl : l ≠ 0) :
    |∑ w : Fin (n + 1) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiQee d σ n l (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 1 + 1) * (Ch d σ (n + 1) l.val 2 - torusM d σ (n + 1))|
      ≤ B4 d σ n * ((((n + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 1)
          + ((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ (n + 1 - 1) * (2 * N + ((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiQee d σ n l p| ≤ B4 d σ n := fun p =>
    bd2 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (cK_bound hσ d _)
      (cK_bound hσ d _)
  have hc1 : ∀ y z', ∫ z, PhiQee d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    have e : (fun z => PhiQee d σ n l (y, z, z')) = fun z => (cyT d σ y
        * (heatP d σ 1 (y l - z') - 1)) * (heatP d σ 1 (y 0 - z) - 1) := funext fun z => by
      simp only [PhiQee]; ring
    rw [e, cent hσ d]
  have hc2 : ∀ y z, ∫ z', PhiQee d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    have e : (fun z' => PhiQee d σ n l (y, z, z')) = fun z' => (cyT d σ y
        * (heatP d σ 1 (y 0 - z) - 1)) * (heatP d σ 1 (y l - z') - 1) := funext fun z' => by
      simp only [PhiQee]
    rw [e, cent hσ d]
  have hL : ∀ w : Fin (n + 1) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiQee d σ n l (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = Ch d σ (n + 1) l.val 2 - torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => PhiQee d σ n l (p.1, p.2, p.2))
      ((PhiQee_meas hσ d n l).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)))
      (B := B4 d σ n) (fun p => hB _)]
    have e : ∀ y : Fin (n + 1) → FlatTorus d, ∫ z, PhiQee d σ n l (y, z, z) ∂flatTorusMeasure d
        = cyT d σ y * (heatP d σ 2 (y 0 - y l) - 1) := by
      intro y
      have e1 : (fun z => PhiQee d σ n l (y, z, z)) = fun z => cyT d σ y
          * ((heatP d σ 1 (y 0 - z) - 1) * (heatP d σ 1 (y l - z) - 1)) := funext fun z => by
        simp only [PhiQee]; ring
      rw [e1, integral_const_mul, conv_cc hσ d]
    simp only [e]
    rw [chordc_value hσ d X h_indep hX hlaw w hw l 2 (by norm_num), if_neg hl]
  exact quad_stat_gen X h_indep hX hlaw N (n + 1) (PhiQee d σ n l) (PhiQee_meas hσ d n l)
    (B4_nonneg hσ d n) hB hc1 hc2 _ (Ch_bound4 hσ d n l hl (by norm_num)) hL

end Q3stats

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

section Q3stats2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `E[cy2(X_w) p(x_l - x_q) (p_c(x_0 - x_q) - 1)] = ∫ p_l p_{k-l} p_{c+1} - m_k` (`l ≠ 0`). -/
theorem tail_chord {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {N n : ℕ} (w : Fin (n + 2) → Fin N)
    (hw : Injective w) (l : Fin (n + 1)) (hl : l ≠ 0) (c : ℕ) (hc : 1 ≤ c) :
    ∫ ω, cy2 d σ (fun i => X (w i) ω)
        * heatP d σ 1 (X (w l.castSucc) ω - X (w (Fin.last (n + 1))) ω)
        * (heatP d σ c (X (w (0 : Fin (n + 1)).castSucc) ω - X (w (Fin.last (n + 1))) ω) - 1) ∂μ
      = Ch d σ (n + 1) l.val (c + 1) - torusM d σ (n + 1) := by
  have hM := torusM_one_ge hσ d
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have hpc := (heatP_cont hσ d hc).measurable
  have hF : Measurable fun y : Fin (n + 2) → FlatTorus d => cy2 d σ y
      * heatP d σ 1 (y l.castSucc - y (Fin.last (n + 1)))
      * (heatP d σ c (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))) - 1) :=
    ((cy2_meas hσ d n).mul (hp.comp ((measurable_pi_apply l.castSucc).sub
      (measurable_pi_apply (Fin.last (n + 1)))))).mul
      ((hpc.comp ((measurable_pi_apply (0 : Fin (n + 1)).castSucc).sub
        (measurable_pi_apply (Fin.last (n + 1))))).sub_const 1)
  rw [int_last X h_indep hX hlaw w hw _ hF (B := B4 d σ n)
    (fun y => bd2 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2
      (hP_abs hσ d le_rfl _) (cKc_bound hσ d hc _))]
  have e : ∀ (y' : Fin (n + 1) → FlatTorus d), ∫ z, cy2 d σ (Fin.snoc y' z : Fin (n + 2) → _)
      * heatP d σ 1 ((Fin.snoc y' z : Fin (n + 2) → _) l.castSucc
          - (Fin.snoc y' z : Fin (n + 2) → _) (Fin.last (n + 1)))
      * (heatP d σ c ((Fin.snoc y' z : Fin (n + 2) → _) (0 : Fin (n + 1)).castSucc
          - (Fin.snoc y' z : Fin (n + 2) → _) (Fin.last (n + 1))) - 1) ∂flatTorusMeasure d
      = cyT d σ y' * (heatP d σ (c + 1) (y' 0 - y' l) - 1) := by
    intro y'
    simp only [cy2, Fin.snoc_castSucc, Fin.snoc_last]
    have : ∀ z, cyT d σ y' * heatP d σ 1 (y' l - z) * (heatP d σ c (y' 0 - z) - 1)
        = cyT d σ y' * (heatP d σ 1 (y' l - z) * (heatP d σ c (y' 0 - z) - 1)) :=
      fun z => by ring
    simp_rw [this]
    rw [integral_const_mul, conv_pk hσ d hc, heatP_flip d σ (c + 1) (y' l) (y' 0)]
  simp only [e]
  rw [chordc_value hσ d X h_indep hX hlaw (fun i => w i.castSucc)
    (fun a b h => Fin.castSucc_injective _ (hw h)) l (c + 1) (by omega), if_neg hl]

/-- `E[cy2(X_w) p(x_0 - x_q) (p_c(x_l - x_q) - 1)] = ∫ p_l p_{k-l} p_{c+1} - m_k` (`l ≠ 0`). -/
theorem tail_chord' {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {N n : ℕ} (w : Fin (n + 2) → Fin N)
    (hw : Injective w) (l : Fin (n + 1)) (hl : l ≠ 0) (c : ℕ) (hc : 1 ≤ c) :
    ∫ ω, cy2 d σ (fun i => X (w i) ω)
        * heatP d σ 1 (X (w (0 : Fin (n + 1)).castSucc) ω - X (w (Fin.last (n + 1))) ω)
        * (heatP d σ c (X (w l.castSucc) ω - X (w (Fin.last (n + 1))) ω) - 1) ∂μ
      = Ch d σ (n + 1) l.val (c + 1) - torusM d σ (n + 1) := by
  have hM := torusM_one_ge hσ d
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have hpc := (heatP_cont hσ d hc).measurable
  have hF : Measurable fun y : Fin (n + 2) → FlatTorus d => cy2 d σ y
      * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
      * (heatP d σ c (y l.castSucc - y (Fin.last (n + 1))) - 1) :=
    ((cy2_meas hσ d n).mul (hp.comp ((measurable_pi_apply (0 : Fin (n + 1)).castSucc).sub
      (measurable_pi_apply (Fin.last (n + 1)))))).mul
      ((hpc.comp ((measurable_pi_apply l.castSucc).sub
        (measurable_pi_apply (Fin.last (n + 1))))).sub_const 1)
  rw [int_last X h_indep hX hlaw w hw _ hF (B := B4 d σ n)
    (fun y => bd2 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2
      (hP_abs hσ d le_rfl _) (cKc_bound hσ d hc _))]
  have e : ∀ (y' : Fin (n + 1) → FlatTorus d), ∫ z, cy2 d σ (Fin.snoc y' z : Fin (n + 2) → _)
      * heatP d σ 1 ((Fin.snoc y' z : Fin (n + 2) → _) (0 : Fin (n + 1)).castSucc
          - (Fin.snoc y' z : Fin (n + 2) → _) (Fin.last (n + 1)))
      * (heatP d σ c ((Fin.snoc y' z : Fin (n + 2) → _) l.castSucc
          - (Fin.snoc y' z : Fin (n + 2) → _) (Fin.last (n + 1))) - 1) ∂flatTorusMeasure d
      = cyT d σ y' * (heatP d σ (c + 1) (y' 0 - y' l) - 1) := by
    intro y'
    simp only [cy2, Fin.snoc_castSucc, Fin.snoc_last]
    have : ∀ z, cyT d σ y' * heatP d σ 1 (y' 0 - z) * (heatP d σ c (y' l - z) - 1)
        = cyT d σ y' * (heatP d σ 1 (y' 0 - z) * (heatP d σ c (y' l - z) - 1)) :=
      fun z => by ring
    simp_rw [this]
    rw [integral_const_mul, conv_pk hσ d hc]
  simp only [e]
  rw [chordc_value hσ d X h_indep hX hlaw (fun i => w i.castSucc)
    (fun a b h => Fin.castSucc_injective _ (hw h)) l (c + 1) (by omega), if_neg hl]

end Q3stats2

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

section Q3stats3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `ε_{v_0} (P̃ε)_{v_l}`: `cycle · c(x₀ - z) p(x_l - x_q) c(x_q - z')`. -/
noncomputable def PhiQeb (d : ℕ) (σ : ℝ) (n : ℕ) (l : Fin (n + 1))
    (p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cy2 d σ p.1 * (heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc - p.2.1) - 1)
    * heatP d σ 1 (p.1 l.castSucc - p.1 (Fin.last (n + 1)))
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)) - p.2.2) - 1)

/-- `(P̃ε)_{v_0} ε_{v_l}`: `cycle · p(x₀ - x_q) c(x_q - z) c(x_l - z')`. -/
noncomputable def PhiQbe (d : ℕ) (σ : ℝ) (n : ℕ) (l : Fin (n + 1))
    (p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cy2 d σ p.1 * heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc - p.1 (Fin.last (n + 1)))
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)) - p.2.1) - 1)
    * (heatP d σ 1 (p.1 l.castSucc - p.2.2) - 1)

theorem PhiQeb_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) (l : Fin (n + 1)) :
    Measurable (PhiQeb d σ n l) := by
  unfold PhiQeb
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have a0 : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (0 : Fin (n + 1)).castSucc := (measurable_pi_apply _).comp measurable_fst
  have al : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 l.castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 1)) := (measurable_pi_apply _).comp measurable_fst
  exact ((((cy2_meas hσ d n).comp measurable_fst).mul ((hp.comp
    (a0.sub (measurable_fst.comp measurable_snd))).sub_const 1)).mul (hp.comp (al.sub aq))).mul
    ((hp.comp (aq.sub (measurable_snd.comp measurable_snd))).sub_const 1)

theorem PhiQbe_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) (l : Fin (n + 1)) :
    Measurable (PhiQbe d σ n l) := by
  unfold PhiQbe
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have a0 : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (0 : Fin (n + 1)).castSucc := (measurable_pi_apply _).comp measurable_fst
  have al : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 l.castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq : Measurable fun p : (Fin (n + 2) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 1)) := (measurable_pi_apply _).comp measurable_fst
  exact ((((cy2_meas hσ d n).comp measurable_fst).mul (hp.comp (a0.sub aq))).mul
    ((hp.comp (aq.sub (measurable_fst.comp measurable_snd))).sub_const 1)).mul
    ((hp.comp (al.sub (measurable_snd.comp measurable_snd))).sub_const 1)

/-- **`Q₃`, type `ε (P̃ε)` at the positions `0, l`:** main term `N^{k+2} (∫ p_l p_{k-l} p₃ - m_k)`. -/
theorem meanQeb {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) (l : Fin (n + 1)) (hl : l ≠ 0) :
    |∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiQeb d σ n l (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 2 + 1) * (Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1))|
      ≤ B4 d σ n * ((((n + 2 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 2)
          + ((Prs (n + 2)).card : ℝ) * (N : ℝ) ^ (n + 2 - 1) * (2 * N + ((n + 2 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiQeb d σ n l p| ≤ B4 d σ n := fun p =>
    bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (cK_bound hσ d _)
      (hP_abs hσ d le_rfl _) (cK_bound hσ d _)
  have hc1 : ∀ y z', ∫ z, PhiQeb d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    have e : (fun z => PhiQeb d σ n l (y, z, z')) = fun z => (cy2 d σ y
        * heatP d σ 1 (y l.castSucc - y (Fin.last (n + 1)))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z') - 1))
        * (heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - z) - 1) := funext fun z => by
      simp only [PhiQeb]; ring
    rw [e, cent hσ d]
  have hc2 : ∀ y z, ∫ z', PhiQeb d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    have e : (fun z' => PhiQeb d σ n l (y, z, z')) = fun z' => (cy2 d σ y
        * (heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - z) - 1)
        * heatP d σ 1 (y l.castSucc - y (Fin.last (n + 1))))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z') - 1) := funext fun z' => by
      simp only [PhiQeb]
    rw [e, cent hσ d]
  have hL : ∀ w : Fin (n + 2) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiQeb d σ n l (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => PhiQeb d σ n l (p.1, p.2, p.2))
      ((PhiQeb_meas hσ d n l).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)))
      (B := B4 d σ n) (fun p => hB _)]
    have e : ∀ y : Fin (n + 2) → FlatTorus d, ∫ z, PhiQeb d σ n l (y, z, z) ∂flatTorusMeasure d
        = cy2 d σ y * heatP d σ 1 (y l.castSucc - y (Fin.last (n + 1)))
          * (heatP d σ 2 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))) - 1) := by
      intro y
      have e1 : (fun z => PhiQeb d σ n l (y, z, z)) = fun z => (cy2 d σ y
          * heatP d σ 1 (y l.castSucc - y (Fin.last (n + 1))))
          * ((heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - z) - 1)
            * (heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1)) := funext fun z => by
        simp only [PhiQeb]; ring
      rw [e1, integral_const_mul, conv_cc hσ d]
    simp only [e]
    exact tail_chord hσ d X h_indep hX hlaw w hw l hl 2 (by norm_num)
  exact quad_stat_gen X h_indep hX hlaw N (n + 2) (PhiQeb d σ n l) (PhiQeb_meas hσ d n l)
    (B4_nonneg hσ d n) hB hc1 hc2 _ (Ch_bound4 hσ d n l hl (by norm_num)) hL

/-- **`Q₃`, type `(P̃ε) ε` at the positions `0, l`:** main term `N^{k+2} (∫ p_l p_{k-l} p₃ - m_k)`. -/
theorem meanQbe {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) (l : Fin (n + 1)) (hl : l ≠ 0) :
    |∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiQbe d σ n l (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 2 + 1) * (Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1))|
      ≤ B4 d σ n * ((((n + 2 : ℕ) : ℝ) + ((n + 2 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 2)
          + ((Prs (n + 2)).card : ℝ) * (N : ℝ) ^ (n + 2 - 1) * (2 * N + ((n + 2 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiQbe d σ n l p| ≤ B4 d σ n := fun p =>
    bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (cK_bound hσ d _)
  have hc1 : ∀ y z', ∫ z, PhiQbe d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    have e : (fun z => PhiQbe d σ n l (y, z, z')) = fun z => (cy2 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
        * (heatP d σ 1 (y l.castSucc - z') - 1))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1) := funext fun z => by
      simp only [PhiQbe]; ring
    rw [e, cent hσ d]
  have hc2 : ∀ y z, ∫ z', PhiQbe d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    have e : (fun z' => PhiQbe d σ n l (y, z, z')) = fun z' => (cy2 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
        * (heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1))
        * (heatP d σ 1 (y l.castSucc - z') - 1) := funext fun z' => by
      simp only [PhiQbe]
    rw [e, cent hσ d]
  have hL : ∀ w : Fin (n + 2) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiQbe d σ n l (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => PhiQbe d σ n l (p.1, p.2, p.2))
      ((PhiQbe_meas hσ d n l).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)))
      (B := B4 d σ n) (fun p => hB _)]
    have e : ∀ y : Fin (n + 2) → FlatTorus d, ∫ z, PhiQbe d σ n l (y, z, z) ∂flatTorusMeasure d
        = cy2 d σ y * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1)))
          * (heatP d σ 2 (y l.castSucc - y (Fin.last (n + 1))) - 1) := by
      intro y
      have e1 : (fun z => PhiQbe d σ n l (y, z, z)) = fun z => (cy2 d σ y
          * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc - y (Fin.last (n + 1))))
          * ((heatP d σ 1 (y (Fin.last (n + 1)) - z) - 1)
            * (heatP d σ 1 (y l.castSucc - z) - 1)) := funext fun z => by
        simp only [PhiQbe]; ring
      rw [e1, integral_const_mul, conv_cc hσ d, heatP_flip d σ 2 (y (Fin.last (n + 1)))]
    simp only [e]
    exact tail_chord' hσ d X h_indep hX hlaw w hw l hl 2 (by norm_num)
  exact quad_stat_gen X h_indep hX hlaw N (n + 2) (PhiQbe d σ n l) (PhiQbe_meas hσ d n l)
    (B4_nonneg hσ d n) hB hc1 hc2 _ (Ch_bound4 hσ d n l hl (by norm_num)) hL

end Q3stats3

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 PiBound CTG.Reals.TorusReduction

section Q3BB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `(P̃ε)_{v_0} (P̃ε)_{v_l}`: `cycle · p(x₀ - x_q) c(x_q - z) p(x_l - x_{q'}) c(x_{q'} - z')`. -/
noncomputable def PhiQbb (d : ℕ) (σ : ℝ) (n : ℕ) (l : Fin (n + 1))
    (p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d) : ℝ :=
  cy3 d σ p.1 * heatP d σ 1 (p.1 (0 : Fin (n + 1)).castSucc.castSucc - p.1 (Fin.last (n + 1)).castSucc)
    * (heatP d σ 1 (p.1 (Fin.last (n + 1)).castSucc - p.2.1) - 1)
    * heatP d σ 1 (p.1 l.castSucc.castSucc - p.1 (Fin.last (n + 2)))
    * (heatP d σ 1 (p.1 (Fin.last (n + 2)) - p.2.2) - 1)

theorem PhiQbb_meas {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) (l : Fin (n + 1)) :
    Measurable (PhiQbb d σ n l) := by
  unfold PhiQbb
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have a0 : Measurable fun p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (0 : Fin (n + 1)).castSucc.castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq : Measurable fun p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 1)).castSucc := (measurable_pi_apply _).comp measurable_fst
  have al : Measurable fun p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 l.castSucc.castSucc := (measurable_pi_apply _).comp measurable_fst
  have aq' : Measurable fun p : (Fin (n + 3) → FlatTorus d) × FlatTorus d × FlatTorus d =>
      p.1 (Fin.last (n + 2)) := (measurable_pi_apply _).comp measurable_fst
  exact (((((cy3_meas hσ d n).comp measurable_fst).mul (hp.comp (a0.sub aq))).mul
    ((hp.comp (aq.sub (measurable_fst.comp measurable_snd))).sub_const 1)).mul
    (hp.comp (al.sub aq'))).mul
    ((hp.comp (aq'.sub (measurable_snd.comp measurable_snd))).sub_const 1)

/-- **`Q₃`, type `(P̃ε)(P̃ε)` at the positions `0, l`:** main term `N^{k+3} (∫ p_l p_{k-l} p₄ - m_k)`. -/
theorem meanQbb {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N n : ℕ) (l : Fin (n + 1)) (hl : l ≠ 0) :
    |∑ w : Fin (n + 3) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, PhiQbb d σ n l (fun i => X (w i) ω, X u ω, X u' ω) ∂μ
        - (N : ℝ) ^ (n + 3 + 1) * (Ch d σ (n + 1) l.val 4 - torusM d σ (n + 1))|
      ≤ B4 d σ n * ((((n + 3 : ℕ) : ℝ) + ((n + 3 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (n + 3)
          + ((Prs (n + 3)).card : ℝ) * (N : ℝ) ^ (n + 3 - 1) * (2 * N + ((n + 3 : ℕ) : ℝ) ^ 2)) := by
  have hM := torusM_one_ge hσ d
  have hp := (heatP_cont hσ d (le_refl 1)).measurable
  have hB : ∀ p, |PhiQbb d σ n l p| ≤ B4 d σ n := fun p =>
    bd4 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (hP_abs hσ d le_rfl _) (cK_bound hσ d _)
  have hc1 : ∀ y z', ∫ z, PhiQbb d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z'
    have e : (fun z => PhiQbb d σ n l (y, z, z')) = fun z => (cy3 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
        * heatP d σ 1 (y l.castSucc.castSucc - y (Fin.last (n + 2)))
        * (heatP d σ 1 (y (Fin.last (n + 2)) - z') - 1))
        * (heatP d σ 1 (y (Fin.last (n + 1)).castSucc - z) - 1) := funext fun z => by
      simp only [PhiQbb]; ring
    rw [e, cent hσ d]
  have hc2 : ∀ y z, ∫ z', PhiQbb d σ n l (y, z, z') ∂flatTorusMeasure d = 0 := by
    intro y z
    have e : (fun z' => PhiQbb d σ n l (y, z, z')) = fun z' => (cy3 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
        * (heatP d σ 1 (y (Fin.last (n + 1)).castSucc - z) - 1)
        * heatP d σ 1 (y l.castSucc.castSucc - y (Fin.last (n + 2))))
        * (heatP d σ 1 (y (Fin.last (n + 2)) - z') - 1) := funext fun z' => by
      simp only [PhiQbb]
    rw [e, cent hσ d]
  have hL : ∀ w : Fin (n + 3) → Fin N, Injective w → ∀ u, u ∉ Finset.univ.image w →
      ∫ ω, PhiQbb d σ n l (fun i => X (w i) ω, X u ω, X u ω) ∂μ
        = Ch d σ (n + 1) l.val 4 - torusM d σ (n + 1) := by
    intro w hw u hu
    have hu' : ∀ i, (w i : ℕ) ≠ (u : ℕ) := fun i h =>
      hu (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Fin.ext h⟩)
    rw [integrate_extra X h_indep hX hlaw (fun i => (w i : ℕ)) u hu'
      (fun p => PhiQbb d σ n l (p.1, p.2, p.2))
      ((PhiQbb_meas hσ d n l).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)))
      (B := B4 d σ n) (fun p => hB _)]
    obtain ⟨F, hFd⟩ : ∃ F : (Fin (n + 3) → FlatTorus d) → ℝ, F = fun y => cy3 d σ y
        * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
        * heatP d σ 1 (y l.castSucc.castSucc - y (Fin.last (n + 2)))
        * (heatP d σ 2 (y (Fin.last (n + 1)).castSucc - y (Fin.last (n + 2))) - 1) := ⟨_, rfl⟩
    have e : ∀ y : Fin (n + 3) → FlatTorus d, ∫ z, PhiQbb d σ n l (y, z, z) ∂flatTorusMeasure d
        = F y := by
      intro y
      have e1 : (fun z => PhiQbb d σ n l (y, z, z)) = fun z => (cy3 d σ y
          * heatP d σ 1 (y (0 : Fin (n + 1)).castSucc.castSucc - y (Fin.last (n + 1)).castSucc)
          * heatP d σ 1 (y l.castSucc.castSucc - y (Fin.last (n + 2))))
          * ((heatP d σ 1 (y (Fin.last (n + 1)).castSucc - z) - 1)
            * (heatP d σ 1 (y (Fin.last (n + 2)) - z) - 1)) := funext fun z => by
        simp only [PhiQbb]; ring
      rw [e1, integral_const_mul, conv_cc hσ d, hFd]
    simp only [e]
    have hF : Measurable F := by
      rw [hFd]
      have hp2 := (heatP_cont hσ d (by norm_num : 1 ≤ 2)).measurable
      exact (((cy3_meas hσ d n).mul (hp.comp ((measurable_pi_apply _).sub (measurable_pi_apply _)))).mul
        (hp.comp ((measurable_pi_apply _).sub (measurable_pi_apply _)))).mul
        ((hp2.comp ((measurable_pi_apply (Fin.last (n + 1)).castSucc).sub
          (measurable_pi_apply (Fin.last (n + 2))))).sub_const 1)
    rw [int_last X h_indep hX hlaw w hw F hF (B := B4 d σ n) (fun y => by
      rw [hFd]
      exact bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2
        (hP_abs hσ d le_rfl _) (hP_abs hσ d le_rfl _) (cKc_bound hσ d (by norm_num) _))]
    have e2 : ∀ y' : Fin (n + 2) → FlatTorus d,
        ∫ z, F (Fin.snoc y' z) ∂flatTorusMeasure d
          = cy2 d σ y' * heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - y' (Fin.last (n + 1)))
            * (heatP d σ 3 (y' l.castSucc - y' (Fin.last (n + 1))) - 1) := by
      intro y'
      rw [hFd]
      simp only [cy3, cy2, Fin.snoc_castSucc, Fin.snoc_last]
      have : ∀ z, cyT d σ (fun a : Fin (n + 1) => y' a.castSucc)
          * heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - y' (Fin.last (n + 1)))
          * heatP d σ 1 (y' l.castSucc - z)
          * (heatP d σ 2 (y' (Fin.last (n + 1)) - z) - 1)
          = (cyT d σ (fun a : Fin (n + 1) => y' a.castSucc)
            * heatP d σ 1 (y' (0 : Fin (n + 1)).castSucc - y' (Fin.last (n + 1))))
            * (heatP d σ 1 (y' l.castSucc - z)
              * (heatP d σ 2 (y' (Fin.last (n + 1)) - z) - 1)) := fun z => by ring
      simp_rw [this]
      rw [integral_const_mul, conv_pk hσ d (by norm_num : 1 ≤ 2)]
    simp only [e2]
    exact tail_chord' hσ d X h_indep hX hlaw (fun i => w i.castSucc)
      (fun a b h => Fin.castSucc_injective _ (hw h)) l hl 3 (by norm_num)
  exact quad_stat_gen X h_indep hX hlaw N (n + 3) (PhiQbb d σ n l) (PhiQbb_meas hσ d n l)
    (B4_nonneg hσ d n) hB hc1 hc2 _ (Ch_bound4 hσ d n l hl (by norm_num)) hL

end Q3BB

end BiasGeneral5

namespace BiasGeneral6

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

/-! # A101: `prop:bias` for every `k`: bridges, identification, mean, final statement -/

section Bridges

theorem heatTorus_eq_heatP (d : ℕ) (σ : ℝ) (u : FlatTorus d) :
    heatTorus d (2 * Real.pi ^ 2 * σ) u = heatP d σ 1 u := by
  rw [heatP_eq d σ le_rfl]; simp

theorem heatP_eq_pker (d : ℕ) (σ : ℝ) {s : ℕ} (hs : 1 ≤ s) (u : FlatTorus d) :
    heatP d σ s u = pker d ((s : ℝ) * σ) u := by
  rw [heatP_eq d σ hs]; rfl

theorem torusM_eq_pker (d : ℕ) (σ : ℝ) (s : ℕ) : torusM d σ s = pker d ((s : ℝ) * σ) 0 := rfl

theorem Ch_eq (d : ℕ) (σ : ℝ) (k l c : ℕ) (hl : 1 ≤ l) (hlk : l < k) (hc : 1 ≤ c) :
    Ch d σ k l c = ∫ u, pker d ((l : ℝ) * σ) u * pker d (((k - l : ℕ) : ℝ) * σ) u
      * pker d ((c : ℝ) * σ) u ∂flatTorusMeasure d := by
  unfold Ch
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [heatP_eq_pker d σ hl, heatP_eq_pker d σ (by omega : 1 ≤ k - l), heatP_eq_pker d σ hc]

variable {G : Type*}

/-- `ε_a = ρ_a - 1 = (1/N) ∑_u (p(x_a - x_u) - 1)` with the sum over `Fin N`. -/
theorem eps_row (d : ℕ) (σ : ℝ) {N : ℕ} (hN : 0 < N) (x : ℕ → FlatTorus d) (a : ℕ) :
    heatRho d σ N x a - 1 = 1 / (N : ℝ) * ∑ u : Fin N, (heatP d σ 1 (x a - x u) - 1) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have e3 : heatRho d σ N x a
      = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) / (N : ℝ) := rfl
  have e4 : ∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)
      = ∑ u : Fin N, heatP d σ 1 (x a - x u) := by
    rw [← Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) N]
    exact Finset.sum_congr rfl fun u _ => heatTorus_eq_heatP d σ _
  rw [e3, e4, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  field_simp

/-- `∑_i (P̃^k)_ii f_i = N^{-k} ∑_v cycle(x_v) f(v_0)`, `P̃ = p(x_a - x_b)/N`. -/
theorem diag_sum (d : ℕ) (σ : ℝ) (N n : ℕ) (x : ℕ → FlatTorus d) (f : Fin N → ℝ) :
    ∑ i, (Matrix.of (fun a b : Fin N => heatP d σ 1 (x a - x b) / N) ^ (n + 1)) i i * f i
      = (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * f (v 0)) / (N : ℝ) ^ (n + 1) := by
  rw [Finset.sum_div]
  have e : ∀ i : Fin N, (Matrix.of (fun a b : Fin N => heatP d σ 1 (x a - x b) / N) ^ (n + 1)) i i
      = ∑ w : Fin n → Fin N, cw (fun a b : Fin N => heatP d σ 1 (x a - x b) / N)
          (Fin.cons i w : Fin (n + 1) → Fin N) := by
    intro i
    rw [pow_apply_pth]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [cw_eq_pth]; simp only [Fin.cons_zero, Fin.tail_cons]; rfl
  simp only [e, Finset.sum_mul]
  rw [BiasVariance3.sum_cons]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w _ => ?_
  rw [cw, cyT, cycP]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fin.cons_zero]
  ring

end Bridges

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

/-! ## (b) The terms of the expansion as sums over index tuples (pointwise) -/

section Ident

variable {d : ℕ} {σ : ℝ}

/-- `ε_a = (1/N) ∑_u (p(x_a - x_u) - 1)`. -/
noncomputable def eV (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (a : ℕ) : ℝ :=
  1 / (N : ℝ) * ∑ u : Fin N, (heatP d σ 1 (x a - x u) - 1)

/-- `(P̃ε)_a = (1/N) ∑_q p(x_a - x_q) ε_q`. -/
noncomputable def bV (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (a : ℕ) : ℝ :=
  1 / (N : ℝ) * ∑ q : Fin N, heatP d σ 1 (x a - x q) * eV d σ N x q

/-- `(P̃ε²)_a = (1/N) ∑_q p(x_a - x_q) ε_q²`. -/
noncomputable def sV (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (a : ℕ) : ℝ :=
  1 / (N : ℝ) * ∑ q : Fin N, heatP d σ 1 (x a - x q) * eV d σ N x q ^ 2

theorem sum_snoc {α : Type*} [Fintype α] {m : ℕ} (g : (Fin (m + 1) → α) → ℝ) :
    ∑ w : Fin (m + 1) → α, g w = ∑ v : Fin m → α, ∑ q : α, g (Fin.snoc v q) := by
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => α)) (fun p => g (Fin.snoc p.2 p.1)) g
    (fun p => rfl), Fintype.sum_prod_type, Finset.sum_comm]

theorem snoc0 {α : Type*} {m : ℕ} (v : Fin (m + 1) → α) (q : α) :
    (Fin.snoc v q : Fin (m + 2) → α) 0 = v 0 := by
  rw [← Fin.castSucc_zero]; exact Fin.snoc_castSucc (α := fun _ => α) _ _ _

variable (d σ)

theorem idA (N n : ℕ) (x : ℕ → FlatTorus d) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * eV d σ N x (v 0)
      = (∑ v : Fin (n + 1) → Fin N, ∑ u : Fin N, PhiA d σ n (fun a => x (v a), x u)) / N := by
  simp only [eV, PhiA, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  ring

theorem idB (N n : ℕ) (x : ℕ → FlatTorus d) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * bV d σ N x (v 0)
      = (∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, PhiB d σ n (fun a => x (w a), x u)) / N ^ 2 := by
  rw [sum_snoc (m := n + 1)]
  simp only [bV, eV, PhiB, Finset.mul_sum, Finset.sum_div, Fin.snoc_castSucc, Fin.snoc_last, snoc0]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun u _ => ?_
  ring

theorem idEE (N n : ℕ) (x : ℕ → FlatTorus d) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * eV d σ N x (v 0) ^ 2
      = (∑ v : Fin (n + 1) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiEE d σ n (fun a => x (v a), x u, x u')) / N ^ 2 := by
  simp only [eV, PhiEE, sq, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun u' _ => ?_
  ring

theorem idS (N n : ℕ) (x : ℕ → FlatTorus d) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * sV d σ N x (v 0)
      = (∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiS d σ n (fun a => x (w a), x u, x u')) / N ^ 3 := by
  rw [sum_snoc (m := n + 1)]
  simp only [sV, eV, PhiS, cy2, sq, Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
    Fin.snoc_castSucc, Fin.snoc_last, snoc0]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

theorem idEB (N n : ℕ) (x : ℕ → FlatTorus d) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * (eV d σ N x (v 0) * bV d σ N x (v 0))
      = (∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiEB d σ n (fun a => x (w a), x u, x u')) / N ^ 3 := by
  rw [sum_snoc (m := n + 1)]
  simp only [bV, eV, PhiEB, cy2, Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
    Fin.snoc_castSucc, Fin.snoc_last, snoc0]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

end Ident

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

section Ident2

variable (d : ℕ) (σ : ℝ)

theorem snoc00 {α : Type*} {m : ℕ} (v : Fin (m + 1) → α) (q q' : α) :
    (Fin.snoc (Fin.snoc v q : Fin (m + 2) → α) q' : Fin (m + 3) → α) (0 : Fin (m + 1)).castSucc.castSucc
      = v 0 := by
  simp [Fin.snoc_castSucc]

theorem idBB (N n : ℕ) (x : ℕ → FlatTorus d) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * bV d σ N x (v 0) ^ 2
      = (∑ w : Fin (n + 3) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiBB d σ n (fun a => x (w a), x u, x u')) / N ^ 4 := by
  rw [sum_snoc (m := n + 2)]
  simp only [sum_snoc (α := Fin N) (m := n + 1)]
  simp only [bV, eV, PhiBB, cy3, sq, Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
    Fin.snoc_castSucc, Fin.snoc_last]
  refine Finset.sum_congr rfl fun v _ => ?_
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ =>
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

theorem idQee (N n : ℕ) (x : ℕ → FlatTorus d) (l : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * (eV d σ N x (v 0) * eV d σ N x (v l))
      = (∑ v : Fin (n + 1) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiQee d σ n l (fun a => x (v a), x u, x u')) / N ^ 2 := by
  simp only [eV, PhiQee, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

theorem idQeb (N n : ℕ) (x : ℕ → FlatTorus d) (l : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * (eV d σ N x (v 0) * bV d σ N x (v l))
      = (∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiQeb d σ n l (fun a => x (w a), x u, x u')) / N ^ 3 := by
  rw [sum_snoc (m := n + 1)]
  simp only [bV, eV, PhiQeb, cy2, Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
    Fin.snoc_castSucc, Fin.snoc_last]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

theorem idQbe (N n : ℕ) (x : ℕ → FlatTorus d) (l : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * (bV d σ N x (v 0) * eV d σ N x (v l))
      = (∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiQbe d σ n l (fun a => x (w a), x u, x u')) / N ^ 3 := by
  rw [sum_snoc (m := n + 1)]
  simp only [bV, eV, PhiQbe, cy2, Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
    Fin.snoc_castSucc, Fin.snoc_last]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

theorem idQbb (N n : ℕ) (x : ℕ → FlatTorus d) (l : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * (bV d σ N x (v 0) * bV d σ N x (v l))
      = (∑ w : Fin (n + 3) → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          PhiQbb d σ n l (fun a => x (w a), x u, x u')) / N ^ 4 := by
  rw [sum_snoc (m := n + 2)]
  simp only [sum_snoc (α := Fin N) (m := n + 1)]
  simp only [bV, eV, PhiQbb, cy3, Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
    Fin.snoc_castSucc, Fin.snoc_last]
  refine Finset.sum_congr rfl fun v _ => ?_
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ =>
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  ring

end Ident2

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

/-! ## (c) The mean of the polynomial statistic for every `k` -/

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {G : Type*} [MeasurableSpace G]

theorem bm2 (X : ℕ → Ω → G) (hX : ∀ j, Measurable (X j)) {N s : ℕ}
    (Φ : (Fin s → G) × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ p, |Φ p| ≤ B) :
    BM (fun ω => ∑ w : Fin s → Fin N, ∑ u : Fin N, Φ (fun a => X (w a) ω, X u ω)) :=
  BM.sum _ _ fun w _ => BM.sum _ _ fun u _ =>
    ⟨hΦ.comp ((measurable_pi_lambda _ fun a => hX _).prodMk (hX _)), B, fun ω => hB _⟩

theorem bm3 (X : ℕ → Ω → G) (hX : ∀ j, Measurable (X j)) {N s : ℕ}
    (Φ : (Fin s → G) × G × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ p, |Φ p| ≤ B) :
    BM (fun ω => ∑ w : Fin s → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
      Φ (fun a => X (w a) ω, X u ω, X u' ω)) :=
  BM.sum _ _ fun w _ => BM.sum _ _ fun u _ => BM.sum _ _ fun u' _ =>
    ⟨hΦ.comp ((measurable_pi_lambda _ fun a => hX _).prodMk ((hX _).prodMk (hX _))), B,
      fun ω => hB _⟩

theorem int2 (X : ℕ → Ω → G) (hX : ∀ j, Measurable (X j)) {N s : ℕ}
    (Φ : (Fin s → G) × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ p, |Φ p| ≤ B) :
    ∫ ω, ∑ w : Fin s → Fin N, ∑ u : Fin N, Φ (fun a => X (w a) ω, X u ω) ∂μ
      = ∑ w : Fin s → Fin N, ∑ u : Fin N, ∫ ω, Φ (fun a => X (w a) ω, X u ω) ∂μ := by
  have hb : ∀ (w : Fin s → Fin N) (u : Fin N), BM fun ω => Φ (fun a => X (w a) ω, X u ω) :=
    fun w u => ⟨hΦ.comp ((measurable_pi_lambda _ fun a => hX _).prodMk (hX _)), B, fun ω => hB _⟩
  rw [integral_finset_sum _ fun w _ => (BM.sum _ _ fun u _ => hb w u).integrable]
  exact Finset.sum_congr rfl fun w _ =>
    integral_finset_sum _ fun u _ => (hb w u).integrable

theorem int3 (X : ℕ → Ω → G) (hX : ∀ j, Measurable (X j)) {N s : ℕ}
    (Φ : (Fin s → G) × G × G → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hB : ∀ p, |Φ p| ≤ B) :
    ∫ ω, ∑ w : Fin s → Fin N, ∑ u : Fin N, ∑ u' : Fin N, Φ (fun a => X (w a) ω, X u ω, X u' ω) ∂μ
      = ∑ w : Fin s → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, Φ (fun a => X (w a) ω, X u ω, X u' ω) ∂μ := by
  have hb : ∀ (w : Fin s → Fin N) (u u' : Fin N),
      BM fun ω => Φ (fun a => X (w a) ω, X u ω, X u' ω) := fun w u u' =>
    ⟨hΦ.comp ((measurable_pi_lambda _ fun a => hX _).prodMk ((hX _).prodMk (hX _))), B,
      fun ω => hB _⟩
  rw [integral_finset_sum _ fun w _ =>
    (BM.sum _ _ fun u _ => BM.sum _ _ fun u' _ => hb w u u').integrable]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [integral_finset_sum _ fun u _ => (BM.sum _ _ fun u' _ => hb w u u').integrable]
  exact Finset.sum_congr rfl fun u _ => integral_finset_sum _ fun u' _ => (hb w u u').integrable

end Generic

theorem scale {S L C : ℝ} {N p : ℕ} (hN : 1 ≤ N) (h : |S - (N : ℝ) ^ (p + 1) * L| ≤ C * (N : ℝ) ^ p) :
    |S / (N : ℝ) ^ (p + 2) - L / N| ≤ C / (N : ℝ) ^ 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have e : S / (N : ℝ) ^ (p + 2) - L / N = (S - (N : ℝ) ^ (p + 1) * L) / (N : ℝ) ^ (p + 2) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (pow_pos hNp _), div_le_div_iff₀ (pow_pos hNp _) (pow_pos hNp _)]
  calc |S - (N : ℝ) ^ (p + 1) * L| * (N : ℝ) ^ 2 ≤ C * (N : ℝ) ^ p * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = C * (N : ℝ) ^ (p + 2) := by ring

theorem quad_pow {N s : ℕ} (hN : 1 ≤ N) (hs : 1 ≤ s) {B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P) :
    B * (((s : ℝ) + (s : ℝ) ^ 2) * (N : ℝ) ^ s + P * (N : ℝ) ^ (s - 1) * (2 * N + (s : ℝ) ^ 2))
      ≤ B * (((s : ℝ) + (s : ℝ) ^ 2) + P * (2 + (s : ℝ) ^ 2)) * (N : ℝ) ^ s := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ (s - 1) * N = (N : ℝ) ^ s := by
    rw [← pow_succ]; congr 1; omega
  have h2 : (N : ℝ) ^ (s - 1) ≤ (N : ℝ) ^ s := pow_le_pow_right₀ hN1 (by omega)
  have h3 : P * (N : ℝ) ^ (s - 1) * (2 * N + (s : ℝ) ^ 2)
      ≤ P * (2 + (s : ℝ) ^ 2) * (N : ℝ) ^ s := by
    have : (N : ℝ) ^ (s - 1) * (2 * N + (s : ℝ) ^ 2) ≤ (2 + (s : ℝ) ^ 2) * (N : ℝ) ^ s := by
      nlinarith [sq_nonneg (s : ℝ)]
    nlinarith
  nlinarith

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

section Terms

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
  (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
  (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
include hσ h_indep hX hlaw

/-- The constant of a statistic with two row sums of arity `s`. -/
noncomputable def cQ (d : ℕ) (σ : ℝ) (n s : ℕ) (P : ℝ) : ℝ :=
  B4 d σ n * (((s : ℝ) + (s : ℝ) ^ 2) + P * (2 + (s : ℝ) ^ 2))

theorem tA {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    |∫ ω, (∑ v : Fin (n + 1) → Fin N, ∑ u : Fin N, PhiA d σ n (fun a => X (v a) ω, X u ω))
        / (N : ℝ) ^ (n + 2) ∂μ - (∑ r, LA d σ n r) / N|
      ≤ 2 * ((n + 1 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1)
          * ((Prs (n + 1)).card : ℝ) / (N : ℝ) ^ 2 := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiA d σ n p| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 := by
    intro p; unfold PhiA
    rw [abs_mul, abs_of_nonneg (cyT_bounds hσ d p.1).1]
    exact mul_le_mul (cyT_bounds hσ d p.1).2 (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  rw [integral_div, int2 X hX _ (PhiA_meas hσ d n) hB]
  have h := meanA hσ d X h_indep hX hlaw N n
  rw [Nat.add_sub_cancel] at h
  refine scale (p := n) hN ?_
  calc _ ≤ 2 * ((n + 1 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1)
        * (((Prs (n + 1)).card : ℝ) * (N : ℝ) ^ n) := h
    _ = _ := by ring

theorem tB {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    |∫ ω, (∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, PhiB d σ n (fun a => X (w a) ω, X u ω))
        / (N : ℝ) ^ (n + 1 + 2) ∂μ - (∑ r, LB d σ n r) / N|
      ≤ 2 * ((n + 2 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1)
          * ((Prs (n + 2)).card : ℝ) / (N : ℝ) ^ 2 := by
  have hM := torusM_one_ge hσ d
  have hB : ∀ p, |PhiB d σ n p| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    intro p
    unfold PhiB
    rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1,
      abs_of_nonneg (heatP_nonneg hσ d 1 _)]
    exact mul_le_mul (mul_le_mul (cyT_bounds hσ d _).2 (heatP_le hσ d le_rfl _)
      (heatP_nonneg hσ d 1 _) (by positivity)) (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  rw [integral_div, int2 X hX _ (PhiB_meas hσ d n) hB]
  have h := meanB hσ d X h_indep hX hlaw N n
  rw [show n + 2 - 1 = n + 1 by omega] at h
  refine scale (p := n + 1) hN ?_
  calc _ ≤ 2 * ((n + 2 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1)
        * (((Prs (n + 2)).card : ℝ) * (N : ℝ) ^ (n + 1)) := h
    _ = _ := by ring

/-- The generic step for the statistics with two row sums. -/
theorem tQ {N : ℕ} (hN : 1 ≤ N) (n s : ℕ) (hs : 1 ≤ s)
    (Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ) (hΦ : Measurable Φ)
    (hB : ∀ p, |Φ p| ≤ B4 d σ n) (L : ℝ)
    (hm : |∑ w : Fin s → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          ∫ ω, Φ (fun i => X (w i) ω, X u ω, X u' ω) ∂μ - (N : ℝ) ^ (s + 1) * L|
      ≤ B4 d σ n * (((s : ℝ) + (s : ℝ) ^ 2) * (N : ℝ) ^ s
          + ((Prs s).card : ℝ) * (N : ℝ) ^ (s - 1) * (2 * N + (s : ℝ) ^ 2))) :
    |∫ ω, (∑ w : Fin s → Fin N, ∑ u : Fin N, ∑ u' : Fin N,
          Φ (fun a => X (w a) ω, X u ω, X u' ω)) / (N : ℝ) ^ (s + 2) ∂μ - L / N|
      ≤ cQ d σ n s ((Prs s).card) / (N : ℝ) ^ 2 := by
  rw [integral_div, int3 X hX _ hΦ hB]
  exact scale (p := s) hN (hm.trans ((quad_pow hN hs (B4_nonneg hσ d n)
    (Nat.cast_nonneg _)).trans (le_of_eq (by unfold cQ; ring))))

end Terms

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

section QTdef

/-- The pieces of the polynomial statistic as functions of the points. -/
noncomputable def gA (d : ℕ) (σ : ℝ) (N n : ℕ) (x : ℕ → FlatTorus d) : ℝ :=
  (∑ v : Fin (n + 1) → Fin N, ∑ u : Fin N, PhiA d σ n (fun a => x (v a), x u)) / (N : ℝ) ^ (n + 2)
noncomputable def gB (d : ℕ) (σ : ℝ) (N n : ℕ) (x : ℕ → FlatTorus d) : ℝ :=
  (∑ w : Fin (n + 2) → Fin N, ∑ u : Fin N, PhiB d σ n (fun a => x (w a), x u))
    / (N : ℝ) ^ (n + 1 + 2)
noncomputable def g3 {s : ℕ} (N : ℕ) {d : ℕ} (Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ)
    (x : ℕ → FlatTorus d) : ℝ :=
  (∑ w : Fin s → Fin N, ∑ u : Fin N, ∑ u' : Fin N, Φ (fun a => x (w a), x u, x u'))
    / (N : ℝ) ^ (s + 2)

/-- **The polynomial statistic `Q₀ + Q₁ + Q₂ + Q₃` for every `k = n + 1`, as sums over index
    tuples** (it equals the subtracted sum of `trace_expansion_paper` at the sample, see
    `QT_eq`). -/
noncomputable def QT (d : ℕ) (σ : ℝ) (N n : ℕ) (x : ℕ → FlatTorus d) : ℝ :=
  (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))) / (N : ℝ) ^ (n + 1)
  + ((n : ℝ) + 1) * (-2 * gA d σ N n x + gB d σ N n x + 3 * g3 N (PhiEE d σ n) x
      - 3 * g3 N (PhiEB d σ n) x + g3 N (PhiBB d σ n) x - g3 N (PhiS d σ n) x)
  + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) x - 2 * g3 N (PhiQeb d σ n l) x
        - 2 * g3 N (PhiQbe d σ n l) x + g3 N (PhiQbb d σ n l) x)

/-- The main term `Q₀ + (Q₁+Q₂+Q₃ at the order 1/N)`. -/
noncomputable def Mt (d : ℕ) (σ : ℝ) (N n : ℕ) : ℝ :=
  torusM d σ (n + 1) - ((Prs (n + 1)).card : ℝ) * torusM d σ (n + 1) / N
    + (∑ p ∈ Prs (n + 1), Ip (torusM d σ) (n + 1) p) / N
  + ((n : ℝ) + 1) * (-2 * ((∑ r, LA d σ n r) / N) + (∑ r, LB d σ n r) / N
      + 3 * ((torusM d σ 2 - 1) * torusM d σ (n + 1) / N)
      - 3 * ((torusM d σ 3 - 1) * torusM d σ (n + 1) / N)
      + (torusM d σ 4 - 1) * torusM d σ (n + 1) / N
      - (torusM d σ 2 - 1) * torusM d σ (n + 1) / N)
  + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * ((Ch d σ (n + 1) l.val 2 - torusM d σ (n + 1)) / N)
        - 2 * ((Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1)) / N)
        - 2 * ((Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1)) / N)
        + (Ch d σ (n + 1) l.val 4 - torusM d σ (n + 1)) / N)

/-- The constant of the remainder. -/
noncomputable def Ctot (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  (torusM d σ 1 + torusM d σ 1 * torusM d σ 1 + 2 * torusM d σ 1 ^ (n + 1))
      * ((Prs (n + 1)).card : ℝ) ^ 2
  + ((n : ℝ) + 1) * (2 * (2 * ((n + 1 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1)
        * ((Prs (n + 1)).card : ℝ))
      + 2 * ((n + 2 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1)
        * ((Prs (n + 2)).card : ℝ)
      + 3 * cQ d σ n (n + 1) ((Prs (n + 1)).card) + 3 * cQ d σ n (n + 2) ((Prs (n + 2)).card)
      + cQ d σ n (n + 3) ((Prs (n + 3)).card) + cQ d σ n (n + 2) ((Prs (n + 2)).card))
  + ((n : ℝ) + 1) / 2 * (n : ℝ) * (4 * cQ d σ n (n + 1) ((Prs (n + 1)).card)
      + 4 * cQ d σ n (n + 2) ((Prs (n + 2)).card) + cQ d σ n (n + 3) ((Prs (n + 3)).card))

end QTdef

section MeanQT

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem BM.div_const {f : Ω → ℝ} (hf : BM f) (c : ℝ) : BM (fun ω => f ω / c) := by
  obtain ⟨B, hB⟩ := hf.bdd
  refine ⟨hf.meas.div_const c, B / |c|, fun ω => ?_⟩
  rw [abs_div]
  exact div_le_div_of_nonneg_right (hB ω) (abs_nonneg c)

end MeanQT

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

section MeanQT2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integral_lin6 {f1 f2 f3 f4 f5 f6 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (h6 : Integrable f6 μ) :
    ∫ ω, (-2 * f1 ω + f2 ω + 3 * f3 ω - 3 * f4 ω + f5 ω - f6 ω) ∂μ
      = -2 * ∫ ω, f1 ω ∂μ + ∫ ω, f2 ω ∂μ + 3 * ∫ ω, f3 ω ∂μ - 3 * ∫ ω, f4 ω ∂μ
        + ∫ ω, f5 ω ∂μ - ∫ ω, f6 ω ∂μ := by
  have g1 : Integrable (fun ω => -2 * f1 ω) μ := h1.const_mul _
  have g3 : Integrable (fun ω => 3 * f3 ω) μ := h3.const_mul _
  have g4 : Integrable (fun ω => 3 * f4 ω) μ := h4.const_mul _
  have k2 : Integrable (fun ω => -2 * f1 ω + f2 ω) μ := g1.add h2
  have k3 : Integrable (fun ω => -2 * f1 ω + f2 ω + 3 * f3 ω) μ := k2.add g3
  have k4 : Integrable (fun ω => -2 * f1 ω + f2 ω + 3 * f3 ω - 3 * f4 ω) μ := k3.sub g4
  have k5 : Integrable (fun ω => -2 * f1 ω + f2 ω + 3 * f3 ω - 3 * f4 ω + f5 ω) μ := k4.add h5
  rw [integral_sub k5 h6, integral_add k4 h5, integral_sub k3 g4, integral_add k2 g3,
    integral_add g1 h2, integral_const_mul, integral_const_mul, integral_const_mul]

theorem integral_lin4 {f1 f2 f3 f4 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ)
    (h3 : Integrable f3 μ) (h4 : Integrable f4 μ) :
    ∫ ω, (4 * f1 ω - 2 * f2 ω - 2 * f3 ω + f4 ω) ∂μ
      = 4 * ∫ ω, f1 ω ∂μ - 2 * ∫ ω, f2 ω ∂μ - 2 * ∫ ω, f3 ω ∂μ + ∫ ω, f4 ω ∂μ := by
  have g1 : Integrable (fun ω => 4 * f1 ω) μ := h1.const_mul _
  have g2 : Integrable (fun ω => 2 * f2 ω) μ := h2.const_mul _
  have g3 : Integrable (fun ω => 2 * f3 ω) μ := h3.const_mul _
  have k2 : Integrable (fun ω => 4 * f1 ω - 2 * f2 ω) μ := g1.sub g2
  have k3 : Integrable (fun ω => 4 * f1 ω - 2 * f2 ω - 2 * f3 ω) μ := k2.sub g3
  rw [integral_add k3 h4, integral_sub k2 g3, integral_sub g1 g2, integral_const_mul,
    integral_const_mul, integral_const_mul]

/-- The bounds of the summands by `B4`. -/
theorem phi_bounds {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) (l : Fin (n + 1)) :
    (∀ p, |PhiEE d σ n p| ≤ B4 d σ n) ∧ (∀ p, |PhiEB d σ n p| ≤ B4 d σ n)
    ∧ (∀ p, |PhiBB d σ n p| ≤ B4 d σ n) ∧ (∀ p, |PhiS d σ n p| ≤ B4 d σ n)
    ∧ (∀ p, |PhiQee d σ n l p| ≤ B4 d σ n) ∧ (∀ p, |PhiQeb d σ n l p| ≤ B4 d σ n)
    ∧ (∀ p, |PhiQbe d σ n l p| ≤ B4 d σ n) ∧ (∀ p, |PhiQbb d σ n l p| ≤ B4 d σ n) := by
  have hM := torusM_one_ge hσ d
  refine ⟨fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_,
    fun p => ?_, fun p => ?_⟩
  · exact bd2 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (cK_bound hσ d _)
      (cK_bound hσ d _)
  · exact bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (cK_bound hσ d _)
      (hP_abs hσ d le_rfl _) (cK_bound hσ d _)
  · exact bd4 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (hP_abs hσ d le_rfl _) (cK_bound hσ d _)
  · exact bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (cK_bound hσ d _)
  · exact bd2 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (cK_bound hσ d _)
      (cK_bound hσ d _)
  · exact bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (cK_bound hσ d _)
      (hP_abs hσ d le_rfl _) (cK_bound hσ d _)
  · exact bd3 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (cK_bound hσ d _)
  · exact bd4 hM (by positivity) (cyT_bounds hσ d _).1 (cyT_bounds hσ d _).2 (hP_abs hσ d le_rfl _)
      (cK_bound hσ d _) (hP_abs hσ d le_rfl _) (cK_bound hσ d _)

/-- The arithmetic of the triangle inequality for the three groups of terms. -/
theorem comb_bound {ι : Type*} (s : Finset ι) {c c' a0 b0 e0 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
      e1 e2 e3 e4 e5 e6 f1 f2 f3 f4 : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    {x1 x2 x3 x4 y1 y2 y3 y4 : ι → ℝ}
    (h0 : |a0 - b0| ≤ e0) (h1 : |a1 - b1| ≤ e1) (h2 : |a2 - b2| ≤ e2) (h3 : |a3 - b3| ≤ e3)
    (h4 : |a4 - b4| ≤ e4) (h5 : |a5 - b5| ≤ e5) (h6 : |a6 - b6| ≤ e6)
    (k1 : ∀ l ∈ s, |x1 l - y1 l| ≤ f1) (k2 : ∀ l ∈ s, |x2 l - y2 l| ≤ f2)
    (k3 : ∀ l ∈ s, |x3 l - y3 l| ≤ f3) (k4 : ∀ l ∈ s, |x4 l - y4 l| ≤ f4) :
    |(a0 + c * (-2 * a1 + a2 + 3 * a3 - 3 * a4 + a5 - a6)
        + c' * ∑ l ∈ s, (4 * x1 l - 2 * x2 l - 2 * x3 l + x4 l))
      - (b0 + c * (-2 * b1 + b2 + 3 * b3 - 3 * b4 + b5 - b6)
        + c' * ∑ l ∈ s, (4 * y1 l - 2 * y2 l - 2 * y3 l + y4 l))|
      ≤ e0 + c * (2 * e1 + e2 + 3 * e3 + 3 * e4 + e5 + e6)
        + c' * ((s.card : ℝ) * (4 * f1 + 2 * f2 + 2 * f3 + f4)) := by
  have hs : |∑ l ∈ s, (4 * x1 l - 2 * x2 l - 2 * x3 l + x4 l)
      - ∑ l ∈ s, (4 * y1 l - 2 * y2 l - 2 * y3 l + y4 l)|
      ≤ (s.card : ℝ) * (4 * f1 + 2 * f2 + 2 * f3 + f4) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun l hl => ?_
    have g1 := k1 l hl; have g2 := k2 l hl; have g3 := k3 l hl; have g4 := k4 l hl
    rw [abs_le] at g1 g2 g3 g4 ⊢
    constructor <;> linarith
  have hr : |(-2 * a1 + a2 + 3 * a3 - 3 * a4 + a5 - a6)
      - (-2 * b1 + b2 + 3 * b3 - 3 * b4 + b5 - b6)|
      ≤ 2 * e1 + e2 + 3 * e3 + 3 * e4 + e5 + e6 := by
    rw [abs_le] at h1 h2 h3 h4 h5 h6 ⊢
    constructor <;> linarith
  have e : (a0 + c * (-2 * a1 + a2 + 3 * a3 - 3 * a4 + a5 - a6)
        + c' * ∑ l ∈ s, (4 * x1 l - 2 * x2 l - 2 * x3 l + x4 l))
      - (b0 + c * (-2 * b1 + b2 + 3 * b3 - 3 * b4 + b5 - b6)
        + c' * ∑ l ∈ s, (4 * y1 l - 2 * y2 l - 2 * y3 l + y4 l))
      = (a0 - b0) + c * ((-2 * a1 + a2 + 3 * a3 - 3 * a4 + a5 - a6)
          - (-2 * b1 + b2 + 3 * b3 - 3 * b4 + b5 - b6))
        + c' * (∑ l ∈ s, (4 * x1 l - 2 * x2 l - 2 * x3 l + x4 l)
          - ∑ l ∈ s, (4 * y1 l - 2 * y2 l - 2 * y3 l + y4 l)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h0 ?_)) ?_)
  · rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hr hc
  · rw [abs_mul, abs_of_nonneg hc']; exact mul_le_mul_of_nonneg_left hs hc'

variable {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
  (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
  (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
include hσ h_indep hX hlaw

/-- **(c) The mean of the polynomial statistic `Q₀ + Q₁ + Q₂ + Q₃` for every `k = n + 1 ≥ 2`**:
    it equals the main term `Mt` up to `Ctot / N²`. -/
theorem meanQT {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    |∫ ω, QT d σ N n (fun j => X j ω) ∂μ - Mt d σ N n| ≤ Ctot d σ n / (N : ℝ) ^ 2 := by
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
  have i0 : Integrable (fun ω => (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω))
      / (N : ℝ) ^ (n + 1)) μ :=
    ((BM.sum _ _ fun v _ => (⟨(cyT_meas hσ d n).comp (measurable_pi_lambda _ fun a => hX _),
      torusM d σ 1 ^ (n + 1), fun ω => by
        rw [abs_of_nonneg (cyT_bounds hσ d _).1]; exact (cyT_bounds hσ d _).2⟩ :
          BM fun ω => cyT d σ (fun a => X (v a) ω))).div_const _).integrable
  have iA : Integrable (fun ω => gA d σ N n (fun j => X j ω)) μ :=
    ((bm2 X hX _ (PhiA_meas hσ d n) hPA).div_const _).integrable
  have iB : Integrable (fun ω => gB d σ N n (fun j => X j ω)) μ :=
    ((bm2 X hX _ (PhiB_meas hσ d n) hPBb).div_const _).integrable
  have i3 : ∀ {s : ℕ} (Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ),
      Measurable Φ → (∀ p, |Φ p| ≤ B4 d σ n) →
      Integrable (fun ω => g3 N Φ (fun j => X j ω)) μ :=
    fun Φ hΦ hB => ((bm3 X hX Φ hΦ hB).div_const _).integrable
  have iEE := i3 _ (PhiEE_meas hσ d n) (hPB 0).1
  have iEB := i3 _ (PhiEB_meas hσ d n) (hPB 0).2.1
  have iBB := i3 _ (PhiBB_meas hσ d n) (hPB 0).2.2.1
  have iS := i3 _ (PhiS_meas hσ d n) (hPB 0).2.2.2.1
  have iqee := fun l => i3 _ (PhiQee_meas hσ d n l) (hPB l).2.2.2.2.1
  have iqeb := fun l => i3 _ (PhiQeb_meas hσ d n l) (hPB l).2.2.2.2.2.1
  have iqbe := fun l => i3 _ (PhiQbe_meas hσ d n l) (hPB l).2.2.2.2.2.2.1
  have iqbb := fun l => i3 _ (PhiQbb_meas hσ d n l) (hPB l).2.2.2.2.2.2.2
  have kG : Integrable (fun ω => -2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω)) μ :=
    (((((iA.const_mul (-2)).add iB).add (iEE.const_mul 3)).sub (iEB.const_mul 3)).add iBB).sub iS
  have kHl : ∀ l : Fin (n + 1), Integrable (fun ω => 4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)) μ := fun l =>
    ((((iqee l).const_mul 4).sub ((iqeb l).const_mul 2)).sub ((iqbe l).const_mul 2)).add (iqbb l)
  have kH : Integrable (fun ω => ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω))) μ :=
    integrable_finset_sum _ fun l _ => kHl l
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
  have hHs : ∫ ω, ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)) ∂μ
      = ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * ∫ ω, g3 N (PhiQee d σ n l) (fun j => X j ω) ∂μ
      - 2 * ∫ ω, g3 N (PhiQeb d σ n l) (fun j => X j ω) ∂μ
      - 2 * ∫ ω, g3 N (PhiQbe d σ n l) (fun j => X j ω) ∂μ
      + ∫ ω, g3 N (PhiQbb d σ n l) (fun j => X j ω) ∂μ) := by
    rw [integral_finset_sum _ fun l _ => kHl l]
    exact Finset.sum_congr rfl fun l _ => integral_lin4 (iqee l) (iqeb l) (iqbe l) (iqbb l)
  have kG' : Integrable (fun ω => ((n : ℝ) + 1) * (-2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω))) μ := kG.const_mul _
  have kH' : Integrable (fun ω => ((n : ℝ) + 1) / 2 * (∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)))) μ := kH.const_mul _
  have kL : Integrable (fun ω => (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω)) / (N : ℝ) ^ (n + 1) + ((n : ℝ) + 1) * (-2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω))) μ := i0.add kG'
  rw [eQ, integral_add kL kH', integral_add i0 kG',
    integral_const_mul, integral_const_mul, integral_lin6 iA iB iEE iEB iBB iS, hHs]
  -- the eleven estimates
  have h0 : |∫ ω, (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω)) / (N : ℝ) ^ (n + 1) ∂μ
      - (torusM d σ (n + 1) - ((Prs (n + 1)).card : ℝ) * torusM d σ (n + 1) / N
        + (∑ p ∈ Prs (n + 1), Ip (torusM d σ) (n + 1) p) / N)|
      ≤ (torusM d σ 1 + torusM d σ 1 * torusM d σ 1 + 2 * torusM d σ 1 ^ (n + 1))
          * ((Prs (n + 1)).card : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    have h := mean_Q0 (torusRK hσ d) X h_indep hX hlaw (N := N) (n := n) (by omega) hn
    have e0 : (fun ω => (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω))
        / (N : ℝ) ^ (n + 1)) = fun ω => (Matrix.of (fun a b : Fin N =>
          heatP d σ 1 (X a ω - X b ω) / N) ^ (n + 1)).trace :=
      funext fun ω => (trace_tilde (fun i (x y : FlatTorus d) => heatP d σ i (x - y)) N n
        (fun a : Fin N => X a ω)).symm
    rw [e0]; exact h
  have h1 : |∫ ω, gA d σ N n (fun j => X j ω) ∂μ - (∑ r, LA d σ n r) / N|
      ≤ 2 * ((n + 1 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1)
          * ((Prs (n + 1)).card : ℝ) / (N : ℝ) ^ 2 := tA hσ d X h_indep hX hlaw hN n
  have h2 : |∫ ω, gB d σ N n (fun j => X j ω) ∂μ - (∑ r, LB d σ n r) / N|
      ≤ 2 * ((n + 2 : ℕ) : ℝ) * (torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1)
          * ((Prs (n + 2)).card : ℝ) / (N : ℝ) ^ 2 := tB hσ d X h_indep hX hlaw hN n
  have hpos : ∀ s : ℕ, 0 ≤ (((s : ℝ) + (s : ℝ) ^ 2) * (N : ℝ) ^ s
      + ((Prs s).card : ℝ) * (N : ℝ) ^ (s - 1) * (2 * N + (s : ℝ) ^ 2)) := fun s => by positivity
  have h3 : |∫ ω, g3 N (PhiEE d σ n) (fun j => X j ω) ∂μ
      - (torusM d σ 2 - 1) * torusM d σ (n + 1) / N| ≤ cQ d σ n (n + 1) ((Prs (n + 1)).card)
        / (N : ℝ) ^ 2 :=
    tQ hσ d X h_indep hX hlaw hN n (n + 1) (by omega) _ (PhiEE_meas hσ d n) (hPB 0).1 _
      ((meanEE hσ d X h_indep hX hlaw N n).trans (mul_le_mul_of_nonneg_right hB4M (hpos _)))
  have h4 : |∫ ω, g3 N (PhiEB d σ n) (fun j => X j ω) ∂μ
      - (torusM d σ 3 - 1) * torusM d σ (n + 1) / N| ≤ cQ d σ n (n + 2) ((Prs (n + 2)).card)
        / (N : ℝ) ^ 2 :=
    tQ hσ d X h_indep hX hlaw hN n (n + 2) (by omega) _ (PhiEB_meas hσ d n) (hPB 0).2.1 _
      (meanEB hσ d X h_indep hX hlaw N n)
  have h5 : |∫ ω, g3 N (PhiBB d σ n) (fun j => X j ω) ∂μ
      - (torusM d σ 4 - 1) * torusM d σ (n + 1) / N| ≤ cQ d σ n (n + 3) ((Prs (n + 3)).card)
        / (N : ℝ) ^ 2 :=
    tQ hσ d X h_indep hX hlaw hN n (n + 3) (by omega) _ (PhiBB_meas hσ d n) (hPB 0).2.2.1 _
      (meanBB hσ d X h_indep hX hlaw N n)
  have h6 : |∫ ω, g3 N (PhiS d σ n) (fun j => X j ω) ∂μ
      - (torusM d σ 2 - 1) * torusM d σ (n + 1) / N| ≤ cQ d σ n (n + 2) ((Prs (n + 2)).card)
        / (N : ℝ) ^ 2 :=
    tQ hσ d X h_indep hX hlaw hN n (n + 2) (by omega) _ (PhiS_meas hσ d n) (hPB 0).2.2.2.1 _
      (meanS hσ d X h_indep hX hlaw N n)
  have k1 : ∀ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      |∫ ω, g3 N (PhiQee d σ n l) (fun j => X j ω) ∂μ
        - (Ch d σ (n + 1) l.val 2 - torusM d σ (n + 1)) / N|
        ≤ cQ d σ n (n + 1) ((Prs (n + 1)).card) / (N : ℝ) ^ 2 := fun l hl =>
    tQ hσ d X h_indep hX hlaw hN n (n + 1) (by omega) _ (PhiQee_meas hσ d n l)
      (hPB l).2.2.2.2.1 _ (meanQee hσ d X h_indep hX hlaw N n l (Finset.ne_of_mem_erase hl))
  have k2 : ∀ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      |∫ ω, g3 N (PhiQeb d σ n l) (fun j => X j ω) ∂μ
        - (Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1)) / N|
        ≤ cQ d σ n (n + 2) ((Prs (n + 2)).card) / (N : ℝ) ^ 2 := fun l hl =>
    tQ hσ d X h_indep hX hlaw hN n (n + 2) (by omega) _ (PhiQeb_meas hσ d n l)
      (hPB l).2.2.2.2.2.1 _ (meanQeb hσ d X h_indep hX hlaw N n l (Finset.ne_of_mem_erase hl))
  have k3 : ∀ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      |∫ ω, g3 N (PhiQbe d σ n l) (fun j => X j ω) ∂μ
        - (Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1)) / N|
        ≤ cQ d σ n (n + 2) ((Prs (n + 2)).card) / (N : ℝ) ^ 2 := fun l hl =>
    tQ hσ d X h_indep hX hlaw hN n (n + 2) (by omega) _ (PhiQbe_meas hσ d n l)
      (hPB l).2.2.2.2.2.2.1 _ (meanQbe hσ d X h_indep hX hlaw N n l (Finset.ne_of_mem_erase hl))
  have k4 : ∀ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      |∫ ω, g3 N (PhiQbb d σ n l) (fun j => X j ω) ∂μ
        - (Ch d σ (n + 1) l.val 4 - torusM d σ (n + 1)) / N|
        ≤ cQ d σ n (n + 3) ((Prs (n + 3)).card) / (N : ℝ) ^ 2 := fun l hl =>
    tQ hσ d X h_indep hX hlaw hN n (n + 3) (by omega) _ (PhiQbb_meas hσ d n l)
      (hPB l).2.2.2.2.2.2.2 _ (meanQbb hσ d X h_indep hX hlaw N n l (Finset.ne_of_mem_erase hl))
  unfold Mt
  refine (comb_bound _ (by positivity) (by positivity) h0 h1 h2 h3 h4 h5 h6 k1 k2 k3 k4).trans
    (le_of_eq ?_)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  unfold Ctot
  push_cast
  ring

/-- The polynomial statistic is integrable. -/
theorem QT_integrable {N n : ℕ} :
    Integrable (fun ω => QT d σ N n (fun j => X j ω)) μ := by
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
  have i0 : Integrable (fun ω => (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω))
      / (N : ℝ) ^ (n + 1)) μ :=
    ((BM.sum _ _ fun v _ => (⟨(cyT_meas hσ d n).comp (measurable_pi_lambda _ fun a => hX _),
      torusM d σ 1 ^ (n + 1), fun ω => by
        rw [abs_of_nonneg (cyT_bounds hσ d _).1]; exact (cyT_bounds hσ d _).2⟩ :
          BM fun ω => cyT d σ (fun a => X (v a) ω))).div_const _).integrable
  have iA : Integrable (fun ω => gA d σ N n (fun j => X j ω)) μ :=
    ((bm2 X hX _ (PhiA_meas hσ d n) hPA).div_const _).integrable
  have iB : Integrable (fun ω => gB d σ N n (fun j => X j ω)) μ :=
    ((bm2 X hX _ (PhiB_meas hσ d n) hPBb).div_const _).integrable
  have i3 : ∀ {s : ℕ} (Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ),
      Measurable Φ → (∀ p, |Φ p| ≤ B4 d σ n) →
      Integrable (fun ω => g3 N Φ (fun j => X j ω)) μ :=
    fun Φ hΦ hB => ((bm3 X hX Φ hΦ hB).div_const _).integrable
  have iEE := i3 _ (PhiEE_meas hσ d n) (hPB 0).1
  have iEB := i3 _ (PhiEB_meas hσ d n) (hPB 0).2.1
  have iBB := i3 _ (PhiBB_meas hσ d n) (hPB 0).2.2.1
  have iS := i3 _ (PhiS_meas hσ d n) (hPB 0).2.2.2.1
  have iqee := fun l => i3 _ (PhiQee_meas hσ d n l) (hPB l).2.2.2.2.1
  have iqeb := fun l => i3 _ (PhiQeb_meas hσ d n l) (hPB l).2.2.2.2.2.1
  have iqbe := fun l => i3 _ (PhiQbe_meas hσ d n l) (hPB l).2.2.2.2.2.2.1
  have iqbb := fun l => i3 _ (PhiQbb_meas hσ d n l) (hPB l).2.2.2.2.2.2.2
  have kG : Integrable (fun ω => -2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω)) μ :=
    (((((iA.const_mul (-2)).add iB).add (iEE.const_mul 3)).sub (iEB.const_mul 3)).add iBB).sub iS
  have kHl : ∀ l : Fin (n + 1), Integrable (fun ω => 4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)) μ := fun l =>
    ((((iqee l).const_mul 4).sub ((iqeb l).const_mul 2)).sub ((iqbe l).const_mul 2)).add (iqbb l)
  have kH : Integrable (fun ω => ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω))) μ :=
    integrable_finset_sum _ fun l _ => kHl l
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
  have kG' : Integrable (fun ω => ((n : ℝ) + 1) * (-2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω))) μ := kG.const_mul _
  have kH' : Integrable (fun ω => ((n : ℝ) + 1) / 2 * (∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)))) μ := kH.const_mul _
  have kL : Integrable (fun ω => (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω)) / (N : ℝ) ^ (n + 1) + ((n : ℝ) + 1) * (-2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω))) μ := i0.add kG'
  rw [eQ]
  exact kL.add kH'

end MeanQT2

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

section MtArith

theorem erase0_sum (n : ℕ) (f : ℕ → ℝ) :
    ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), f l.val = ∑ l ∈ Finset.Ico 1 (n + 1), f l := by
  have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin (n + 1))) (fun l => f l.val)
    (Finset.mem_univ 0)
  rw [Fin.sum_univ_eq_sum_range (fun l => f l) (n + 1), Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h1
  simp only [Fin.val_zero] at h1
  linarith

theorem card_erase0 (n : ℕ) : ((Finset.univ.erase (0 : Fin (n + 1))).card : ℝ) = n := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  simp

theorem sumCh (d : ℕ) (σ : ℝ) (n c : ℕ) (hc : 1 ≤ c) :
    ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), Ch d σ (n + 1) l.val c = sigC d σ (n + 1) c := by
  rw [erase0_sum n (fun l => Ch d σ (n + 1) l c)]
  unfold sigC
  refine Finset.sum_congr rfl fun l hl => ?_
  have := Finset.mem_Ico.mp hl
  exact Ch_eq d σ (n + 1) l c this.1 this.2 hc

theorem sumCh_sub (d : ℕ) (σ : ℝ) (n c : ℕ) (hc : 1 ≤ c) :
    ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), (Ch d σ (n + 1) l.val c - torusM d σ (n + 1))
      = sigC d σ (n + 1) c - n * torusM d σ (n + 1) := by
  rw [Finset.sum_sub_distrib, sumCh d σ n c hc, Finset.sum_const, nsmul_eq_mul, card_erase0]

theorem sumLA (d : ℕ) (σ : ℝ) (n : ℕ) :
    ∑ r, LA d σ n r = (torusM d σ 1 - 1) * torusM d σ (n + 1) + sigC d σ (n + 1) 1
      - n * torusM d σ (n + 1) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
  have e : ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)), LA d σ n r
      = ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)), (Ch d σ (n + 1) r.val 1 - torusM d σ (n + 1)) :=
    Finset.sum_congr rfl fun r hr => by
      unfold LA; rw [if_neg (Finset.ne_of_mem_erase hr)]
  rw [e, sumCh_sub d σ n 1 le_rfl]
  unfold LA; rw [if_pos rfl]; ring

theorem sumLB (d : ℕ) (σ : ℝ) (n : ℕ) :
    ∑ r, LB d σ n r = (torusM d σ 1 - 1) * torusM d σ (n + 1)
      + (torusM d σ 2 - 1) * torusM d σ (n + 1) + sigC d σ (n + 1) 2
      - n * torusM d σ (n + 1) := by
  rw [Fin.sum_univ_castSucc]
  have hlast : LB d σ n (Fin.last (n + 1)) = (torusM d σ 1 - 1) * torusM d σ (n + 1) := by
    unfold LB; rw [if_pos rfl]
  have hcs : ∀ i : Fin (n + 1), LB d σ n i.castSucc
      = if i = 0 then (torusM d σ 2 - 1) * torusM d σ (n + 1)
        else Ch d σ (n + 1) i.val 2 - torusM d σ (n + 1) := by
    intro i
    unfold LB
    rw [if_neg (Fin.castSucc_lt_last i).ne, Fin.val_castSucc]
    by_cases h : i = 0
    · subst h; simp
    · rw [if_neg (fun h' => h (Fin.ext (by simpa using h'))), if_neg h]
  simp only [hcs, hlast]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1))), if_pos rfl]
  have e : ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (if r = 0 then (torusM d σ 2 - 1) * torusM d σ (n + 1)
        else Ch d σ (n + 1) r.val 2 - torusM d σ (n + 1))
      = ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)), (Ch d σ (n + 1) r.val 2 - torusM d σ (n + 1)) :=
    Finset.sum_congr rfl fun r hr => if_neg (Finset.ne_of_mem_erase hr)
  rw [e, sumCh_sub d σ n 2 (by norm_num)]
  ring

/-- **The main term is `m_k + β_k / N`** (`k = n + 1`), Step 7 of `prop:bias`. -/
theorem Mt_eq (d : ℕ) (σ : ℝ) (N n : ℕ) :
    Mt d σ N n = torusM d σ (n + 1) + betaK d σ (n + 1) / N := by
  have hcp := card_Prs (n + 1)
  have hIp := sum_Ip (torusM d σ) (n + 1)
  have hQ : ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * ((Ch d σ (n + 1) l.val 2 - torusM d σ (n + 1)) / N)
        - 2 * ((Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1)) / N)
        - 2 * ((Ch d σ (n + 1) l.val 3 - torusM d σ (n + 1)) / N)
        + (Ch d σ (n + 1) l.val 4 - torusM d σ (n + 1)) / N)
      = (4 * (sigC d σ (n + 1) 2 - n * torusM d σ (n + 1))
        - 4 * (sigC d σ (n + 1) 3 - n * torusM d σ (n + 1))
        + (sigC d σ (n + 1) 4 - n * torusM d σ (n + 1))) / N := by
    rw [← sumCh_sub d σ n 2 (by norm_num), ← sumCh_sub d σ n 3 (by norm_num),
      ← sumCh_sub d σ n 4 (by norm_num), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by ring
  unfold Mt betaK sig0
  rw [sumLA, sumLB, hQ]
  have hc : ((Prs (n + 1)).card : ℝ) = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2 := by
    linarith
  have hI : ∑ p ∈ Prs (n + 1), Ip (torusM d σ) (n + 1) p
      = ((n + 1 : ℕ) : ℝ) * (∑ l ∈ Finset.Ico 1 (n + 1), torusM d σ l * torusM d σ (n + 1 - l)) / 2 := by
    linarith
  rw [hc, hI]
  push_cast
  ring

end MtArith

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction

section QTeq

variable {d : ℕ} {σ : ℝ}

theorem cw_eq (N n : ℕ) (x : ℕ → FlatTorus d) (v : Fin (n + 1) → Fin N) :
    cw (fun i j : Fin N => heatP d σ 1 (x i - x j) / (N : ℝ)) v
      = cyT d σ (fun a => x (v a)) / (N : ℝ) ^ (n + 1) := by
  simp only [cw, cyT, cycP]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The pair term of `Q₃` for one position `l`. -/
theorem pair_term (N n : ℕ) (x : ℕ → FlatTorus d) (l : Fin (n + 1)) :
    ∑ v : Fin (n + 1) → Fin N, cw (fun i j : Fin N => heatP d σ 1 (x i - x j) / (N : ℝ)) v
        * ((-2 * eV d σ N x (v 0) + bV d σ N x (v 0)) * (-2 * eV d σ N x (v l) + bV d σ N x (v l)))
      = 4 * g3 N (PhiQee d σ n l) x - 2 * g3 N (PhiQeb d σ n l) x
        - 2 * g3 N (PhiQbe d σ n l) x + g3 N (PhiQbb d σ n l) x := by
  simp only [cw_eq]
  have e : ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) / (N : ℝ) ^ (n + 1)
        * ((-2 * eV d σ N x (v 0) + bV d σ N x (v 0)) * (-2 * eV d σ N x (v l) + bV d σ N x (v l)))
      = (4 * ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))
            * (eV d σ N x (v 0) * eV d σ N x (v l))
          - 2 * ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))
            * (eV d σ N x (v 0) * bV d σ N x (v l))
          - 2 * ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))
            * (bV d σ N x (v 0) * eV d σ N x (v l))
          + ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))
            * (bV d σ N x (v 0) * bV d σ N x (v l))) / (N : ℝ) ^ (n + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [e, idQee, idQeb, idQbe, idQbb]
  unfold g3
  ring

/-- **(b) Identification**: the subtracted sum of `trace_expansion_paper` at the sample, with
    `ε = eV`, `bv = bV`, `sv = sV`, is the tuple statistic `QT`. -/
theorem QT_eq (N n : ℕ) (x : ℕ → FlatTorus d) (K : Fin N → Fin N → ℝ)
    (hK : K = fun i j : Fin N => heatP d σ 1 (x i - x j)) :
    (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace
      + ((n : ℝ) + 1) * ∑ i, (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)) i i
          * ((-2 * eV d σ N x i + bV d σ N x i) + (3 * eV d σ N x i ^ 2
            - 3 * eV d σ N x i * bV d σ N x i + bV d σ N x i ^ 2 - sV d σ N x i))
      + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
          ∑ v : Fin (n + 1) → Fin N, cw (fun i j => K i j / (N : ℝ)) v
            * ((-2 * eV d σ N x (v 0) + bV d σ N x (v 0))
              * (-2 * eV d σ N x (v l) + bV d σ N x (v l)))
      = QT d σ N n x := by
  subst hK
  beta_reduce
  have hT : (Matrix.of (fun i j : Fin N => heatP d σ 1 (x i - x j) / (N : ℝ)) ^ (n + 1)).trace
      = (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))) / (N : ℝ) ^ (n + 1) :=
    trace_tilde (fun i (y z : FlatTorus d) => heatP d σ i (y - z)) N n (fun a : Fin N => x a)
  have hS := diag_sum d σ N n x (fun i => (-2 * eV d σ N x i + bV d σ N x i) + (3 * eV d σ N x i ^ 2
            - 3 * eV d σ N x i * bV d σ N x i + bV d σ N x i ^ 2 - sV d σ N x i))
  have hS2 : ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))
        * ((-2 * eV d σ N x (v 0) + bV d σ N x (v 0)) + (3 * eV d σ N x (v 0) ^ 2
          - 3 * eV d σ N x (v 0) * bV d σ N x (v 0) + bV d σ N x (v 0) ^ 2 - sV d σ N x (v 0)))
      = -2 * ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * eV d σ N x (v 0)
        + ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * bV d σ N x (v 0)
        + 3 * ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * eV d σ N x (v 0) ^ 2
        - 3 * ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))
            * (eV d σ N x (v 0) * bV d σ N x (v 0))
        + ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * bV d σ N x (v 0) ^ 2
        - ∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a)) * sV d σ N x (v 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hT, hS, hS2, idA, idB, idEE, idEB, idBB, idS,
    Finset.sum_congr rfl fun l _ => pair_term N n x l]
  unfold QT gA gB g3
  ring

end QTeq

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction BiasVariance BiasVariance4

section Bounds

theorem abs_avg1 {N n : ℕ} (hN : 1 ≤ N) (f : (Fin (n + 1) → Fin N) → ℝ) {B : ℝ}
    (hB : ∀ v, |f v| ≤ B) : |(∑ v, f v) / (N : ℝ) ^ (n + 1)| ≤ B := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_div, abs_of_pos (pow_pos hNp _), div_le_iff₀ (pow_pos hNp _)]
  calc |∑ v, f v| ≤ ∑ v, |f v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v : Fin (n + 1) → Fin N, B := Finset.sum_le_sum fun v _ => hB v
    _ = B * (N : ℝ) ^ (n + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul]; push_cast; ring

theorem abs_avg2 {N s p : ℕ} (hN : 1 ≤ N) (hp : p = s + 1) (f : (Fin s → Fin N) → Fin N → ℝ)
    {B : ℝ} (hB : ∀ w u, |f w u| ≤ B) : |(∑ w, ∑ u, f w u) / (N : ℝ) ^ p| ≤ B := by
  subst hp
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_div, abs_of_pos (pow_pos hNp _), div_le_iff₀ (pow_pos hNp _)]
  calc |∑ w, ∑ u, f w u| ≤ ∑ w, ∑ u, |f w u| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun w _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _w : Fin s → Fin N, ∑ _u : Fin N, B :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun u _ => hB w u
    _ = B * (N : ℝ) ^ (s + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul]; push_cast; ring

theorem abs_avg3 {N s : ℕ} (hN : 1 ≤ N) (f : (Fin s → Fin N) → Fin N → Fin N → ℝ)
    {B : ℝ} (hB : ∀ w u u', |f w u u'| ≤ B) :
    |(∑ w, ∑ u, ∑ u', f w u u') / (N : ℝ) ^ (s + 2)| ≤ B := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_div, abs_of_pos (pow_pos hNp _), div_le_iff₀ (pow_pos hNp _)]
  calc |∑ w, ∑ u, ∑ u', f w u u'| ≤ ∑ w, ∑ u, ∑ u', |f w u u'| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun u _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _w : Fin s → Fin N, ∑ _u : Fin N, ∑ _u' : Fin N, B :=
        Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun u _ =>
          Finset.sum_le_sum fun u' _ => hB w u u'
    _ = B * (N : ℝ) ^ (s + 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul]; push_cast; ring

/-- The deterministic bound of the polynomial statistic. -/
noncomputable def CQT (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  torusM d σ 1 ^ (n + 1)
    + ((n : ℝ) + 1) * (2 * (torusM d σ 1 ^ (n + 1) * torusM d σ 1)
      + torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 + 8 * B4 d σ n)
    + ((n : ℝ) + 1) / 2 * (n : ℝ) * (9 * B4 d σ n)

theorem QT_abs {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {N : ℕ} (hN : 1 ≤ N) (n : ℕ)
    (x : ℕ → FlatTorus d) : |QT d σ N n x| ≤ CQT d σ n := by
  have hM := torusM_one_ge hσ d
  have hPB := fun l => phi_bounds hσ d n l
  have h0 : |(∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => x (v a))) / (N : ℝ) ^ (n + 1)|
      ≤ torusM d σ 1 ^ (n + 1) := abs_avg1 hN _ fun v => by
    rw [abs_of_nonneg (cyT_bounds hσ d _).1]; exact (cyT_bounds hσ d _).2
  have hA : |gA d σ N n x| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 :=
    abs_avg2 (s := n + 1) hN rfl _ fun v u => by
      unfold PhiA
      rw [abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1]
      exact mul_le_mul (cyT_bounds hσ d _).2 (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  have hB : |gB d σ N n x| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 :=
    abs_avg2 (s := n + 2) hN (by omega) _ fun w u => by
      unfold PhiB
      rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1,
        abs_of_nonneg (heatP_nonneg hσ d 1 _)]
      exact mul_le_mul (mul_le_mul (cyT_bounds hσ d _).2 (heatP_le hσ d le_rfl _)
        (heatP_nonneg hσ d 1 _) (by positivity)) (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  have h3 : ∀ {s : ℕ} (Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ),
      (∀ p, |Φ p| ≤ B4 d σ n) → |g3 N Φ x| ≤ B4 d σ n :=
    fun Φ hΦ => abs_avg3 hN _ fun w u u' => hΦ _
  have hB4 := B4_nonneg hσ d n
  have hG : |-2 * gA d σ N n x + gB d σ N n x + 3 * g3 N (PhiEE d σ n) x
      - 3 * g3 N (PhiEB d σ n) x + g3 N (PhiBB d σ n) x - g3 N (PhiS d σ n) x|
      ≤ 2 * (torusM d σ 1 ^ (n + 1) * torusM d σ 1)
        + torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 + 8 * B4 d σ n := by
    have a1 := h3 _ (hPB 0).1; have a2 := h3 _ (hPB 0).2.1
    have a3 := h3 _ (hPB 0).2.2.1; have a4 := h3 _ (hPB 0).2.2.2.1
    rw [abs_le] at hA hB a1 a2 a3 a4 ⊢
    constructor <;> linarith
  have hH : |∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) x - 2 * g3 N (PhiQeb d σ n l) x
        - 2 * g3 N (PhiQbe d σ n l) x + g3 N (PhiQbb d σ n l) x)| ≤ (n : ℝ) * (9 * B4 d σ n) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← card_erase0 n, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun l _ => ?_
    have a1 := h3 _ (hPB l).2.2.2.2.1; have a2 := h3 _ (hPB l).2.2.2.2.2.1
    have a3 := h3 _ (hPB l).2.2.2.2.2.2.1; have a4 := h3 _ (hPB l).2.2.2.2.2.2.2
    rw [abs_le] at a1 a2 a3 a4 ⊢
    constructor <;> linarith
  unfold QT CQT
  have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h0 ?_)) ?_)
  · rw [abs_mul, abs_of_nonneg hn0]; exact mul_le_mul_of_nonneg_left hG hn0
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) / 2), mul_assoc]
    exact mul_le_mul_of_nonneg_left hH (by positivity)

end Bounds

section Good

/-- **On the normalisation event** `|ρ_a - 1| ≤ δ ≤ 1/8`, for every `k = n + 1`:
    `|Tr P^k - QT| ≤ gC(k) k (9/8)^n (17/8) δ m₁ (1/N) ∑_a ε_a²` (deterministic). -/
theorem trace_QT_good {d : ℕ} {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) (n : ℕ)
    (x : ℕ → FlatTorus d) {δ : ℝ} (hδ : δ ≤ 1 / 8)
    (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ) :
    |((torusWalk d σ N x) ^ (n + 1)).trace - QT d σ N n x|
      ≤ gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * (17 / 8)
          * (δ * torusM d σ 1 * (1 / (N : ℝ) * ∑ i : Fin N, eV d σ N x i ^ 2)) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hKP : torusK d σ N x = fun i j : Fin N => heatP d σ 1 (x i - x j) := by
    funext i j; exact heatTorus_eq_heatP d σ _
  have h := trace_expansion_paper hN (torusK d σ N x) (torusRho d σ N x)
    (fun i => eV d σ N x i) (fun i => bV d σ N x i) (fun i => sV d σ N x i)
    (M := torusM d σ 1) (δ := δ)
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
    hδ (fun i => by
      show |eV d σ N x i| ≤ δ
      rw [show eV d σ N x i = heatRho d σ N x i - 1 from (eps_row d σ hN x i).symm]
      exact hρ i) n
  rw [← QT_eq N n x (torusK d σ N x) hKP]
  exact h

theorem eV_sq_sum {Ω : Type*} {d : ℕ} (σ : ℝ) {N : ℕ} (hN : 0 < N) (X : ℕ → Ω → FlatTorus d)
    (ω : Ω) :
    1 / (N : ℝ) * ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2
      = 1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω := by
  have hq : ∀ q : ℕ, eV d σ N (fun j => X j ω) q = 1 / (N : ℝ) * Hrow (cK d σ) X N q ω :=
    fun q => (eps_row d σ hN (fun j => X j ω) q).symm.trans
      (SecondStageTrace2.eps_eq_Hrow d σ N hN X ω q)
  simp only [hq]
  rw [Fin.sum_univ_eq_sum_range (fun i => (1 / (N : ℝ) * Hrow (cK d σ) X N i ω) ^ 2) N,
    Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

end Good

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 PiBound
  CTG.Reals.TorusReduction BiasVariance BiasVariance4

section Final

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The constant of the expansion remainder: `gC(k) k (9/8)^n (17/8)` for `k = n + 1`. -/
noncomputable def gK (n : ℕ) : ℝ := gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * (17 / 8)

theorem gK_nonneg (n : ℕ) : 0 ≤ gK n := by
  unfold gK; have := gC_nonneg (n + 1); positivity

/-- **`prop:bias` for every `k = n + 1 ≥ 2`, with self-loops, heat kernel on the flat torus,
    general normalisation event.** For independent uniform points, `N ≥ 1` and `0 ≤ δ ≤ 1/8`:
    `|E Tr P^k - m_k - β_k/N| ≤ 2 gK δ m₁³/N + Ctot/N² + (N + CQT) · P(max_a |ρ_a - 1| > δ)`,
    with `β_k = betaK d σ k` (the `β_k` of the proposition with `ρ = p(0)`). -/
theorem bias_general [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (n : ℕ) (hn : 1 ≤ n) :
    |∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - (torusM d σ (n + 1) + betaK d σ (n + 1) / N)|
      ≤ 2 * gK n * δ * torusM d σ 1 ^ 3 / N + Ctot d σ n / (N : ℝ) ^ 2
        + (N + CQT d σ n)
          * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
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
  have hpt : ∀ ω, |((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - QT d σ N n (fun j => X j ω)|
      ≤ gK n * δ * M * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
          Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω)
        + (N + CQT d σ n) * Gc.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ
    · have hnot : ω ∉ Gc := by rw [hGc]; exact fun h => h hω
      rw [Set.indicator_of_notMem hnot, mul_zero, add_zero, hMd]
      have h := trace_QT_good hσ hN' n (fun j => X j ω) hδ hω
      rw [eV_sq_sum σ hN' X ω] at h
      refine h.trans (le_of_eq ?_)
      unfold gK; ring
    · have hin : ω ∈ Gc := by rw [hGc]; exact hω
      rw [Set.indicator_of_mem hin, mul_one]
      have hq := QT_abs hσ d hN n (fun j => X j ω)
      have h0 : 0 ≤ gK n * δ * M * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
          Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) :=
        mul_nonneg (mul_nonneg (mul_nonneg hgK hδ0) hM0)
          (mul_nonneg (by positivity) (hS2n ω))
      obtain ⟨q1, q2⟩ := abs_le.mp hq
      obtain ⟨s1, s2⟩ := abs_le.mp (hTb ω)
      rw [abs_le]; constructor <;> linarith only [q1, q2, s1, s2, h0]
  have bg1 := BM.const_mul (gK n * δ * M) (BM.const_mul (1 / (N : ℝ) ^ 3) bS2)
  have ig2 : Integrable (fun ω => (N + CQT d σ n) * Gc.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hGcm).const_mul _
  obtain ⟨g1, hg1⟩ : ∃ g1 : Ω → ℝ, g1 = fun ω => gK n * δ * M * (1 / (N : ℝ) ^ 3
      * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) := ⟨_, rfl⟩
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
  have e2 := H.mean_E2 N
  have r := H.rs_le hN
  rw [← hMd] at r
  have hS2 : ∫ ω, ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ ≤ N * (2 * N * M ^ 2) := by
    rw [e2]; exact mul_le_mul_of_nonneg_left r hNpos.le
  have hfirst : gK n * δ * M * (1 / (N : ℝ) ^ 3 * ∫ ω, ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ) ≤ 2 * gK n * δ * M ^ 3 / N := by
    have h1 : 1 / (N : ℝ) ^ 3 * ∫ ω, ∑ q ∈ Finset.range N,
        Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ
        ≤ 1 / (N : ℝ) ^ 3 * (N * (2 * N * M ^ 2)) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg hgK hδ0) hM0 :
      0 ≤ gK n * δ * M)
    have e : gK n * δ * M * (1 / (N : ℝ) ^ 3 * (N * (2 * N * M ^ 2)))
        = 2 * gK n * δ * M ^ 3 / N := by
      field_simp
    linarith only [h2, e]
  obtain ⟨i1, i2⟩ := abs_le.mp hint
  obtain ⟨m1, m2⟩ := abs_le.mp hQm
  rw [abs_le]; constructor <;> linarith only [i1, i2, m1, m2, hfirst]

/-- **`prop:bias` for every `k = n + 1 ≥ 2`, with self-loops, heat kernel on the flat torus.**
    Under the hypotheses of `norm_sample` (`σ ≤ 1`, `d ≥ 1`, `N ≥ 2`, `kernelC1 d · δ' ≤ 1`
    with `δ' = √(m₁ log N / N)`):
    `|E Tr P^k - m_k - β_k/N| ≤ 2 gK normC δ' m₁³/N + Ctot/N² + (N + CQT)/N³`. -/
theorem bias_general_sample [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    |∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - (torusM d σ (n + 1) + betaK d σ (n + 1) / N)|
      ≤ 2 * gK n * (TorusReductionL1.normC d * δp) * torusM d σ 1 ^ 3 / N
        + Ctot d σ n / (N : ℝ) ^ 2 + (N + CQT d σ n) * (1 / (N : ℝ) ^ 3) := by
  have hr : kernelC1 d * δp * Real.sqrt ((1 : ℕ) : ℝ) ≤ 1 := by
    rw [Nat.cast_one, Real.sqrt_one, mul_one]; exact hrange
  obtain ⟨h8, hp⟩ := TorusReductionL1.norm_sample hσ hσ1 d hd X h_indep hX hlaw N 1 hN2
    Nat.one_pos hMp hδp hr
  have hδ0 : 0 ≤ TorusReductionL1.normC d * δp := by
    rw [hδp]; exact mul_nonneg (TorusReductionL1.normC_nonneg d) (Real.sqrt_nonneg _)
  have h := bias_general X h_indep hX hlaw hσ N (by omega) hδ0 h8 n hn
  have hM := torusM_one_ge hσ d
  have hc : (0 : ℝ) ≤ N + CQT d σ n := by
    have := B4_nonneg hσ d n
    unfold CQT; positivity
  have := mul_le_mul_of_nonneg_left hp hc
  linarith only [h, this]

end Final

end BiasGeneral6

end CTG.Reals2
