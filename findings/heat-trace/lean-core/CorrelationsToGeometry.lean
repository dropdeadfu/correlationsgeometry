/-
  From Correlations to Geometry (version 3) -- machine-checked algebraic core of Section 9
  Lean 4.29.0, core library only (no Mathlib).

  WHAT IS CHECKED HERE
  Every statement below is a finite algebraic consequence of the coefficient tables of the paper
  (Table "species", the table in Proposition "Mass terms", formula (pforms)).
  The entries of these tables are INPUTS: they are the results of the field-theoretic
  computations of the paper and are not derived in this file.

  In addition, Section 8 (namespace CTG.HeatTrace) checks the finite and order-theoretic core
  of Theorems "Poisson representation" and "Convergence of the heat trace" (3.11, 3.12) and of
  Appendix G (including the mode-by-mode estimates of Theorem G.4 on the rate, of the corrected
  estimator of Theorem G.5, and the discrete-time trace), over an arbitrary ordered field with a function `exp` satisfying
  exp(x+y) = exp(x) exp(y) and exp(x) ≥ 1 + x. The spectral theorem for the symmetric matrix S,
  the convergence of the exponential series, and (where stated) two Taylor bounds are inputs.

  Sections on limits (end of file): convergence of sequences is defined directly in an ordered
  field; the Poisson identity as an equality of series, the passage to infinitely many modes and
  the dominated-convergence step of Theorem G.7 are proven there, with the EXISTENCE of the sums
  of the series, and for Theorem G.7 the laws of large numbers, as hypotheses.

  Section on the Archimedean property (end of file): in an Archimedean ordered field the Taylor
  bounds of the exponential function, which are hypotheses (`IsExp2`, `IsExp3`) in the earlier
  sections, are DERIVED from exp(x+y) = exp(x) exp(y) and exp(x) ≥ 1 + x by Riemann sums
  (`isExp3_of_arch`). All statements with `IsExp2`/`IsExp3` therefore hold with `IsExp` alone there.
  The same sections prove the convergence of the exponential series (`tends_pexp`) and, with it,
  the Poisson identity `poisson_identity` and `fixed_scale_limit_arch`, whose only remaining
  hypotheses are the existence of the sums over the modes and, for the latter, the laws of large
  numbers.

  WHAT IS NOT CHECKED HERE
  None of the analytic theorems (graph Laplacian limits, decay law, heat trace, X-ray form,
  variable gap) and none of the field-theoretic computations that produce the table entries.

  Numbers are rationals; the common units (Lambda^2/960 pi^2, m^2/2880 pi^2, m^2 L/96 pi^2)
  are factored out exactly as in the paper.
-/

namespace CTG

/-! ## 0. Elementary lemmas on ordered fields (for `Rat`) -/

theorem le_of_mul_le {S T lam c : Rat} (hS : 0 < S) (h : lam * S = T) (hc : c * S ≤ T) :
    c ≤ lam := by
  apply Classical.byContradiction
  intro hn
  have h1 : lam < c := Rat.not_le.mp hn
  have h2 := Rat.mul_lt_mul_of_pos_left h1 hS
  grind

theorem ge_of_mul_ge {S T lam c : Rat} (hS : 0 < S) (h : lam * S = T) (hc : T ≤ c * S) :
    lam ≤ c := by
  apply Classical.byContradiction
  intro hn
  have h1 : c < lam := Rat.not_le.mp hn
  have h2 := Rat.mul_lt_mul_of_pos_left h1 hS
  grind

theorem sq_pos_of_ne {H : Rat} (h : H ≠ 0) : 0 < H * H := by
  rcases Rat.le_total (a := H) (b := 0) with h0 | h0
  · have hneg : 0 < -H := by grind
    have := Rat.mul_pos hneg hneg
    grind
  · have hpos : 0 < H := by grind
    exact Rat.mul_pos hpos hpos

/-! ## 1. Leading order: Table "species" (units Lambda^2 / 960 pi^2, D = 3) -/

/-- kinetic coefficient `a`, longitudinal coefficient `ell`, curvature coefficient `bR`
    (fixed number of modes), zero-point energy `vac` in units of one scalar field. -/
structure Row where
  a : Rat
  ell : Rat
  bR : Rat
  vac : Rat

def scalar (zeta : Rat) : Row := ⟨2 * (1 - 30 * zeta), 8 * (1 - 10 * zeta), 10 * (1 - 6 * zeta), 1⟩
def dirac : Row := ⟨12, 8, 20, -4⟩
def maxwell : Row := ⟨24, 16, -40, 2⟩
def proca : Row := ⟨26, 24, -30, 3⟩

/-- The three numbers per field of Remark "Reduced form": heat coefficient `kappa`,
    signed number of degrees of freedom `d`, deviation from conformality `nu`. -/
structure Red where
  kappa : Rat
  d : Rat
  nu : Rat

def redScalar (zeta : Rat) : Red := ⟨1 - 6 * zeta, 1, 1 - 6 * zeta⟩
def redDirac : Red := ⟨2, -4, 0⟩
def redMaxwell : Red := ⟨-4, 2, 0⟩
def redProca : Red := ⟨-3, 3, 1⟩

/-- Formula (reduced), first line. -/
def ofRed (r : Red) : Row :=
  ⟨-10 * r.kappa - 8 * r.d + 20 * r.nu, -20 / 3 * r.kappa - 16 / 3 * r.d + 20 * r.nu,
    10 * r.kappa, r.d⟩

/-- The reduced form reproduces all four rows of Table "species". -/
theorem reduced_scalar (zeta : Rat) : ofRed (redScalar zeta) = scalar zeta := by
  simp [ofRed, redScalar, scalar]; grind
theorem reduced_dirac : ofRed redDirac = dirac := by simp [ofRed, redDirac, dirac]; grind
theorem reduced_maxwell : ofRed redMaxwell = maxwell := by simp [ofRed, redMaxwell, maxwell]; grind
theorem reduced_proca : ofRed redProca = proca := by simp [ofRed, redProca, proca]; grind

/-- The massive vector field is the sum of the Maxwell field and a minimal scalar field. -/
theorem proca_eq_maxwell_add_scalar :
    proca.a = maxwell.a + (scalar 0).a ∧ proca.ell = maxwell.ell + (scalar 0).ell ∧
    proca.bR = maxwell.bR + (scalar 0).bR ∧ proca.vac = maxwell.vac + (scalar 0).vac := by
  simp [proca, maxwell, scalar]; grind

/-- Ratio of the kinetic coefficients scalar : Dirac : Maxwell = 1 : 6 : 12. -/
theorem ratio_a : dirac.a = 6 * (scalar 0).a ∧ maxwell.a = 12 * (scalar 0).a := by
  simp [dirac, maxwell, scalar]; grind

/-! ### Sums over a field content -/

/-- Number of entries and sum of a list of couplings, as rationals. -/
def cnt : List Rat → Rat
  | [] => 0
  | _ :: zs => 1 + cnt zs
def tot : List Rat → Rat
  | [] => 0
  | z :: zs => z + tot zs
def sumScalars (f : Row → Rat) : List Rat → Rat
  | [] => 0
  | z :: zs => f (scalar z) + sumScalars f zs

theorem sumScalars_a (zs : List Rat) : sumScalars Row.a zs = 2 * cnt zs - 60 * tot zs := by
  induction zs with
  | nil => simp [sumScalars, cnt, tot]; grind
  | cons z zs ih => simp [sumScalars, cnt, tot, scalar, ih]; grind
theorem sumScalars_ell (zs : List Rat) : sumScalars Row.ell zs = 8 * cnt zs - 80 * tot zs := by
  induction zs with
  | nil => simp [sumScalars, cnt, tot]; grind
  | cons z zs ih => simp [sumScalars, cnt, tot, scalar, ih]; grind
theorem sumScalars_bR (zs : List Rat) : sumScalars Row.bR zs = 10 * cnt zs - 60 * tot zs := by
  induction zs with
  | nil => simp [sumScalars, cnt, tot]; grind
  | cons z zs ih => simp [sumScalars, cnt, tot, scalar, ih]; grind

/-- Sums for `Ns` scalar fields with total coupling `X`, `Nd` Dirac and `Nv` Maxwell fields. -/
def Sa (Ns X Nd Nv : Rat) : Rat := 2 * Ns - 60 * X + dirac.a * Nd + maxwell.a * Nv
def Sell (Ns X Nd Nv : Rat) : Rat := 8 * Ns - 80 * X + dirac.ell * Nd + maxwell.ell * Nv
def SbR (Ns X Nd Nv : Rat) : Rat := 10 * Ns - 60 * X + dirac.bR * Nd + maxwell.bR * Nv
def Svac (Ns Nd Nv : Rat) : Rat := Ns + dirac.vac * Nd + maxwell.vac * Nv

/-- Corollary "Field contents", formula (content). -/
theorem content_ell (Ns X Nd Nv : Rat) : Sell Ns X Nd Nv = 8 * (Ns + Nd + 2 * Nv - 10 * X) := by
  simp [Sell, dirac, maxwell]; grind
theorem content_bR_sub_a (Ns X Nd Nv : Rat) :
    SbR Ns X Nd Nv - Sa Ns X Nd Nv = 8 * (Ns + Nd - 8 * Nv) := by
  simp [SbR, Sa, dirac, maxwell]; grind

/-- `lambda = 1` and `c_T = 1` at leading order iff `Ns + Nd = 8 Nv` and `X = Nv`. -/
theorem content_iff (Ns X Nd Nv : Rat) :
    (Sell Ns X Nd Nv = 0 ∧ SbR Ns X Nd Nv = Sa Ns X Nd Nv) ↔ (Ns + Nd = 8 * Nv ∧ X = Nv) := by
  simp [Sell, SbR, Sa, dirac, maxwell]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> grind

theorem content_a (Ns X Nd Nv : Rat) (h1 : Ns + Nd = 8 * Nv) (h2 : X = Nv) :
    Sa Ns X Nd Nv = 10 * (6 * Nv - Ns) := by
  simp [Sa, dirac, maxwell]; grind

/-- Formula (N4): with vanishing leading vacuum energy the induced action vanishes. -/
theorem content_N4 (Ns X Nd Nv : Rat) (h1 : Sell Ns X Nd Nv = 0)
    (h2 : SbR Ns X Nd Nv = Sa Ns X Nd Nv) (h3 : Svac Ns Nd Nv = 0) :
    Ns = 6 * Nv ∧ Nd = 2 * Nv ∧ Sa Ns X Nd Nv = 0 ∧ SbR Ns X Nd Nv = 0 := by
  simp [Sell, SbR, Sa, Svac, dirac, maxwell] at *; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Example after Corollary "Field contents": one scalar with zeta = 1, seven Dirac, one Maxwell. -/
theorem example_1_7_1 : Sell 1 1 7 1 = 0 ∧ SbR 1 1 7 1 = Sa 1 1 7 1 ∧ Sa 1 1 7 1 = 50 := by
  simp [Sell, SbR, Sa, dirac, maxwell]; grind

/-- Profile dependence (text after Proposition "profile"): general `q`. -/
def SbRsubA_q (q Ns X Nd Nv : Rat) : Rat :=
  10 * q * (Ns - 6 * X + 2 * Nd - 4 * Nv) - 2 * (Ns - 30 * X + 6 * Nd + 12 * Nv)

theorem profile_q_one (Ns X Nd Nv : Rat) :
    SbRsubA_q 1 Ns X Nd Nv = SbR Ns X Nd Nv - Sa Ns X Nd Nv := by
  simp [SbRsubA_q, SbR, Sa, dirac, maxwell]; grind

theorem profile_factor (q Ns X Nd Nv : Rat) (h1 : Sell Ns X Nd Nv = 0)
    (h2 : SbRsubA_q q Ns X Nd Nv = 0) (h3 : Svac Ns Nd Nv = 0) :
    (15 * q + 5) * (Nd - 2 * Nv) = 0 := by
  simp [Sell, SbRsubA_q, Svac, dirac, maxwell] at *; grind

/-- For every profile (`q ≥ 1`) the three conditions force `Nd = 2 Nv`, `Ns = 6 Nv`. -/
theorem profile_N4 (q Ns X Nd Nv : Rat) (hq : 1 ≤ q) (h1 : Sell Ns X Nd Nv = 0)
    (h2 : SbRsubA_q q Ns X Nd Nv = 0) (h3 : Svac Ns Nd Nv = 0) :
    Nd = 2 * Nv ∧ Ns = 6 * Nv := by
  have h := profile_factor q Ns X Nd Nv h1 h2 h3
  rcases Rat.mul_eq_zero.mp h with h | h
  · exfalso; grind
  · simp [Svac, dirac, maxwell] at h3; constructor <;> grind

/-! ## 2. The kinetic coupling `lambda = 1 - ell / a` -/

/-- Proposition "Kinetic coupling": `a > 0`, `ell ≥ 0` give `lambda ≤ 1`. -/
theorem lambda_le_one {a ell lam : Rat} (ha : 0 < a) (hl : 0 ≤ ell) (h : lam * a = a - ell) :
    lam ≤ 1 := ge_of_mul_ge ha h (by grind)

/-- Equality holds iff a longitudinal shift costs nothing. -/
theorem lambda_eq_one_iff {a ell lam : Rat} (ha : 0 < a) (h : lam * a = a - ell) :
    lam = 1 ↔ ell = 0 := by
  constructor
  · intro h1; subst h1; grind
  · intro h1
    have h2 : (lam - 1) * a = 0 := by grind
    rcases Rat.mul_eq_zero.mp h2 with h3 | h3 <;> grind

/-- Scalar field with momentum cutoff in `D` dimensions: `a = 2`, `ell = D^2 - 1`,
    hence `lambda = (3 - D^2) / 2` (formula (lambdaval)). -/
theorem lambda_scalar (D lam : Rat) (h : lam * 2 = 2 - (D * D - 1)) : lam = (3 - D * D) / 2 := by
  grind
theorem lambda_scalar_D3 (lam : Rat) (h : lam * 2 = 2 - (3 * 3 - 1)) : lam = -3 := by grind

/-- `lambda` and `c_T^2 = bR / a` of a row with `a ≠ 0`. -/
def lam (r : Row) : Rat := 1 - r.ell / r.a
def cT2 (r : Row) : Rat := r.bR / r.a

/-- Table "models", continuum rows. -/
theorem table_scalar : lam (scalar 0) = -3 ∧ cT2 (scalar 0) = 5 := by
  simp [lam, cT2, scalar]; grind
theorem table_dirac : lam dirac = 1 / 3 ∧ cT2 dirac = 5 / 3 := by
  simp [lam, cT2, dirac]; grind
theorem table_conformal_scalar :
    lam (scalar (1 / 6)) = 1 / 3 ∧ cT2 (scalar (1 / 6)) = 0 ∧ (scalar (1 / 6)).a = -8 := by
  simp [lam, cT2, scalar]; grind
theorem table_maxwell : lam maxwell = 1 / 3 ∧ cT2 maxwell = -5 / 3 := by
  simp [lam, cT2, maxwell]; grind
theorem table_proca : lam proca = 1 / 13 ∧ cT2 proca = -15 / 13 := by
  simp [lam, cT2, proca]; grind

/-- Formula (mixed): minimal scalars and Dirac fields. `lam * S = S - 4 (Ns + Nd)` with
    `S = Ns + 6 Nd` is `lambda = 1 - 4 (Ns + Nd) / (Ns + 6 Nd)`. -/
theorem mixed_sums (Ns Nd : Rat) :
    Sa Ns 0 Nd 0 = 2 * (Ns + 6 * Nd) ∧ Sell Ns 0 Nd 0 = 8 * (Ns + Nd) ∧
    SbR Ns 0 Nd 0 = 10 * (Ns + 2 * Nd) := by
  simp [Sa, Sell, SbR, dirac, maxwell]; grind

theorem mixed_lambda_range {Ns Nd lam : Rat} (hs : 0 ≤ Ns) (hd : 0 ≤ Nd) (hpos : 0 < Ns + 6 * Nd)
    (h : lam * (Ns + 6 * Nd) = (Ns + 6 * Nd) - 4 * (Ns + Nd)) : -3 ≤ lam ∧ lam ≤ 1 / 3 :=
  ⟨le_of_mul_le hpos h (by grind), ge_of_mul_ge hpos h (by grind)⟩

theorem mixed_cT2_range {Ns Nd c : Rat} (hs : 0 ≤ Ns) (hd : 0 ≤ Nd) (hpos : 0 < Ns + 6 * Nd)
    (h : c * (Ns + 6 * Nd) = 5 * (Ns + 2 * Nd)) : 5 / 3 ≤ c ∧ c ≤ 5 :=
  ⟨le_of_mul_le hpos h (by grind), ge_of_mul_ge hpos h (by grind)⟩

/-- The row `Ns = 4 Nd` of Table "models". -/
theorem table_Ns_4Nd (lam c : Rat) (h1 : lam * (4 + 6) = (4 + 6) - 4 * (4 + 1))
    (h2 : c * (4 + 6) = 5 * (4 + 2)) : lam = -1 ∧ c = 3 := by
  constructor <;> grind

/-! ## 3. Homogeneous expansion and the sign of the Friedmann equation -/

/-- For `K_ab = H h_ab` in `D = 3`: `K_ab K^ab = 3 H^2`, `K^2 = 9 H^2`, so
    `a (K_ab K^ab - lambda K^2) = 3 a (1 - 3 lambda) H^2`. -/
theorem LK_homogeneous (a lam H : Rat) :
    a * (3 * (H * H) - lam * ((3 * H) * (3 * H))) = 3 * a * (1 - 3 * lam) * (H * H) := by grind

/-- `rho = 3 a (3 lambda - 1) H^2` is negative for `a > 0`, `lambda < 1/3`, `H ≠ 0`. -/
theorem friedmann_wrong_sign {a lam H rho : Rat} (ha : 0 < a) (hl : lam < 1 / 3) (hH : H ≠ 0)
    (h : rho = 3 * a * (3 * lam - 1) * (H * H)) : rho < 0 := by
  have h1 : 0 < a * (H * H) := Rat.mul_pos ha (sq_pos_of_ne hH)
  have h2 : 0 < 1 - 3 * lam := by grind
  have h3 := Rat.mul_pos h2 h1
  grind

/-! ## 4. Concavity of the ground-state energy (core of Proposition "nocancel")

  `E b` is the minimum over states `psi` of `f psi + b * g psi` (energy linear in the shift
  amplitude `b`, state space independent of `b`). Then `E` is concave. Stated over `Rat`
  as an ordered field; the argument uses only the order and field axioms. -/

theorem energy_concave {Psi : Type} (f g : Psi → Rat) (E : Rat → Rat)
    (hle : ∀ b psi, E b ≤ f psi + b * g psi) (hatt : ∀ b, ∃ psi, E b = f psi + b * g psi)
    (b1 b2 t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * E b1 + (1 - t) * E b2 ≤ E (t * b1 + (1 - t) * b2) := by
  obtain ⟨psi, hpsi⟩ := hatt (t * b1 + (1 - t) * b2)
  have h1 := Rat.mul_le_mul_of_nonneg_left (hle b1 psi) ht0
  have h2 := Rat.mul_le_mul_of_nonneg_left (hle b2 psi) (show (0 : Rat) ≤ 1 - t by grind)
  rw [hpsi]
  grind

/-- Consequence: the even part of the energy change is non-positive, for every kind of field. -/
theorem energy_second_order_nonpos {Psi : Type} (f g : Psi → Rat) (E : Rat → Rat)
    (hle : ∀ b psi, E b ≤ f psi + b * g psi) (hatt : ∀ b, ∃ psi, E b = f psi + b * g psi)
    (b : Rat) : E b + E (-b) ≤ 2 * E 0 := by
  have h := energy_concave f g E hle hatt b (-b) (1 / 2) (by grind) (by grind)
  have h0 : (1 / 2 : Rat) * b + (1 - 1 / 2) * (-b) = 0 := by grind
  rw [h0] at h
  grind

/-- A sum of non-positive contributions vanishes only if each one vanishes
    (two species; the text after Proposition "nocancel"). -/
theorem no_cancellation {e1 e2 : Rat} (h1 : e1 ≤ 0) (h2 : e2 ≤ 0) (h : e1 + e2 = 0) :
    e1 = 0 ∧ e2 = 0 := by constructor <;> grind

/-! ## 5. Next order: Proposition "Mass terms" (units m^2 / 2880 pi^2; `w` in m^2 L / 96 pi^2) -/

structure Fin3 where
  w : Rat
  af : Rat
  bf : Rat
  ellf : Rat

def fScalar (zeta : Rat) : Fin3 := ⟨1 - 6 * zeta, 31 - 90 * zeta, 15 * (1 - 6 * zeta), -6 * (1 - 20 * zeta)⟩
def fDirac : Fin3 := ⟨2, 26, 30, -36⟩
def fProca : Fin3 := ⟨-3, -117, -45, -18⟩

/-- Formula (reduced), second line, with `w = kappa`. -/
def fOfRed (r : Red) : Fin3 :=
  ⟨r.kappa, 45 * r.kappa + 16 * r.d - 30 * r.nu, 15 * r.kappa, 10 * r.kappa + 14 * r.d - 30 * r.nu⟩

theorem reduced_fScalar (zeta : Rat) : fOfRed (redScalar zeta) = fScalar zeta := by
  simp [fOfRed, redScalar, fScalar]; grind
theorem reduced_fDirac : fOfRed redDirac = fDirac := by simp [fOfRed, redDirac, fDirac]; grind
theorem reduced_fProca : fOfRed redProca = fProca := by simp [fOfRed, redProca, fProca]; grind

/-- `b_f - a_f = -16, +4, +72` for scalar, Dirac, massive vector. -/
theorem finite_noncovariant (zeta : Rat) :
    (fScalar zeta).bf - (fScalar zeta).af = -16 ∧ fDirac.bf - fDirac.af = 4 ∧
    fProca.bf - fProca.af = 72 := by
  simp [fScalar, fDirac, fProca]; grind

/-! ### Proposition "Linear relations", from the reduced form (`Str 1 = d` per field) -/

theorem relation_i (r : Red) :
    (ofRed r).a = 3 / 4 * (ofRed r).ell - 1 / 4 * ((ofRed r).bR - (ofRed r).a) - 2 * r.d := by
  simp [ofRed]; grind
theorem relation_ii (r : Red) :
    20 * (-(fOfRed r).w) = (fOfRed r).ellf + ((fOfRed r).bf - (fOfRed r).af) + 2 * r.d := by
  simp [fOfRed]; grind
theorem relation_iii (r : Red) :
    (fOfRed r).af = -3 / 4 * (fOfRed r).ellf - 7 / 4 * ((fOfRed r).bf - (fOfRed r).af) - 3 / 2 * r.d := by
  simp [fOfRed]; grind

/-- Corollary "vanish", in the reduced form: covariance (`ell = 0`, `bR = a`) and vanishing
    supertrace (`d = 0`) force `kappa = nu = 0` and `a = 0`, at the leading order ... -/
theorem vanish_leading (r : Red) (h1 : (ofRed r).ell = 0) (h2 : (ofRed r).bR = (ofRed r).a)
    (h3 : r.d = 0) : r.kappa = 0 ∧ r.nu = 0 ∧ (ofRed r).a = 0 := by
  simp [ofRed] at *; refine ⟨?_, ?_, ?_⟩ <;> grind
/-- ... and at the order `m^2` (finite parts and logarithm). -/
theorem vanish_finite (r : Red) (h1 : (fOfRed r).ellf = 0) (h2 : (fOfRed r).bf = (fOfRed r).af)
    (h3 : r.d = 0) : r.kappa = 0 ∧ r.nu = 0 ∧ (fOfRed r).af = 0 ∧ (fOfRed r).w = 0 := by
  simp [fOfRed] at *; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ### Corollary "The next order": sums with `Ms, Md, Mv` and `Z = sum zeta m^2` -/

def Nell (Z Ms Md Mv : Rat) : Rat := 120 * Z - 6 * Ms - 36 * Md - 18 * Mv
def Nlog (Z Ms Md Mv : Rat) : Rat := 6 * Z - Ms - 2 * Md + 3 * Mv
def Naf (Z Ms Md Mv : Rat) : Rat := 31 * Ms - 90 * Z + 26 * Md - 117 * Mv
def NbSubA (Ms Md Mv : Rat) : Rat := -16 * Ms + 4 * Md + 72 * Mv
def StrM2 (Ms Md Mv : Rat) : Rat := Ms + 3 * Mv - 4 * Md

/-- These are the sums of the table of Proposition "Mass terms" (one field of each kind). -/
theorem next_sums (zeta ms md mv : Rat) :
    (fScalar zeta).ellf * ms + fDirac.ellf * md + fProca.ellf * mv = Nell (zeta * ms) ms md mv ∧
    -(fScalar zeta).w * ms - fDirac.w * md - fProca.w * mv = Nlog (zeta * ms) ms md mv ∧
    (fScalar zeta).af * ms + fDirac.af * md + fProca.af * mv = Naf (zeta * ms) ms md mv ∧
    ((fScalar zeta).bf - (fScalar zeta).af) * ms + (fDirac.bf - fDirac.af) * md
      + (fProca.bf - fProca.af) * mv = NbSubA ms md mv := by
  simp [fScalar, fDirac, fProca, Nell, Nlog, Naf, NbSubA]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- (i) Without massive vector fields a positive kinetic term forces `sum ell > 0`. -/
theorem next_i (Z Ms Md : Rat) (hs : 0 ≤ Ms) (hd : 0 ≤ Md) (ha : 0 < Nlog Z Ms Md 0) :
    Nell Z Ms Md 0 = 20 * Nlog Z Ms Md 0 + 14 * Ms + 4 * Md ∧ 20 * Nlog Z Ms Md 0 ≤ Nell Z Ms Md 0
    ∧ 0 < Nell Z Ms Md 0 := by
  simp [Nell, Nlog] at *; refine ⟨?_, ?_, ?_⟩ <;> grind

/-- (ii) A positive kinetic term and `sum ell ≤ 0` are compatible iff `7 Ms + 2 Md < 39 Mv`. -/
theorem next_ii (Ms Md Mv : Rat) :
    (∃ Z : Rat, 0 < Nlog Z Ms Md Mv ∧ Nell Z Ms Md Mv ≤ 0) ↔ 7 * Ms + 2 * Md < 39 * Mv := by
  simp only [Nlog, Nell]
  constructor
  · intro ⟨Z, h1, h2⟩; grind
  · intro h; exact ⟨(6 * Ms + 36 * Md + 18 * Mv) / 120, by grind, by grind⟩

/-- The example after Corollary "The next order" (masses in units of `m_v^2`). -/
theorem next_example :
    Nell (3 / 8) (9 / 2) 0 1 = 0 ∧ NbSubA (9 / 2) 0 1 = 0 ∧ Nlog (3 / 8) (9 / 2) 0 1 = 3 / 4 ∧
    StrM2 (9 / 2) 0 1 ≠ 0 := by
  simp [Nell, NbSubA, Nlog, StrM2]; refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- Its leading order: five scalars with total coupling 1, two Dirac fields, one massive vector. -/
theorem next_example_leading :
    8 * 5 - 80 * 1 + dirac.ell * 2 + proca.ell = (0 : Rat) ∧
    (10 * 5 - 60 * 1 + dirac.bR * 2 + proca.bR) - (2 * 5 - 60 * 1 + dirac.a * 2 + proca.a) = (0 : Rat) ∧
    5 + dirac.vac * 2 + proca.vac = (0 : Rat) := by
  simp [dirac, proca]; refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Corollary "vanish", sharp cutoff: the conditions at the order `m^2` fix the ratios
    `Ms : Z : Md : Mv = 5 : 1 : 2 : 1`, and then the induced action vanishes. -/
theorem vanish_ratios (Z Ms Md Mv : Rat) (h1 : StrM2 Ms Md Mv = 0) (h2 : Nell Z Ms Md Mv = 0)
    (h3 : NbSubA Ms Md Mv = 0) :
    Ms = 5 * Mv ∧ Z = Mv ∧ Md = 2 * Mv ∧ Nlog Z Ms Md Mv = 0 ∧ Naf Z Ms Md Mv = 0 := by
  simp [StrM2, Nell, NbSubA, Nlog, Naf] at *; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- General profile: `b_f = 30 kappa (r - 1/2)`; the three numbers of (iii). -/
def NbSubA_r (r Z Ms Md Mv : Rat) : Rat :=
  (30 * r - 46) * Ms - 180 * (r - 1) * Z + (60 * r - 56) * Md + (162 - 90 * r) * Mv

theorem profile_numbers (r zeta : Rat) :
    30 * (1 - 6 * zeta) * (r - 1 / 2) - (fScalar zeta).af = (30 * r - 46) - 180 * (r - 1) * zeta ∧
    30 * fDirac.w * (r - 1 / 2) - fDirac.af = 60 * r - 56 ∧
    30 * fProca.w * (r - 1 / 2) - fProca.af = 162 - 90 * r := by
  simp [fScalar, fDirac, fProca]; refine ⟨?_, ?_, ?_⟩ <;> grind

theorem profile_sharp (Z Ms Md Mv : Rat) : NbSubA_r 1 Z Ms Md Mv = NbSubA Ms Md Mv := by
  simp [NbSubA_r, NbSubA]; grind

theorem vanish_factor (r Z Ms Md Mv : Rat) (h1 : StrM2 Ms Md Mv = 0) (h2 : Nell Z Ms Md Mv = 0) :
    NbSubA_r r Z Ms Md Mv = (90 * r - 150) * (Md - 2 * Mv) := by
  simp [StrM2, Nell, NbSubA_r] at *
  have hZ : Z = Md / 2 := by grind
  have hM : Ms = 4 * Md - 3 * Mv := by grind
  subst hZ; subst hM; grind

/-- The ratios hold for every profile (`r ≤ 1`). -/
theorem vanish_ratios_profile (r Z Ms Md Mv : Rat) (hr : r ≤ 1) (h1 : StrM2 Ms Md Mv = 0)
    (h2 : Nell Z Ms Md Mv = 0) (h3 : NbSubA_r r Z Ms Md Mv = 0) :
    Ms = 5 * Mv ∧ Z = Mv ∧ Md = 2 * Mv ∧ Nlog Z Ms Md Mv = 0 ∧ Naf Z Ms Md Mv = 0 := by
  rw [vanish_factor r Z Ms Md Mv h1 h2] at h3
  have hMd : Md = 2 * Mv := by
    rcases Rat.mul_eq_zero.mp h3 with h | h <;> grind
  simp [StrM2, Nell, Nlog, Naf] at *; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-! ## 6. Form fields in any dimension (Proposition "pforms", formula (reducedD)) -/

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- Number of polarisations `d` and index `I` of a `p`-form in `D = n + 1` dimensions. -/
def dP (D p : Nat) : Int := binom (D - 1) p
def iP (D p : Nat) : Int := if p = 0 then 0 else binom (D - 3) (p - 1)
def aP (D p : Nat) : Int := 2 * dP D p + 4 * ((D : Int) ^ 2 - 4) * iP D p
def ellP (D p : Nat) : Int := ((D : Int) ^ 2 - 1) * dP D p
def kappaP (D p : Nat) : Int := dP D p - 6 * iP D p

/-- Formula (reducedD), multiplied by 3 and with `(D-1)^2 nu = d (D-1-2p)^2`,
    so that everything is an integer. -/
def aRed3 (D p : Nat) : Int :=
  -2 * D * ((D : Int) ^ 2 - 4) * kappaP D p - D * ((D : Int) ^ 2 - 1) * dP D p
    + 3 * ((D : Int) + 2) * dP D p * ((D : Int) - 1 - 2 * p) ^ 2
def ellRed3 (D p : Nat) : Int :=
  -2 * ((D : Int) - 1) * ((D : Int) ^ 2 - 4) * kappaP D p - ((D : Int) - 1) * ((D : Int) ^ 2 - 1) * dP D p
    + 3 * ((D : Int) + 2) * dP D p * ((D : Int) - 1 - 2 * p) ^ 2

def checkForms (Dmax : Nat) : Bool :=
  (List.range (Dmax - 2)).all fun i =>
    let D := i + 3
    (List.range D).all fun p =>
      aRed3 D p == 3 * aP D p && ellRed3 D p == 3 * ellP D p
      -- duality p <-> D - 1 - p
      && aP D p == aP D (D - 1 - p) && ellP D p == ellP D (D - 1 - p)
      && kappaP D p == kappaP D (D - 1 - p)
      -- (D-1)^2 nu = (D-1)^2 d - 4 (D-1)(D-2) I
      && dP D p * ((D : Int) - 1 - 2 * p) ^ 2
          == ((D : Int) - 1) ^ 2 * dP D p - 4 * ((D : Int) - 1) * ((D : Int) - 2) * iP D p

/-- The three-parameter law reproduces all form fields for `3 ≤ D ≤ 12`, with duality. -/
theorem forms_checked : checkForms 12 = true := by decide

/-- `D = 3`: the 1-form is the Maxwell row, the 0-form and the 2-form the minimal scalar. -/
theorem forms_D3 :
    aP 3 1 = 24 ∧ ellP 3 1 = 16 ∧ kappaP 3 1 = -4 ∧ aP 3 0 = 2 ∧ ellP 3 0 = 8 ∧ aP 3 2 = 2 := by
  decide

/-- `a = b_fix / D + (2/3)(D^2 - 1) d` with `b_fix = -(2/3) D (D^2 - 4) kappa`,
    written without the division: `D a = b_fix + (2/3) D (D^2 - 1) d`, for all `d, I`. -/
theorem forms_structure (D d I : Rat) :
    D * (2 * d + 4 * (D * D - 4) * I)
      = -(2 / 3) * D * (D * D - 4) * (d - 6 * I) + 2 / 3 * D * (D * D - 1) * d := by
  grind

/-! ## 7. Time reversal and the local symplectic invariants (Proposition "Todd")

  Covariance matrix of two modes in the order `(phi_A, pi_A, phi_B, pi_B)`. Time reversal
  `(phi, pi) -> (phi, -pi)` flips the sign of every entry with exactly one momentum index.
  The four local symplectic invariants `det sigma_A`, `det sigma_B`, `det sigma_AB`, `det sigma`
  are unchanged. (That they form a complete set is a cited theorem, not checked here.) -/

def det2 (a b c d : Rat) : Rat := a * d - b * c
def det3 (a b c d e f g h i : Rat) : Rat := a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
def det4 (m11 m12 m13 m14 m21 m22 m23 m24 m31 m32 m33 m34 m41 m42 m43 m44 : Rat) : Rat :=
  m11 * det3 m22 m23 m24 m32 m33 m34 m42 m43 m44 - m12 * det3 m21 m23 m24 m31 m33 m34 m41 m43 m44
    + m13 * det3 m21 m22 m24 m31 m32 m34 m41 m42 m44 - m14 * det3 m21 m22 m23 m31 m32 m33 m41 m42 m43

theorem todd_local (x y p : Rat) : det2 x (-y) (-y) p = det2 x y y p := by simp [det2]; grind
theorem todd_cross (c11 c12 c21 c22 : Rat) : det2 c11 (-c12) (-c21) c22 = det2 c11 c12 c21 c22 := by
  simp [det2]; grind
theorem todd_global (x1 y1 p1 x2 y2 p2 c11 c12 c21 c22 : Rat) :
    det4 x1 (-y1) c11 (-c12) (-y1) p1 (-c21) c22 c11 (-c21) x2 (-y2) (-c12) c22 (-y2) p2
      = det4 x1 y1 c11 c12 y1 p1 c21 c22 c11 c21 x2 y2 c12 c22 y2 p2 := by
  simp [det4, det3]; grind

end CTG

/-! ## 8. The heat trace (Theorems 3.11, 3.12 and Appendix G) -/

set_option linter.unusedSectionVars false

namespace CTG.HeatTrace
open Lean.Grind

section Exp
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

theorem mul_self_nonneg (a : α) : 0 ≤ a * a := by
  have h := OrderedRing.sq_nonneg (a := a)
  have h2 : a ^ 2 = a * a := by grind
  rw [h2] at h; exact h

/-- An exponential function on an ordered field, characterised by two properties only. -/
structure IsExp (exp : α → α) : Prop where
  add : ∀ x y, exp (x + y) = exp x * exp y
  ge : ∀ x, 1 + x ≤ exp x

namespace IsExp
variable {exp : α → α}

theorem zero (h : IsExp exp) : exp 0 = 1 := by
  have h1 := h.add 0 0
  rw [show (0 : α) + 0 = 0 by grind] at h1
  have h2 := h.ge 0
  have h3 : (0 : α) ≤ exp 0 - 1 := by grind
  have h4 := OrderedRing.mul_le_mul_of_nonneg_left (show (1 : α) ≤ exp 0 by grind) h3
  grind

theorem nonneg (h : IsExp exp) (x : α) : 0 ≤ exp x := by
  have h1 := h.add (x / 2) (x / 2)
  rw [show x / 2 + x / 2 = x by grind] at h1
  rw [h1]; exact mul_self_nonneg _

theorem tangent (h : IsExp exp) (x y : α) : exp y * (1 + (x - y)) ≤ exp x := by
  have h1 := h.add y (x - y)
  rw [show y + (x - y) = x by grind] at h1
  rw [h1]
  exact OrderedRing.mul_le_mul_of_nonneg_left (h.ge (x - y)) (h.nonneg y)

theorem mono (h : IsExp exp) {x y : α} (hxy : x ≤ y) : exp x ≤ exp y := by
  have h1 := h.tangent y x
  have h2 := OrderedRing.mul_nonneg (h.nonneg x) (show (0 : α) ≤ y - x by grind)
  grind

theorem le_one (h : IsExp exp) {x : α} (hx : x ≤ 0) : exp x ≤ 1 := by
  have := h.mono hx; rw [h.zero] at this; exact this

/-- `|e^{-x} - e^{-y}| ≤ |x - y| e^{-min(x,y)}` (used for the low modes), for `x ≤ y`. -/
theorem lipschitz (h : IsExp exp) {x y : α} (hxy : x ≤ y) :
    0 ≤ exp (-x) - exp (-y) ∧ exp (-x) - exp (-y) ≤ (y - x) * exp (-x) := by
  have h1 := h.tangent (-y) (-x)
  have h2 := h.mono (show -y ≤ -x by grind)
  constructor <;> grind
end IsExp

/-! ### The trace as a sum over the eigenvalues `s_a` of `S`

  `heat exp tau s = sum_a exp(-tau (1 - s_a))` is `Tr e^{-t L}` in terms of the spectrum of `S`
  (the spectral theorem for the symmetric matrix `S` is the bridge and is not formalised).
  `cnt s = N`, `lsum s = Tr S = Tr P`, `lsumsq s = Tr S^2 = Tr P^2`. -/

def lsum : List α → α
  | [] => 0
  | a :: l => a + lsum l
def cnt : List α → α
  | [] => 0
  | _ :: l => 1 + cnt l
def lsumsq : List α → α
  | [] => 0
  | a :: l => a * a + lsumsq l
def heat (exp : α → α) (tau : α) : List α → α
  | [] => 0
  | a :: l => exp (-(tau * (1 - a))) + heat exp tau l

variable {exp : α → α}

/-- Upper bound of Theorem "Poisson representation": `Tr e^{-tL} ≤ N`. -/
theorem heat_le_cnt (h : IsExp exp) {tau : α} (ht : 0 ≤ tau) :
    ∀ s : List α, (∀ a ∈ s, a ≤ 1) → heat exp tau s ≤ cnt s
  | [], _ => by simp [heat, cnt] <;> grind
  | a :: l, hs => by
    have ih := heat_le_cnt h ht l (fun b hb => hs b (List.mem_cons_of_mem _ hb))
    have ha : a ≤ 1 := hs a List.mem_cons_self
    have h1 := OrderedRing.mul_nonneg ht (show (0 : α) ≤ 1 - a by grind)
    have h2 := h.le_one (show -(tau * (1 - a)) ≤ 0 by grind)
    simp [heat, cnt] <;> grind

/-- Supporting-line inequality for the whole trace, at an arbitrary point `y`. -/
theorem heat_tangent (h : IsExp exp) (tau y : α) :
    ∀ s : List α, exp y * (cnt s + (tau * lsum s - tau * cnt s) - cnt s * y) ≤ heat exp tau s
  | [] => by simp [heat, cnt, lsum] <;> grind
  | a :: l => by
    have ih := heat_tangent h tau y l
    have h1 := h.tangent (-(tau * (1 - a))) y
    simp [heat, cnt, lsum] <;> grind

/-- Two-term bound: `e^{-tau} (N + tau Tr P) ≤ Tr e^{-tL}`, with no condition on the spectrum.
    Equivalently the twice-subtracted trace is nonnegative. -/
theorem heat_two_term (h : IsExp exp) (tau : α) (s : List α) :
    exp (-tau) * (cnt s + tau * lsum s) ≤ heat exp tau s := by
  have h1 := heat_tangent h tau (-tau) s
  grind

/-- Lower bound of Theorem "Poisson representation": `N e^{-tau} ≤ Tr e^{-tL}`.
    Only `Tr P ≥ 0` and `tau ≥ 0` are used. -/
theorem cnt_mul_exp_le_heat (h : IsExp exp) {tau : α} (ht : 0 ≤ tau) (s : List α)
    (hs : 0 ≤ lsum s) : cnt s * exp (-tau) ≤ heat exp tau s := by
  have h1 := heat_two_term h tau s
  have h2 := OrderedRing.mul_nonneg (h.nonneg (-tau)) (OrderedRing.mul_nonneg ht hs)
  grind

/-- Jensen form: `N e^{-tau (1 - m)} ≤ Tr e^{-tL}` with `m = Tr P / N` (written `N m = Tr P`). -/
theorem heat_jensen (h : IsExp exp) (tau m : α) (s : List α) (hm : cnt s * m = lsum s) :
    cnt s * exp (-(tau * (1 - m))) ≤ heat exp tau s := by
  have h1 := heat_tangent h tau (-(tau * (1 - m))) s
  have h2 : cnt s + (tau * lsum s - tau * cnt s) - cnt s * (-(tau * (1 - m))) = cnt s := by
    rw [← hm]; grind
  rw [h2] at h1; grind

/-- The trace is nonincreasing in `tau`. -/
theorem heat_antitone (h : IsExp exp) {t1 t2 : α} (ht : t1 ≤ t2) :
    ∀ s : List α, (∀ a ∈ s, a ≤ 1) → heat exp t2 s ≤ heat exp t1 s
  | [], _ => by simp [heat] <;> grind
  | a :: l, hs => by
    have ih := heat_antitone h ht l (fun b hb => hs b (List.mem_cons_of_mem _ hb))
    have ha : a ≤ 1 := hs a List.mem_cons_self
    have h1 := OrderedRing.mul_nonneg (show (0 : α) ≤ t2 - t1 by grind) (show (0 : α) ≤ 1 - a by grind)
    have h2 := h.mono (show -(t2 * (1 - a)) ≤ -(t1 * (1 - a)) by grind)
    simp [heat] <;> grind

/-- Weighted Jensen inequality (supporting-line form), for the diagonal entries
    `(e^{tau S})_{ii} = sum_a w_a e^{tau s_a}` with `w_a = |v_a(i)|^2`. -/
def wsum : List (α × α) → α
  | [] => 0
  | p :: l => p.1 + wsum l
def wxsum : List (α × α) → α
  | [] => 0
  | p :: l => p.1 * p.2 + wxsum l
def wexpsum (exp : α → α) : List (α × α) → α
  | [] => 0
  | p :: l => p.1 * exp p.2 + wexpsum exp l

theorem wjensen_tangent (h : IsExp exp) (y : α) :
    ∀ l : List (α × α), (∀ p ∈ l, 0 ≤ p.1) →
      exp y * (wsum l + wxsum l - wsum l * y) ≤ wexpsum exp l
  | [], _ => by simp [wsum, wxsum, wexpsum] <;> grind
  | p :: l, hl => by
    have ih := wjensen_tangent h y l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left (h.tangent p.2 y) (hl p List.mem_cons_self)
    simp [wsum, wxsum, wexpsum] <;> grind

/-- `exp(sum_a w_a x_a) ≤ sum_a w_a exp(x_a)` for weights `w_a ≥ 0` with `sum_a w_a = 1`. -/
theorem wjensen (h : IsExp exp) (l : List (α × α)) (hw : ∀ p ∈ l, 0 ≤ p.1) (h1 : wsum l = 1) :
    exp (wxsum l) ≤ wexpsum exp l := by
  have h2 := wjensen_tangent h (wxsum l) l hw
  rw [h1] at h2; grind

/-! ### Second order: the high modes of Theorem "Convergence of the heat trace"

  The two Taylor bounds `e^x - 1 - x ≤ (x^2/2) e^{max(x,0)}` are standard facts of real
  analysis; they are HYPOTHESES here. -/

structure IsExp2 (exp : α → α) : Prop extends IsExp exp where
  taylor_nonneg : ∀ x, 0 ≤ x → exp x - 1 - x ≤ x * x / 2 * exp x
  taylor_nonpos : ∀ x, x ≤ 0 → exp x - 1 - x ≤ x * x / 2

/-- One mode with `s ≤ 1 - kappa`:
    `e^{-tau} (e^{tau s} - 1 - tau s) ≤ (tau s)^2/2 e^{-kappa tau}`. -/
theorem high_mode (h : IsExp2 exp) {tau kappa s : α} (ht : 0 ≤ tau)
    (hk1 : kappa ≤ 1) (hs : s ≤ 1 - kappa) :
    exp (-tau) * (exp (tau * s) - 1 - tau * s) ≤ (tau * s) * (tau * s) / 2 * exp (-(kappa * tau)) := by
  have hE : IsExp exp := h.toIsExp
  have hsq : (0 : α) ≤ (tau * s) * (tau * s) / 2 := by
    have := mul_self_nonneg (tau * s); grind
  by_cases h0 : 0 ≤ s
  · have hx := OrderedRing.mul_nonneg ht h0
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left (h.taylor_nonneg (tau * s) hx) (hE.nonneg (-tau))
    have h2 := hE.add (-tau) (tau * s)
    have h3 := OrderedRing.mul_nonneg ht (show (0 : α) ≤ 1 - s - kappa by grind)
    have h4 := hE.mono (show -tau + tau * s ≤ -(kappa * tau) by grind)
    rw [h2] at h4
    have h5 := OrderedRing.mul_le_mul_of_nonneg_left h4 hsq
    have h6 : exp (-tau) * (tau * s * (tau * s) / 2 * exp (tau * s))
        = tau * s * (tau * s) / 2 * (exp (-tau) * exp (tau * s)) := by grind
    rw [h6] at h1
    exact Std.le_trans h1 h5
  · have hs0 : s ≤ 0 := by grind
    have hx := OrderedRing.mul_nonneg ht (show (0 : α) ≤ -s by grind)
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left
      (h.taylor_nonpos (tau * s) (by grind)) (hE.nonneg (-tau))
    have h3 := OrderedRing.mul_nonneg ht (show (0 : α) ≤ 1 - kappa by grind)
    have h4 := hE.mono (show -tau ≤ -(kappa * tau) by grind)
    have h5 := OrderedRing.mul_le_mul_of_nonneg_left h4 hsq
    have h6 : exp (-tau) * (tau * s * (tau * s) / 2) = tau * s * (tau * s) / 2 * exp (-tau) := by grind
    rw [h6] at h1
    exact Std.le_trans h1 h5

def phisum (exp : α → α) (tau : α) : List α → α
  | [] => 0
  | a :: l => exp (-tau) * (exp (tau * a) - 1 - tau * a) + phisum exp tau l

/-- Sum over the high modes: `≤ (tau^2/2) e^{-kappa tau} Tr S^2`. -/
theorem high_modes (h : IsExp2 exp) {tau kappa : α} (ht : 0 ≤ tau)
    (hk1 : kappa ≤ 1) :
    ∀ s : List α, (∀ a ∈ s, a ≤ 1 - kappa) →
      phisum exp tau s ≤ tau * tau / 2 * exp (-(kappa * tau)) * lsumsq s
  | [], _ => by simp [phisum, lsumsq] <;> grind
  | a :: l, hs => by
    have ih := high_modes h ht hk1 l (fun b hb => hs b (List.mem_cons_of_mem _ hb))
    have h1 := high_mode h ht hk1 (hs a List.mem_cons_self)
    simp [phisum, lsumsq] <;> grind

/-- Exact identity: `Tr e^{-tL} = e^{-tau} (N + tau Tr P) + sum_a e^{-tau} phi(tau s_a)`. -/
theorem heat_eq_two_term_add (h : IsExp exp) (tau : α) :
    ∀ s : List α, heat exp tau s = exp (-tau) * (cnt s + tau * lsum s) + phisum exp tau s
  | [] => by simp [heat, cnt, lsum, phisum] <;> grind
  | a :: l => by
    have ih := heat_eq_two_term_add h tau l
    have h1 := h.add (-tau) (tau * a)
    rw [show -tau + tau * a = -(tau * (1 - a)) by grind] at h1
    simp [heat, cnt, lsum, phisum] <;> grind

/-- Two-sided bound for the twice-subtracted trace:
    `0 ≤ Tr e^{-tL} - e^{-tau}(N + tau Tr P) ≤ (tau^2/2) Tr S^2`. -/
theorem two_term_remainder (h : IsExp2 exp) {tau : α} (ht : 0 ≤ tau) (s : List α)
    (hs : ∀ a ∈ s, a ≤ 1) :
    0 ≤ heat exp tau s - exp (-tau) * (cnt s + tau * lsum s) ∧
    heat exp tau s - exp (-tau) * (cnt s + tau * lsum s) ≤ tau * tau / 2 * lsumsq s := by
  have hE : IsExp exp := h.toIsExp
  have h1 := heat_two_term hE tau s
  have h2 := heat_eq_two_term_add hE tau s
  have h3 := high_modes h ht (show (0 : α) ≤ 1 by grind) s
    (fun a ha => by have := hs a ha; grind)
  rw [show -((0 : α) * tau) = 0 by grind, hE.zero] at h3
  constructor <;> grind

end Exp

/-! ### The random walk: `0 ≤ Tr P^k ≤ N` and the Poisson partial sums

  `I` is the list of nodes, matrices are functions `ι → ι → α`. The hypothesis `hI` says that
  `I` lists every node exactly once (the identity matrix has row sums one). -/

section Walk
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {ι : Type}

def msum : List ι → (ι → α) → α
  | [], _ => 0
  | i :: I, f => f i + msum I f
def ncnt : List ι → α
  | [] => 0
  | _ :: I => 1 + ncnt I

theorem msum_congr : ∀ (I : List ι) (f g : ι → α), (∀ i ∈ I, f i = g i) → msum I f = msum I g
  | [], _, _, _ => rfl
  | i :: I, f, g, h => by
    have ih := msum_congr I f g (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have h1 := h i List.mem_cons_self
    simp [msum, ih, h1]

theorem msum_nonneg : ∀ (I : List ι) (f : ι → α), (∀ i ∈ I, 0 ≤ f i) → 0 ≤ msum I f
  | [], _, _ => by simp [msum] <;> grind
  | i :: I, f, h => by
    have ih := msum_nonneg I f (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have h1 := h i List.mem_cons_self
    simp [msum] <;> grind

theorem msum_le : ∀ (I : List ι) (f g : ι → α), (∀ i ∈ I, f i ≤ g i) → msum I f ≤ msum I g
  | [], _, _, _ => by simp [msum] <;> grind
  | i :: I, f, g, h => by
    have ih := msum_le I f g (fun j hj => h j (List.mem_cons_of_mem _ hj))
    have h1 := h i List.mem_cons_self
    simp [msum] <;> grind

theorem msum_zero : ∀ (I : List ι), msum I (fun _ => (0 : α)) = 0
  | [] => rfl
  | _ :: I => by
    have ih : msum I (fun _ => (0 : α)) = 0 := msum_zero I
    simp [msum, ih] <;> grind

theorem msum_one : ∀ (I : List ι), msum I (fun _ => (1 : α)) = ncnt I
  | [] => rfl
  | _ :: I => by
    have ih : msum I (fun _ => (1 : α)) = ncnt I := msum_one I
    simp [msum, ncnt, ih]

theorem msum_add : ∀ (I : List ι) (f g : ι → α), msum I (fun i => f i + g i) = msum I f + msum I g
  | [], _, _ => by simp [msum] <;> grind
  | _ :: I, f, g => by have ih := msum_add I f g; simp [msum, ih] <;> grind

theorem msum_mul_left (c : α) : ∀ (I : List ι) (f : ι → α), msum I (fun i => c * f i) = c * msum I f
  | [], _ => by simp [msum] <;> grind
  | _ :: I, f => by have ih := msum_mul_left c I f; simp [msum, ih] <;> grind

/-- Exchange of two finite sums. -/
theorem msum_comm (J : List ι) : ∀ (I : List ι) (f : ι → ι → α),
    msum I (fun i => msum J (fun j => f i j)) = msum J (fun j => msum I (fun i => f i j))
  | [], f => by simp [msum]; exact (msum_zero J).symm
  | i :: I, f => by
    have ih := msum_comm J I f
    have h1 := msum_add J (fun j => f i j) (fun j => msum I (fun i => f i j))
    simp [msum, ih]; exact h1.symm

def mmul (I : List ι) (A B : ι → ι → α) : ι → ι → α := fun i j => msum I (fun k => A i k * B k j)
def tr (I : List ι) (A : ι → ι → α) : α := msum I (fun i => A i i)

/-- Row-stochastic matrix with nonnegative entries. -/
structure Stoch (I : List ι) (P : ι → ι → α) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  row : ∀ i, msum I (fun j => P i j) = 1

theorem Stoch.mul {I : List ι} {A B : ι → ι → α} (hA : Stoch I A) (hB : Stoch I B) :
    Stoch I (mmul I A B) where
  nonneg := fun i j => msum_nonneg I _ (fun k _ => OrderedRing.mul_nonneg (hA.nonneg i k) (hB.nonneg k j))
  row := fun i => by
    have h1 := msum_comm (α := α) I I (fun j k => A i k * B k j)
    have h2 : msum I (fun k => msum I (fun j => A i k * B k j)) = msum I (fun k => A i k) := by
      apply msum_congr
      intro k _
      rw [msum_mul_left, hB.row k]; grind
    simp only [mmul]
    rw [h1, h2, hA.row i]

variable [DecidableEq ι]

def mone : ι → ι → α := fun i j => if i = j then 1 else 0
def mpow (I : List ι) (P : ι → ι → α) : Nat → ι → ι → α
  | 0 => mone
  | k + 1 => mmul I (mpow I P k) P

theorem Stoch.pow {I : List ι} {P : ι → ι → α} (hI : Stoch I (mone (α := α))) (hP : Stoch I P) :
    ∀ k, Stoch I (mpow I P k)
  | 0 => hI
  | k + 1 => Stoch.mul (Stoch.pow hI hP k) hP

/-- A term of a sum of nonnegative terms is at most the sum. -/
theorem le_msum_of_mem : ∀ (I : List ι) (f : ι → α), (∀ j, 0 ≤ f j) → ∀ i ∈ I, f i ≤ msum I f
  | [], _, _, _, hi => by cases hi
  | k :: I, f, hf, i, hi => by
    have hrest := msum_nonneg I f (fun j _ => hf j)
    rcases List.mem_cons.mp hi with h | h
    · subst h; simp [msum] <;> grind
    · have ih := le_msum_of_mem I f hf i h
      have := hf k
      simp [msum] <;> grind

/-- `Tr P^0 = N`. -/
theorem tr_pow_zero (I : List ι) (P : ι → ι → α) : tr I (mpow I P 0) = ncnt I := by
  have h : msum I (fun i => mone (α := α) i i) = msum I (fun _ => (1 : α)) :=
    msum_congr I _ _ (fun i _ => by simp [mone])
  simp only [tr, mpow]; rw [h, msum_one]

/-- `0 ≤ Tr P^k ≤ N` for a row-stochastic matrix with nonnegative entries. -/
theorem tr_pow_bounds {I : List ι} {P : ι → ι → α} (hI : Stoch I (mone (α := α))) (hP : Stoch I P)
    (k : Nat) : 0 ≤ tr I (mpow I P k) ∧ tr I (mpow I P k) ≤ ncnt I := by
  have hk := Stoch.pow hI hP k
  constructor
  · exact msum_nonneg I _ (fun i _ => hk.nonneg i i)
  · have h1 : msum I (fun i => mpow I P k i i) ≤ msum I (fun _ => (1 : α)) := by
      apply msum_le
      intro i hi
      have h2 := le_msum_of_mem I (fun j => mpow I P k i j) (fun j => hk.nonneg i j) i hi
      rw [hk.row i] at h2; exact h2
    rw [msum_one] at h1; exact h1

/-- Partial sums of the series `sum_k c_k Tr P^k` (Poisson weights: `c_k = e^{-tau} tau^k / k!`). -/
def psum (I : List ι) (P : ι → ι → α) (c : Nat → α) : Nat → α
  | 0 => c 0 * tr I (mpow I P 0)
  | m + 1 => psum I P c m + c (m + 1) * tr I (mpow I P (m + 1))
def csum (c : Nat → α) : Nat → α
  | 0 => c 0
  | m + 1 => csum c m + c (m + 1)

/-- Theorem "Poisson representation", coefficientwise: every partial sum of the series lies
    between its first term `c_0 N` and `N sum_{k ≤ m} c_k`, for arbitrary weights `c_k ≥ 0`. -/
theorem psum_bounds {I : List ι} {P : ι → ι → α} (hI : Stoch I (mone (α := α))) (hP : Stoch I P)
    (c : Nat → α) (hc : ∀ k, 0 ≤ c k) :
    ∀ m, c 0 * ncnt I ≤ psum I P c m ∧ psum I P c m ≤ ncnt I * csum c m
  | 0 => by
    simp only [psum, csum]; rw [tr_pow_zero]; constructor <;> grind
  | m + 1 => by
    have ih := psum_bounds hI hP c hc m
    have hb := tr_pow_bounds hI hP (m + 1)
    have h1 := OrderedRing.mul_nonneg (hc (m + 1)) hb.1
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left hb.2 (hc (m + 1))
    simp only [psum, csum]; constructor <;> grind

/-- The partial sums are nondecreasing in `m`. -/
theorem psum_mono {I : List ι} {P : ι → ι → α} (hI : Stoch I (mone (α := α))) (hP : Stoch I P)
    (c : Nat → α) (hc : ∀ k, 0 ≤ c k) (m : Nat) : psum I P c m ≤ psum I P c (m + 1) := by
  have h1 := OrderedRing.mul_nonneg (hc (m + 1)) (tr_pow_bounds hI hP (m + 1)).1
  simp only [psum]; grind

end Walk

/-! ### Non-vacuity: a two-node walk over the rationals satisfies the hypotheses -/

def P2 : Bool → Bool → Rat := fun i j =>
  match i, j with
  | false, false => 1 / 2
  | false, true => 1 / 2
  | true, false => 1 / 3
  | true, true => 2 / 3

theorem two_nodes_enum : Stoch [false, true] (mone (α := Rat) (ι := Bool)) where
  nonneg := fun i j => by cases i <;> cases j <;> simp [mone] <;> grind
  row := fun i => by cases i <;> simp [msum, mone] <;> grind

theorem two_nodes_stoch : Stoch [false, true] P2 where
  nonneg := fun i j => by cases i <;> cases j <;> simp [P2] <;> grind
  row := fun i => by cases i <;> simp [msum, P2] <;> grind

/-- `Tr P = 7/6` and `Tr P^2 = 37/36` for this walk; both lie in `[0, 2]`. -/
theorem two_nodes_traces :
    tr [false, true] (mpow [false, true] P2 1) = 7 / 6 ∧
    tr [false, true] (mpow [false, true] P2 2) = 37 / 36 := by
  simp [tr, mpow, mmul, msum, mone, P2] <;> grind

end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### The rate in the exactly solvable case (Theorem G.4) and the discrete-time trace

  Mode by mode: `u = sigma lambda`, `tau = t / sigma`, so that `tau u = t lambda`.
  Graph mode `a = exp(-tau (1 - exp(-u)))`, continuum mode `b = exp(-tau u)`. -/

section Rate
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- `e^y - 1 ≤ y e^y`. -/
theorem IsExp.sub_one_le (h : IsExp exp) (y : α) : exp y - 1 ≤ y * exp y := by
  have h1 := OrderedRing.mul_le_mul_of_nonneg_left (h.ge (-y)) (h.nonneg y)
  have h2 := h.add y (-y)
  rw [show y + -y = (0 : α) by grind, h.zero] at h2
  grind

/-- Lower bound: every graph mode lies above the continuum mode, `b ≤ a`. -/
theorem walk_mode_ge (h : IsExp exp) {tau : α} (ht : 0 ≤ tau) (u : α) :
    exp (-(tau * u)) ≤ exp (-(tau * (1 - exp (-u)))) := by
  have h1 := h.ge (-u)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left (show 1 - exp (-u) ≤ u by grind) ht
  exact h.mono (by grind)

/-- Upper bound for a low mode (`0 ≤ u ≤ 1`): `a - b ≤ (tau u^2 / 2) e^{-tau u / 2}`,
    that is `(x^2 / 2 tau) e^{-x/2}` with `x = tau u = t lambda`. -/
theorem walk_mode_le (h : IsExp2 exp) {tau u : α} (ht : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    exp (-(tau * (1 - exp (-u)))) - exp (-(tau * u)) ≤ tau * u * u / 2 * exp (-(tau * u / 2)) := by
  have hE : IsExp exp := h.toIsExp
  -- 1 - e^{-u} ≥ u - u^2/2
  have h1 := h.taylor_nonpos (-u) (by grind)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left (show u - u * u / 2 ≤ 1 - exp (-u) by grind) ht
  -- a ≤ exp(-tau u + y), y = tau u^2 / 2
  have h3 := hE.mono (show -(tau * (1 - exp (-u))) ≤ -(tau * u) + tau * u * u / 2 by grind)
  have h4 := hE.add (-(tau * u)) (tau * u * u / 2)
  -- y ≥ 0 and y ≤ tau u / 2
  have htu := OrderedRing.mul_nonneg ht hu0
  have hy0 : (0 : α) ≤ tau * u * u / 2 := by
    have := OrderedRing.mul_nonneg htu hu0; grind
  have hy1 : tau * u * u / 2 ≤ tau * u / 2 := by
    have := OrderedRing.mul_nonneg htu (show (0 : α) ≤ 1 - u by grind); grind
  -- e^y - 1 ≤ y e^y, multiplied by b ≥ 0
  have h5 := OrderedRing.mul_le_mul_of_nonneg_left (hE.sub_one_le (tau * u * u / 2))
    (hE.nonneg (-(tau * u)))
  -- y * exp(-tau u + y) ≤ y * exp(-tau u / 2)
  have h6 := hE.mono (show -(tau * u) + tau * u * u / 2 ≤ -(tau * u / 2) by grind)
  have h7 := OrderedRing.mul_le_mul_of_nonneg_left h6 hy0
  rw [h4] at h3 h7
  have h8 : exp (-(tau * u)) * (tau * u * u / 2 * exp (tau * u * u / 2))
      = tau * u * u / 2 * (exp (-(tau * u)) * exp (tau * u * u / 2)) := by grind
  rw [h8] at h5
  have h9 := Std.le_trans h5 h7
  grind

/-- A high mode with `0 ≤ s ≤ s0`: `e^{-tau} (e^{tau s} - 1) ≤ tau s e^{-tau (1 - s0)}`. -/
theorem walk_high_mode (h : IsExp exp) {tau s s0 : α} (ht : 0 ≤ tau) (hs0 : 0 ≤ s) (hs : s ≤ s0) :
    exp (-tau) * (exp (tau * s) - 1) ≤ tau * s * exp (-(tau * (1 - s0))) := by
  have h1 := OrderedRing.mul_le_mul_of_nonneg_left (h.sub_one_le (tau * s)) (h.nonneg (-tau))
  have h2 := h.add (-tau) (tau * s)
  have h3 := OrderedRing.mul_nonneg ht (show (0 : α) ≤ s0 - s by grind)
  have h4 := h.mono (show -tau + tau * s ≤ -(tau * (1 - s0)) by grind)
  rw [h2] at h4
  have h5 := OrderedRing.mul_le_mul_of_nonneg_left h4 (OrderedRing.mul_nonneg ht hs0)
  have h6 : exp (-tau) * (tau * s * exp (tau * s)) = tau * s * (exp (-tau) * exp (tau * s)) := by grind
  rw [h6] at h1
  exact Std.le_trans h1 h5

/-- Sum over the low modes: `0 ≤ sum (a - b) ≤ sum (tau u^2/2) e^{-tau u/2}`. -/
def lowdiff (exp : α → α) (tau : α) : List α → α
  | [] => 0
  | u :: l => (exp (-(tau * (1 - exp (-u)))) - exp (-(tau * u))) + lowdiff exp tau l
def lowbound (exp : α → α) (tau : α) : List α → α
  | [] => 0
  | u :: l => tau * u * u / 2 * exp (-(tau * u / 2)) + lowbound exp tau l

theorem low_modes_rate (h : IsExp2 exp) {tau : α} (ht : 0 ≤ tau) :
    ∀ l : List α, (∀ u ∈ l, 0 ≤ u ∧ u ≤ 1) →
      0 ≤ lowdiff exp tau l ∧ lowdiff exp tau l ≤ lowbound exp tau l
  | [], _ => by simp [lowdiff, lowbound] <;> grind
  | u :: l, hl => by
    have ih := low_modes_rate h ht l (fun v hv => hl v (List.mem_cons_of_mem _ hv))
    have hu := hl u List.mem_cons_self
    have h1 := walk_mode_ge h.toIsExp ht u
    have h2 := walk_mode_le h ht hu.1 hu.2
    simp [lowdiff, lowbound] <;> constructor <;> grind

/-! Discrete time: `s^k ≤ e^{-k (1 - s)}` and the bound for the high modes. -/

def pw (s : α) : Nat → α
  | 0 => 1
  | k + 1 => s * pw s k
def ncast : Nat → α
  | 0 => 0
  | k + 1 => ncast k + 1

theorem pw_nonneg {s : α} (hs : 0 ≤ s) : ∀ k, 0 ≤ pw s k
  | 0 => by simp [pw] <;> grind
  | k + 1 => by simpa [pw] using OrderedRing.mul_nonneg hs (pw_nonneg hs k)

/-- Every mode of the discrete-time trace lies below the continuous-time one:
    `s^k ≤ e^{-k(1-s)}` for `s ≥ 0`. Hence `Tr P^k ≤ Tr e^{-tL}` at `tau = k` when `S ≥ 0`. -/
theorem pw_le_exp (h : IsExp exp) {s : α} (hs : 0 ≤ s) :
    ∀ k : Nat, pw s k ≤ exp (-(ncast k * (1 - s)))
  | 0 => by
    have := h.zero
    simp [pw, ncast] <;> grind
  | k + 1 => by
    have ih := pw_le_exp h hs k
    have h1 := h.ge (-(1 - s))
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left ih hs
    have h3 := OrderedRing.mul_le_mul_of_nonneg_left (show s ≤ exp (-(1 - s)) by grind)
      (h.nonneg (-(ncast k * (1 - s))))
    have h4 := h.add (-(ncast k * (1 - s))) (-(1 - s))
    rw [show -(ncast k * (1 - s)) + -(1 - s) = -((ncast k + 1) * (1 - s)) by grind] at h4
    simp only [pw, ncast]
    rw [h4]
    grind

/-- High modes in discrete time: `s^{k+2} ≤ (1 - kappa)^k s^2` for `0 ≤ s ≤ 1 - kappa`. -/
theorem pw_high {s kappa : α} (hs0 : 0 ≤ s) (hs : s ≤ 1 - kappa) :
    ∀ k : Nat, pw s (k + 2) ≤ pw (1 - kappa) k * (s * s)
  | 0 => by simp [pw] <;> grind
  | k + 1 => by
    have ih := pw_high hs0 hs k
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left ih hs0
    have hk : (0 : α) ≤ 1 - kappa := by grind
    have h2 := OrderedRing.mul_nonneg (pw_nonneg hk k) (mul_self_nonneg s)
    have h3 := OrderedRing.mul_le_mul_of_nonneg_left hs h2
    simp only [pw] at *
    grind

end Rate
end CTG.HeatTrace

set_option linter.unusedVariables false
namespace CTG.HeatTrace
open Lean.Grind

/-! ### Second order: Theorem G.4(iii) and the corrected estimator (Theorem G.5), mode by mode

  Notation as before: `u = sigma lambda ∈ [0,1]`, `x = tau u`, `q = tau u^2/2 = x^2/(2 tau)`,
  `w = 1 - e^{-u}`, `b = e^{-x}` (continuum mode), `a = e^{-tau w} = b e^{y}` (graph mode),
  `y = tau (u - w)`. -/

section Second
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- The purely algebraic core. `E` stands for `e^y`; the hypotheses on `w` and `E` are the
    Taylor bounds of the exponential function. -/
theorem second_order_core {tau u w b y E : α}
    (ht : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (w0 : u - u * u / 2 ≤ w) (w1 : w ≤ u - u * u / 2 + u * u * u / 6) (w2 : w ≤ u)
    (hb : 0 ≤ b) (hy : y = tau * u - tau * w)
    (E1 : 1 + y ≤ E) (E2 : E - 1 - y ≤ y * y / 2 * E) (E3 : E - 1 ≤ y * E) :
    -- (A) second-order expansion
    (-(tau * u * u * u / 6 * b) ≤ b * E - b - tau * u * u / 2 * b ∧
      b * E - b - tau * u * u / 2 * b ≤ (tau * u * u / 2) * (tau * u * u / 2) / 2 * (b * E)) ∧
    -- (B) corrected estimator
    (-(tau * u * u * u / 6 * b + (tau * u * u / 2) * (tau * u * u / 2) * (b * E))
        ≤ b * E * (1 - tau * w * w / 2) - b ∧
      b * E * (1 - tau * w * w / 2) - b
        ≤ (tau * u * u / 2) * (tau * u * u / 2) / 2 * (b * E) + tau * u * u * u / 2 * b) := by
  -- abbreviations as facts
  have hq0 : (0 : α) ≤ tau * u * u / 2 := by
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg ht hu0) hu0; grind
  -- y ∈ [0, q]
  have hy0 : 0 ≤ y := by
    have := OrderedRing.mul_nonneg ht (show (0 : α) ≤ u - w by grind); grind
  have hyq : y ≤ tau * u * u / 2 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left (show u - w ≤ u * u / 2 by grind) ht; grind
  -- rho = q - y ∈ [0, tau u^3/6]
  have hrho : tau * u * u / 2 - y ≤ tau * u * u * u / 6 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left (show w - u + u * u / 2 ≤ u * u * u / 6 by grind) ht
    grind
  -- y^2 ≤ q^2
  have hyy : y * y ≤ (tau * u * u / 2) * (tau * u * u / 2) := by
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left hyq hy0
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left hyq hq0
    grind
  have hE0 : 0 ≤ E := by grind
  have hE1 : 0 ≤ E - 1 := by grind
  -- term1 = E - 1 - y ∈ [0, q^2 E / 2]
  have ht1a : 0 ≤ E - 1 - y := by grind
  have ht1b : E - 1 - y ≤ (tau * u * u / 2) * (tau * u * u / 2) / 2 * E := by
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left
      (show y * y / 2 ≤ (tau * u * u / 2) * (tau * u * u / 2) / 2 by grind) hE0
    grind
  have hb1a := OrderedRing.mul_nonneg hb ht1a
  have hb1b := OrderedRing.mul_le_mul_of_nonneg_left ht1b hb
  have hbrho := OrderedRing.mul_le_mul_of_nonneg_left hrho hb
  have hbrho0 := OrderedRing.mul_nonneg hb (show (0 : α) ≤ tau * u * u / 2 - y by grind)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · grind
  · grind
  -- (B): bounds on w^2
  have hw00 : (0 : α) ≤ u - u * u / 2 := by
    have := OrderedRing.mul_nonneg hu0 (show (0 : α) ≤ 1 - u / 2 by grind); grind
  have hw_nonneg : 0 ≤ w := by grind
  have hww_hi : w * w ≤ u * u := by
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left w2 hw_nonneg
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left w2 hu0
    grind
  have hww_lo : u * u - u * u * u ≤ w * w := by
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left w0 hw00
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left w0 hw_nonneg
    have h3 := mul_self_nonneg (u * u)
    grind
  -- term2 = tau (u - w - w^2/2) ∈ [-tau u^3/6, tau u^3/2]
  have ht2a := OrderedRing.mul_le_mul_of_nonneg_left
    (show -(u * u * u / 6) ≤ u - w - w * w / 2 by grind) ht
  have ht2b := OrderedRing.mul_le_mul_of_nonneg_left
    (show u - w - w * w / 2 ≤ u * u * u / 2 by grind) ht
  have hb2a := OrderedRing.mul_le_mul_of_nonneg_left ht2a hb
  have hb2b := OrderedRing.mul_le_mul_of_nonneg_left ht2b hb
  -- term3 = (E - 1) tau w^2/2 ∈ [0, q^2 E]
  have hW0 : (0 : α) ≤ tau * w * w / 2 := by
    have := OrderedRing.mul_nonneg ht (mul_self_nonneg w); grind
  have hWq : tau * w * w / 2 ≤ tau * u * u / 2 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left hww_hi ht; grind
  have hyE0 : 0 ≤ y * E := OrderedRing.mul_nonneg hy0 hE0
  have ht3a := OrderedRing.mul_nonneg hE1 hW0
  have ht3b := OrderedRing.mul_le_mul_of_nonneg_left E3 hW0          -- W (E-1) ≤ W (y E)
  have ht3c := OrderedRing.mul_le_mul_of_nonneg_left hWq hyE0        -- (yE) W ≤ (yE) q
  have hqE0 : 0 ≤ tau * u * u / 2 * E := OrderedRing.mul_nonneg hq0 hE0
  have ht3d := OrderedRing.mul_le_mul_of_nonneg_left hyq hqE0        -- (qE) y ≤ (qE) q
  have ht3 : (E - 1) * (tau * w * w / 2) ≤ (tau * u * u / 2) * (tau * u * u / 2) * E := by grind
  have hb3a := OrderedRing.mul_nonneg hb ht3a
  have hb3b := OrderedRing.mul_le_mul_of_nonneg_left ht3 hb
  -- decomposition
  have hdec : b * E * (1 - tau * w * w / 2) - b
      = b * (E - 1 - y) + b * (tau * (u - w - w * w / 2)) - b * ((E - 1) * (tau * w * w / 2)) := by
    rw [hy]; grind
  rw [hdec]
  constructor <;> grind

end Second

section SecondExp
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- Third-order Taylor bound of `e^{-u}` from below, as a HYPOTHESIS. -/
structure IsExp3 (exp : α → α) : Prop extends IsExp2 exp where
  taylor3 : ∀ u, 0 ≤ u → 1 - u + u * u / 2 - u * u * u / 6 ≤ exp (-u)

/-- The graph mode is `b e^{y}`, and it is at most `e^{-tau u/2}` for a low mode. -/
theorem walk_mode_factor (h : IsExp exp) (tau u : α) :
    exp (-(tau * (1 - exp (-u))))
      = exp (-(tau * u)) * exp (tau * u - tau * (1 - exp (-u))) := by
  have h1 := h.add (-(tau * u)) (tau * u - tau * (1 - exp (-u)))
  rw [show -(tau * u) + (tau * u - tau * (1 - exp (-u))) = -(tau * (1 - exp (-u))) by grind] at h1
  exact h1

theorem walk_mode_half (h : IsExp2 exp) {tau u : α} (ht : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    exp (-(tau * (1 - exp (-u)))) ≤ exp (-(tau * u / 2)) := by
  have hE : IsExp exp := h.toIsExp
  have h1 := h.taylor_nonpos (-u) (by grind)
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left (show u - u * u / 2 ≤ 1 - exp (-u) by grind) ht
  have h3 := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg ht hu0) (show (0 : α) ≤ 1 - u by grind)
  exact hE.mono (by grind)

/-- Theorem G.4(iii), one low mode:
    `-(x^3/6 tau^2) e^{-x} ≤ a - b - (x^2/2 tau) b ≤ (x^4/8 tau^2) e^{-x/2}`. -/
theorem walk_mode_second (h : IsExp3 exp) {tau u : α} (ht : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    -(tau * u * u * u / 6 * exp (-(tau * u)))
        ≤ exp (-(tau * (1 - exp (-u)))) - exp (-(tau * u)) - tau * u * u / 2 * exp (-(tau * u)) ∧
    exp (-(tau * (1 - exp (-u)))) - exp (-(tau * u)) - tau * u * u / 2 * exp (-(tau * u))
        ≤ (tau * u * u / 2) * (tau * u * u / 2) / 2 * exp (-(tau * u / 2)) := by
  have h2 : IsExp2 exp := h.toIsExp2
  have hE : IsExp exp := h2.toIsExp
  have w0 : u - u * u / 2 ≤ 1 - exp (-u) := by have := h2.taylor_nonpos (-u) (by grind); grind
  have w1 : 1 - exp (-u) ≤ u - u * u / 2 + u * u * u / 6 := by have := h.taylor3 u hu0; grind
  have w2 : 1 - exp (-u) ≤ u := by have := hE.ge (-u); grind
  have hy0 : 0 ≤ tau * u - tau * (1 - exp (-u)) := by
    have := OrderedRing.mul_nonneg ht (show (0 : α) ≤ u - (1 - exp (-u)) by grind); grind
  have core := second_order_core (b := exp (-(tau * u)))
    (y := tau * u - tau * (1 - exp (-u))) (E := exp (tau * u - tau * (1 - exp (-u))))
    ht hu0 hu1 w0 w1 w2 (hE.nonneg _) rfl (hE.ge _) (h2.taylor_nonneg _ hy0) (hE.sub_one_le _)
  have hf := walk_mode_factor hE tau u
  have hhalf := walk_mode_half h2 ht hu0 hu1
  have hqq : (0 : α) ≤ (tau * u * u / 2) * (tau * u * u / 2) / 2 := by
    have := mul_self_nonneg (tau * u * u / 2); grind
  have hm := OrderedRing.mul_le_mul_of_nonneg_left hhalf hqq
  rw [← hf] at core
  obtain ⟨⟨cA1, cA2⟩, _⟩ := core
  constructor
  · exact cA1
  · exact Std.le_trans cA2 hm

/-- Theorem G.5 (corrected estimator), one low mode, with `z = tau w = t mu`:
    `|a (1 - z^2/2 tau) - b| ≤ (x^3/2 + x^4/4) e^{-x/2} / tau^2`. -/
theorem walk_mode_corrected (h : IsExp3 exp) {tau u : α} (ht : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    -((tau * u * u * u / 2 + (tau * u * u / 2) * (tau * u * u / 2)) * exp (-(tau * u / 2)))
        ≤ exp (-(tau * (1 - exp (-u)))) * (1 - tau * (1 - exp (-u)) * (1 - exp (-u)) / 2)
            - exp (-(tau * u)) ∧
    exp (-(tau * (1 - exp (-u)))) * (1 - tau * (1 - exp (-u)) * (1 - exp (-u)) / 2)
            - exp (-(tau * u))
        ≤ (tau * u * u * u / 2 + (tau * u * u / 2) * (tau * u * u / 2)) * exp (-(tau * u / 2)) := by
  have h2 : IsExp2 exp := h.toIsExp2
  have hE : IsExp exp := h2.toIsExp
  have w0 : u - u * u / 2 ≤ 1 - exp (-u) := by have := h2.taylor_nonpos (-u) (by grind); grind
  have w1 : 1 - exp (-u) ≤ u - u * u / 2 + u * u * u / 6 := by have := h.taylor3 u hu0; grind
  have w2 : 1 - exp (-u) ≤ u := by have := hE.ge (-u); grind
  have hy0 : 0 ≤ tau * u - tau * (1 - exp (-u)) := by
    have := OrderedRing.mul_nonneg ht (show (0 : α) ≤ u - (1 - exp (-u)) by grind); grind
  have core := second_order_core (b := exp (-(tau * u)))
    (y := tau * u - tau * (1 - exp (-u))) (E := exp (tau * u - tau * (1 - exp (-u))))
    ht hu0 hu1 w0 w1 w2 (hE.nonneg _) rfl (hE.ge _) (h2.taylor_nonneg _ hy0) (hE.sub_one_le _)
  have hf := walk_mode_factor hE tau u
  rw [← hf] at core
  obtain ⟨_, cB1, cB2⟩ := core
  -- a ≤ e^{-x/2} and b ≤ e^{-x/2}
  have hhalf := walk_mode_half h2 ht hu0 hu1
  have htu := OrderedRing.mul_nonneg ht hu0
  have hbhalf := hE.mono (show -(tau * u) ≤ -(tau * u / 2) by grind)
  have hu3 : (0 : α) ≤ tau * u * u * u / 2 := by
    have := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg htu hu0) hu0; grind
  have hu36 : (0 : α) ≤ tau * u * u * u / 6 := by grind
  have hqq : (0 : α) ≤ (tau * u * u / 2) * (tau * u * u / 2) := mul_self_nonneg _
  have m1 := OrderedRing.mul_le_mul_of_nonneg_left hbhalf hu3
  have m2 := OrderedRing.mul_le_mul_of_nonneg_left hbhalf hu36
  have m3 := OrderedRing.mul_le_mul_of_nonneg_left hhalf hqq
  have m4 := OrderedRing.mul_nonneg hu3 (hE.nonneg (-(tau * u / 2)))
  have m5 := OrderedRing.mul_nonneg hqq (hE.nonneg (-(tau * u / 2)))
  have m6 := OrderedRing.mul_nonneg hqq (hE.nonneg (-(tau * (1 - exp (-u)))))
  have hw : tau * (1 - exp (-u)) * (1 - exp (-u)) / 2 = tau * (1 - exp (-u)) * (1 - exp (-u)) / 2 := rfl
  constructor <;> grind

end SecondExp

/-! ### The Poisson identity for finitely many modes and finitely many terms

  `sum_k sum_{j ≤ m} c_j s_k^j = sum_{j ≤ m} c_j (sum_k s_k^j)`: the exchange of the two sums in
  Theorem G.4(i). With `c_j = tau^j / j!` and `m → ∞` this is the Poisson identity; the limit is a
  statement about real series and is not formalised. -/

section Poisson
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- `sum_{j ≤ m} c_j s^j`. -/
def poly (c : Nat → α) (s : α) : Nat → α
  | 0 => c 0 * pw s 0
  | m + 1 => poly c s m + c (m + 1) * pw s (m + 1)
/-- `sum_k s_k^j` (the trace of the `j`-th power of the walk). -/
def powsum (j : Nat) : List α → α
  | [] => 0
  | s :: l => pw s j + powsum j l
/-- `sum_k sum_{j ≤ m} c_j s_k^j`. -/
def polysum (c : Nat → α) (m : Nat) : List α → α
  | [] => 0
  | s :: l => poly c s m + polysum c m l
/-- `sum_{j ≤ m} c_j sum_k s_k^j`. -/
def momsum (c : Nat → α) (l : List α) : Nat → α
  | 0 => c 0 * powsum 0 l
  | m + 1 => momsum c l m + c (m + 1) * powsum (m + 1) l

theorem poisson_exchange (c : Nat → α) : ∀ (m : Nat) (l : List α), polysum c m l = momsum c l m
  | m, [] => by
    induction m with
    | zero => simp [polysum, momsum, powsum] <;> grind
    | succ m ih => simp [polysum, momsum, powsum] at * <;> grind
  | m, s :: l => by
    have ih := poisson_exchange c m l
    have key : ∀ m, poly c s m + momsum c l m = momsum c (s :: l) m := by
      intro m
      induction m with
      | zero => simp [poly, momsum, powsum] <;> grind
      | succ m ihm => simp [poly, momsum, powsum] at * <;> grind
    simp only [polysum]; rw [ih]; exact key m

variable {exp : α → α}

/-- One-sided finite Poisson bound. If the partial sums `sum_{j ≤ m} c_j x^j` lie below `e^x`
    for `x ≥ 0` (HYPOTHESIS; true for `c_j = 1/j!`), then for nonnegative modes
    `e^{-tau} (sum_{j ≤ m} c_j tau^j Tr P^j - N) ≤ sum_k (e^{-tau(1 - s_k)} - e^{-tau})`. -/
def subheat (exp : α → α) (tau : α) : List α → α
  | [] => 0
  | s :: l => (exp (-(tau * (1 - s))) - exp (-tau)) + subheat exp tau l

theorem poisson_lower (h : IsExp exp) (c : Nat → α) (m : Nat)
    (hT : ∀ x : α, 0 ≤ x → poly c x m ≤ exp x) {tau : α} (ht : 0 ≤ tau) :
    ∀ l : List α, (∀ s ∈ l, 0 ≤ s) →
      exp (-tau) * (polysum c m (l.map (fun s => tau * s)) - cnt l) ≤ subheat exp tau l
  | [], _ => by simp [polysum, cnt, subheat] <;> grind
  | s :: l, hl => by
    have ih := poisson_lower h c m hT ht l (fun r hr => hl r (List.mem_cons_of_mem _ hr))
    have hs := hl s List.mem_cons_self
    have h1 := hT (tau * s) (OrderedRing.mul_nonneg ht hs)
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left h1 (h.nonneg (-tau))
    have h3 := h.add (-tau) (tau * s)
    rw [show -tau + tau * s = -(tau * (1 - s)) by grind] at h3
    simp only [List.map, polysum, cnt, subheat]
    grind

end Poisson
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Sums over an arbitrary finite family of modes

  The bounds below hold for every finite list of modes with constants that do not depend on the
  number of modes. The passage to infinitely many modes (monotone limits of real series) is
  not formalised: the core library has no real numbers. -/

section Families
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

def fsum (f : α → α) : List α → α
  | [] => 0
  | u :: l => f u + fsum f l

theorem fsum_le (f g : α → α) : ∀ l : List α, (∀ u ∈ l, f u ≤ g u) → fsum f l ≤ fsum g l
  | [], _ => by simp [fsum] <;> grind
  | u :: l, h => by
    have ih := fsum_le f g l (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have h1 := h u List.mem_cons_self
    simp [fsum] <;> grind

/-- Theorem G.4(iii) summed over finitely many low modes. -/
theorem low_modes_second (h : IsExp3 exp) {tau : α} (ht : 0 ≤ tau) (l : List α)
    (hl : ∀ u ∈ l, 0 ≤ u ∧ u ≤ 1) :
    fsum (fun u => -(tau * u * u * u / 6 * exp (-(tau * u)))) l
      ≤ fsum (fun u => exp (-(tau * (1 - exp (-u)))) - exp (-(tau * u))
            - tau * u * u / 2 * exp (-(tau * u))) l ∧
    fsum (fun u => exp (-(tau * (1 - exp (-u)))) - exp (-(tau * u))
            - tau * u * u / 2 * exp (-(tau * u))) l
      ≤ fsum (fun u => (tau * u * u / 2) * (tau * u * u / 2) / 2 * exp (-(tau * u / 2))) l :=
  ⟨fsum_le _ _ l (fun u hu => (walk_mode_second h ht (hl u hu).1 (hl u hu).2).1),
   fsum_le _ _ l (fun u hu => (walk_mode_second h ht (hl u hu).1 (hl u hu).2).2)⟩

/-- Theorem G.5 summed over finitely many low modes. -/
theorem low_modes_corrected (h : IsExp3 exp) {tau : α} (ht : 0 ≤ tau) (l : List α)
    (hl : ∀ u ∈ l, 0 ≤ u ∧ u ≤ 1) :
    fsum (fun u => -((tau * u * u * u / 2 + (tau * u * u / 2) * (tau * u * u / 2))
            * exp (-(tau * u / 2)))) l
      ≤ fsum (fun u => exp (-(tau * (1 - exp (-u))))
            * (1 - tau * (1 - exp (-u)) * (1 - exp (-u)) / 2) - exp (-(tau * u))) l ∧
    fsum (fun u => exp (-(tau * (1 - exp (-u))))
            * (1 - tau * (1 - exp (-u)) * (1 - exp (-u)) / 2) - exp (-(tau * u))) l
      ≤ fsum (fun u => (tau * u * u * u / 2 + (tau * u * u / 2) * (tau * u * u / 2))
            * exp (-(tau * u / 2))) l :=
  ⟨fsum_le _ _ l (fun u hu => (walk_mode_corrected h ht (hl u hu).1 (hl u hu).2).1),
   fsum_le _ _ l (fun u hu => (walk_mode_corrected h ht (hl u hu).1 (hl u hu).2).2)⟩

end Families
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

section Signed
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- `|s P| ≤ m M` for `|s| ≤ m`, `|P| ≤ M`, without absolute values. -/
theorem abs_mul_le {s P m M : α} (hs1 : -m ≤ s) (hs2 : s ≤ m) (hP1 : -M ≤ P) (hP2 : P ≤ M) :
    -(m * M) ≤ s * P ∧ s * P ≤ m * M := by
  have h1 := OrderedRing.mul_nonneg (show (0 : α) ≤ m - s by grind) (show (0 : α) ≤ M - P by grind)
  have h2 := OrderedRing.mul_nonneg (show (0 : α) ≤ m + s by grind) (show (0 : α) ≤ M + P by grind)
  have h3 := OrderedRing.mul_nonneg (show (0 : α) ≤ m - s by grind) (show (0 : α) ≤ M + P by grind)
  have h4 := OrderedRing.mul_nonneg (show (0 : α) ≤ m + s by grind) (show (0 : α) ≤ M - P by grind)
  constructor <;> grind

end Signed

/-! ### Theorem G.5: the high modes of the corrected estimator -/

section CorrectedHigh
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- Algebraic core, `E = e^{tau s}`:
    `|(E - 1)(1 - tau (1-s)^2/2) + (tau/2)(1 - (1-s)^2)| ≤ tau s (2 + tau/2) E`. -/
theorem corrected_high_core {tau s E : α} (ht : 0 ≤ tau) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hE1 : 1 ≤ E) (hE3 : E - 1 ≤ tau * s * E) :
    -(tau * s * (2 + tau / 2) * E)
        ≤ (E - 1) * (1 - tau * (1 - s) * (1 - s) / 2) + tau / 2 * (1 - (1 - s) * (1 - s)) ∧
    (E - 1) * (1 - tau * (1 - s) * (1 - s) / 2) + tau / 2 * (1 - (1 - s) * (1 - s))
        ≤ tau * s * (2 + tau / 2) * E := by
  have h1s : (0 : α) ≤ 1 - s := by grind
  have hsq0 := mul_self_nonneg (1 - s)
  have hsq1 : (1 - s) * (1 - s) ≤ 1 := by
    have := OrderedRing.mul_le_mul_of_nonneg_left (show 1 - s ≤ 1 by grind) h1s; grind
  have hA0 := OrderedRing.mul_nonneg ht hsq0                                   -- 0 ≤ tau (1-s)^2
  have hA1 := OrderedRing.mul_le_mul_of_nonneg_left hsq1 ht                    -- tau (1-s)^2 ≤ tau
  have hE0 : (0 : α) ≤ E - 1 := by grind
  have p1 := OrderedRing.mul_nonneg hE0 (show (0 : α) ≤ tau * ((1 - s) * (1 - s)) / 2 by grind)
  have p2 := OrderedRing.mul_nonneg hE0
    (show (0 : α) ≤ 1 - tau * ((1 - s) * (1 - s)) / 2 + tau / 2 by grind)
  have p3 := OrderedRing.mul_le_mul_of_nonneg_left hE3 (show (0 : α) ≤ tau / 2 by grind)
  have hts := OrderedRing.mul_nonneg ht hs0
  have p4 := OrderedRing.mul_nonneg hts (show (0 : α) ≤ 1 - s / 2 by grind)   -- tau s (1 - s/2) ≥ 0
  have p5 := OrderedRing.mul_nonneg hts hs0                                    -- tau s^2 ≥ 0
  have p6 := OrderedRing.mul_nonneg hts hE0                                    -- tau s (E-1) ≥ 0
  have htsE := OrderedRing.mul_nonneg hts (show (0 : α) ≤ E by grind)
  have p7 := OrderedRing.mul_nonneg htsE (show (0 : α) ≤ tau / 2 by grind)
  constructor <;> grind

/-- Theorem G.5, one high mode with `0 ≤ s ≤ s0 ≤ 1`:
    `|e^{-tau}[e^{tau s}(1 - tau(1-s)^2/2) - 1 + tau/2]| ≤ tau s (2 + tau/2) e^{-tau(1-s0)}`. -/
theorem corrected_high_mode (h : IsExp exp) {tau s s0 : α} (ht : 0 ≤ tau) (hs0 : 0 ≤ s)
    (hs : s ≤ s0) (hs1 : s0 ≤ 1) :
    -(tau * s * (2 + tau / 2) * exp (-(tau * (1 - s0))))
        ≤ exp (-tau) * (exp (tau * s) * (1 - tau * (1 - s) * (1 - s) / 2) - 1 + tau / 2) ∧
    exp (-tau) * (exp (tau * s) * (1 - tau * (1 - s) * (1 - s) / 2) - 1 + tau / 2)
        ≤ tau * s * (2 + tau / 2) * exp (-(tau * (1 - s0))) := by
  have hts := OrderedRing.mul_nonneg ht hs0
  have hE1 : 1 ≤ exp (tau * s) := by have := h.ge (tau * s); grind
  have core := corrected_high_core ht hs0 (show s ≤ 1 by grind) hE1 (h.sub_one_le (tau * s))
  have hdec : exp (tau * s) * (1 - tau * (1 - s) * (1 - s) / 2) - 1 + tau / 2
      = (exp (tau * s) - 1) * (1 - tau * (1 - s) * (1 - s) / 2)
        + tau / 2 * (1 - (1 - s) * (1 - s)) := by grind
  rw [hdec]
  have hb := h.nonneg (-tau)
  have m1 := OrderedRing.mul_le_mul_of_nonneg_left core.1 hb
  have m2 := OrderedRing.mul_le_mul_of_nonneg_left core.2 hb
  have hadd := h.add (-tau) (tau * s)
  have h3 := OrderedRing.mul_nonneg ht (show (0 : α) ≤ s0 - s by grind)
  have hmono := h.mono (show -tau + tau * s ≤ -(tau * (1 - s0)) by grind)
  rw [hadd] at hmono
  have hc : (0 : α) ≤ tau * s * (2 + tau / 2) := by
    have := OrderedRing.mul_nonneg hts (show (0 : α) ≤ 2 + tau / 2 by grind); grind
  have m3 := OrderedRing.mul_le_mul_of_nonneg_left hmono hc
  constructor <;> grind

end CorrectedHigh

/-! ### Theorem G.6: profiles other than the Gaussian one, mode by mode -/

section Profile
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- A mode of the form `b e^{y}` with `b = e^{-x}`, where `y` differs from the main term `p` by at
    most `r` and `|y| ≤ x/4`:
    `-r e^{-x/2} ≤ b e^{y} - b - p b ≤ (y^2/2 + r) e^{-x/2}`.
    Used with `p = beta x^2/2 tau` (continuous time) and `p = (beta-1) x^2/2 tau` (discrete time). -/
theorem exp_mode_expansion (h : IsExp2 exp) {x y p r : α} (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hy1 : -r ≤ y - p) (hy2 : y - p ≤ r) (hs1 : -(x / 4) ≤ y) (hs2 : y ≤ x / 4) :
    -(r * exp (-(x / 2))) ≤ exp (-x + y) - exp (-x) - p * exp (-x) ∧
    exp (-x + y) - exp (-x) - p * exp (-x) ≤ (y * y / 2 + r) * exp (-(x / 2)) := by
  have hE : IsExp exp := h.toIsExp
  have hadd := hE.add (-x) y
  have hb := hE.nonneg (-x)
  have hbh := hE.mono (show -x ≤ -(x / 2) by grind)           -- b ≤ e^{-x/2}
  have hh := hE.nonneg (-(x / 2))
  have hyy : (0 : α) ≤ y * y / 2 := by have := mul_self_nonneg y; grind
  -- b (y - p) ∈ [-r b, r b] ⊂ [-r e^{-x/2}, r e^{-x/2}]
  have q1 := OrderedRing.mul_le_mul_of_nonneg_left hy1 hb
  have q2 := OrderedRing.mul_le_mul_of_nonneg_left hy2 hb
  have q3 := OrderedRing.mul_le_mul_of_nonneg_left hbh hr
  -- b (E - 1 - y) ≥ 0
  have t0 := OrderedRing.mul_nonneg hb (show (0 : α) ≤ exp y - 1 - y by have := hE.ge y; grind)
  rw [hadd]
  by_cases hy0 : 0 ≤ y
  · -- E - 1 - y ≤ (y^2/2) E and b E ≤ e^{-x/2}
    have t1 := OrderedRing.mul_le_mul_of_nonneg_left (h.taylor_nonneg y hy0) hb
    have hbE := hE.mono (show -x + y ≤ -(x / 2) by grind)
    rw [hadd] at hbE
    have t2 := OrderedRing.mul_le_mul_of_nonneg_left hbE hyy
    constructor <;> grind
  · have t1 := OrderedRing.mul_le_mul_of_nonneg_left (h.taylor_nonpos y (by grind)) hb
    have t2 := OrderedRing.mul_le_mul_of_nonneg_left hbh hyy
    constructor <;> grind

/-- Theorem G.6(i), one low mode. `s = F(u)` with `|s - 1 + u - beta u^2/2| ≤ c3 u^3`, and
    `y = tau (u - (1 - s))` with `|y| ≤ tau u/4`. Then, with `q = tau u^2/2`, `r = tau c3 u^3`:
    `-r e^{-x/2} ≤ a - b - beta q b ≤ (y^2/2 + r) e^{-x/2}`. -/
theorem profile_low_mode (h : IsExp2 exp) {tau u s beta c3 : α} (ht : 0 ≤ tau) (hu : 0 ≤ u)
    (hc : 0 ≤ c3) (hF1 : -(c3 * u * u * u) ≤ s - (1 - u + beta * u * u / 2))
    (hF2 : s - (1 - u + beta * u * u / 2) ≤ c3 * u * u * u)
    (hs1 : -(tau * u / 4) ≤ tau * u - tau * (1 - s)) (hs2 : tau * u - tau * (1 - s) ≤ tau * u / 4) :
    -(tau * (c3 * u * u * u) * exp (-(tau * u / 2)))
        ≤ exp (-(tau * (1 - s))) - exp (-(tau * u)) - beta * (tau * u * u / 2) * exp (-(tau * u)) ∧
    exp (-(tau * (1 - s))) - exp (-(tau * u)) - beta * (tau * u * u / 2) * exp (-(tau * u))
        ≤ ((tau * u - tau * (1 - s)) * (tau * u - tau * (1 - s)) / 2 + tau * (c3 * u * u * u))
            * exp (-(tau * u / 2)) := by
  have htu := OrderedRing.mul_nonneg ht hu
  have hr : (0 : α) ≤ tau * (c3 * u * u * u) := by
    have h1 := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hc hu) hu) hu
    exact OrderedRing.mul_nonneg ht h1
  have g1 := OrderedRing.mul_le_mul_of_nonneg_left hF1 ht
  have g2 := OrderedRing.mul_le_mul_of_nonneg_left hF2 ht
  have key := exp_mode_expansion h (x := tau * u) (y := tau * u - tau * (1 - s))
    (p := beta * (tau * u * u / 2)) (r := tau * (c3 * u * u * u)) htu hr (by grind) (by grind) hs1 hs2
  rw [show -(tau * u) + (tau * u - tau * (1 - s)) = -(tau * (1 - s)) by grind] at key
  exact key

/-- Theorem G.6(i), one high mode with `|s| ≤ m ≤ 1 - delta`:
    `|e^{-tau(1-s)} - e^{-tau}| ≤ tau m e^{-delta tau}`. -/
theorem profile_high_mode (h : IsExp exp) {tau s m delta : α} (ht : 0 ≤ tau) (hm1 : -m ≤ s)
    (hm2 : s ≤ m) (hd0 : 0 ≤ delta) (hmd : m ≤ 1 - delta) :
    -(tau * m * exp (-(delta * tau))) ≤ exp (-(tau * (1 - s))) - exp (-tau) ∧
    exp (-(tau * (1 - s))) - exp (-tau) ≤ tau * m * exp (-(delta * tau)) := by
  have hm0 : 0 ≤ m := by grind
  have hb := h.nonneg (-tau)
  have hadd := h.add (-tau) (tau * s)
  rw [show -tau + tau * s = -(tau * (1 - s)) by grind] at hadd
  have htm := OrderedRing.mul_nonneg ht hm0
  have hd := h.nonneg (-(delta * tau))
  have hRHS := OrderedRing.mul_nonneg htm hd
  -- e^{-tau} ≤ e^{-delta tau}
  have hd1 := OrderedRing.mul_nonneg ht (show (0 : α) ≤ 1 - delta by grind)
  have hbd := h.mono (show -tau ≤ -(delta * tau) by grind)
  -- lower: e^{tau s} - 1 ≥ tau s ≥ -tau m
  have l1 := h.ge (tau * s)
  have l2 := OrderedRing.mul_le_mul_of_nonneg_left hm1 ht
  have l3 := OrderedRing.mul_le_mul_of_nonneg_left
    (show -(tau * m) ≤ exp (tau * s) - 1 by grind) hb
  have l4 := OrderedRing.mul_le_mul_of_nonneg_left hbd htm
  constructor
  · rw [hadd]; grind
  · by_cases hs0 : 0 ≤ s
    · have u1 := OrderedRing.mul_le_mul_of_nonneg_left (h.sub_one_le (tau * s)) hb
      have u2 := OrderedRing.mul_nonneg ht (show (0 : α) ≤ 1 - delta - s by grind)
      have u3 := h.mono (show -(tau * (1 - s)) ≤ -(delta * tau) by grind)
      have hts := OrderedRing.mul_nonneg ht hs0
      have u4 := OrderedRing.mul_le_mul_of_nonneg_left u3 hts          -- tau s a ≤ tau s e^{-δτ}
      have u5 := OrderedRing.mul_le_mul_of_nonneg_left hm2 ht          -- tau s ≤ tau m
      have u6 := OrderedRing.mul_le_mul_of_nonneg_left u5 hd           -- e^{-δτ} tau s ≤ e^{-δτ} tau m
      have u7 : exp (-tau) * (tau * s * exp (tau * s)) = tau * s * exp (-(tau * (1 - s))) := by
        rw [hadd]; grind
      rw [u7] at u1
      rw [hadd]; grind
    · have hts := OrderedRing.mul_nonneg ht (show (0 : α) ≤ -s by grind)
      have u1 := h.le_one (show tau * s ≤ 0 by grind)
      have u2 := OrderedRing.mul_le_mul_of_nonneg_left u1 hb
      rw [hadd]; grind

/-! Discrete time: `(e^{v})^k = e^{k v}` and the bounds for powers of signed numbers. -/

theorem pw_exp (h : IsExp exp) (v : α) : ∀ k : Nat, pw (exp v) k = exp (ncast k * v)
  | 0 => by
    have := h.zero
    simp only [pw, ncast]; rw [show (0 : α) * v = 0 by grind]; exact this.symm
  | k + 1 => by
    have ih := pw_exp h v k
    have h1 := h.add v (ncast k * v)
    simp only [pw, ncast]
    rw [ih, ← h1, show v + ncast k * v = (ncast k + 1) * v by grind]

/-- Theorem G.6(ii), one low mode: if `ln s = -u + beta' u^2/2 + rho` with `|rho| ≤ c u^3`
    (written `s = e^{...}`), then with `tau = k` and `y = k (beta' u^2/2 + rho)`, `|y| ≤ k u/4`:
    `-r e^{-x/2} ≤ s^k - b - beta' q b ≤ (y^2/2 + r) e^{-x/2}`, `r = k c u^3`. -/
theorem profile_low_mode_discrete (h : IsExp2 exp) (k : Nat) {u s betap c rho : α} (hu : 0 ≤ u)
    (hc : 0 ≤ c) (hs : s = exp (-u + (betap * u * u / 2 + rho)))
    (hr1 : -(c * u * u * u) ≤ rho) (hr2 : rho ≤ c * u * u * u)
    (hy1 : -(ncast k * u / 4) ≤ ncast k * (betap * u * u / 2 + rho))
    (hy2 : ncast k * (betap * u * u / 2 + rho) ≤ ncast k * u / 4)
    (hk : (0 : α) ≤ ncast k) :
    -(ncast k * (c * u * u * u) * exp (-(ncast k * u / 2)))
        ≤ pw s k - exp (-(ncast k * u)) - betap * (ncast k * u * u / 2) * exp (-(ncast k * u)) ∧
    pw s k - exp (-(ncast k * u)) - betap * (ncast k * u * u / 2) * exp (-(ncast k * u))
        ≤ ((ncast k * (betap * u * u / 2 + rho)) * (ncast k * (betap * u * u / 2 + rho)) / 2
            + ncast k * (c * u * u * u)) * exp (-(ncast k * u / 2)) := by
  have hE : IsExp exp := h.toIsExp
  have hpw := pw_exp hE (-u + (betap * u * u / 2 + rho)) k
  rw [← hs] at hpw
  have hku := OrderedRing.mul_nonneg hk hu
  have hr : (0 : α) ≤ ncast k * (c * u * u * u) := by
    have h1 := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hc hu) hu) hu
    exact OrderedRing.mul_nonneg hk h1
  have g1 := OrderedRing.mul_le_mul_of_nonneg_left hr1 hk
  have g2 := OrderedRing.mul_le_mul_of_nonneg_left hr2 hk
  have key := exp_mode_expansion h (x := ncast k * u) (y := ncast k * (betap * u * u / 2 + rho))
    (p := betap * (ncast k * u * u / 2)) (r := ncast k * (c * u * u * u)) hku hr
    (by grind) (by grind) hy1 hy2
  rw [show -(ncast k * u) + ncast k * (betap * u * u / 2 + rho)
      = ncast k * (-u + (betap * u * u / 2 + rho)) by grind, ← hpw] at key
  exact key

theorem ncast_nonneg : ∀ k : Nat, (0 : α) ≤ ncast k
  | 0 => by simp [ncast] <;> grind
  | k + 1 => by
    have ih : (0 : α) ≤ ncast k := ncast_nonneg k
    simp only [ncast]; grind

/-- `|s^k| ≤ m^k` for `|s| ≤ m`. -/
theorem pw_abs_le {s m : α} (hm1 : -m ≤ s) (hm2 : s ≤ m) :
    ∀ k : Nat, -(pw m k) ≤ pw s k ∧ pw s k ≤ pw m k
  | 0 => by simp [pw] <;> grind
  | k + 1 => by
    have ih := pw_abs_le hm1 hm2 k
    have := abs_mul_le hm1 hm2 ih.1 ih.2
    simpa [pw] using this

theorem pw_mono {m n : α} (hm0 : 0 ≤ m) (hmn : m ≤ n) : ∀ k : Nat, pw m k ≤ pw n k
  | 0 => by simp [pw] <;> grind
  | k + 1 => by
    have ih := pw_mono hm0 hmn k
    have h1 := OrderedRing.mul_le_mul_of_nonneg_left ih hm0
    have h2 := OrderedRing.mul_le_mul_of_nonneg_left hmn (pw_nonneg (show (0 : α) ≤ n by grind) k)
    simp only [pw]; grind

/-- Theorem G.6(ii), one high mode: `|s^{k+1}| ≤ (1 - delta)^k m` for `|s| ≤ m ≤ 1 - delta`. -/
theorem profile_high_mode_discrete {s m delta : α} (hm1 : -m ≤ s) (hm2 : s ≤ m)
    (hmd : m ≤ 1 - delta) (k : Nat) :
    -(pw (1 - delta) k * m) ≤ pw s (k + 1) ∧ pw s (k + 1) ≤ pw (1 - delta) k * m := by
  have hm0 : 0 ≤ m := by grind
  have h1 := pw_abs_le hm1 hm2 (k + 1)
  have h2 := pw_mono hm0 hmd k
  have h3 := OrderedRing.mul_le_mul_of_nonneg_left h2 hm0
  have e : pw s (k + 1) = s * pw s k := rfl
  have e2 : pw m (k + 1) = m * pw m k := rfl
  rw [e2] at h1; rw [e] at h1 ⊢
  constructor <;> grind

end Profile

/-! ### Theorem G.7, step 2: replacing `p_N` by `p` in a product of `j` factors

  If `|a_l| ≤ M`, `|b_l| ≤ M` and `|a_l - b_l| ≤ eps` for all factors, then
  `|prod a - prod b| ≤ B` with `B = n eps M^{n-1}`, defined by `B_0 = 0`,
  `B_{n+1} = M B_n + eps M^n`. -/

section Products
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

def prodL : List (α × α) → α
  | [] => 1
  | p :: l => p.1 * prodL l
def prodR : List (α × α) → α
  | [] => 1
  | p :: l => p.2 * prodR l
def lenN : List (α × α) → Nat
  | [] => 0
  | _ :: l => lenN l + 1
def pertBound (M eps : α) : List (α × α) → α
  | [] => 0
  | _ :: l => M * pertBound M eps l + eps * pw M (lenN l)

theorem prodR_abs {M : α} (hM : 0 ≤ M) :
    ∀ l : List (α × α), (∀ p ∈ l, -M ≤ p.2 ∧ p.2 ≤ M) →
      -(pw M (lenN l)) ≤ prodR l ∧ prodR l ≤ pw M (lenN l)
  | [], _ => by simp [prodR, lenN, pw] <;> grind
  | p :: l, hl => by
    have ih := prodR_abs hM l (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have hp := hl p List.mem_cons_self
    have := abs_mul_le hp.1 hp.2 ih.1 ih.2
    simpa [prodR, lenN, pw] using this

theorem product_perturbation {M eps : α} (hM : 0 ≤ M) (he : 0 ≤ eps) :
    ∀ l : List (α × α),
      (∀ p ∈ l, (-M ≤ p.1 ∧ p.1 ≤ M) ∧ (-M ≤ p.2 ∧ p.2 ≤ M) ∧ (-eps ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ eps)) →
      -(pertBound M eps l) ≤ prodL l - prodR l ∧ prodL l - prodR l ≤ pertBound M eps l
  | [], _ => by simp [prodL, prodR, pertBound] <;> grind
  | p :: l, hl => by
    have hl' := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have ih := product_perturbation hM he l hl'
    have hp := hl p List.mem_cons_self
    have hR := prodR_abs hM l (fun q hq => (hl' q hq).2.1)
    have t1 := abs_mul_le hp.1.1 hp.1.2 ih.1 ih.2                -- |a (A - B)| ≤ M Bound
    have t2 := abs_mul_le hp.2.2.1 hp.2.2.2 hR.1 hR.2            -- |(a - b) B| ≤ eps M^n
    have hdec : p.1 * prodL l - p.2 * prodR l
        = p.1 * (prodL l - prodR l) + (p.1 - p.2) * prodR l := by grind
    simp only [prodL, prodR, pertBound]
    rw [hdec]
    constructor <;> grind

end Products
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Limits of sequences and series in an ordered field

  The core library has no real numbers. Convergence is therefore defined directly, for sequences
  in an arbitrary ordered field, and the EXISTENCE of the limits that occur (the sums of the
  series) is a hypothesis of each statement; for real series with nonnegative bounded partial
  sums it is automatic. No completeness is used. -/

section Limits
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- `f n → L`. -/
def Tends (f : Nat → α) (L : α) : Prop :=
  ∀ e : α, 0 < e → ∃ N : Nat, ∀ n, N ≤ n → L - e < f n ∧ f n < L + e

theorem tends_const (c : α) : Tends (fun _ => c) c :=
  fun e he => ⟨0, fun n _ => by constructor <;> grind⟩

/-- Limits preserve `≤`. -/
theorem le_of_tends {f g : Nat → α} {F G : α} (hfg : ∀ n, f n ≤ g n) (hf : Tends f F)
    (hg : Tends g G) : F ≤ G := by
  apply Classical.byContradiction
  intro hn
  have hlt : G < F := by grind
  obtain ⟨N1, h1⟩ := hf ((F - G) / 2) (by grind)
  obtain ⟨N2, h2⟩ := hg ((F - G) / 2) (by grind)
  have a := h1 (N1 + N2) (by omega)
  have b := h2 (N1 + N2) (by omega)
  have c := hfg (N1 + N2)
  grind

theorem tends_unique {f : Nat → α} {L1 L2 : α} (h1 : Tends f L1) (h2 : Tends f L2) : L1 = L2 := by
  have a := le_of_tends (fun n => Std.le_refl (f n)) h1 h2
  have b := le_of_tends (fun n => Std.le_refl (f n)) h2 h1
  grind

theorem tends_add {f g : Nat → α} {F G : α} (hf : Tends f F) (hg : Tends g G) :
    Tends (fun n => f n + g n) (F + G) := by
  intro e he
  obtain ⟨N1, h1⟩ := hf (e / 2) (by grind)
  obtain ⟨N2, h2⟩ := hg (e / 2) (by grind)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have a := h1 n (by omega)
  have b := h2 n (by omega)
  constructor <;> grind

theorem tends_mul_left {f : Nat → α} {F : α} (c : α) (hc : 0 ≤ c) (hf : Tends f F) :
    Tends (fun n => c * f n) (c * F) := by
  intro e he
  have hd : (c + 1) * (e / (c + 1)) = e := by grind
  have hdpos : 0 < e / (c + 1) := by
    apply Classical.byContradiction
    intro hn
    have h1 := OrderedRing.mul_nonneg (show (0 : α) ≤ c + 1 by grind)
      (show (0 : α) ≤ -(e / (c + 1)) by grind)
    grind
  obtain ⟨N, h⟩ := hf (e / (c + 1)) hdpos
  refine ⟨N, fun n hn => ?_⟩
  have a := h n hn
  have m1 := OrderedRing.mul_le_mul_of_nonneg_left (show F - e / (c + 1) ≤ f n by grind) hc
  have m2 := OrderedRing.mul_le_mul_of_nonneg_left (show f n ≤ F + e / (c + 1) by grind) hc
  constructor <;> grind

theorem tends_shift {f : Nat → α} {L : α} (J : Nat) (hf : Tends f L) :
    Tends (fun i => f (J + i)) L := by
  intro e he
  obtain ⟨N, h⟩ := hf e he
  exact ⟨N, fun n hn => h (J + n) (by omega)⟩

theorem mono_le {f : Nat → α} (hm : ∀ n, f n ≤ f (n + 1)) (m : Nat) : ∀ i, f m ≤ f (m + i)
  | 0 => Std.le_refl _
  | i + 1 => Std.le_trans (mono_le hm m i) (hm (m + i))

/-- A nondecreasing sequence lies below its limit. -/
theorem mono_le_limit {f : Nat → α} {L : α} (hm : ∀ n, f n ≤ f (n + 1)) (hf : Tends f L)
    (m : Nat) : f m ≤ L := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨N, h⟩ := hf (f m - L) (by grind)
  have a := h (m + N) (by omega)
  have b := mono_le hm m N
  grind

/-- `sum_{j ≤ m} g j`. -/
def jsum (g : Nat → α) : Nat → α
  | 0 => g 0
  | m + 1 => jsum g m + g (m + 1)
/-- `sum_{k < n} f k`. -/
def psumN (f : Nat → α) : Nat → α
  | 0 => 0
  | n + 1 => psumN f n + f n

theorem tends_jsum {a : Nat → Nat → α} {L : Nat → α} (h : ∀ j, Tends (fun N => a N j) (L j)) :
    ∀ J, Tends (fun N => jsum (fun j => a N j) J) (jsum L J)
  | 0 => h 0
  | J + 1 => tends_add (tends_jsum h J) (h (J + 1))

theorem tends_psumN {a : Nat → Nat → α} {L : Nat → α} (h : ∀ k, Tends (fun m => a m k) (L k)) :
    ∀ n, Tends (fun m => psumN (fun k => a m k) n) (psumN L n)
  | 0 => tends_const 0
  | n + 1 => tends_add (tends_psumN h n) (h n)

theorem psumN_le {f g : Nat → α} (h : ∀ k, f k ≤ g k) : ∀ n, psumN f n ≤ psumN g n
  | 0 => Std.le_refl _
  | n + 1 => by have := psumN_le h n; have := h n; simp only [psumN]; grind

theorem psumN_add (f g : Nat → α) : ∀ n, psumN (fun k => f k + g k) n = psumN f n + psumN g n
  | 0 => by simp only [psumN]; grind
  | n + 1 => by have := psumN_add f g n; simp only [psumN]; grind

theorem psumN_mul_left (c : α) (f : Nat → α) : ∀ n, psumN (fun k => c * f k) n = c * psumN f n
  | 0 => by simp only [psumN]; grind
  | n + 1 => by have := psumN_mul_left c f n; simp only [psumN]; grind

theorem psumN_mono {f : Nat → α} (h : ∀ k, 0 ≤ f k) (n : Nat) : psumN f n ≤ psumN f (n + 1) := by
  have := h n; simp only [psumN]; grind

/-- Sums over infinitely many modes: a termwise inequality passes to the sums of the series. -/
theorem series_le {f g : Nat → α} {F G : α} (h : ∀ k, f k ≤ g k) (hf : Tends (psumN f) F)
    (hg : Tends (psumN g) G) : F ≤ G :=
  le_of_tends (psumN_le h) hf hg

end Limits

/-! ### Infinitely many modes: Theorems G.4(ii), G.4(iii) and G.5 for the low modes -/

section InfiniteFamilies
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- Theorem G.4(ii), low modes, for a sequence of modes `u_k ∈ [0,1]`:
    `0 ≤ sum_k (a_k - b_k) ≤ sum_k (x_k^2/2 tau) e^{-x_k/2}`. -/
theorem low_modes_rate_series (h : IsExp2 exp) {tau : α} (ht : 0 ≤ tau) (u : Nat → α)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ 1) {A B : α}
    (hA : Tends (psumN fun k => exp (-(tau * (1 - exp (-(u k))))) - exp (-(tau * u k))) A)
    (hB : Tends (psumN fun k => tau * u k * u k / 2 * exp (-(tau * u k / 2))) B) :
    0 ≤ A ∧ A ≤ B := by
  constructor
  · have hz : Tends (psumN fun _ : Nat => (0 : α)) 0 := by
      have e : (psumN fun _ : Nat => (0 : α)) = fun _ => 0 := by
        funext n; induction n with
        | zero => rfl
        | succ n ih => simp only [psumN, ih]; grind
      rw [e]; exact tends_const 0
    exact series_le (fun k => by have := walk_mode_ge h.toIsExp ht (u k); grind) hz hA
  · exact series_le (fun k => walk_mode_le h ht (hu k).1 (hu k).2) hA hB

/-- Theorem G.4(iii), low modes, for a sequence of modes. -/
theorem low_modes_second_series (h : IsExp3 exp) {tau : α} (ht : 0 ≤ tau) (u : Nat → α)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ 1) {L A B : α}
    (hL : Tends (psumN fun k => -(tau * u k * u k * u k / 6 * exp (-(tau * u k)))) L)
    (hA : Tends (psumN fun k => exp (-(tau * (1 - exp (-(u k))))) - exp (-(tau * u k))
            - tau * u k * u k / 2 * exp (-(tau * u k))) A)
    (hB : Tends (psumN fun k => (tau * u k * u k / 2) * (tau * u k * u k / 2) / 2
            * exp (-(tau * u k / 2))) B) :
    L ≤ A ∧ A ≤ B :=
  ⟨series_le (fun k => (walk_mode_second h ht (hu k).1 (hu k).2).1) hL hA,
   series_le (fun k => (walk_mode_second h ht (hu k).1 (hu k).2).2) hA hB⟩

/-- Theorem G.5, low modes, for a sequence of modes. -/
theorem low_modes_corrected_series (h : IsExp3 exp) {tau : α} (ht : 0 ≤ tau) (u : Nat → α)
    (hu : ∀ k, 0 ≤ u k ∧ u k ≤ 1) {L A B : α}
    (hL : Tends (psumN fun k => -((tau * u k * u k * u k / 2
            + (tau * u k * u k / 2) * (tau * u k * u k / 2)) * exp (-(tau * u k / 2)))) L)
    (hA : Tends (psumN fun k => exp (-(tau * (1 - exp (-(u k)))))
            * (1 - tau * (1 - exp (-(u k))) * (1 - exp (-(u k))) / 2) - exp (-(tau * u k))) A)
    (hB : Tends (psumN fun k => (tau * u k * u k * u k / 2
            + (tau * u k * u k / 2) * (tau * u k * u k / 2)) * exp (-(tau * u k / 2))) B) :
    L ≤ A ∧ A ≤ B :=
  ⟨series_le (fun k => (walk_mode_corrected h ht (hu k).1 (hu k).2).1) hL hA,
   series_le (fun k => (walk_mode_corrected h ht (hu k).1 (hu k).2).2) hA hB⟩

end InfiniteFamilies

/-! ### The Poisson identity as an equality of series (Theorem G.4(i))

  `E_k = sum_j c_j s_k^j` (inner series), `T = sum_k E_k`, `p_j = sum_k s_k^j`.
  Then `sum_j c_j p_j = T`. With `c_0 = 0`, `c_j = e^{-tau} tau^j / j!` one has
  `E_k = e^{-tau(1 - s_k)} - e^{-tau}`, `T = T_sigma(t)` and `p_j = Theta(j sigma)`. -/

section PoissonSeries
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

theorem poly_nonneg {c : Nat → α} (hc : ∀ j, 0 ≤ c j) {x : α} (hx : 0 ≤ x) : ∀ m, 0 ≤ poly c x m
  | 0 => by simpa [poly] using OrderedRing.mul_nonneg (hc 0) (pw_nonneg hx 0)
  | m + 1 => by
    have ih := poly_nonneg hc hx m
    have := OrderedRing.mul_nonneg (hc (m + 1)) (pw_nonneg hx (m + 1))
    simp only [poly]; grind

theorem poly_mono {c : Nat → α} (hc : ∀ j, 0 ≤ c j) {x : α} (hx : 0 ≤ x) (m : Nat) :
    poly c x m ≤ poly c x (m + 1) := by
  have := OrderedRing.mul_nonneg (hc (m + 1)) (pw_nonneg hx (m + 1))
  simp only [poly]; grind

/-- Exchange of the two sums for finitely many modes and terms (sequence form). -/
theorem poly_psum_exchange (c : Nat → α) (s : Nat → α) (n : Nat) :
    ∀ m, psumN (fun k => poly c (s k) m) n
      = jsum (fun j => c j * psumN (fun k => pw (s k) j) n) m
  | 0 => by
    have := psumN_mul_left (c 0) (fun k => pw (s k) 0) n
    simp only [poly, jsum]; exact this
  | m + 1 => by
    have ih := poly_psum_exchange c s n m
    have h1 := psumN_add (fun k => poly c (s k) m) (fun k => c (m + 1) * pw (s k) (m + 1)) n
    have h2 := psumN_mul_left (c (m + 1)) (fun k => pw (s k) (m + 1)) n
    simp only [poly, jsum]
    rw [h1, h2, ih]

/-- The Poisson identity (Tonelli for a double series with nonnegative terms). -/
theorem poisson_series (c s : Nat → α) (hc : ∀ j, 0 ≤ c j) (hs : ∀ k, 0 ≤ s k)
    {E p : Nat → α} {T : α}
    (hE : ∀ k, Tends (fun m => poly c (s k) m) (E k))
    (hT : Tends (psumN E) T)
    (hp : ∀ j, Tends (fun n => psumN (fun k => pw (s k) j) n) (p j)) :
    Tends (jsum fun j => c j * p j) T := by
  -- for fixed m: sum over the modes of the truncated inner series converges to the m-th partial sum
  have hSm : ∀ m, Tends (fun n => psumN (fun k => poly c (s k) m) n) (jsum (fun j => c j * p j) m) := by
    intro m
    have e : (fun n => psumN (fun k => poly c (s k) m) n)
        = fun n => jsum (fun j => c j * psumN (fun k => pw (s k) j) n) m := by
      funext n; exact poly_psum_exchange c s n m
    rw [e]
    exact tends_jsum (a := fun n j => c j * psumN (fun k => pw (s k) j) n)
      (fun j => tends_mul_left (c j) (hc j) (hp j)) m
  have hpolyE : ∀ k m, poly c (s k) m ≤ E k :=
    fun k m => mono_le_limit (fun m => poly_mono hc (hs k) m) (hE k) m
  have hupper : ∀ m, jsum (fun j => c j * p j) m ≤ T :=
    fun m => le_of_tends (psumN_le (fun k => hpolyE k m)) (hSm m) hT
  intro e he
  obtain ⟨N0, hN0⟩ := hT (e / 2) (by grind)
  have a0 := hN0 N0 (Nat.le_refl _)
  have hfin := tends_psumN (a := fun m k => poly c (s k) m) hE N0
  obtain ⟨M0, hM0⟩ := hfin (e / 2) (by grind)
  refine ⟨M0, fun m hm => ?_⟩
  have a1 := hM0 m hm
  have a2 : psumN (fun k => poly c (s k) m) N0 ≤ jsum (fun j => c j * p j) m :=
    mono_le_limit (fun n => psumN_mono (fun k => poly_nonneg hc (hs k) m) n) (hSm m) N0
  have a3 := hupper m
  constructor <;> grind

end PoissonSeries

/-! ### Theorem G.7, step 3, and Corollary G.8

  Dominated convergence for series: if `0 ≤ a_N(j) ≤ B`, `a_N(j) → m_j` for every `j`, and
  `sum_j c_j` converges, then `sum_j c_j a_N(j) → sum_j c_j m_j`.
  In Theorem G.7, `a_N(j) = Tr P_N^j`, `c_j = e^{-tau} tau^j/j!` for `j ≥ 1` (`c_0 = 0`), and
  `B = M + M^2`. The convergence `Tr P_N^j → m_j` (steps 1 and 2: laws of large numbers) is a
  HYPOTHESIS here; probability theory is not formalised. -/

section Dominated
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

theorem jsum_mono {g : Nat → α} (h : ∀ j, 0 ≤ g j) (m : Nat) : jsum g m ≤ jsum g (m + 1) := by
  have := h (m + 1); simp only [jsum]; grind

/-- Tail estimate: `P_{J0} ≤ S ≤ P_{J0} + B (C - C_{J0})`. -/
theorem series_tail (c : Nat → α) (hc : ∀ j, 0 ≤ c j) {Csum : α} (hC : Tends (jsum c) Csum)
    (b : Nat → α) {B : α} (hb0 : ∀ j, 0 ≤ b j) (hbB : ∀ j, b j ≤ B) {S : α}
    (hS : Tends (jsum fun j => c j * b j) S) (J0 : Nat) :
    jsum (fun j => c j * b j) J0 ≤ S ∧
    S ≤ jsum (fun j => c j * b j) J0 + B * (Csum - jsum c J0) := by
  have hB0 : 0 ≤ B := Std.le_trans (hb0 0) (hbB 0)
  have hterm : ∀ j, 0 ≤ c j * b j := fun j => OrderedRing.mul_nonneg (hc j) (hb0 j)
  constructor
  · exact mono_le_limit (fun m => jsum_mono hterm m) hS J0
  · have step : ∀ i, jsum (fun j => c j * b j) (J0 + i)
        ≤ jsum (fun j => c j * b j) J0 + B * (jsum c (J0 + i) - jsum c J0) := by
      intro i
      induction i with
      | zero => simp only [Nat.add_zero]; grind
      | succ i ih =>
        have h1 := OrderedRing.mul_le_mul_of_nonneg_left (hbB (J0 + i + 1)) (hc (J0 + i + 1))
        have e1 : jsum (fun j => c j * b j) (J0 + (i + 1))
            = jsum (fun j => c j * b j) (J0 + i) + c (J0 + i + 1) * b (J0 + i + 1) := rfl
        have e2 : jsum c (J0 + (i + 1)) = jsum c (J0 + i) + c (J0 + i + 1) := rfl
        rw [e1, e2]; grind
    have hCle : ∀ i, jsum c (J0 + i) ≤ Csum :=
      fun i => mono_le_limit (fun m => jsum_mono hc m) hC (J0 + i)
    have step2 : ∀ i, jsum (fun j => c j * b j) (J0 + i)
        ≤ jsum (fun j => c j * b j) J0 + B * (Csum - jsum c J0) := by
      intro i
      have h1 := step i
      have h2 := OrderedRing.mul_le_mul_of_nonneg_left (hCle i) hB0
      grind
    exact le_of_tends step2 (tends_shift J0 hS) (tends_const _)

/-- Dominated convergence for series. -/
theorem dominated_series (c : Nat → α) (hc : ∀ j, 0 ≤ c j) {Csum : α} (hC : Tends (jsum c) Csum)
    (a : Nat → Nat → α) {B : α} (ha0 : ∀ N j, 0 ≤ a N j) (haB : ∀ N j, a N j ≤ B)
    (m : Nat → α) (hconv : ∀ j, Tends (fun N => a N j) (m j))
    (S : Nat → α) (hS : ∀ N, Tends (jsum fun j => c j * a N j) (S N))
    {Sinf : α} (hSinf : Tends (jsum fun j => c j * m j) Sinf) :
    Tends S Sinf := by
  have hB0 : 0 ≤ B := Std.le_trans (ha0 0 0) (haB 0 0)
  have hm0 : ∀ j, 0 ≤ m j := fun j => le_of_tends (fun N => ha0 N j) (tends_const 0) (hconv j)
  have hmB : ∀ j, m j ≤ B := fun j => le_of_tends (fun N => haB N j) (hconv j) (tends_const B)
  intro e he
  have hd : 3 * (B + 1) * (e / (3 * (B + 1))) = e := by grind
  have hdpos : 0 < e / (3 * (B + 1)) := by
    apply Classical.byContradiction
    intro hn
    have h1 := OrderedRing.mul_nonneg (show (0 : α) ≤ 3 * (B + 1) by grind)
      (show (0 : α) ≤ -(e / (3 * (B + 1))) by grind)
    grind
  obtain ⟨J0, hJ0⟩ := hC (e / (3 * (B + 1))) hdpos
  have hC0 := hJ0 J0 (Nat.le_refl _)
  have hCle : jsum c J0 ≤ Csum := mono_le_limit (fun m => jsum_mono hc m) hC J0
  -- B * tail < e/3
  have htail := OrderedRing.mul_le_mul_of_nonneg_left
    (show Csum - jsum c J0 ≤ e / (3 * (B + 1)) by grind) hB0
  have hBt : B * (Csum - jsum c J0) < e / 3 := by grind
  -- finite part
  have hfin := tends_jsum (a := fun N j => c j * a N j)
    (fun j => tends_mul_left (c j) (hc j) (hconv j)) J0
  obtain ⟨N1, hN1⟩ := hfin (e / 3) (by grind)
  have tinf := series_tail c hc hC m hm0 hmB hSinf J0
  refine ⟨N1, fun N hN => ?_⟩
  have tN := series_tail c hc hC (a N) (ha0 N) (haB N) (hS N) J0
  have f := hN1 N hN
  constructor <;> grind

/-- Theorem G.7(ii) with Corollary G.8: if the traces of the powers of the sampled walk converge
    to the moments `p_j = sum_k s_k^j` of the population walk and are bounded by `B`, then the
    subtracted trace `S_N = sum_j c_j Tr P_N^j` converges to `T = sum_k sum_j c_j s_k^j`. -/
theorem fixed_scale_limit (c s : Nat → α) (hc : ∀ j, 0 ≤ c j) (hs : ∀ k, 0 ≤ s k)
    {Csum : α} (hC : Tends (jsum c) Csum)
    {E p : Nat → α} {T : α}
    (hE : ∀ k, Tends (fun m => poly c (s k) m) (E k)) (hT : Tends (psumN E) T)
    (hp : ∀ j, Tends (fun n => psumN (fun k => pw (s k) j) n) (p j))
    (a : Nat → Nat → α) {B : α} (ha0 : ∀ N j, 0 ≤ a N j) (haB : ∀ N j, a N j ≤ B)
    (hconv : ∀ j, Tends (fun N => a N j) (p j))
    (S : Nat → α) (hS : ∀ N, Tends (jsum fun j => c j * a N j) (S N)) :
    Tends S T :=
  dominated_series c hc hC a ha0 haB p hconv S hS (poisson_series c s hc hs hE hT hp)

end Dominated
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### The Taylor bounds of the exponential function from the Archimedean property

  So far the Taylor bounds were hypotheses (`IsExp2`, `IsExp3`). Here they are DERIVED from the
  two defining properties of `exp` (`IsExp`) in an Archimedean ordered field, by Riemann sums:
  `e^{(n+1)h} - e^{nh} = e^{nh}(e^h - 1)` is summed over `n` and the step `h = x/N` is sent to
  zero with the Archimedean property. No completeness, no calculus. -/

section Arch
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- The Archimedean property of the ordered field. -/
def Archimedean (α : Type) [Field α] [LE α] [LT α] : Prop := ∀ x : α, ∃ n : Nat, x < ncast n

/-- If `N a ≤ c` for all positive integers `N`, then `a ≤ 0`. -/
theorem arch_limit (harch : Archimedean α) {a c : α} (h : ∀ n : Nat, ncast (n + 1) * a ≤ c) :
    a ≤ 0 := by
  apply Classical.byContradiction
  intro hn
  have ha : 0 < a := by grind
  obtain ⟨n, hn1⟩ := harch (c / a)
  have h1 := OrderedRing.mul_lt_mul_of_pos_left hn1 ha
  have h2 : a * (c / a) = c := by grind
  have h3 := h n
  simp only [ncast] at h3
  grind

theorem ncast_succ_pos (n : Nat) : (0 : α) < ncast (n + 1) := by
  have := ncast_nonneg (α := α) n; simp only [ncast]; grind

theorem ncast_succ_cancel (n : Nat) (u : α) : ncast (n + 1) * (u / ncast (n + 1)) = u := by
  have := ncast_succ_pos (α := α) n; grind

theorem div_nonneg_of_pos {v N : α} (hv : 0 ≤ v) (hN : 0 < N) : 0 ≤ v / N := by
  apply Classical.byContradiction
  intro hc
  have h1 := OrderedRing.mul_pos hN (show (0 : α) < -(v / N) by grind)
  have h2 : N * (v / N) = v := by grind
  grind

/-- Riemann sum for `1 - e^{-u}` from below: `N h - h^2 N(N+1)/2 ≤ 1 - e^{-N h}`. -/
theorem riemann_neg (h : IsExp exp) {hh : α} (hh0 : 0 ≤ hh) :
    ∀ n : Nat, ncast n * hh - hh * hh * (ncast n * (ncast n + 1)) / 2 ≤ 1 - exp (-(ncast n * hh))
  | 0 => by
    have e : exp (-((0 : α) * hh)) = 1 := by rw [show -((0 : α) * hh) = 0 by grind]; exact h.zero
    simp only [ncast]; rw [e]; grind
  | n + 1 => by
    have ih := riemann_neg h hh0 n
    have hadd := h.add (-((ncast n + 1) * hh)) hh
    rw [show -((ncast n + 1) * hh) + hh = -(ncast n * hh) by grind] at hadd
    have hA := h.nonneg (-((ncast n + 1) * hh))
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left (show hh ≤ exp hh - 1 by have := h.ge hh; grind) hA
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left
      (show 1 - (ncast n + 1) * hh ≤ exp (-((ncast n + 1) * hh)) by
        have := h.ge (-((ncast n + 1) * hh)); grind) hh0
    simp only [ncast]
    grind

/-- `e^x - 1 - x ≤ x^2/2` for `x ≤ 0`. -/
theorem taylor_nonpos_of_arch (h : IsExp exp) (harch : Archimedean α) (x : α) (hx : x ≤ 0) :
    exp x - 1 - x ≤ x * x / 2 := by
  have key : exp x - 1 - x - x * x / 2 ≤ 0 := by
    apply arch_limit harch (c := x * x / 2)
    intro n
    have hN := ncast_succ_cancel (α := α) n (-x)
    have hNpos := ncast_succ_pos (α := α) n
    have hh0 : (0 : α) ≤ -x / ncast (n + 1) := div_nonneg_of_pos (by grind) hNpos
    have r := riemann_neg h hh0 (n + 1)
    rw [hN, show -(-x) = x by grind] at r
    have m := OrderedRing.mul_le_mul_of_nonneg_left r (show (0 : α) ≤ ncast (n + 1) by grind)
    have id1 : ncast (n + 1) * ((-x / ncast (n + 1)) * (-x / ncast (n + 1))
          * (ncast (n + 1) * (ncast (n + 1) + 1)) / 2)
        = (ncast (n + 1) * (-x / ncast (n + 1))) * (ncast (n + 1) * (-x / ncast (n + 1)))
          * (ncast (n + 1) + 1) / 2 := by grind
    rw [hN] at id1
    grind
  grind

/-- Riemann sum for `e^{x} - 1` from above:
    `e^{N h} - 1 ≤ N h + h^2 (N(N+1)/2) e^{N h}`. -/
theorem riemann_pos (h : IsExp exp) {hh : α} (hh0 : 0 ≤ hh) :
    ∀ n : Nat, exp (ncast n * hh) - 1
      ≤ ncast n * hh + hh * hh * (ncast n * (ncast n + 1)) / 2 * exp (ncast n * hh)
  | 0 => by
    have e : exp ((0 : α) * hh) = 1 := by rw [show (0 : α) * hh = 0 by grind]; exact h.zero
    simp only [ncast]; rw [e]; grind
  | n + 1 => by
    have ih := riemann_pos h hh0 n
    have hN0 := ncast_nonneg (α := α) n
    have hadd := h.add (ncast n * hh) hh
    rw [show ncast n * hh + hh = (ncast n + 1) * hh by grind] at hadd
    have hE := h.nonneg (ncast n * hh)
    -- e^{Nh}(e^h - 1) ≤ h e^{(N+1)h}
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left (h.sub_one_le hh) hE
    -- h (B - 1) ≤ h (N+1) h B
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left (h.sub_one_le ((ncast n + 1) * hh)) hh0
    -- e^{Nh} ≤ B, times the nonnegative coefficient
    have hmono := h.mono (show ncast n * hh ≤ (ncast n + 1) * hh by
      have := OrderedRing.mul_nonneg hh0 (show (0 : α) ≤ 1 by grind); grind)
    have hc : (0 : α) ≤ hh * hh * (ncast n * (ncast n + 1)) / 2 := by
      have a1 := OrderedRing.mul_nonneg hh0 hh0
      have a2 := OrderedRing.mul_nonneg hN0 (show (0 : α) ≤ ncast n + 1 by grind)
      have a3 := OrderedRing.mul_nonneg a1 a2
      grind
    have m3 := OrderedRing.mul_le_mul_of_nonneg_left hmono hc
    have dec : exp ((ncast n + 1) * hh) - 1
        = (exp (ncast n * hh) - 1) + exp (ncast n * hh) * (exp hh - 1) := by rw [hadd]; grind
    have m1' : exp (ncast n * hh) * (exp hh - 1) ≤ hh * exp ((ncast n + 1) * hh) := by
      rw [hadd]; grind
    simp only [ncast]
    grind

/-- `e^x - 1 - x ≤ (x^2/2) e^x` for `x ≥ 0`. -/
theorem taylor_nonneg_of_arch (h : IsExp exp) (harch : Archimedean α) (x : α) (hx : 0 ≤ x) :
    exp x - 1 - x ≤ x * x / 2 * exp x := by
  have key : exp x - 1 - x - x * x / 2 * exp x ≤ 0 := by
    apply arch_limit harch (c := x * x / 2 * exp x)
    intro n
    have hN := ncast_succ_cancel (α := α) n x
    have hNpos := ncast_succ_pos (α := α) n
    have hh0 : (0 : α) ≤ x / ncast (n + 1) := div_nonneg_of_pos (by grind) hNpos
    have r := riemann_pos h hh0 (n + 1)
    rw [hN] at r
    have m := OrderedRing.mul_le_mul_of_nonneg_left r (show (0 : α) ≤ ncast (n + 1) by grind)
    have id1 : ncast (n + 1) * ((x / ncast (n + 1)) * (x / ncast (n + 1))
          * (ncast (n + 1) * (ncast (n + 1) + 1)) / 2 * exp x)
        = (ncast (n + 1) * (x / ncast (n + 1))) * (ncast (n + 1) * (x / ncast (n + 1)))
          * (ncast (n + 1) + 1) / 2 * exp x := by grind
    rw [hN] at id1
    grind
  grind

/-- `sq n = sum_{k<n} k^2`, with `3 sq n ≤ n^3`. -/
def sq : Nat → α
  | 0 => 0
  | n + 1 => sq n + ncast n * ncast n

theorem sq_le : ∀ n : Nat, (sq n : α) * 3 ≤ ncast n * ncast n * ncast n
  | 0 => by simp only [sq, ncast]; grind
  | n + 1 => by
    have ih : (sq n : α) * 3 ≤ ncast n * ncast n * ncast n := sq_le n
    have hN := ncast_nonneg (α := α) n
    have hN2 := mul_self_nonneg (ncast (α := α) n)
    simp only [sq, ncast]; grind

theorem sq_nonneg : ∀ n : Nat, (0 : α) ≤ sq n
  | 0 => by simp only [sq]; grind
  | n + 1 => by
    have ih : (0 : α) ≤ sq n := sq_nonneg n
    have := mul_self_nonneg (ncast (α := α) n)
    simp only [sq]; grind

/-- Riemann sum for `1 - e^{-u}` from above, with the second-order bound of `e^{-v}`:
    `1 - e^{-N h} ≤ N h - h^2 N(N-1)/2 + h^3 sq(N)/2`. -/
theorem riemann_neg3 (h : IsExp exp) (harch : Archimedean α) {hh : α} (hh0 : 0 ≤ hh) :
    ∀ n : Nat, 1 - exp (-(ncast n * hh))
      ≤ ncast n * hh - hh * hh * (ncast n * (ncast n - 1)) / 2 + hh * hh * hh * sq n / 2
  | 0 => by
    have e : exp (-((0 : α) * hh)) = 1 := by rw [show -((0 : α) * hh) = 0 by grind]; exact h.zero
    simp only [ncast, sq]; rw [e]; grind
  | n + 1 => by
    have ih := riemann_neg3 h harch hh0 n
    have hN0 := ncast_nonneg (α := α) n
    have hadd := h.add (-(ncast n * hh)) (-hh)
    rw [show -(ncast n * hh) + -hh = -((ncast n + 1) * hh) by grind] at hadd
    have hE := h.nonneg (-(ncast n * hh))
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left
      (show 1 - exp (-hh) ≤ hh by have := h.ge (-hh); grind) hE
    have hNh := OrderedRing.mul_nonneg hN0 hh0
    have t := taylor_nonpos_of_arch h harch (-(ncast n * hh)) (by grind)
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left
      (show exp (-(ncast n * hh)) ≤ 1 - ncast n * hh + (ncast n * hh) * (ncast n * hh) / 2 by grind) hh0
    simp only [ncast, sq]
    rw [hadd]
    grind

/-- `1 - u + u^2/2 - u^3/6 ≤ e^{-u}` for `u ≥ 0`. -/
theorem taylor3_of_arch (h : IsExp exp) (harch : Archimedean α) (u : α) (hu : 0 ≤ u) :
    1 - u + u * u / 2 - u * u * u / 6 ≤ exp (-u) := by
  have key : 1 - u + u * u / 2 - u * u * u / 6 - exp (-u) ≤ 0 := by
    apply arch_limit harch (c := u * u / 2)
    intro n
    have hN := ncast_succ_cancel (α := α) n u
    have hNpos := ncast_succ_pos (α := α) n
    have hh0 : (0 : α) ≤ u / ncast (n + 1) := div_nonneg_of_pos (by grind) hNpos
    have r := riemann_neg3 h harch hh0 (n + 1)
    rw [hN] at r
    -- h^3 sq ≤ u^3 / 3
    have h3 : (0 : α) ≤ (u / ncast (n + 1)) * (u / ncast (n + 1)) * (u / ncast (n + 1)) :=
      OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hh0 hh0) hh0
    have s1 := OrderedRing.mul_le_mul_of_nonneg_left (sq_le (α := α) (n + 1)) h3
    have id3 : (u / ncast (n + 1)) * (u / ncast (n + 1)) * (u / ncast (n + 1))
          * (ncast (n + 1) * ncast (n + 1) * ncast (n + 1))
        = (ncast (n + 1) * (u / ncast (n + 1))) * (ncast (n + 1) * (u / ncast (n + 1)))
          * (ncast (n + 1) * (u / ncast (n + 1))) := by grind
    rw [hN] at id3
    have m := OrderedRing.mul_le_mul_of_nonneg_left r (show (0 : α) ≤ ncast (n + 1) by grind)
    have id1 : ncast (n + 1) * ((u / ncast (n + 1)) * (u / ncast (n + 1))
          * (ncast (n + 1) * (ncast (n + 1) - 1)) / 2)
        = (ncast (n + 1) * (u / ncast (n + 1))) * (ncast (n + 1) * (u / ncast (n + 1)))
          * (ncast (n + 1) - 1) / 2 := by grind
    rw [hN] at id1
    -- N * (h^3 sq / 2) ≤ N * u^3/6
    have s2 := OrderedRing.mul_le_mul_of_nonneg_left
      (show (u / ncast (n + 1)) * (u / ncast (n + 1)) * (u / ncast (n + 1)) * sq (n + 1) / 2
          ≤ u * u * u / 6 by grind) (show (0 : α) ≤ ncast (n + 1) by grind)
    grind
  grind

/-- In an Archimedean ordered field the two defining properties of `exp` imply all Taylor
    bounds that were hypotheses before. -/
theorem isExp2_of_arch (h : IsExp exp) (harch : Archimedean α) : IsExp2 exp :=
  { toIsExp := h
    taylor_nonneg := taylor_nonneg_of_arch h harch
    taylor_nonpos := taylor_nonpos_of_arch h harch }

theorem isExp3_of_arch (h : IsExp exp) (harch : Archimedean α) : IsExp3 exp :=
  { toIsExp2 := isExp2_of_arch h harch
    taylor3 := taylor3_of_arch h harch }

end Arch
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

section Arch2
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- Riemann sum for `e^x - 1` from below: `N h + h^2 N(N-1)/2 ≤ e^{N h} - 1`. -/
theorem riemann_pos_lower (h : IsExp exp) {hh : α} (hh0 : 0 ≤ hh) :
    ∀ n : Nat, ncast n * hh + hh * hh * (ncast n * (ncast n - 1)) / 2 ≤ exp (ncast n * hh) - 1
  | 0 => by
    have e : exp ((0 : α) * hh) = 1 := by rw [show (0 : α) * hh = 0 by grind]; exact h.zero
    simp only [ncast]; rw [e]; grind
  | n + 1 => by
    have ih := riemann_pos_lower h hh0 n
    have hadd := h.add (ncast n * hh) hh
    rw [show ncast n * hh + hh = (ncast n + 1) * hh by grind] at hadd
    have hE := h.nonneg (ncast n * hh)
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left (show hh ≤ exp hh - 1 by have := h.ge hh; grind) hE
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left
      (show 1 + ncast n * hh ≤ exp (ncast n * hh) by have := h.ge (ncast n * hh); grind) hh0
    have dec : exp ((ncast n + 1) * hh) - 1
        = (exp (ncast n * hh) - 1) + exp (ncast n * hh) * (exp hh - 1) := by rw [hadd]; grind
    simp only [ncast]
    grind

/-- `1 + x + x^2/2 ≤ e^x` for `x ≥ 0`. -/
theorem exp_ge_second (h : IsExp exp) (harch : Archimedean α) (x : α) (hx : 0 ≤ x) :
    1 + x + x * x / 2 ≤ exp x := by
  have key : 1 + x + x * x / 2 - exp x ≤ 0 := by
    apply arch_limit harch (c := x * x / 2)
    intro n
    have hN := ncast_succ_cancel (α := α) n x
    have hNpos := ncast_succ_pos (α := α) n
    have hh0 : (0 : α) ≤ x / ncast (n + 1) := div_nonneg_of_pos hx hNpos
    have r := riemann_pos_lower h hh0 (n + 1)
    rw [hN] at r
    have m := OrderedRing.mul_le_mul_of_nonneg_left r (show (0 : α) ≤ ncast (n + 1) by grind)
    have id1 : ncast (n + 1) * ((x / ncast (n + 1)) * (x / ncast (n + 1))
          * (ncast (n + 1) * (ncast (n + 1) - 1)) / 2)
        = (ncast (n + 1) * (x / ncast (n + 1))) * (ncast (n + 1) * (x / ncast (n + 1)))
          * (ncast (n + 1) - 1) / 2 := by grind
    rw [hN] at id1
    grind
  grind

/-- `e^{-(v + v^2)} ≤ 1 - v` for `0 ≤ v ≤ 1/2` (a lower bound for the logarithm, without it). -/
theorem exp_neg_le_one_sub (h : IsExp exp) (harch : Archimedean α) {v : α} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1 / 2) : exp (-(v + v * v)) ≤ 1 - v := by
  have hvv := mul_self_nonneg v
  have hw0 : 0 ≤ v + v * v := by grind
  have hB := exp_ge_second h harch (v + v * v) hw0
  have hA := h.nonneg (-(v + v * v))
  have hAB := h.add (-(v + v * v)) (v + v * v)
  rw [show -(v + v * v) + (v + v * v) = (0 : α) by grind, h.zero] at hAB
  -- polynomial inequality (1 - v) Q ≥ 1 with Q = 1 + w + w^2/2, w = v + v^2
  have p1 := OrderedRing.mul_le_mul_of_nonneg_left hv1 hv0            -- v^2 ≤ v/2
  have p2 := OrderedRing.mul_le_mul_of_nonneg_left p1 hv0             -- v^3 ≤ v^2/2
  have hpoly0 : (0 : α) ≤ 1 - v - v * v - v * (v * v) := by grind
  have p3 := OrderedRing.mul_nonneg hvv hpoly0                        -- v^2 (1 - v - v^2 - v^3) ≥ 0
  have hQ : 1 ≤ (1 - v) * (1 + (v + v * v) + (v + v * v) * (v + v * v) / 2) := by grind
  -- A ≤ A (1-v) Q ≤ (1-v) A B = 1 - v
  have q1 := OrderedRing.mul_le_mul_of_nonneg_left hQ hA
  have hA1 := OrderedRing.mul_nonneg hA (show (0 : α) ≤ 1 - v by grind)
  have q2 := OrderedRing.mul_le_mul_of_nonneg_left hB hA1
  have e1 : exp (-(v + v * v)) * (1 - v) * exp (v + v * v)
      = (1 - v) * (exp (-(v + v * v)) * exp (v + v * v)) := by grind
  rw [e1, ← hAB] at q2
  have e2 : exp (-(v + v * v)) * ((1 - v) * (1 + (v + v * v) + (v + v * v) * (v + v * v) / 2))
      = exp (-(v + v * v)) * (1 - v) * (1 + (v + v * v) + (v + v * v) * (v + v * v) / 2) := by grind
  rw [e2] at q1
  have q3 := Std.le_trans q1 q2
  grind

/-- Proposition G.21 (trace in discrete time), one low mode with `v = 1 - s ∈ [0, 1/2]`:
    `e^{-k(v + v^2)} ≤ s^k ≤ e^{-k v}`. -/
theorem pw_sandwich (h : IsExp exp) (harch : Archimedean α) {v : α} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1 / 2) :
    ∀ k : Nat, exp (-(ncast k * (v + v * v))) ≤ pw (1 - v) k ∧ pw (1 - v) k ≤ exp (-(ncast k * v))
  | 0 => by
    have e1 : exp (-((0 : α) * (v + v * v))) = 1 := by
      rw [show -((0 : α) * (v + v * v)) = 0 by grind]; exact h.zero
    have e2 : exp (-((0 : α) * v)) = 1 := by rw [show -((0 : α) * v) = 0 by grind]; exact h.zero
    simp only [pw, ncast]; rw [e1, e2]; constructor <;> grind
  | k + 1 => by
    have ih := pw_sandwich h harch hv0 hv1 k
    have hs0 : (0 : α) ≤ 1 - v := by grind
    have base := exp_neg_le_one_sub h harch hv0 hv1
    have hup := h.ge (-v)
    have a1 := h.add (-(v + v * v)) (-(ncast k * (v + v * v)))
    rw [show -(v + v * v) + -(ncast k * (v + v * v)) = -((ncast k + 1) * (v + v * v)) by grind] at a1
    have a2 := h.add (-v) (-(ncast k * v))
    rw [show -v + -(ncast k * v) = -((ncast k + 1) * v) by grind] at a2
    -- lower: e^{-w} e^{-k w} ≤ (1-v) e^{-kw} ≤ (1-v) s^k
    have l1 := OrderedRing.mul_le_mul_of_nonneg_left base (h.nonneg (-(ncast k * (v + v * v))))
    have l2 := OrderedRing.mul_le_mul_of_nonneg_left ih.1 hs0
    -- upper: (1-v) s^k ≤ (1-v) e^{-kv} ≤ e^{-v} e^{-kv}
    have u1 := OrderedRing.mul_le_mul_of_nonneg_left ih.2 hs0
    have u2 := OrderedRing.mul_le_mul_of_nonneg_left (show 1 - v ≤ exp (-v) by grind)
      (h.nonneg (-(ncast k * v)))
    simp only [pw, ncast]
    rw [a1, a2]
    constructor <;> grind

/-- `0 ≤ e^{-kv} - s^k ≤ k v^2 e^{-kv}`: the low-mode estimate in the proof of
    Proposition G.21, with no hypothesis on logarithms. -/
theorem discrete_low_mode (h : IsExp exp) (harch : Archimedean α) {v : α} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1 / 2) (k : Nat) :
    0 ≤ exp (-(ncast k * v)) - pw (1 - v) k ∧
    exp (-(ncast k * v)) - pw (1 - v) k ≤ ncast k * (v * v) * exp (-(ncast k * v)) := by
  have sw := pw_sandwich h harch hv0 hv1 k
  have hk := ncast_nonneg (α := α) k
  have hadd := h.add (-(ncast k * v)) (-(ncast k * (v * v)))
  rw [show -(ncast k * v) + -(ncast k * (v * v)) = -(ncast k * (v + v * v)) by grind] at hadd
  have g := h.ge (-(ncast k * (v * v)))
  have m := OrderedRing.mul_le_mul_of_nonneg_left g (h.nonneg (-(ncast k * v)))
  rw [hadd] at sw
  constructor <;> grind

end Arch2

/-! ### The round sphere and profiles with a jump: the algebra -/

section SphereAlgebra
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- Taylor coefficients of `P_l(cos theta) = 1 + a2 theta^2 + a4 theta^4 + ...` from
    `f'' + cot(theta) f' + lam f = 0`, `cot = 1/theta - theta/3 - ...`:
    the conditions at the orders `theta^0` and `theta^2`. -/
theorem legendre_coefficients (lam : α) :
    4 * (-(lam / 4)) + lam = 0 ∧
    16 * (lam * (3 * lam - 2) / 192) - 2 * (-(lam / 4)) / 3 + lam * (-(lam / 4)) = 0 := by
  constructor <;> grind

/-- `s_l = 1 + a2 m2 + a4 m4 = 1 - sigma_xi lam + (m4/64) lam^2` with
    `sigma_xi = m2/4 + m4/96`. -/
theorem sphere_low_mode (lam m2 m4 : α) :
    1 + (-(lam / 4)) * m2 + (lam * (3 * lam - 2) / 192) * m4
      = 1 - (m2 / 4 + m4 / 96) * lam + m4 / 64 * (lam * lam) := by grind

/-- With `m2 I0 = I2`, `I0 = x - x^2/3`, `I2 = 2 x^2 - 4 x^3/3`, `m4 = 8 x^2` (`x = xi^2`):
    `sigma_xi - (x/2)(1 - x/6) = -(x^3/18) / (1 - x/3)`, of the order `xi^6`. -/
theorem sphere_sigma (x m2 : α) (h : m2 * (x - x * x / 3) = 2 * (x * x) - 4 * (x * x * x) / 3) :
    (m2 / 4 + 8 * (x * x) / 96 - x / 2 * (1 - x / 6)) * (x - x * x / 3)
      = -(x * x * x * x) / 18 := by
  grind

/-- Uniform distribution on the unit ball of `R^d`: `E X_1^2 = 1/(d+2)`,
    `E X_1^4 = 3/((d+2)(d+4))`, hence `beta = (d+2)/(d+4)`. -/
theorem ball_beta (d b : α) (hd : 0 < d)
    (hb : b * (3 * ((1 / (d + 2)) * (1 / (d + 2)))) = 3 / ((d + 2) * (d + 4))) :
    b * (d + 4) = d + 2 := by
  have h2 : (d + 2) * (1 / (d + 2)) = 1 := by grind
  have h4 : (d + 4) * (1 / (d + 4)) = 1 := by grind
  have h24 : ((d + 2) * (d + 4)) * (3 / ((d + 2) * (d + 4))) = 3 := by
    have : (0 : α) < (d + 2) * (d + 4) := OrderedRing.mul_pos (by grind) (by grind)
    grind
  grind

end SphereAlgebra
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### The partial sums of the exponential series lie below the exponential function

  `term j x = x^j / j!`, `pexp m x = sum_{j ≤ m} x^j / j!`. In an Archimedean ordered field
  `pexp m x ≤ exp x` for `x ≥ 0`, by induction on `m` with Riemann sums. This removes the
  hypothesis of `poisson_lower`. (The convergence `pexp m x → exp x` is not proven here.) -/

section ExpSeries
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

def term : Nat → α → α
  | 0, _ => 1
  | j + 1, x => term j x * x / ncast (j + 1)
def pexp : Nat → α → α
  | 0, _ => 1
  | m + 1, x => pexp m x + term (m + 1) x

theorem term_nonneg {x : α} (hx : 0 ≤ x) : ∀ j : Nat, 0 ≤ term j x
  | 0 => by simp only [term]; grind
  | j + 1 => by
    have ih := term_nonneg hx j
    have h1 := OrderedRing.mul_nonneg ih hx
    simp only [term]
    exact div_nonneg_of_pos h1 (ncast_succ_pos j)

theorem term_succ_mul (j : Nat) (x : α) : ncast (j + 1) * term (j + 1) x = term j x * x := by
  have := ncast_succ_pos (α := α) j
  simp only [term]; grind

/-- `term (j+1) (a+h) - term (j+1) a ≤ h term j (a+h)` for `a, h ≥ 0`
    (the mean value inequality for `x^{j+1}/(j+1)!`). -/
theorem term_increment {a hh : α} (ha : 0 ≤ a) (hh0 : 0 ≤ hh) :
    ∀ j : Nat, term (j + 1) (a + hh) - term (j + 1) a ≤ hh * term j (a + hh)
  | 0 => by
    have e1 : term 1 (a + hh) = a + hh := by
      simp only [term, ncast]; grind
    have e2 : term 1 a = a := by simp only [term, ncast]; grind
    rw [e1, e2]; simp only [term]; grind
  | j + 1 => by
    have ih := term_increment ha hh0 j
    have hpos := ncast_succ_pos (α := α) (j + 1)
    have s1 := term_succ_mul (j + 1) (a + hh)
    have s2 := term_succ_mul (j + 1) a
    have s0 := term_succ_mul j (a + hh)
    have tj := term_nonneg (show (0 : α) ≤ a + hh by grind) j
    have tj1 := term_nonneg (show (0 : α) ≤ a + hh by grind) (j + 1)
    -- (term(j+1)(a+h) - term(j+1) a) a ≤ h term j (a+h) a ≤ h (j+1) term (j+1) (a+h)
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left ih ha
    have m2 := OrderedRing.mul_nonneg (OrderedRing.mul_nonneg hh0 tj) hh0
    have s0h : hh * (ncast (j + 1) * term (j + 1) (a + hh)) = hh * (term j (a + hh) * (a + hh)) := by
      rw [s0]
    -- N * (lhs) ≤ N * (rhs) with N = ncast (j+2)
    have key : ncast (j + 1 + 1) * (term (j + 1 + 1) (a + hh) - term (j + 1 + 1) a)
        ≤ ncast (j + 1 + 1) * (hh * term (j + 1) (a + hh)) := by
      have e : ncast (j + 1 + 1) = ncast (j + 1) + (1 : α) := rfl
      rw [show ncast (j + 1 + 1) * (term (j + 1 + 1) (a + hh) - term (j + 1 + 1) a)
          = ncast (j + 1 + 1) * term (j + 1 + 1) (a + hh) - ncast (j + 1 + 1) * term (j + 1 + 1) a by grind,
        s1, s2, e]
      grind
    apply Classical.byContradiction
    intro hn
    have hlt : hh * term (j + 1) (a + hh) < term (j + 1 + 1) (a + hh) - term (j + 1 + 1) a := by grind
    have := OrderedRing.mul_lt_mul_of_pos_left hlt hpos
    grind

theorem pexp_increment {a hh : α} (ha : 0 ≤ a) (hh0 : 0 ≤ hh) :
    ∀ m : Nat, pexp (m + 1) (a + hh) - pexp (m + 1) a ≤ hh * pexp m (a + hh)
  | 0 => by
    have t := term_increment ha hh0 0
    have e0 : term 0 (a + hh) = (1 : α) := rfl
    rw [e0] at t
    simp only [pexp] at *; grind
  | m + 1 => by
    have ih := pexp_increment ha hh0 m
    have t := term_increment ha hh0 (m + 1)
    simp only [pexp] at *; grind

theorem pexp_zero_arg : ∀ m : Nat, pexp m (0 : α) = 1
  | 0 => rfl
  | m + 1 => by
    have ih : pexp m (0 : α) = 1 := pexp_zero_arg m
    have hpos := ncast_succ_pos (α := α) m
    have t : term (m + 1) (0 : α) = 0 := by simp only [term]; grind
    simp only [pexp]; rw [t]; grind

/-- If `pexp m ≤ exp` on `[0, ∞)`, then
    `-h (pexp m (N h) - 1) ≤ exp (N h) - pexp (m+1) (N h)`. -/
theorem pexp_riemann (h : IsExp exp) (m : Nat) (hm : ∀ x : α, 0 ≤ x → pexp m x ≤ exp x)
    {hh : α} (hh0 : 0 ≤ hh) :
    ∀ n : Nat, -(hh * (pexp m (ncast n * hh) - 1)) ≤ exp (ncast n * hh) - pexp (m + 1) (ncast n * hh)
  | 0 => by
    have e : exp ((0 : α) * hh) = 1 := by rw [show (0 : α) * hh = 0 by grind]; exact h.zero
    have z1 := pexp_zero_arg (α := α) m
    have z2 := pexp_zero_arg (α := α) (m + 1)
    simp only [ncast]
    rw [show (0 : α) * hh = 0 by grind] at e ⊢
    rw [e, z1, z2]; grind
  | n + 1 => by
    have ih := pexp_riemann h m hm hh0 n
    have hN := ncast_nonneg (α := α) n
    have hNh := OrderedRing.mul_nonneg hN hh0
    have hadd := h.add (ncast n * hh) hh
    rw [show ncast n * hh + hh = (ncast n + 1) * hh by grind] at hadd
    have hE := h.nonneg (ncast n * hh)
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left (show hh ≤ exp hh - 1 by have := h.ge hh; grind) hE
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left (hm (ncast n * hh) hNh) hh0
    have inc := pexp_increment (a := ncast n * hh) hNh hh0 m
    rw [show ncast n * hh + hh = (ncast n + 1) * hh by grind] at inc
    have dec : exp ((ncast n + 1) * hh)
        = exp (ncast n * hh) + exp (ncast n * hh) * (exp hh - 1) := by rw [hadd]; grind
    simp only [ncast]
    grind

/-- `sum_{j ≤ m} x^j / j! ≤ e^x` for `x ≥ 0`. -/
theorem pexp_le_exp (h : IsExp exp) (harch : Archimedean α) :
    ∀ (m : Nat) (x : α), 0 ≤ x → pexp m x ≤ exp x
  | 0, x, hx => by have := h.ge x; simp only [pexp]; grind
  | m + 1, x, hx => by
    have hm := pexp_le_exp h harch m
    have key : pexp (m + 1) x - exp x ≤ 0 := by
      apply arch_limit harch (c := x * (pexp m x - 1))
      intro n
      have hN := ncast_succ_cancel (α := α) n x
      have hNpos := ncast_succ_pos (α := α) n
      have hh0 : (0 : α) ≤ x / ncast (n + 1) := div_nonneg_of_pos hx hNpos
      have r := pexp_riemann h m hm hh0 (n + 1)
      rw [hN] at r
      have mm := OrderedRing.mul_le_mul_of_nonneg_left r (show (0 : α) ≤ ncast (n + 1) by grind)
      have id1 : ncast (n + 1) * -(x / ncast (n + 1) * (pexp m x - 1))
          = -((ncast (n + 1) * (x / ncast (n + 1))) * (pexp m x - 1)) := by grind
      rw [hN] at id1
      grind
    grind

/-- `x^j / j! = (1/j!) x^j` in the notation of `poly`: `term j x = term j 1 * pw x j`. -/
theorem term_eq (x : α) : ∀ j : Nat, term j x = term j 1 * pw x j
  | 0 => by simp only [term, pw]; grind
  | j + 1 => by
    have ih := term_eq x j
    have hpos := ncast_succ_pos (α := α) j
    simp only [term, pw]; rw [ih]; grind

theorem poly_eq_pexp (x : α) : ∀ m : Nat, poly (fun j => term j (1 : α)) x m = pexp m x
  | 0 => by simp only [poly, pexp, term, pw]; grind
  | m + 1 => by
    have ih := poly_eq_pexp x m
    have t := term_eq x (m + 1)
    simp only [poly, pexp]; rw [ih, t]

/-- The one-sided finite Poisson bound without analytic hypotheses, in an Archimedean field:
    `e^{-tau} (sum_k sum_{j ≤ m} (tau s_k)^j / j! - N) ≤ sum_k (e^{-tau(1 - s_k)} - e^{-tau})`
    for nonnegative modes `s_k`. -/
theorem poisson_lower_arch (h : IsExp exp) (harch : Archimedean α) (m : Nat) {tau : α}
    (ht : 0 ≤ tau) (l : List α) (hl : ∀ s ∈ l, 0 ≤ s) :
    exp (-tau) * (polysum (fun j => term j (1 : α)) m (l.map (fun s => tau * s)) - cnt l)
      ≤ subheat exp tau l :=
  poisson_lower h (fun j => term j (1 : α)) m
    (fun x hx => by rw [poly_eq_pexp]; exact pexp_le_exp h harch m x hx) ht l hl

end ExpSeries
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Convergence of the exponential series, and the Poisson identity without analytic
    hypotheses on the exponential function

  In an Archimedean ordered field with `exp` as in `IsExp`:
  `0 ≤ e^x - sum_{j ≤ m} x^j/j! ≤ (x^{m+1}/(m+1)!) e^x` for `x ≥ 0`, and `x^m/m! → 0`.
  Hence `sum_{j ≤ m} x^j/j! → e^x`. -/

section ExpSeries2
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

theorem term_zero_arg : ∀ j : Nat, term (j + 1) (0 : α) = 0
  | j => by have hpos := ncast_succ_pos (α := α) j; simp only [term]; grind

/-- `h term j a ≤ term (j+1) (a+h) - term (j+1) a` for `a, h ≥ 0`. -/
theorem term_increment_lower {a hh : α} (ha : 0 ≤ a) (hh0 : 0 ≤ hh) :
    ∀ j : Nat, hh * term j a ≤ term (j + 1) (a + hh) - term (j + 1) a
  | 0 => by
    have e1 : term 1 (a + hh) = a + hh := by simp only [term, ncast]; grind
    have e2 : term 1 a = a := by simp only [term, ncast]; grind
    have e0 : term 0 a = (1 : α) := rfl
    rw [e1, e2, e0]; grind
  | j + 1 => by
    have ih := term_increment_lower ha hh0 j
    have hpos := ncast_succ_pos (α := α) (j + 1)
    have s1 := term_succ_mul (j + 1) (a + hh)
    have s2 := term_succ_mul (j + 1) a
    have s0 := term_succ_mul j a
    have tj := term_nonneg ha j
    have tj1 := term_nonneg ha (j + 1)
    -- monotonicity: term (j+1) a ≤ term (j+1) (a+h)
    have hmono : term (j + 1) a ≤ term (j + 1) (a + hh) := by
      have := OrderedRing.mul_nonneg hh0 tj; grind
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left ih ha            -- a h t_j(a) ≤ a (Δ)
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left hmono hh0        -- h T(a) ≤ h T(a+h)
    have s0h : hh * (ncast (j + 1) * term (j + 1) a) = hh * (term j a * a) := by rw [s0]
    have key : ncast (j + 1 + 1) * (hh * term (j + 1) a)
        ≤ ncast (j + 1 + 1) * (term (j + 1 + 1) (a + hh) - term (j + 1 + 1) a) := by
      have e : ncast (j + 1 + 1) = ncast (j + 1) + (1 : α) := rfl
      rw [show ncast (j + 1 + 1) * (term (j + 1 + 1) (a + hh) - term (j + 1 + 1) a)
          = ncast (j + 1 + 1) * term (j + 1 + 1) (a + hh) - ncast (j + 1 + 1) * term (j + 1 + 1) a by grind,
        s1, s2, e]
      grind
    apply Classical.byContradiction
    intro hn
    have hlt : term (j + 1 + 1) (a + hh) - term (j + 1 + 1) a < hh * term (j + 1) a := by grind
    have := OrderedRing.mul_lt_mul_of_pos_left hlt hpos
    grind

theorem pexp_increment_lower {a hh : α} (ha : 0 ≤ a) (hh0 : 0 ≤ hh) :
    ∀ m : Nat, hh * pexp m a ≤ pexp (m + 1) (a + hh) - pexp (m + 1) a
  | 0 => by
    have t := term_increment_lower ha hh0 0
    have e0 : term 0 a = (1 : α) := rfl
    rw [e0] at t
    simp only [pexp] at *; grind
  | m + 1 => by
    have ih := pexp_increment_lower ha hh0 m
    have t := term_increment_lower ha hh0 (m + 1)
    simp only [pexp] at *; grind

/-- Riemann sum for the remainder, given the remainder bound of order `m`. -/
theorem remainder_riemann (h : IsExp exp) (m : Nat)
    (hm : ∀ y : α, 0 ≤ y → exp y - pexp m y ≤ term (m + 1) y * exp y) {hh : α} (hh0 : 0 ≤ hh) :
    ∀ n : Nat, exp (ncast n * hh) - pexp (m + 1) (ncast n * hh)
      ≤ exp (ncast n * hh) * (term (m + 2) (ncast n * hh) + hh * term (m + 1) (ncast n * hh))
        + hh * (pexp m (ncast n * hh) - 1)
  | 0 => by
    have e : exp ((0 : α) * hh) = 1 := by rw [show (0 : α) * hh = 0 by grind]; exact h.zero
    have z1 := pexp_zero_arg (α := α) m
    have z2 := pexp_zero_arg (α := α) (m + 1)
    have t1 := term_zero_arg (α := α) (m + 1)
    have t2 := term_zero_arg (α := α) m
    simp only [ncast]
    rw [show (0 : α) * hh = 0 by grind] at e ⊢
    rw [e, z1, z2, t1, t2]; grind
  | n + 1 => by
    have ih := remainder_riemann h m hm hh0 n
    have hN := ncast_nonneg (α := α) n
    have hNh := OrderedRing.mul_nonneg hN hh0
    have hN1h : (0 : α) ≤ (ncast n + 1) * hh := OrderedRing.mul_nonneg (by grind) hh0
    have hadd := h.add (ncast n * hh) hh
    rw [show ncast n * hh + hh = (ncast n + 1) * hh by grind] at hadd
    have hE := h.nonneg (ncast n * hh)
    have hE1 := h.nonneg ((ncast n + 1) * hh)
    -- e^{Nh}(e^h - 1) ≤ h e^{(N+1)h}
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left (h.sub_one_le hh) hE
    have m1' : exp (ncast n * hh) * (exp hh - 1) ≤ hh * exp ((ncast n + 1) * hh) := by
      rw [hadd]; grind
    -- increments of pexp
    have incL := pexp_increment_lower (a := ncast n * hh) hNh hh0 m
    rw [show ncast n * hh + hh = (ncast n + 1) * hh by grind] at incL
    -- remainder bound of order m at (N+1)h, times h
    have r := OrderedRing.mul_le_mul_of_nonneg_left (hm ((ncast n + 1) * hh) hN1h) hh0
    -- term (m+2) (Nh) + h term (m+1) (Nh) ≤ term (m+2) ((N+1)h)
    have tinc := term_increment_lower (a := ncast n * hh) hNh hh0 (m + 1)
    rw [show ncast n * hh + hh = (ncast n + 1) * hh by grind] at tinc
    -- monotonicity of exp and nonnegativity of the bracket
    have hmono := h.mono (show ncast n * hh ≤ (ncast n + 1) * hh by grind)
    have tb1 := term_nonneg hNh (m + 2)
    have tb2 := OrderedRing.mul_nonneg hh0 (term_nonneg hNh (m + 1))
    have b1 := OrderedRing.mul_le_mul_of_nonneg_left hmono
      (show (0 : α) ≤ term (m + 2) (ncast n * hh) + hh * term (m + 1) (ncast n * hh) by grind)
    have b2 := OrderedRing.mul_le_mul_of_nonneg_left
      (show term (m + 2) (ncast n * hh) + hh * term (m + 1) (ncast n * hh)
          ≤ term (m + 2) ((ncast n + 1) * hh) by grind) hE1
    have dec : exp ((ncast n + 1) * hh)
        = exp (ncast n * hh) + exp (ncast n * hh) * (exp hh - 1) := by rw [hadd]; grind
    simp only [ncast]
    grind

/-- Remainder bound: `e^x - sum_{j ≤ m} x^j/j! ≤ (x^{m+1}/(m+1)!) e^x` for `x ≥ 0`. -/
theorem exp_remainder (h : IsExp exp) (harch : Archimedean α) :
    ∀ (m : Nat) (x : α), 0 ≤ x → exp x - pexp m x ≤ term (m + 1) x * exp x
  | 0, x, hx => by
    have e1 : term 1 x = x := by simp only [term, ncast]; grind
    have := h.sub_one_le x
    simp only [pexp]; rw [e1]; grind
  | m + 1, x, hx => by
    have hm := exp_remainder h harch m
    have key : exp x - pexp (m + 1) x - term (m + 2) x * exp x ≤ 0 := by
      apply arch_limit harch (c := x * (exp x * term (m + 1) x + (pexp m x - 1)))
      intro n
      have hN := ncast_succ_cancel (α := α) n x
      have hNpos := ncast_succ_pos (α := α) n
      have hh0 : (0 : α) ≤ x / ncast (n + 1) := div_nonneg_of_pos hx hNpos
      have r := remainder_riemann h m hm hh0 (n + 1)
      rw [hN] at r
      have mm := OrderedRing.mul_le_mul_of_nonneg_left r (show (0 : α) ≤ ncast (n + 1) by grind)
      have id1 : ncast (n + 1) * (exp x * (term (m + 2) x + x / ncast (n + 1) * term (m + 1) x)
            + x / ncast (n + 1) * (pexp m x - 1))
          = ncast (n + 1) * (exp x * term (m + 2) x)
            + (ncast (n + 1) * (x / ncast (n + 1))) * (exp x * term (m + 1) x + (pexp m x - 1)) := by
        grind
      rw [hN] at id1
      grind
    grind

end ExpSeries2
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

section ExpSeries3
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

theorem ncast_le_add (M : Nat) : ∀ i : Nat, (ncast M : α) ≤ ncast (M + i)
  | 0 => Std.le_refl _
  | i + 1 => by
    have ih : (ncast M : α) ≤ ncast (M + i) := ncast_le_add M i
    have e : (ncast (M + (i + 1)) : α) = ncast (M + i) + 1 := rfl
    rw [e]; grind

/-- `2 x^{m+1}/(m+1)! ≤ x^m/m!` once `2x ≤ m+1`. -/
theorem term_halving {x : α} (hx : 0 < x) (m : Nat) (hm : 2 * x ≤ ncast (m + 1)) :
    2 * term (m + 1) x ≤ term m x := by
  have s := term_succ_mul m x
  have t1 := term_nonneg (show (0 : α) ≤ x by grind) (m + 1)
  have h1 := OrderedRing.mul_nonneg (show (0 : α) ≤ ncast (m + 1) - 2 * x by grind) t1
  apply Classical.byContradiction
  intro hn
  have h2 := OrderedRing.mul_pos hx (show (0 : α) < 2 * term (m + 1) x - term m x by grind)
  grind

theorem pw_two_ge : ∀ i : Nat, (ncast i : α) + 1 ≤ pw 2 i
  | 0 => by simp only [ncast, pw]; grind
  | i + 1 => by
    have ih : (ncast i : α) + 1 ≤ pw 2 i := pw_two_ge i
    have hi := ncast_nonneg (α := α) i
    simp only [ncast, pw]; grind

theorem term_geometric {x : α} (hx : 0 < x) (M0 : Nat) (hM : 2 * x ≤ ncast M0) :
    ∀ i : Nat, pw 2 i * term (M0 + i) x ≤ term M0 x
  | 0 => by simp only [pw, Nat.add_zero]; grind
  | i + 1 => by
    have ih := term_geometric hx M0 hM i
    have hle : (ncast M0 : α) ≤ ncast (M0 + i + 1) := ncast_le_add M0 (i + 1)
    have hh := term_halving hx (M0 + i) (by grind)
    have hp := pw_nonneg (show (0 : α) ≤ 2 by grind) i
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left hh hp
    have e : term (M0 + (i + 1)) x = term (M0 + i + 1) x := rfl
    simp only [pw]; rw [e]; grind

/-- `x^m / m! → 0`. -/
theorem tends_term (harch : Archimedean α) {x : α} (hx : 0 ≤ x) :
    Tends (fun m => term m x) 0 := by
  intro e he
  by_cases hx0 : x = 0
  · refine ⟨1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have := term_zero_arg (α := α) k
    rw [hx0]
    show (0 : α) - e < term (k + 1) 0 ∧ term (k + 1) 0 < 0 + e
    rw [this]; constructor <;> grind
  · have hxpos : 0 < x := by grind
    obtain ⟨M0, hM0⟩ := harch (2 * x)
    obtain ⟨i0, hi0⟩ := harch (term M0 x / e)
    refine ⟨M0 + i0, fun n hn => ?_⟩
    obtain ⟨i, rfl, hi⟩ : ∃ i, n = M0 + i ∧ i0 ≤ i := ⟨n - M0, by omega, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, i = i0 + d := ⟨i - i0, by omega⟩
    have g := term_geometric hxpos M0 (by grind) (i0 + d)
    have t0 := term_nonneg hx (M0 + (i0 + d))
    have p2 := pw_two_ge (α := α) (i0 + d)
    have hmono : (ncast i0 : α) ≤ ncast (i0 + d) := ncast_le_add i0 d
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left p2 t0
    have he2 : e * (term M0 x / e) = term M0 x := by grind
    show (0 : α) - e < term (M0 + (i0 + d)) x ∧ term (M0 + (i0 + d)) x < 0 + e
    constructor
    · grind
    · apply Classical.byContradiction
      intro hc
      have hge : e ≤ term (M0 + (i0 + d)) x := by grind
      -- (ncast i + 1) * e ≤ (ncast i + 1) * term ≤ term M0 x, but ncast i * e > term M0 x
      have hi1 : (0 : α) ≤ ncast (i0 + d) + 1 := by have := ncast_nonneg (α := α) (i0 + d); grind
      have m2 := OrderedRing.mul_le_mul_of_nonneg_left hge hi1
      have m3 := OrderedRing.mul_lt_mul_of_pos_left hi0 he
      have m4 := OrderedRing.mul_le_mul_of_nonneg_left hmono (show (0 : α) ≤ e by grind)
      grind

/-- The exponential series converges: `sum_{j ≤ m} x^j / j! → e^x` for `x ≥ 0`. -/
theorem tends_pexp (h : IsExp exp) (harch : Archimedean α) {x : α} (hx : 0 ≤ x) :
    Tends (fun m => pexp m x) (exp x) := by
  have ht := tends_shift 1 (tends_mul_left (exp x) (h.nonneg x) (tends_term harch hx))
  intro e he
  obtain ⟨N, hN⟩ := ht e he
  refine ⟨N, fun n hn => ?_⟩
  have a := hN n hn
  have up := pexp_le_exp h harch n x hx
  have rem := exp_remainder h harch n x hx
  have e1 : term (1 + n) x = term (n + 1) x := by rw [Nat.add_comm]
  simp only [] at a
  rw [e1] at a
  constructor <;> grind

/-- The Poisson weights `c_0 = 0`, `c_j = e^{-tau} tau^j / j!` for `j ≥ 1`. -/
def poissonW (exp : α → α) (tau : α) : Nat → α
  | 0 => 0
  | j + 1 => exp (-tau) * term (j + 1) tau

theorem term_mul (a b : α) : ∀ j : Nat, term j (a * b) = term j a * pw b j
  | 0 => by simp only [term, pw]; grind
  | j + 1 => by
    have ih := term_mul a b j
    have hpos := ncast_succ_pos (α := α) j
    simp only [term, pw]; rw [ih]; grind

theorem poly_poisson (tau s : α) :
    ∀ m : Nat, poly (poissonW exp tau) s m = exp (-tau) * (pexp m (tau * s) - 1)
  | 0 => by simp only [poly, poissonW, pexp, pw]; grind
  | m + 1 => by
    have ih : poly (poissonW exp tau) s m = exp (-tau) * (pexp m (tau * s) - 1) := poly_poisson tau s m
    have t := term_mul tau s (m + 1)
    simp only [poly, poissonW, pexp]; rw [ih, t]; grind

theorem poissonW_nonneg (h : IsExp exp) {tau : α} (ht : 0 ≤ tau) : ∀ j, 0 ≤ poissonW exp tau j
  | 0 => by simp only [poissonW]; grind
  | j + 1 => by
    simpa [poissonW] using OrderedRing.mul_nonneg (h.nonneg (-tau)) (term_nonneg ht (j + 1))

/-- The inner series: `sum_j c_j s^j = e^{-tau(1-s)} - e^{-tau}`. -/
theorem tends_poly_poisson (h : IsExp exp) (harch : Archimedean α) {tau s : α} (ht : 0 ≤ tau)
    (hs : 0 ≤ s) :
    Tends (fun m => poly (poissonW exp tau) s m) (exp (-(tau * (1 - s))) - exp (-tau)) := by
  have hts := OrderedRing.mul_nonneg ht hs
  have t1 := tends_mul_left (exp (-tau)) (h.nonneg (-tau)) (tends_pexp h harch hts)
  have t2 := tends_add t1 (tends_const (-(exp (-tau))))
  have hadd := h.add (-tau) (tau * s)
  rw [show -tau + tau * s = -(tau * (1 - s)) by grind] at hadd
  have ef : (fun m => poly (poissonW exp tau) s m)
      = fun m => exp (-tau) * pexp m (tau * s) + -(exp (-tau)) := by
    funext m; rw [poly_poisson]; grind
  have eL : exp (-(tau * (1 - s))) - exp (-tau) = exp (-tau) * exp (tau * s) + -(exp (-tau)) := by
    rw [hadd]; grind
  rw [ef, eL]; exact t2

/-- **The Poisson identity (Theorem G.4(i)) in an Archimedean ordered field.**
    For modes `s_k ≥ 0`: if the subtracted trace `T = sum_k (e^{-tau(1-s_k)} - e^{-tau})` and the
    moments `p_j = sum_k s_k^j` exist, then `sum_{j ≥ 1} e^{-tau} (tau^j/j!) p_j = T`.
    The only hypotheses are the existence of these sums over the modes. -/
theorem poisson_identity (h : IsExp exp) (harch : Archimedean α) {tau : α} (ht : 0 ≤ tau)
    (s : Nat → α) (hs : ∀ k, 0 ≤ s k) {p : Nat → α} {T : α}
    (hT : Tends (psumN fun k => exp (-(tau * (1 - s k))) - exp (-tau)) T)
    (hp : ∀ j, Tends (fun n => psumN (fun k => pw (s k) j) n) (p j)) :
    Tends (jsum fun j => poissonW exp tau j * p j) T :=
  poisson_series (poissonW exp tau) s (poissonW_nonneg h ht) hs
    (E := fun k => exp (-(tau * (1 - s k))) - exp (-tau))
    (fun k => tends_poly_poisson h harch ht (hs k)) hT hp

theorem pw_one : ∀ j : Nat, pw (1 : α) j = 1
  | 0 => rfl
  | j + 1 => by have ih : pw (1 : α) j = 1 := pw_one j; simp only [pw]; rw [ih]; grind

theorem jsum_eq_poly_one (c : Nat → α) : ∀ m : Nat, jsum c m = poly c 1 m
  | 0 => by simp only [jsum, poly, pw]; grind
  | m + 1 => by
    have ih := jsum_eq_poly_one c m
    have p1 := pw_one (α := α) (m + 1)
    simp only [jsum, poly]; rw [ih, p1]; grind

/-- `sum_{j ≥ 1} e^{-tau} tau^j / j! = 1 - e^{-tau}`. -/
theorem tends_poissonW_sum (h : IsExp exp) (harch : Archimedean α) {tau : α} (ht : 0 ≤ tau) :
    Tends (jsum (poissonW exp tau)) (1 - exp (-tau)) := by
  have t := tends_poly_poisson h harch ht (show (0 : α) ≤ 1 by grind)
  have e : (fun m => poly (poissonW exp tau) 1 m) = jsum (poissonW exp tau) := by
    funext m; exact (jsum_eq_poly_one _ m).symm
  rw [e, show -(tau * (1 - 1)) = (0 : α) by grind, h.zero] at t
  exact t

/-- **Theorem G.7(ii) with Corollary G.8 in an Archimedean ordered field.**
    Hypotheses: the traces `a N j = Tr P_N^j` of the sampled walk are bounded and converge to the
    moments `p_j = sum_k s_k^j` of the population walk (laws of large numbers, not formalised);
    for each `N` the Poisson series of the sampled graph has the sum `S N` (Theorem 3.11); and the
    sums over the modes of the population walk exist. Conclusion: `S N → T`. -/
theorem fixed_scale_limit_arch (h : IsExp exp) (harch : Archimedean α) {tau : α} (ht : 0 ≤ tau)
    (s : Nat → α) (hs : ∀ k, 0 ≤ s k) {p : Nat → α} {T : α}
    (hT : Tends (psumN fun k => exp (-(tau * (1 - s k))) - exp (-tau)) T)
    (hp : ∀ j, Tends (fun n => psumN (fun k => pw (s k) j) n) (p j))
    (a : Nat → Nat → α) {B : α} (ha0 : ∀ N j, 0 ≤ a N j) (haB : ∀ N j, a N j ≤ B)
    (hconv : ∀ j, Tends (fun N => a N j) (p j))
    (S : Nat → α) (hS : ∀ N, Tends (jsum fun j => poissonW exp tau j * a N j) (S N)) :
    Tends S T :=
  dominated_series (poissonW exp tau) (poissonW_nonneg h ht) (tends_poissonW_sum h harch ht)
    a ha0 haB p hconv S hS (poisson_identity h harch ht s hs hT hp)

end ExpSeries3
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Proposition G.11 (estimated normalisation) and Proposition G.18 (gap on the sphere):
    the elementary inequalities -/

section Round7
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

def prod1 : List α → α
  | [] => 1
  | t :: l => (1 + t) * prod1 l
def lenA : List α → α
  | [] => 0
  | _ :: l => lenA l + 1
def lenNat : List α → Nat
  | [] => 0
  | _ :: l => lenNat l + 1

/-- For `|theta_s| ≤ a`:
    `|prod_s (1 + theta_s) - 1| ≤ (1+a)^n - 1` and
    `|prod_s (1 + theta_s) - 1 - sum_s theta_s| ≤ (1+a)^n - 1 - n a`. -/
theorem product_expansion {a : α} (ha : 0 ≤ a) :
    ∀ l : List α, (∀ t ∈ l, -a ≤ t ∧ t ≤ a) →
      (-(pw (1 + a) (lenNat l) - 1) ≤ prod1 l - 1 ∧ prod1 l - 1 ≤ pw (1 + a) (lenNat l) - 1) ∧
      (-(pw (1 + a) (lenNat l) - 1 - lenA l * a) ≤ prod1 l - 1 - lsum l ∧
        prod1 l - 1 - lsum l ≤ pw (1 + a) (lenNat l) - 1 - lenA l * a)
  | [], _ => by simp [prod1, lenNat, lenA, lsum, pw] <;> grind
  | t :: l, hl => by
    have ih := product_expansion ha l (fun r hr => hl r (List.mem_cons_of_mem _ hr))
    have ht := hl t List.mem_cons_self
    obtain ⟨⟨i1, i2⟩, ⟨j1, j2⟩⟩ := ih
    have hQ1 : (0 : α) ≤ pw (1 + a) (lenNat l) - 1 := by grind
    -- |(1+t)(P-1)| ≤ (1+a)(Q-1) and |t (P-1)| ≤ a (Q-1)
    have b1 := abs_mul_le (show -(1 + a) ≤ 1 + t by grind) (show 1 + t ≤ 1 + a by grind) i1 i2
    have b2 := abs_mul_le ht.1 ht.2 i1 i2
    have d1 : (1 + t) * prod1 l - 1 = (1 + t) * (prod1 l - 1) + t := by grind
    have d2 : (1 + t) * prod1 l - 1 - (t + lsum l)
        = (prod1 l - 1 - lsum l) + t * (prod1 l - 1) := by grind
    simp only [prod1, lenNat, lenA, lsum, pw]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

/-- Proposition G.18, low modes on the sphere: for `0 ≤ u ≤ 1/2`, `0 ≤ beta ≤ 51/50`,
    `c ≤ 27/50` and `|s - (1 - u + beta u^2/2)| ≤ c u^3`: `2/5 ≤ s ≤ 1 - (3/5) u`. -/
theorem sphere_gap_low {u s beta c : α} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (hb0 : 0 ≤ beta)
    (hb1 : beta ≤ 51 / 50) (hc0 : 0 ≤ c) (hc1 : c ≤ 27 / 50)
    (h1 : -(c * (u * u * u)) ≤ s - (1 - u + beta * (u * u) / 2))
    (h2 : s - (1 - u + beta * (u * u) / 2) ≤ c * (u * u * u)) :
    2 / 5 ≤ s ∧ s ≤ 1 - 3 / 5 * u := by
  have huu := mul_self_nonneg u
  have p1 := OrderedRing.mul_le_mul_of_nonneg_left hu1 hu0                 -- u^2 ≤ u/2
  have p2 := OrderedRing.mul_le_mul_of_nonneg_left p1 hu0                  -- u^3 ≤ u^2/2
  have hu3 : (0 : α) ≤ u * u * u := by
    have := OrderedRing.mul_nonneg huu hu0; grind
  have q1 := OrderedRing.mul_le_mul_of_nonneg_left hb1 huu                 -- beta u^2 ≤ (51/50) u^2
  have q0 := OrderedRing.mul_nonneg hb0 huu
  have q2 := OrderedRing.mul_le_mul_of_nonneg_left hc1 hu3                 -- c u^3 ≤ (27/50) u^3
  have q3 := OrderedRing.mul_nonneg hc0 hu3
  constructor <;> grind

end Round7
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Theorem G.14 (joint regime with a polynomially decreasing kernel scale):
    the elementary inequalities of the proof -/

section JointPoly
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {exp : α → α}

/-- Estimated against exact normalisation: for `0 ≤ delta ≤ 1/8`,
    `(1+delta)/(1-delta)^2 ≤ 1 + 4 delta` and `(1-delta)/(1+delta)^2 ≥ 1 - 4 delta`
    (written without division). Hence `|theta_ij| ≤ 4 delta`. -/
theorem theta_bounds {d : α} (h0 : 0 ≤ d) (h1 : d ≤ 1 / 8) :
    1 + d ≤ (1 + 4 * d) * ((1 - d) * (1 - d)) ∧ (1 - 4 * d) * ((1 + d) * (1 + d)) ≤ 1 - d := by
  have p1 := OrderedRing.mul_nonneg h0 (show (0 : α) ≤ 1 - 7 * d by grind)
  have p2 := OrderedRing.mul_nonneg (mul_self_nonneg d) h0
  have p3 := mul_self_nonneg d
  constructor <;> grind

/-- `e^x ≤ 1 + 2x` for `0 ≤ x ≤ 1/2`. -/
theorem exp_le_one_add_two_mul (h : IsExp exp) {x : α} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    exp x ≤ 1 + 2 * x := by
  have hadd := h.add x (-x)
  rw [show x + -x = (0 : α) by grind, h.zero] at hadd
  have g := h.ge (-x)
  have m1 := OrderedRing.mul_le_mul_of_nonneg_left g (h.nonneg x)       -- e^x (1 - x) ≤ 1
  have p := OrderedRing.mul_nonneg hx0 (show (0 : α) ≤ 1 - 2 * x by grind)  -- x (1 - 2x) ≥ 0
  apply Classical.byContradiction
  intro hn
  have hlt : 1 + 2 * x < exp x := by grind
  have m2 := OrderedRing.mul_lt_mul_of_pos_left hlt (show (0 : α) < 1 - x by grind)
  grind

/-- `(1 + y)^k ≤ e^{k y}` for `y ≥ 0`. -/
theorem pw_one_add_le_exp (h : IsExp exp) {y : α} (hy : 0 ≤ y) :
    ∀ k : Nat, pw (1 + y) k ≤ exp (ncast k * y)
  | 0 => by
    have e : exp ((0 : α) * y) = 1 := by rw [show (0 : α) * y = 0 by grind]; exact h.zero
    simp only [pw, ncast]; rw [e]; grind
  | k + 1 => by
    have ih := pw_one_add_le_exp h hy k
    have hadd := h.add y (ncast k * y)
    rw [show y + ncast k * y = (ncast k + 1) * y by grind] at hadd
    have m1 := OrderedRing.mul_le_mul_of_nonneg_left ih (show (0 : α) ≤ 1 + y by grind)
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left (h.ge y) (h.nonneg (ncast k * y))
    simp only [pw, ncast]
    rw [hadd]; grind

/-- `(1 + 4 delta)^k - 1 ≤ 8 k delta` if `4 k delta ≤ 1/2`: the cost of the estimated
    normalisation in a closed walk of `k` steps. -/
theorem normalisation_cost (h : IsExp exp) {d : α} (hd : 0 ≤ d) (k : Nat)
    (hk : ncast k * (4 * d) ≤ 1 / 2) : pw (1 + 4 * d) k - 1 ≤ 8 * (ncast k * d) := by
  have h1 := pw_one_add_le_exp h (show (0 : α) ≤ 4 * d by grind) k
  have hk0 := OrderedRing.mul_nonneg (ncast_nonneg (α := α) k) (show (0 : α) ≤ 4 * d by grind)
  have h2 := exp_le_one_add_two_mul h hk0 hk
  grind

end JointPoly
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Propositions G.22 and G.24 (bias and variance of `Tr P^k` at a fixed kernel scale):
    the algebra of the proofs; and the stability of a stochastic matrix in the supremum norm

  Not formalised: the probabilistic statements (moments, Bernstein's inequality, the diagram
  expansion of the expectations, the Hoeffding decomposition). -/

section BiasVariance
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- `1/(1+chi) = 1 - chi + chi^2 - y` with `y = chi^3/(1+chi)`, written without division. -/
theorem inv_one_add_expansion (c y : α) (hy : y * (1 + c) = c * c * c) :
    (1 + c) * (1 - c + c * c - y) = 1 := by grind

/-- Proposition G.22, Step 2: the expansion of `gamma_i = u_i / r_i` to second order with the
    explicit remainder `R_i`. Here `u_i = 1 - e + e^2 + th`, `1/r_i = 1 - chi + chi^2 - y` with
    `chi = e - b + s + z`, and the last term of the remainder is `th / (1 + chi)`. -/
theorem gamma_expansion (e b s z th y : α) :
    (1 - e + e * e + th) * (1 - (e - b + s + z) + (e - b + s + z) * (e - b + s + z) - y)
      = 1 + (-2 * e + b) + (3 * (e * e) - 3 * (e * b) + b * b - s)
        + (-z + (s + z) * (2 * e - 2 * b + s + z) - y
           + e * (s + z - (e - b + s + z) * (e - b + s + z) + y)
           + e * e * (-(e - b + s + z) + (e - b + s + z) * (e - b + s + z) - y)
           + th * (1 - (e - b + s + z) + (e - b + s + z) * (e - b + s + z) - y)) := by grind

/-- Negative control: with the coefficient `2` in place of `3` in the second-order term the
    identity fails (take `e = 1`, all other variables zero). -/
theorem gamma_expansion_control :
    ¬ ((1 - (1 : Int) + 1 * 1) * (1 - 1 + 1 * 1)
        = 1 + (-2 * 1) + 2 * (1 * 1) + (1 * (0 - 1 * 1) + 1 * 1 * (-1 + 1 * 1))) := by
  decide

/-- Proposition G.22, Step 6: `E Q_1 = k E(-2A + B)`. -/
theorem bias_linear_term (k mu rho m2 S1 S2 : α) :
    k * (-2 * (rho * mu + S1 - k * mu) + (rho * mu + m2 * mu + S2 - (k + 1) * mu))
      = k * (-(rho * mu) + m2 * mu - 2 * S1 + S2 + (k - 1) * mu) := by grind

/-- Proposition G.22, Step 6: the four parts of `E Q_2`. -/
theorem bias_second_order_term (k mu m2 m3 m4 : α) :
    k * mu * (3 * (m2 - 1) - 3 * (m3 - 1) + (m4 - 1) - (m2 - 1)) = k * mu * (2 * m2 - 3 * m3 + m4) := by
  grind

/-- Proposition G.22, Step 7: the sum of the four expectations is `beta_k`; the terms
    `k (k-1) mu_k` cancel. (Coefficients of `1/N`; `S_c` are the sums `Sigma_c`.) -/
theorem bias_sum (k mu rho m2 m3 m4 S0 S1 S2 S3 S4 : α) :
    (k * (1 / 2) * S0 - k * (k - 1) * (1 / 2) * mu)
      + k * (-(rho * mu) + m2 * mu - 2 * S1 + S2 + (k - 1) * mu)
      + k * mu * (2 * m2 - 3 * m3 + m4)
      + k * (1 / 2) * (4 * S2 - 4 * S3 + S4 - (k - 1) * mu)
      = k * (1 / 2 * S0 - 2 * S1 + 3 * S2 - 2 * S3 + 1 / 2 * S4) + k * mu * (m4 - 3 * m3 + 3 * m2 - rho) := by
  grind

/-- Proposition G.22: the difference between the graph with and without self-loops, `k ≥ 3`.
    With `rho = M` the sum `Sigma_0` contains the two terms `M m_{k-1}` (`l = 1` and `l = k-1`),
    with `rho = 0` it does not; `T` is the rest of `Sigma_0`. -/
theorem bias_loops (k mk mk1 M m2 m3 m4 T X : α) :
    (k * (1 / 2 * (T + 2 * (M * mk1)) + X) + k * mk * (m4 - 3 * m3 + 3 * m2 - M))
      - (k * (1 / 2 * T + X) + k * mk * (m4 - 3 * m3 + 3 * m2 - 0))
      = k * M * (mk1 - mk) := by grind

/-- Proposition G.24, Step 4: the pair kernels of `Q_0, …, Q_3` add up to `H_k`; the constants
    cancel. Pointwise in `y`: `G = Gamma_k(y)`, `c_j = (p_j * Gamma_k)(y)`, `p_j = p_j(y)`. -/
theorem variance_kernel_sum (k mu G c1 c2 c3 c4 p1 p2 p3 p4 : α) :
    (k * G - k * (k - 1) * mu)
      + 2 * k * (mu * (p2 - p1) + (c2 - 2 * c1) + (k - 1) * mu)
      + 2 * k * mu * (2 * p2 - 3 * p3 + p4)
      + (k * (4 * c2 - 4 * c3 + c4) - k * (k - 1) * mu)
      = k * (G - 4 * c1 + 6 * c2 - 4 * c3 + c4) - 2 * k * mu * (p1 - 3 * p2 + 3 * p3 - p4) := by grind

/-- With self-loops `beta_k = H_k(0) / 2`: the bias is the diagonal of the pair kernel. -/
theorem bias_is_diagonal (k mk S0 S1 S2 S3 S4 m1 m2 m3 m4 : α) :
    1 / 2 * (k * (S0 - 4 * S1 + 6 * S2 - 4 * S3 + S4) - 2 * k * mk * (m1 - 3 * m2 + 3 * m3 - m4))
      = k * (1 / 2 * S0 - 2 * S1 + 3 * S2 - 2 * S3 + 1 / 2 * S4) + k * mk * (m4 - 3 * m3 + 3 * m2 - m1) := by
  grind

end BiasVariance

section SupNorm
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {ι : Type}

theorem msum_sub : ∀ (I : List ι) (f g : ι → α), msum I (fun i => f i - g i) = msum I f - msum I g
  | [], _, _ => by simp [msum] <;> grind
  | _ :: I, f, g => by have ih := msum_sub I f g; simp [msum, ih] <;> grind

/-- The matrix `P` applied to a vector. -/
def mapp (I : List ι) (P : ι → ι → α) (v : ι → α) : ι → α := fun i => msum I (fun j => P i j * v j)

theorem mapp_sub (I : List ι) (P : ι → ι → α) (a b : ι → α) (i : ι) :
    mapp I P (fun j => a j - b j) i = mapp I P a i - mapp I P b i := by
  have h1 : msum I (fun j => P i j * (a j - b j)) = msum I (fun j => P i j * a j - P i j * b j) := by
    apply msum_congr; intro j _; grind
  have h2 := msum_sub I (fun j => P i j * a j) (fun j => P i j * b j)
  simp only [mapp]; rw [h1, h2]

/-- A row-stochastic matrix does not increase the maximum. -/
theorem Stoch.app_le {I : List ι} {P : ι → ι → α} (hP : Stoch I P) {v : ι → α} {c : α}
    (hv : ∀ j, v j ≤ c) (i : ι) : mapp I P v i ≤ c := by
  have h1 : msum I (fun j => P i j * v j) ≤ msum I (fun j => c * P i j) := by
    apply msum_le; intro j _
    have m := OrderedRing.mul_le_mul_of_nonneg_left (hv j) (hP.nonneg i j)
    grind
  have h2 := msum_mul_left c I (fun j => P i j)
  have h3 := hP.row i
  simp only [mapp]; grind

/-- A row-stochastic matrix does not decrease the minimum. -/
theorem Stoch.app_ge {I : List ι} {P : ι → ι → α} (hP : Stoch I P) {v : ι → α} {c : α}
    (hv : ∀ j, c ≤ v j) (i : ι) : c ≤ mapp I P v i := by
  have h1 : msum I (fun j => c * P i j) ≤ msum I (fun j => P i j * v j) := by
    apply msum_le; intro j _
    have m := OrderedRing.mul_le_mul_of_nonneg_left (hv j) (hP.nonneg i j)
    grind
  have h2 := msum_mul_left c I (fun j => P i j)
  have h3 := hP.row i
  simp only [mapp]; grind

/-- Sum of the first `n` terms of a sequence. -/
def nsum (eta : Nat → α) : Nat → α
  | 0 => 0
  | n + 1 => nsum eta n + eta n

/-- Stability and consistency give convergence, in the supremum norm (the deterministic core of
    the comparison of the sampled walk with the population walk). If `v_{n+1} = P v_n` for a
    row-stochastic `P`, and `w` satisfies the same recursion up to a defect `|w_{n+1} - P w_n| ≤ eta_n`,
    then `|v_n - w_n| ≤ e_0 + eta_0 + … + eta_{n-1}`, where `e_0` bounds the initial error. -/
theorem lax_stability {I : List ι} {P : ι → ι → α} (hP : Stoch I P) (v w : Nat → ι → α)
    (eta : Nat → α) (e0 : α)
    (hv : ∀ n i, v (n + 1) i = mapp I P (v n) i)
    (hw : ∀ n i, w (n + 1) i - mapp I P (w n) i ≤ eta n ∧ -(eta n) ≤ w (n + 1) i - mapp I P (w n) i)
    (h0 : ∀ i, v 0 i - w 0 i ≤ e0 ∧ -e0 ≤ v 0 i - w 0 i) :
    ∀ n i, v n i - w n i ≤ e0 + nsum eta n ∧ -(e0 + nsum eta n) ≤ v n i - w n i
  | 0, i => by
    have h := h0 i
    simp only [nsum]; grind
  | n + 1, i => by
    have ih : ∀ j, v n j - w n j ≤ e0 + nsum eta n ∧ -(e0 + nsum eta n) ≤ v n j - w n j :=
      fun j => lax_stability hP v w eta e0 hv hw h0 n j
    have u1 := Stoch.app_le hP (v := fun j => v n j - w n j) (fun j => (ih j).1) i
    have u2 := Stoch.app_ge hP (v := fun j => v n j - w n j) (fun j => (ih j).2) i
    have hs := mapp_sub I P (v n) (w n) i
    have h1 := hv n i
    have h2 := hw n i
    simp only [nsum]; grind

/-- A weighted sum is at most the largest weight times the sum of the absolute values:
    if `0 ≤ A_b ≤ c` and `|h_b| ≤ t_b`, then `|sum_b A_b h_b| ≤ c sum_b t_b`. This is the step
    that uses a bound on the kernel of `P^l` and a bound on the defect in the mean. -/
theorem weighted_sum_bound (I : List ι) (A h t : ι → α) (c : α)
    (hA : ∀ b, 0 ≤ A b ∧ A b ≤ c) (ht : ∀ b, h b ≤ t b ∧ -(t b) ≤ h b) :
    msum I (fun b => A b * h b) ≤ c * msum I t ∧ -(c * msum I t) ≤ msum I (fun b => A b * h b) := by
  have key : ∀ b, A b * h b ≤ c * t b ∧ -(c * t b) ≤ A b * h b := by
    intro b
    have a1 := OrderedRing.mul_le_mul_of_nonneg_left (ht b).1 (hA b).1
    have a2 := OrderedRing.mul_le_mul_of_nonneg_left (ht b).2 (hA b).1
    have a3 := OrderedRing.mul_nonneg (show (0 : α) ≤ c - A b by have := hA b; grind)
      (show (0 : α) ≤ t b by have := ht b; grind)
    constructor <;> grind
  have u := msum_le I (fun b => A b * h b) (fun b => c * t b) (fun b _ => (key b).1)
  have l := msum_le I (fun b => -(c * t b)) (fun b => A b * h b) (fun b _ => (key b).2)
  have e1 := msum_mul_left c I t
  have e2 : msum I (fun b => -(c * t b)) = -(c * msum I t) := by
    have e3 := msum_mul_left (-c) I t
    have e4 : msum I (fun b => -(c * t b)) = msum I (fun b => -c * t b) := by
      apply msum_congr; intro b _; grind
    rw [e4, e3]; grind
  constructor <;> grind

theorem mapp_add (I : List ι) (P : ι → ι → α) (a b : ι → α) (i : ι) :
    mapp I P (fun j => a j + b j) i = mapp I P a i + mapp I P b i := by
  have h1 : msum I (fun j => P i j * (a j + b j)) = msum I (fun j => P i j * a j + P i j * b j) := by
    apply msum_congr; intro j _; grind
  have h2 := msum_add I (fun j => P i j * a j) (fun j => P i j * b j)
  simp only [mapp]; rw [h1, h2]

/-- `P^n` applied to a vector, as an iteration. -/
def miter (I : List ι) (P : ι → ι → α) (v : ι → α) : Nat → ι → α
  | 0 => v
  | n + 1 => mapp I P (miter I P v n)

/-- The telescoping sum of Theorem G.28, Step 1, in recursive form: for a sequence of vectors `w_n`
    (in the application `w_n = R P_pop^n g`, the population walk restricted to the points) let
    `tel_0 = 0` and `tel_{k+1} = (P w_k - w_{k+1}) + P tel_k`. Unrolled, `tel_k` is
    `sum_{l < k} P^l (P w_{k-1-l} - w_{k-l})`. -/
def tel (I : List ι) (P : ι → ι → α) (w : Nat → ι → α) : Nat → ι → α
  | 0 => fun _ => 0
  | k + 1 => fun i => (mapp I P (w k) i - w (k + 1) i) + mapp I P (tel I P w k) i

/-- Theorem G.28, Step 1: `P^k w_0 - w_k` equals the telescoping sum of the one-step defects.
    No property of `P` is used. -/
theorem telescope (I : List ι) (P : ι → ι → α) (w : Nat → ι → α) :
    ∀ k i, miter I P (w 0) k i - w k i = tel I P w k i
  | 0, i => by simp only [miter, tel]; grind
  | k + 1, i => by
    have ih : ∀ j, miter I P (w 0) k j - w k j = tel I P w k j := fun j => telescope I P w k j
    have h1 : mapp I P (tel I P w k) i = mapp I P (fun j => miter I P (w 0) k j - w k j) i := by
      simp only [mapp]; apply msum_congr; intro j _; rw [ih j]
    have h2 := mapp_sub I P (miter I P (w 0) k) (w k) i
    simp only [miter, tel]; grind

/-- Theorem G.28, Step 2 and the end of Step 4: from `D ≤ 4 delta mu + (1 + 4 delta) S`,
    `delta ≤ 6 delta'`, `6 delta' ≤ 1/8` and `S ≤ c mu` one gets `D ≤ (24 delta' + (3/2) c) mu`. -/
theorem kernel_step {D S mu d d' c : α} (hmu : 0 ≤ mu) (hc : 0 ≤ c) (hd0 : 0 ≤ d) (hd : d ≤ 6 * d')
    (hd' : 6 * d' ≤ 1 / 8) (hS : S ≤ c * mu) (hD : D ≤ 4 * d * mu + (1 + 4 * d) * S) :
    D ≤ (24 * d' + 3 / 2 * c) * mu := by
  have a1 := OrderedRing.mul_le_mul_of_nonneg_left hS (show (0 : α) ≤ 1 + 4 * d by grind)
  have a2 := OrderedRing.mul_nonneg hc hmu
  have a3 := OrderedRing.mul_nonneg (show (0 : α) ≤ 1 / 2 - 4 * d by grind) a2
  have a4 := OrderedRing.mul_nonneg (show (0 : α) ≤ 6 * d' - d by grind) hmu
  grind

/-- Theorem G.28, Step 4, the logic of the induction: if `D_1 ≤ mu_1` and the bound for `k + 1`
    follows from the bounds for all `1 ≤ l ≤ k` (as long as `k < K`), then `D_l ≤ mu_l` for all
    `1 ≤ l ≤ K`. The constants do not accumulate, because the hypothesis is used only in the
    form `D_l ≤ mu_l`. -/
theorem bootstrap (D mu : Nat → α) (K : Nat) (h1 : D 1 ≤ mu 1)
    (step : ∀ k, 1 ≤ k → k < K → (∀ l, 1 ≤ l → l ≤ k → D l ≤ mu l) → D (k + 1) ≤ mu (k + 1)) :
    ∀ k, k ≤ K → ∀ l, 1 ≤ l → l ≤ k → D l ≤ mu l
  | 0, _, l, hl1, hl => by omega
  | k + 1, hk, l, hl1, hl => by
    have ih : ∀ l, 1 ≤ l → l ≤ k → D l ≤ mu l := bootstrap D mu K h1 step k (by omega)
    by_cases hlk : l ≤ k
    · exact ih l hl1 hlk
    · have e : l = k + 1 := by omega
      subst e
      by_cases hk0 : k = 0
      · subst hk0; exact h1
      · exact step k (by omega) (by omega) ih

end SupNorm
end CTG.HeatTrace

namespace CTG.TwoMode
open Lean.Grind

/-! ## Proposition 4.2 (mutual information of two modes): the symplectic spectrum, algebra only

  The covariance matrix of the pair in the order `(phi_A, phi_B, pi_A, pi_B)` is block diagonal
  with `X = [[x0, x], [x, x0]]` and `P = [[p0, p], [p, p0]]`. Checked here: the eigenvalues of
  `X P`, and the explicit symplectic matrix `S = diag(A, B)` with `A = D R`, `B = D⁻¹ R`
  (`R` the rotation by 45 degrees, `D = diag(s₊, s₋)`) that brings the covariance matrix to
  `diag(nu₊, nu₋, nu₊, nu₋)`.

  HYPOTHESES (no square roots exist in an arbitrary ordered field): a number `r` with
  `2 r² = 1`, and numbers `a₊ = s₊²`, `a₋ = s₋²` with `a±² (x0 ± x) = p0 ± p`.
  NOT CHECKED: that the entropy of a Gaussian state is the sum of `f` over its symplectic
  eigenvalues, and everything else about quantum states. -/

section Symplectic
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- `X P = [[A, B], [B, A]]` with `A = x0 p0 + x p`, `B = x0 p + x p0`; `(1, 1)` and `(1, -1)`
    are eigenvectors with the eigenvalues `(x0 + x)(p0 + p)` and `(x0 - x)(p0 - p)`. -/
theorem xp_eigenvalues (x0 x p0 p : α) :
    (x0 * p0 + x * p) + (x0 * p + x * p0) = (x0 + x) * (p0 + p)
      ∧ (x0 * p0 + x * p) - (x0 * p + x * p0) = (x0 - x) * (p0 - p) := by
  constructor <;> grind

/-- The characteristic polynomial of `X P`. -/
theorem xp_charpoly (x0 x p0 p lam : α) :
    (x0 * p0 + x * p - lam) * (x0 * p0 + x * p - lam) - (x0 * p + x * p0) * (x0 * p + x * p0)
      = ((x0 + x) * (p0 + p) - lam) * ((x0 - x) * (p0 - p) - lam) := by grind

/-- Negative control: `(x0 + x)(p0 - p)` is not an eigenvalue in general
    (`x0 = 2, x = 1, p0 = 2, p = 1`). -/
theorem xp_charpoly_control :
    ¬ ((2 * 2 + 1 * 1 - (2 + 1) * (2 - 1)) * (2 * 2 + 1 * 1 - (2 + 1) * (2 - 1))
        - (2 * 1 + 1 * 2) * (2 * 1 + 1 * 2) = (0 : Int)) := by decide

/-- The rotation `R = r [[1, 1], [1, -1]]` with `2 r² = 1` is orthogonal and diagonalises
    `X = [[x0, x], [x, x0]]`: `R X Rᵀ = diag(x0 + x, x0 - x)`. Entries `(1,1)`, `(1,2)`, `(2,2)`. -/
theorem rotation_diagonalises (r x0 x : α) (hr : 2 * (r * r) = 1) :
    r * (r * x0 + r * x) + r * (r * x + r * x0) = x0 + x
      ∧ r * (r * x0 + r * x) - r * (r * x + r * x0) = 0
      ∧ r * (r * x0 - r * x) - r * (r * x - r * x0) = x0 - x
      ∧ r * r + r * r = 1 ∧ r * r - r * r = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> grind

/-- Squeezing: if `a² X = P` (so that `a = sqrt(P / X)`), then `nu := a X` satisfies
    `nu² = X P` and `a nu = P`, that is `P / a = nu`: the rescaled variances of position and of
    momentum are both equal to the symplectic eigenvalue. -/
theorem squeeze (a X P : α) (h : a * a * X = P) :
    (a * X) * (a * X) = X * P ∧ a * (a * X) = P := by
  constructor <;> grind

/-- `S = diag(A, B)` with `A = D R`, `B = D⁻¹ R` is symplectic: `A Bᵀ = 1`. Here `t₊ = 1/s₊`,
    `t₋ = 1/s₋`. Entries `(1,1)`, `(1,2)`, `(2,1)`, `(2,2)` of `A Bᵀ`. -/
theorem symplectic_block (r sp sm tp tm : α) (hr : 2 * (r * r) = 1) (hp : sp * tp = 1)
    (hm : sm * tm = 1) :
    (sp * r) * (tp * r) + (sp * r) * (tp * r) = 1
      ∧ (sp * r) * (tm * r) - (sp * r) * (tm * r) = 0
      ∧ (sm * r) * (tp * r) - (sm * r) * (tp * r) = 0
      ∧ (sm * r) * (tm * r) + (sm * r) * (tm * r) = 1 := by
  have e1 : (sp * r) * (tp * r) = (sp * tp) * (r * r) := by grind
  have e2 : (sm * r) * (tm * r) = (sm * tm) * (r * r) := by grind
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- The diagonal form: with `A = D R` and `B = D⁻¹ R`, the `(1,1)` entries of `A X Aᵀ` and of
    `B P Bᵀ` are `s₊² (x0 + x)` and `(p0 + p) / s₊²`; if `s₊⁴ (x0 + x) = p0 + p` both equal
    `nu₊` with `nu₊² = (x0 + x)(p0 + p)`. (The entries `(2,2)` are the same with `x → -x`,
    `p → -p`, and the off-diagonal entries vanish by `rotation_diagonalises`.) -/
theorem symplectic_diagonal (r sp tp x0 x p0 p : α) (hr : 2 * (r * r) = 1) (hp : sp * tp = 1)
    (hs : (sp * sp) * (sp * sp) * (x0 + x) = p0 + p) :
    (sp * r) * ((sp * r) * x0 + (sp * r) * x) + (sp * r) * ((sp * r) * x + (sp * r) * x0)
        = (sp * sp) * (x0 + x)
      ∧ (tp * r) * ((tp * r) * p0 + (tp * r) * p) + (tp * r) * ((tp * r) * p + (tp * r) * p0)
        = (sp * sp) * (x0 + x)
      ∧ ((sp * sp) * (x0 + x)) * ((sp * sp) * (x0 + x)) = (x0 + x) * (p0 + p) := by
  have e1 : (sp * r) * ((sp * r) * x0 + (sp * r) * x) + (sp * r) * ((sp * r) * x + (sp * r) * x0)
      = (sp * sp) * (2 * (r * r)) * (x0 + x) := by grind
  have e2 : (tp * r) * ((tp * r) * p0 + (tp * r) * p) + (tp * r) * ((tp * r) * p + (tp * r) * p0)
      = (tp * tp) * (2 * (r * r)) * (p0 + p) := by grind
  have e3 : (tp * tp) * ((sp * sp) * (sp * sp)) = (sp * tp) * (sp * tp) * (sp * sp) := by grind
  have e4 : (tp * tp) * (p0 + p) = (sp * sp) * (x0 + x) := by
    rw [← hs]
    have : (tp * tp) * ((sp * sp) * (sp * sp) * (x0 + x))
        = (tp * tp) * ((sp * sp) * (sp * sp)) * (x0 + x) := by grind
    rw [this, e3, hp]; grind
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, hr]; grind
  · rw [e2, hr]; grind
  · have h2 := (squeeze (sp * sp) (x0 + x) (p0 + p) hs).1
    exact h2

end Symplectic
end CTG.TwoMode

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Theorem G.38 (eigenvalues of the sampled graph on a flat torus): from powers to eigenvalues -/

section PowersToEigenvalues
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- For `0 ≤ y ≤ x`: `x^{k+1} - y^{k+1} ≥ (k+1) y^k (x - y)`. This is the inequality
    `|x^k - y^k| ≥ k min(x,y)^{k-1} |x - y|` used to pass from `s_j^k` to `s_j`. -/
theorem pw_diff_ge {x y : α} (hy : 0 ≤ y) (hxy : y ≤ x) :
    ∀ k : Nat, ncast (k + 1) * (pw y k * (x - y)) ≤ pw x (k + 1) - pw y (k + 1)
  | 0 => by simp only [pw, ncast]; grind
  | k + 1 => by
    have ih : ncast (k + 1) * (pw y k * (x - y)) ≤ pw x (k + 1) - pw y (k + 1) := pw_diff_ge hy hxy k
    have hXY := pw_mono hy hxy (k + 1)
    have m1 := OrderedRing.mul_nonneg (show (0 : α) ≤ x - y by grind)
      (show (0 : α) ≤ pw x (k + 1) - pw y (k + 1) by grind)
    have m2 := OrderedRing.mul_le_mul_of_nonneg_left ih hy
    have e1 : pw x (k + 1 + 1) = x * pw x (k + 1) := rfl
    have e2 : pw y (k + 1 + 1) = y * pw y (k + 1) := rfl
    have e3 : pw y (k + 1) = y * pw y k := rfl
    have e4 : (ncast (k + 1 + 1) : α) = ncast (k + 1) + 1 := rfl
    have e5 : ncast (k + 1) * (pw y (k + 1) * (x - y)) = y * (ncast (k + 1) * (pw y k * (x - y))) := by
      rw [e3]; grind
    have e6 : (ncast (k + 1) + 1) * (pw y (k + 1) * (x - y))
        = ncast (k + 1) * (pw y (k + 1) * (x - y)) + pw y (k + 1) * (x - y) := by grind
    have e7 : x * pw x (k + 1) - y * pw y (k + 1)
        = y * (pw x (k + 1) - pw y (k + 1)) + (x - y) * (pw x (k + 1) - pw y (k + 1))
          + pw y (k + 1) * (x - y) := by grind
    rw [e1, e2, e4, e6, e7, e5]
    grind

/-- Consequently, if `|x^{k+1} - y^{k+1}| ≤ eta` and both `x^k, y^k ≥ c > 0`, then
    `(k+1) c |x - y| ≤ eta`; stated for `y ≤ x`. -/
theorem root_of_power_bound {x y c eta : α} (hy : 0 ≤ y) (hxy : y ≤ x) (k : Nat)
    (hc : c ≤ pw y k) (hc0 : 0 ≤ c) (h : pw x (k + 1) - pw y (k + 1) ≤ eta) :
    ncast (k + 1) * (c * (x - y)) ≤ eta := by
  have h1 := pw_diff_ge hy hxy k
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left hc (show (0 : α) ≤ x - y by grind)
  have h3 := OrderedRing.mul_le_mul_of_nonneg_left
    (show c * (x - y) ≤ pw y k * (x - y) by grind) (ncast_nonneg (α := α) (k + 1))
  grind

end PowersToEigenvalues
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Corollaries G.39 and G.40 (eigenspaces, delocalisation): the deterministic steps -/

section EigenSteps
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {ι : Type} {exp : α → α}

/-- `sum_i (s A_i - t u_i)^2 ≥ 0`, written out: `s^2 sum A^2 - 2 s t sum A u + t^2 sum u^2 ≥ 0`. -/
theorem msum_quadform (s t : α) : ∀ (I : List ι) (A u : ι → α),
    0 ≤ s * s * msum I (fun i => A i * A i) - 2 * (s * t) * msum I (fun i => A i * u i)
        + t * t * msum I (fun i => u i * u i)
  | [], _, _ => by simp [msum] <;> grind
  | i :: I, A, u => by
    have ih := msum_quadform s t I A u
    have sq := mul_self_nonneg (s * A i - t * u i)
    simp only [msum]; grind

/-- The Cauchy--Schwarz inequality for finite sums. -/
theorem msum_cauchy_schwarz : ∀ (I : List ι) (A u : ι → α),
    msum I (fun i => A i * u i) * msum I (fun i => A i * u i)
      ≤ msum I (fun i => A i * A i) * msum I (fun i => u i * u i)
  | [], _, _ => by simp [msum] <;> grind
  | i :: I, A, u => by
    have ih := msum_cauchy_schwarz I A u
    have q := msum_quadform (u i) (A i) I A u
    simp only [msum]; grind

/-- Corollary G.40, the step `|u_a| ≤ c (sum_i B_i^2)^{1/2}` in squared form: if
    `u_a = c sum_i B_i u_i` and `sum_i u_i^2 ≤ 1`, then `u_a^2 ≤ c^2 sum_i B_i^2`. -/
theorem delocalisation_step (I : List ι) (B u : ι → α) (c ua : α)
    (h : ua = c * msum I (fun i => B i * u i)) (hu : msum I (fun i => u i * u i) ≤ 1) :
    ua * ua ≤ c * c * msum I (fun i => B i * B i) := by
  have cs := msum_cauchy_schwarz I B u
  have hB : 0 ≤ msum I (fun i => B i * B i) := msum_nonneg I _ (fun i _ => mul_self_nonneg (B i))
  have h1 := OrderedRing.mul_le_mul_of_nonneg_left hu hB
  have h2 := OrderedRing.mul_le_mul_of_nonneg_left
    (show msum I (fun i => B i * u i) * msum I (fun i => B i * u i) ≤ msum I (fun i => B i * B i) by grind)
    (mul_self_nonneg c)
  rw [h]; grind

/-- Corollary G.39, the spectral step: if `w` has the coefficients `c_i` in an eigenbasis with
    eigenvalues `mu_i`, and `f_i` is `c_i^2` on the eigenvalues at a distance at least `rho` from
    `a` and zero on the others, then `rho^2 sum f_i ≤ sum (mu_i - a)^2 c_i^2 = |(B - a) w|^2`. -/
theorem spectral_step (I : List ι) (mu c f : ι → α) (a rho : α)
    (hf : ∀ i, f i = 0 ∨ (f i = c i * c i ∧ rho * rho ≤ (mu i - a) * (mu i - a))) :
    rho * rho * msum I f ≤ msum I (fun i => (mu i - a) * (mu i - a) * (c i * c i)) := by
  have key : ∀ i ∈ I, rho * rho * f i ≤ (mu i - a) * (mu i - a) * (c i * c i) := by
    intro i _
    have n1 := OrderedRing.mul_nonneg (mul_self_nonneg (mu i - a)) (mul_self_nonneg (c i))
    cases hf i with
    | inl h0 => rw [h0]; grind
    | inr h1 =>
      have m := OrderedRing.mul_le_mul_of_nonneg_left h1.2 (mul_self_nonneg (c i))
      rw [h1.1]; grind
  have s := msum_le I (fun i => rho * rho * f i) _ key
  have e := msum_mul_left (rho * rho) I f
  grind

/-- Corollary G.39, the separation of the powers: for `u ≤ v`,
    `e^{-u} - e^{-v} ≥ e^{-v} (v - u)`. -/
theorem exp_gap (h : IsExp exp) {u v : α} (huv : u ≤ v) :
    exp (-v) * (v - u) ≤ exp (-u) - exp (-v) := by
  have hadd := h.add (-v) (v - u)
  rw [show -v + (v - u) = -u by grind] at hadd
  have m := OrderedRing.mul_le_mul_of_nonneg_left (h.ge (v - u)) (h.nonneg (-v))
  grind

end EigenSteps
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Theorems G.28 and G.38, Corollary G.40: the deterministic deductions as a whole

  Each statement below is the complete deterministic part of the proof in the paper. What is
  not formalised enters as a HYPOTHESIS: the consistency lemma G.27 and the kernel-matrix lemma
  G.37 (probability), Weyl's inequality for symmetric matrices, and the spectral theorem. -/

section MainDeductions
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]
variable {ι : Type}

theorem pw_succ_le {s : α} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (k : Nat) : pw s (k + 1) ≤ pw s k := by
  have m := OrderedRing.mul_nonneg (show (0 : α) ≤ 1 - s by grind) (pw_nonneg hs0 k)
  have e : pw s (k + 1) = s * pw s k := rfl
  rw [e]; grind

/-- Theorem G.28, Step 4 as a whole (the induction of the kernel estimate).
    HYPOTHESES: `hrec` is Step 2 (the last step of the walk), `hS` is Steps 3 and 4 for one `k`
    given the consistency lemma, with `W k` standing for `2^{d+3} C delta' sqrt k`.
    CONCLUSION: `D_k ≤ mu_k` for `1 ≤ k ≤ K`, and the bound with the explicit constant. -/
theorem kernel_induction (D mu S W : Nat → α) (d d' : α) (K : Nat)
    (hmu : ∀ k, 0 ≤ mu k) (hd0 : 0 ≤ d) (hd : d ≤ 6 * d') (hd' : 6 * d' ≤ 1 / 8)
    (hD1 : D 1 ≤ mu 1)
    (hrec : ∀ k, 1 ≤ k → D (k + 1) ≤ 4 * d * mu (k + 1) + (1 + 4 * d) * S k)
    (hS : ∀ k, 1 ≤ k → k < K → (∀ l, 1 ≤ l → l ≤ k → D l ≤ mu l) → S k ≤ W k * mu (k + 1))
    (hW : ∀ k, 1 ≤ k → k < K → 0 ≤ W k ∧ 24 * d' + 3 / 2 * W k ≤ 1) :
    (∀ k, k ≤ K → ∀ l, 1 ≤ l → l ≤ k → D l ≤ mu l)
      ∧ (∀ k, 1 ≤ k → k < K → D (k + 1) ≤ (24 * d' + 3 / 2 * W k) * mu (k + 1)) := by
  have step : ∀ k, 1 ≤ k → k < K → (∀ l, 1 ≤ l → l ≤ k → D l ≤ mu l) →
      D (k + 1) ≤ (24 * d' + 3 / 2 * W k) * mu (k + 1) := by
    intro k hk1 hkK ih
    exact kernel_step (hmu (k + 1)) (hW k hk1 hkK).1 hd0 hd hd' (hS k hk1 hkK ih) (hrec k hk1)
  have all : ∀ k, k ≤ K → ∀ l, 1 ≤ l → l ≤ k → D l ≤ mu l := by
    apply bootstrap D mu K hD1
    intro k hk1 hkK ih
    have b := step k hk1 hkK ih
    have w := (hW k hk1 hkK).2
    have m := OrderedRing.mul_nonneg (show (0 : α) ≤ 1 - (24 * d' + 3 / 2 * W k) by grind) (hmu (k + 1))
    grind
  refine ⟨all, ?_⟩
  intro k hk1 hkK
  exact step k hk1 hkK (all k (by omega))

/-- Theorem G.38, from (i) to (ii): if `|s^{k+1} - a^{k+1}| ≤ eta` and `a^{k+1} ≥ 2 eta` for
    `s, a ∈ [0, 1]`, then `(k+1) a^{k+1} |s - a| ≤ 2 eta`. With `sigma lambda^N = 1 - s` and
    `sigma lambda^pop = 1 - a` this is `|lambda^N - lambda^pop| ≤ 2 eta / ((k+1) sigma a^{k+1})`. -/
theorem eigenvalue_from_power {s a eta : α} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (k : Nat) (h1 : pw s (k + 1) - pw a (k + 1) ≤ eta) (h2 : pw a (k + 1) - pw s (k + 1) ≤ eta)
    (h3 : 2 * eta ≤ pw a (k + 1)) :
    ncast (k + 1) * (pw a (k + 1) * (s - a)) ≤ 2 * eta
      ∧ ncast (k + 1) * (pw a (k + 1) * (a - s)) ≤ 2 * eta := by
  have hn := ncast_nonneg (α := α) (k + 1)
  have hA := pw_nonneg ha0 (k + 1)
  have hna := OrderedRing.mul_nonneg hn hA
  by_cases hc : a ≤ s
  · have r := root_of_power_bound ha0 hc k (pw_succ_le ha0 ha1 k) hA h1
    have p := OrderedRing.mul_nonneg hna (show (0 : α) ≤ s - a by grind)
    constructor <;> grind
  · have hsa : s ≤ a := by grind
    have c1 := pw_succ_le hs0 hs1 k
    have r := root_of_power_bound (c := 1 / 2 * pw a (k + 1)) hs0 hsa k (by grind) (by grind) h2
    have p := OrderedRing.mul_nonneg hna (show (0 : α) ≤ a - s by grind)
    constructor <;> grind

/-- Theorem G.38 (ii) in the variables of the paper. HYPOTHESIS `hpow`: part (i) of the theorem
    for one `k` (which rests on Theorem G.28, Lemma G.37 and Weyl's inequality). -/
theorem eigtorus_ii {s a eta sigma lamN lamPop : α} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (k : Nat) (hsig : 0 ≤ sigma) (hN : sigma * lamN = 1 - s)
    (hP : sigma * lamPop = 1 - a)
    (hpow : pw s (k + 1) - pw a (k + 1) ≤ eta ∧ pw a (k + 1) - pw s (k + 1) ≤ eta)
    (h3 : 2 * eta ≤ pw a (k + 1)) :
    ncast (k + 1) * (pw a (k + 1) * (sigma * (lamPop - lamN))) ≤ 2 * eta
      ∧ ncast (k + 1) * (pw a (k + 1) * (sigma * (lamN - lamPop))) ≤ 2 * eta := by
  have r := eigenvalue_from_power hs0 hs1 ha0 ha1 k hpow.1 hpow.2 h3
  have e1 : sigma * (lamPop - lamN) = s - a := by grind
  have e2 : sigma * (lamN - lamPop) = a - s := by grind
  rw [e1, e2]; exact r

/-- Corollary G.40 as a whole. HYPOTHESES: `B` is the symmetric matrix `S^k`, `u` an eigenvector
    with eigenvalue `t ≥ t0 > 0` and `sum u_i^2 ≤ 1`, and `kappa` bounds the diagonal entry
    `(S^{2k})_{aa} = sum_i B_{ai} B_{ia}` (from Theorem G.28).
    CONCLUSION: `t0^2 u_a^2 ≤ kappa`. -/
theorem delocalisation (I : List ι) (B : ι → ι → α) (u : ι → α) (t t0 kappa : α) (a : ι)
    (hsym : ∀ i j, B i j = B j i) (heig : msum I (fun i => B a i * u i) = t * u a)
    (ht : t0 ≤ t) (ht0 : 0 ≤ t0) (hu : msum I (fun i => u i * u i) ≤ 1)
    (hdiag : msum I (fun i => B a i * B i a) ≤ kappa) :
    t0 * t0 * (u a * u a) ≤ kappa := by
  have e : msum I (fun i => B a i * B i a) = msum I (fun i => B a i * B a i) := by
    apply msum_congr; intro i _; rw [hsym i a]
  have d1 := delocalisation_step I (B a) u 1 (t * u a) (by rw [heig]; grind) hu
  have sq := mul_self_nonneg (u a)
  have m1 := OrderedRing.mul_nonneg (show (0 : α) ≤ t - t0 by grind) (show (0 : α) ≤ t + t0 by grind)
  have m2 := OrderedRing.mul_nonneg m1 sq
  rw [e] at hdiag
  grind

end MainDeductions
end CTG.HeatTrace

namespace CTG.HeatTrace
open Lean.Grind

/-! ### Reduction of the trace to a polynomial statistic (draft, second stage): the algebra of Step 2 -/

section Reduction
variable {α : Type} [Field α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearOrder α] [OrderedRing α]

/-- The linearisation of `theta_{bi} = u_i / r_b - 1` in the normalisation errors. Here
    `u_i = 1 - e + th` (with `th = e^2/(1+e)`), `r_b = 1 + rho` with
    `rho = eb - pe + pth` (`eb = eps_b`, `pe = (P eps)_b`, `pth = (P theta)_b`), and
    `1/(1 + rho) = 1 - rho + y` with `y = rho^2/(1 + rho)`. The first bracket is `theta^1_{bi}`. -/
theorem theta_linearisation (e eb pe pth th rho y : α) (hrho : rho = eb - pe + pth) :
    (1 - e + th) * (1 - rho + y) - 1
      = (-e - eb + pe) + (-pth + e * rho + th * (1 - rho) + (1 - e + th) * y) := by
  rw [hrho]; grind

/-- The bound `|theta - theta^1| ≤ 14 delta^2`, given the bounds for the four terms of the
    remainder that are derived in the text from `delta ≤ 1/8`. -/
theorem theta_linearisation_bound {t1 t2 t3 t4 d2 : α} (hd : 0 ≤ d2)
    (h1 : t1 ≤ 9 / 7 * d2 ∧ -(9 / 7 * d2) ≤ t1) (h2 : t2 ≤ 16 / 7 * d2 ∧ -(16 / 7 * d2) ≤ t2)
    (h3 : t3 ≤ 3 / 2 * d2 ∧ -(3 / 2 * d2) ≤ t3) (h4 : t4 ≤ 17 / 2 * d2 ∧ -(17 / 2 * d2) ≤ t4) :
    -t1 + t2 + t3 + t4 ≤ 14 * d2 ∧ -(14 * d2) ≤ -t1 + t2 + t3 + t4 := by
  constructor <;> grind

/-- The defect and its linearisation: from `r h = hhat + E` one gets `h - hhat = (1 - r) h + E`. -/
theorem defect_linearisation (r h hhat E : α) (hr : r * h = hhat + E) :
    h - hhat = (1 - r) * h + E := by grind

/-- Negative control for `theta_linearisation`: without the term `e * rho` the identity fails
    (`e = 1`, `eb = 1`, all other variables zero, so that `rho = 1`). -/
theorem theta_linearisation_control :
    ¬ ((1 - (1 : Int) + 0) * (1 - 1 + 0) - 1 = (-1 - 1 + 0) + (-0 + 0 * (1 - 1) + (1 - 1 + 0) * 0)) := by
  decide

end Reduction
end CTG.HeatTrace
