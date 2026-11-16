import Mathlib

/-!
# Field contents and the induced action (Section 9.6 of the paper)

Paper: M. Neuberger, *From Correlations to Geometry* (November 2026).

This file formalises the **arithmetic** of Section 9.6: Proposition 9.18 and
Corollaries 9.14, 9.17 and 9.19, together with the step from the cutoff integrals to the
table of Proposition 9.15.

What is taken as input (not proven here): the entries of Table 2 and of the table in
Proposition 9.15, i.e. the contribution of each kind of field to the coefficients
`a`, `ℓ`, `b_R` of the induced action. They are the definitions below. Everything stated
as a theorem follows from these definitions by exact real arithmetic.
-/

namespace CorrelationsGeometry

/-! ## Leading order: Table 2 -/

/-- A field content: `Ns` scalar fields whose curvature couplings sum to `X = Σ ζᵢ`,
`Nd` Dirac fields, `Nv` Maxwell fields and `Nw` massive vector fields. -/
structure Content where
  /-- number of scalar fields -/
  Ns : ℝ
  /-- sum of the curvature couplings `ζ` of the scalar fields -/
  X : ℝ
  /-- number of Dirac fields -/
  Nd : ℝ
  /-- number of Maxwell fields -/
  Nv : ℝ
  /-- number of massive vector fields -/
  Nw : ℝ

namespace Content

variable (c : Content)

/-- Table 2, column `a` (kinetic coefficient), in units of `Λ²/960π²`. -/
def a : ℝ := 2 * c.Ns - 60 * c.X + 12 * c.Nd + 24 * c.Nv + 26 * c.Nw

/-- Table 2, column `ℓ` (longitudinal coefficient), in units of `Λ²/960π²`. -/
def l : ℝ := 8 * c.Ns - 80 * c.X + 8 * c.Nd + 16 * c.Nv + 24 * c.Nw

/-- Table 2, column `b_R` (curvature coefficient, fixed number of modes), same units. -/
def bR : ℝ := 10 * c.Ns - 60 * c.X + 20 * c.Nd - 40 * c.Nv - 30 * c.Nw

/-- Table 2, last column: `Str 1`, the signed number of degrees of freedom. -/
def str1 : ℝ := c.Ns - 4 * c.Nd + 2 * c.Nv + 3 * c.Nw

/-- **Proposition 9.18 (i).** `Σa = ¾ Σℓ − ¼ Σ(b_R − a) − 2 Str 1` for every content. -/
theorem relation_i : c.a = 3 / 4 * c.l - 1 / 4 * (c.bR - c.a) - 2 * c.str1 := by
  simp only [a, l, bR, str1]; ring

/-- **Corollary 9.14, first identity of (9.25)** (no massive vector fields). -/
theorem sum_l (h : c.Nw = 0) : c.l = 8 * (c.Ns + c.Nd + 2 * c.Nv - 10 * c.X) := by
  simp only [l, h]; ring

/-- **Corollary 9.14, second identity of (9.25)** (no massive vector fields). -/
theorem sum_bR_sub_a (h : c.Nw = 0) : c.bR - c.a = 8 * (c.Ns + c.Nd - 8 * c.Nv) := by
  simp only [a, bR, h]; ring

/-- **Corollary 9.14.** Without massive vector fields, `λ = 1` and `c_T = 1` at leading order
(that is, `Σℓ = 0` and `Σb_R = Σa`) hold if and only if `Ns + Nd = 8 Nv` and `X = Nv`. -/
theorem covariant_iff (h : c.Nw = 0) :
    (c.l = 0 ∧ c.bR = c.a) ↔ (c.Ns + c.Nd = 8 * c.Nv ∧ c.X = c.Nv) := by
  simp only [a, l, bR, h]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **Corollary 9.14.** Under those two conditions `Σa = 10 (6 Nv − Ns)`. -/
theorem a_of_covariant (h : c.Nw = 0) (hl : c.l = 0) (hb : c.bR = c.a) :
    c.a = 10 * (6 * c.Nv - c.Ns) := by
  simp only [a, l, bR, h] at *
  linarith

/-- **Corollary 9.14, last statement.** If in addition the leading vacuum energy cancels
(`Str 1 = 0`, i.e. `Ns + 2 Nv = 4 Nd`), then `Ns = 6 Nv`, `Nd = 2 Nv` and
`Σa = Σℓ = Σb_R = 0`: there is no induced action at order `Λ²`. -/
theorem no_induced_action (h : c.Nw = 0) (hl : c.l = 0) (hb : c.bR = c.a) (hs : c.str1 = 0) :
    c.Ns = 6 * c.Nv ∧ c.Nd = 2 * c.Nv ∧ c.a = 0 ∧ c.l = 0 ∧ c.bR = 0 := by
  simp only [a, l, bR, str1, h] at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Corollary 9.19 at order `Λ²`**, for every content including massive vector fields:
covariance (`Σℓ = 0`, `Σb_R = Σa`) and vanishing `Str 1` force `Σa = 0`. -/
theorem a_eq_zero_of_covariant_of_str1 (hl : c.l = 0) (hb : c.bR = c.a) (hs : c.str1 = 0) :
    c.a = 0 := by
  have := c.relation_i
  rw [hl, hb, hs] at this
  linarith

/-- The example after Corollary 9.14: one scalar field with `ζ = 1`, seven Dirac fields and one
Maxwell field give `Σℓ = 0`, `Σb_R = Σa` and `Σa = 50 > 0`. -/
example :
    (⟨1, 1, 7, 1, 0⟩ : Content).l = 0 ∧
    (⟨1, 1, 7, 1, 0⟩ : Content).bR = (⟨1, 1, 7, 1, 0⟩ : Content).a ∧
    (⟨1, 1, 7, 1, 0⟩ : Content).a = 50 := by
  simp only [a, l, bR]
  norm_num

/-- The kinetic coupling `λ = 1 − ℓ/a` of (9.8), (9.9). -/
noncomputable def lam : ℝ := 1 - c.l / c.a

/-- **Equation (9.19).** For `Ns` minimally coupled scalar fields and `Nd` Dirac fields,
`λ = 1 − 4 (Ns + Nd)/(Ns + 6 Nd)`. -/
theorem lam_scalar_dirac (hX : c.X = 0) (hv : c.Nv = 0) (hw : c.Nw = 0)
    (h : c.Ns + 6 * c.Nd ≠ 0) :
    c.lam = 1 - 4 * (c.Ns + c.Nd) / (c.Ns + 6 * c.Nd) := by
  have h2 : 2 * c.Ns + 12 * c.Nd ≠ 0 := by
    intro h'; apply h; linarith
  have ha : c.a = 2 * c.Ns + 12 * c.Nd := by
    simp only [a, hX, hv, hw]; ring
  have hl : c.l = 8 * c.Ns + 8 * c.Nd := by
    simp only [l, hX, hv, hw]; ring
  rw [lam, ha, hl]
  congr 1
  rw [div_eq_div_iff h2 h]
  ring

/-- **Equation (9.19), range.** No content of minimally coupled scalar and Dirac fields has
`λ` outside `[−3, 1/3]`; in particular none reaches `λ = 1`. -/
theorem lam_scalar_dirac_mem (hX : c.X = 0) (hv : c.Nv = 0) (hw : c.Nw = 0)
    (hs : 0 ≤ c.Ns) (hd : 0 ≤ c.Nd) (h : 0 < c.Ns + c.Nd) :
    -3 ≤ c.lam ∧ c.lam ≤ 1 / 3 := by
  have hpos : 0 < c.Ns + 6 * c.Nd := by linarith
  rw [c.lam_scalar_dirac hX hv hw hpos.ne']
  constructor
  · have : 4 * (c.Ns + c.Nd) / (c.Ns + 6 * c.Nd) ≤ 4 := by
      rw [div_le_iff₀ hpos]; linarith
    linarith
  · have : 2 / 3 ≤ 4 * (c.Ns + c.Nd) / (c.Ns + 6 * c.Nd) := by
      rw [le_div_iff₀ hpos]; linarith
    linarith

/-- Table 3: a single minimally coupled scalar field has `λ = −3`. -/
example : (⟨1, 0, 0, 0, 0⟩ : Content).lam = -3 := by
  simp only [lam, a, l]; norm_num

/-- Table 3: a single Dirac field has `λ = 1/3`. -/
example : (⟨0, 0, 1, 0, 0⟩ : Content).lam = 1 / 3 := by
  simp only [lam, a, l]; norm_num

/-- Table 3: a single Maxwell field has `λ = 1/3`. -/
example : (⟨0, 0, 0, 1, 0⟩ : Content).lam = 1 / 3 := by
  simp only [lam, a, l]; norm_num

/-- Table 3: a single massive vector field has `λ = 1/13`. -/
example : (⟨0, 0, 0, 0, 1⟩ : Content).lam = 1 / 13 := by
  simp only [lam, a, l]; norm_num

/-- Table 3: the content `Ns = 4 Nd` that cancels the leading vacuum energy has `λ = −1`. -/
example : (⟨4, 0, 1, 0, 0⟩ : Content).lam = -1 := by
  simp only [lam, a, l]; norm_num

/-- Table 3: the conformally coupled scalar field (`ζ = 1/6`) has `λ = 1/3`. -/
example : (⟨1, 1 / 6, 0, 0, 0⟩ : Content).lam = 1 / 3 := by
  simp only [lam, a, l]; norm_num

end Content

/-! ## Order `m²`: the table of Proposition 9.15 -/

/-- Mass data of a content: `Ms = Σ m²` over scalar fields, `Z = Σ ζ m²` over scalar fields,
`Md = Σ m²` over Dirac fields, `Mv = Σ m²` over massive vector fields. -/
structure Masses where
  /-- sum of `m²` over the scalar fields -/
  Ms : ℝ
  /-- sum of `ζ m²` over the scalar fields -/
  Z : ℝ
  /-- sum of `m²` over the Dirac fields -/
  Md : ℝ
  /-- sum of `m²` over the massive vector fields -/
  Mv : ℝ

namespace Masses

variable (μ : Masses)

/-- `Σ w m²`, with the weights `w = 1 − 6ζ, 2, −3` of Proposition 9.15. The logarithmic term of
`Σa` (and of `Σb_R`) is `−(Σ w m²) L / 96π²`; it is also `Σ κ m²`. -/
def w : ℝ := μ.Ms - 6 * μ.Z + 2 * μ.Md - 3 * μ.Mv

/-- `Σ a_f m²`, finite part of the kinetic coefficient, in units of `1/2880π²`. -/
def af : ℝ := 31 * μ.Ms - 90 * μ.Z + 26 * μ.Md - 117 * μ.Mv

/-- `Σ ℓ_f m²`, finite part of the longitudinal coefficient, in units of `1/2880π²`. -/
def lf : ℝ := -6 * μ.Ms + 120 * μ.Z - 36 * μ.Md - 18 * μ.Mv

/-- `Σ b_f m²` for the sharp cutoff, in units of `1/2880π²`. -/
def bf : ℝ := 15 * μ.Ms - 90 * μ.Z + 30 * μ.Md - 45 * μ.Mv

/-- `Σ b_f m²` for a cutoff profile with moment ratio `r = μ₁μ₂/μ₃` (Proposition 9.16):
`b_f = 30 κ (r − ½)`. The sharp cutoff is `r = 1`. -/
noncomputable def bfProfile (r : ℝ) : ℝ := 30 * (r - 1 / 2) * μ.w

/-- `Str m²`: bosons minus fermions, weighted by the degrees of freedom `1, 4, 3`. -/
def strm2 : ℝ := μ.Ms - 4 * μ.Md + 3 * μ.Mv

theorem bfProfile_one : μ.bfProfile 1 = μ.bf := by
  simp only [bfProfile, bf, w]; ring

/-- **Proposition 9.18 (ii).** `20 Σ(−w m²) = Σ ℓ_f m² + Σ (b_f − a_f) m² + 2 Str m²`. -/
theorem relation_ii : 20 * (-μ.w) = μ.lf + (μ.bf - μ.af) + 2 * μ.strm2 := by
  simp only [w, af, lf, bf, strm2]; ring

/-- **Proposition 9.18 (iii).** `Σ a_f m² = −¾ Σ ℓ_f m² − 7/4 Σ (b_f − a_f) m² − 3/2 Str m²`. -/
theorem relation_iii : μ.af = -(3 / 4) * μ.lf - 7 / 4 * (μ.bf - μ.af) - 3 / 2 * μ.strm2 := by
  simp only [af, lf, bf, strm2]; ring

/-- **Corollary 9.19 at order `m²` (sharp cutoff).** If the non-covariant terms cancel
(`Σ ℓ_f m² = 0`, `Σ b_f m² = Σ a_f m²`) and `Str m² = 0`, then the logarithmic and the finite
part of `Σa` both vanish. -/
theorem a_eq_zero_of_covariant (hl : μ.lf = 0) (hb : μ.bf = μ.af) (hs : μ.strm2 = 0) :
    μ.w = 0 ∧ μ.af = 0 := by
  have h2 := μ.relation_ii
  have h3 := μ.relation_iii
  rw [hl, hb, hs] at h2 h3
  constructor <;> linarith

/-- **Corollary 9.17 (iii), general profile.** `Σ (b_f − a_f) m²` has the coefficients
`(30r − 46) Ms − 180 (r − 1) Z`, `60r − 56` and `162 − 90r` stated in the paper. -/
theorem bfProfile_sub_af (r : ℝ) :
    μ.bfProfile r - μ.af =
      (30 * r - 46) * μ.Ms - 180 * (r - 1) * μ.Z + (60 * r - 56) * μ.Md
        + (162 - 90 * r) * μ.Mv := by
  simp only [bfProfile, af, w]; ring

/-- **Corollary 9.19, the ratio `Ms : Z : Md : Mv = 5 : 1 : 2 : 1`.** For every cutoff profile with
`r ≤ 1`, the conditions at order `m²` determine the mass sums up to a common factor. -/
theorem ratio_of_covariant (r : ℝ) (hr : r ≤ 1) (hl : μ.lf = 0) (hb : μ.bfProfile r = μ.af)
    (hs : μ.strm2 = 0) :
    μ.Ms = 5 * μ.Mv ∧ μ.Z = μ.Mv ∧ μ.Md = 2 * μ.Mv := by
  simp only [bfProfile, af, lf, strm2, w] at hl hb hs
  have key : (90 * r - 150) * (μ.Md - 2 * μ.Mv) = 0 := by
    linear_combination hb - (21 * r - 37) * hs + 3 * (r - 1) / 2 * hl
  have hne : (90 * r - 150) ≠ 0 := by
    intro h; linarith
  have hd : μ.Md = 2 * μ.Mv := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hne
    · linarith
  refine ⟨?_, ?_, hd⟩ <;> linarith

/-- **Corollary 9.19, conclusion for every profile with `r ≤ 1`:** under the same conditions the
logarithmic and the finite part of `Σa` vanish. -/
theorem a_eq_zero_of_covariant_profile (r : ℝ) (hr : r ≤ 1) (hl : μ.lf = 0)
    (hb : μ.bfProfile r = μ.af) (hs : μ.strm2 = 0) :
    μ.w = 0 ∧ μ.af = 0 := by
  obtain ⟨h1, h2, h3⟩ := μ.ratio_of_covariant r hr hl hb hs
  simp only [w, af, h1, h2, h3]
  constructor <;> ring

/-- **Corollary 9.17 (i).** Without massive vector fields, a positive induced kinetic term for
large `L` (`Σ w m² < 0`) forces `Σ ℓ_f m² > 14 Ms + 4 Md ≥ 0`, hence `λ < 1`. -/
theorem lf_pos_of_no_vector (hv : μ.Mv = 0) (hMs : 0 ≤ μ.Ms) (hMd : 0 ≤ μ.Md) (ha : μ.w < 0) :
    14 * μ.Ms + 4 * μ.Md < μ.lf ∧ 0 < μ.lf := by
  simp only [w, lf, hv] at *
  constructor <;> linarith

/-- **Corollary 9.17 (ii).** A coupling sum `Z` with `Σa > 0` for large `L` and `Σℓ ≤ 0` exists if
and only if `7 Ms + 2 Md < 39 Mv`. -/
theorem exists_Z_iff (Ms Md Mv : ℝ) :
    (∃ Z : ℝ, (⟨Ms, Z, Md, Mv⟩ : Masses).w < 0 ∧ (⟨Ms, Z, Md, Mv⟩ : Masses).lf ≤ 0) ↔
      7 * Ms + 2 * Md < 39 * Mv := by
  simp only [w, lf]
  constructor
  · rintro ⟨Z, h1, h2⟩
    linarith
  · intro h
    refine ⟨(6 * Ms + 36 * Md + 18 * Mv) / 120, ?_, ?_⟩ <;> linarith

/-- The example after Corollary 9.17: one massive vector field of mass `m_v`, two massless Dirac
fields, five scalar fields, one with `m² = 9/2 m_v²` and `ζ = 1/12`. Then the finite non-covariant
terms cancel, the logarithmic coefficient is `¾ m_v²`, and `Str m² ≠ 0` (here `m_v² = 1`). -/
example :
    (⟨9 / 2, 1 / 12 * (9 / 2), 0, 1⟩ : Masses).lf = 0 ∧
    (⟨9 / 2, 1 / 12 * (9 / 2), 0, 1⟩ : Masses).bf = (⟨9 / 2, 1 / 12 * (9 / 2), 0, 1⟩ : Masses).af ∧
    -(⟨9 / 2, 1 / 12 * (9 / 2), 0, 1⟩ : Masses).w = 3 / 4 ∧
    (⟨9 / 2, 1 / 12 * (9 / 2), 0, 1⟩ : Masses).strm2 ≠ 0 := by
  simp only [w, af, lf, bf, strm2]
  norm_num

/-- The leading-order side of the same example: five scalars with `Σζ = 1`, two Dirac fields and
one massive vector field satisfy `Σℓ = 0`, `Σb_R = Σa`, `Str 1 = 0` (and then `Σa = 0`). -/
example :
    (⟨5, 1, 2, 0, 1⟩ : Content).l = 0 ∧
    (⟨5, 1, 2, 0, 1⟩ : Content).bR = (⟨5, 1, 2, 0, 1⟩ : Content).a ∧
    (⟨5, 1, 2, 0, 1⟩ : Content).str1 = 0 ∧
    (⟨5, 1, 2, 0, 1⟩ : Content).a = 0 := by
  simp only [Content.a, Content.l, Content.bR, Content.str1]
  norm_num

end Masses

/-! ## From the cutoff integrals to the table of Proposition 9.15

The integrals `Aₙ = ∫₀^Λ k^{2n+2} ω^{-2n-1} dk` have the expansions (stated in the proof of
Proposition 9.15; taken as input here)

* `A₀ = ½ Λ² + ¼ m² − ½ m² L`,
* `A₁ = ½ Λ² + 5/4 m² − 3/2 m² L`,
* `A₂ = ½ Λ² + 31/12 m² − 5/2 m² L`.

The kinetic coefficient `a` and the combination `a − ℓ` of each field are fixed linear
combinations of `A₀, A₁, A₂` (formulas (9.6)/(9.20), (9.18), (9.23) after the angular averages;
taken as input, in units of `1/π²`). The theorems evaluate these combinations on the three
coefficient vectors and recover the entries of Table 2 and of Proposition 9.15.
-/

namespace MassTerms

/-- scalar field with coupling `ζ`: `a` as a combination of `(A₀, A₂)` -/
noncomputable def scalarA (ζ x0 x2 : ℝ) : ℝ := x2 / 240 - ζ * x0 / 8

/-- scalar field with coupling `ζ`: `a − ℓ` as a combination of `(A₀, A₁, A₂)` -/
noncomputable def scalarAL (ζ x0 x1 x2 : ℝ) : ℝ :=
  -(1 / 32) * ((1 - 4 * ζ) ^ 2 * x0 - 2 / 3 * (1 - 4 * ζ) * x1 + x2 / 15)
    + (2 * ζ ^ 2 - ζ / 2) * x0 / 4

/-- Dirac field (four components): `a` -/
noncomputable def diracA (x1 x2 : ℝ) : ℝ := (x1 / 3 - 2 * x2 / 15) / 8

/-- Dirac field: `a − ℓ` -/
noncomputable def diracAL (x2 : ℝ) : ℝ := x2 / 120

/-- massive vector field: `a` -/
noncomputable def vectorA (x0 x1 x2 : ℝ) : ℝ := (4 * x0 - 8 / 3 * x1 + 2 / 5 * x2) / 32

/-- massive vector field: `a − ℓ` -/
noncomputable def vectorAL (x0 x1 x2 : ℝ) : ℝ := -(-x0 + 2 / 3 * x1 + x2 / 5) / 32

/-- Scalar field, order `Λ²`: `a = 2 (1 − 30ζ)` and `ℓ = 8 (1 − 10ζ)` in units of `Λ²/960π²`. -/
theorem scalar_leading (ζ : ℝ) :
    960 * scalarA ζ (1 / 2) (1 / 2) = 2 * (1 - 30 * ζ) ∧
    960 * (scalarA ζ (1 / 2) (1 / 2) - scalarAL ζ (1 / 2) (1 / 2) (1 / 2)) = 8 * (1 - 10 * ζ) := by
  simp only [scalarA, scalarAL]
  constructor <;> ring

/-- Scalar field, order `m²`: `a_f = 31 − 90ζ` and `ℓ_f = −6 (1 − 20ζ)` in units of `m²/2880π²`. -/
theorem scalar_finite (ζ : ℝ) :
    2880 * scalarA ζ (1 / 4) (31 / 12) = 31 - 90 * ζ ∧
    2880 * (scalarA ζ (1 / 4) (31 / 12) - scalarAL ζ (1 / 4) (5 / 4) (31 / 12))
      = -6 * (1 - 20 * ζ) := by
  simp only [scalarA, scalarAL]
  constructor <;> ring

/-- Scalar field, order `m² L`: `a` has the coefficient `−w/96` with `w = 1 − 6ζ`, and `ℓ` has no
logarithm. -/
theorem scalar_log (ζ : ℝ) :
    -96 * scalarA ζ (-(1 / 2)) (-(5 / 2)) = 1 - 6 * ζ ∧
    scalarA ζ (-(1 / 2)) (-(5 / 2)) - scalarAL ζ (-(1 / 2)) (-(3 / 2)) (-(5 / 2)) = 0 := by
  simp only [scalarA, scalarAL]
  constructor <;> ring

/-- Dirac field: `a = 12`, `ℓ = 8`; `a_f = 26`, `ℓ_f = −36`; `w = 2`, no logarithm in `ℓ`. -/
theorem dirac_all :
    960 * diracA (1 / 2) (1 / 2) = 12 ∧
    960 * (diracA (1 / 2) (1 / 2) - diracAL (1 / 2)) = 8 ∧
    2880 * diracA (5 / 4) (31 / 12) = 26 ∧
    2880 * (diracA (5 / 4) (31 / 12) - diracAL (31 / 12)) = -36 ∧
    -96 * diracA (-(3 / 2)) (-(5 / 2)) = 2 ∧
    diracA (-(3 / 2)) (-(5 / 2)) - diracAL (-(5 / 2)) = 0 := by
  simp only [diracA, diracAL]
  norm_num

/-- Massive vector field: `a = 26`, `ℓ = 24`; `a_f = −117`, `ℓ_f = −18`; `w = −3`, no logarithm
in `ℓ`. -/
theorem vector_all :
    960 * vectorA (1 / 2) (1 / 2) (1 / 2) = 26 ∧
    960 * (vectorA (1 / 2) (1 / 2) (1 / 2) - vectorAL (1 / 2) (1 / 2) (1 / 2)) = 24 ∧
    2880 * vectorA (1 / 4) (5 / 4) (31 / 12) = -117 ∧
    2880 * (vectorA (1 / 4) (5 / 4) (31 / 12) - vectorAL (1 / 4) (5 / 4) (31 / 12)) = -18 ∧
    -96 * vectorA (-(1 / 2)) (-(3 / 2)) (-(5 / 2)) = -3 ∧
    vectorA (-(1 / 2)) (-(3 / 2)) (-(5 / 2)) - vectorAL (-(1 / 2)) (-(3 / 2)) (-(5 / 2)) = 0 := by
  simp only [vectorA, vectorAL]
  norm_num

end MassTerms

end CorrelationsGeometry
