/-
Sixty-first file: the time derivative of the sampled operator and ALL pairs of times of a window, for the periodised
Gaussian kernel on the flat torus.  Namespace `CTG.FlatNPointLatticeDeriv`; imports the compiled module of the
fifty-sixth file; check with `./check_flat_npoint_lattice_deriv.sh`.
`C11`: a small calculus of functions with bounded, Lipschitz derivative (sums, products, inverses, composition).
`kS_C11`: the lattice-sum kernel as a function of the scale; `kS_self_ge` (`latK(x,x) ≥ 1`).
`psi_C11`: for EVERY sample, `s ↦ L_N` (scale `ξ/s`) is `C^{1,1}` on `[a₀, a₁]` with explicit constants; the lower bounds
of the normalisations come from the self-term alone (hence powers of `N` in the constants).
`deriv_from_window`: if `F'` is `M`-Lipschitz on `[p,q]` and every difference quotient with `|τb − τa| ≥ η₀` is at most
`ε`, then `|F'| ≤ ε + M η₀` on `[p,q]`; `slope_le`: then every difference quotient is bounded by the same.
`flat_npoint_lattice_deriv`: under the hypotheses of `flat_npoint_lattice_window`, `2η₀ ≤ q − p`, and the HYPOTHESIS
that `a'` is `L₂`-Lipschitz, outside the same exceptional set (outer measure, same probability bound): for every
`τ ∈ [p,q]` and every sample point the derivative `∂_τ L_N f` exists and
`|∂_τ L_N f − 2a'(τ) lapG f/a(τ)³| ≤ B_II := 2E + 2ξ²C₂ + M_tot η₀`, `|∂_τ L_N f − ∂_τ L_ξ f| ≤ B_II + ξ²C₂`, and for ALL
pairs `τa ≠ τb` of the window the two difference-quotient inequalities hold with these bounds.
LIMITS: `M_tot` is explicit but very large (powers of `N` up to about `N⁶`, and `1/ξ²`); `η₀` is a free parameter and the
choice that makes `M_tot η₀` small (polynomially small `η₀`, larger `L`) is NOT made in a statement, so this is not
yet a rate statement for the derivative; inequality (I) carries the extra term `ξ²C₂`; measurability of the exceptional
set is not shown; flat torus, conformal family, Gaussian kernel only.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryFlatNPointLatticeWindow

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss CTG.FlatNPointGaussFull
  CTG.FlatNPointGaussLattice CTG.FlatNPointLatticePop CTG.FlatNPointLatticeDirect
  CTG.FlatNPointClose CTG.FlatNPointWindow CTG.FlatNPointLatticeWindow

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointLatticeDeriv

/-! ### Stage 1: a C^{1,1} calculus -/

/-- `φ` is differentiable on `U` with derivative `φ'`, `|φ| ≤ B0`, `|φ'| ≤ B1`, `φ'` is
`B2`-Lipschitz on `U`. -/
structure C11 (U : Set ℝ) (φ φ' : ℝ → ℝ) (B0 B1 B2 : ℝ) : Prop where
  deriv : ∀ s ∈ U, HasDerivAt φ (φ' s) s
  b0 : ∀ s ∈ U, |φ s| ≤ B0
  b1 : ∀ s ∈ U, |φ' s| ≤ B1
  lip : ∀ s ∈ U, ∀ t ∈ U, |φ' s - φ' t| ≤ B2 * |s - t|

namespace C11

variable {U : Set ℝ} {φ φ' ψ ψ' : ℝ → ℝ} {B0 B1 B2 C0 C1 C2 : ℝ}

theorem lip0 (h : C11 U φ φ' B0 B1 B2) (hU : Convex ℝ U) {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) :
    |φ s - φ t| ≤ B1 * |s - t| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ) (f' := φ')
    (fun x hx => (h.deriv x hx).hasDerivWithinAt) (fun x hx => by
      rw [Real.norm_eq_abs]; exact h.b1 x hx) hU ht hs
  simpa [Real.norm_eq_abs] using this

theorem mono (h : C11 U φ φ' B0 B1 B2) {B0' B1' B2' : ℝ} (h0 : B0 ≤ B0') (h1 : B1 ≤ B1')
    (h2 : B2 ≤ B2') : C11 U φ φ' B0' B1' B2' :=
  ⟨h.deriv, fun s hs => (h.b0 s hs).trans h0, fun s hs => (h.b1 s hs).trans h1,
    fun s hs t ht => (h.lip s hs t ht).trans (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))⟩

theorem congr (h : C11 U φ φ' B0 B1 B2) {χ : ℝ → ℝ} (he : ∀ s, χ s = φ s) :
    C11 U χ φ' B0 B1 B2 := by
  have : χ = φ := funext he
  subst this; exact h

theorem const (c : ℝ) : C11 U (fun _ => c) (fun _ => 0) |c| 0 0 :=
  ⟨fun s _ => hasDerivAt_const s c, fun _ _ => le_rfl, fun _ _ => by simp,
    fun _ _ _ _ => by simp⟩

theorem const_mul (h : C11 U φ φ' B0 B1 B2) (c : ℝ) :
    C11 U (fun s => c * φ s) (fun s => c * φ' s) (|c| * B0) (|c| * B1) (|c| * B2) := by
  refine ⟨fun s hs => (h.deriv s hs).const_mul c, fun s hs => ?_, fun s hs => ?_,
    fun s hs t ht => ?_⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.b0 s hs) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.b1 s hs) (abs_nonneg _)
  · rw [← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.lip s hs t ht) (abs_nonneg _)

theorem add (h : C11 U φ φ' B0 B1 B2) (g : C11 U ψ ψ' C0 C1 C2) :
    C11 U (fun s => φ s + ψ s) (fun s => φ' s + ψ' s) (B0 + C0) (B1 + C1) (B2 + C2) := by
  refine ⟨fun s hs => (h.deriv s hs).add (g.deriv s hs), fun s hs => ?_, fun s hs => ?_,
    fun s hs t ht => ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (h.b0 s hs) (g.b0 s hs))
  · exact (abs_add_le _ _).trans (add_le_add (h.b1 s hs) (g.b1 s hs))
  · have e : φ' s + ψ' s - (φ' t + ψ' t) = (φ' s - φ' t) + (ψ' s - ψ' t) := by ring
    rw [e, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (h.lip s hs t ht) (g.lip s hs t ht))

theorem sum {ι : Type*} (u : Finset ι) {F F' : ι → ℝ → ℝ}
    (h : ∀ j ∈ u, C11 U (F j) (F' j) B0 B1 B2) :
    C11 U (fun s => ∑ j ∈ u, F j s) (fun s => ∑ j ∈ u, F' j s)
      (u.card * B0) (u.card * B1) (u.card * B2) := by
  refine ⟨fun s hs => HasDerivAt.fun_sum fun j hj => (h j hj).deriv s hs, fun s hs => ?_,
    fun s hs => ?_, fun s hs t ht => ?_⟩
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul u (fun j => |F j s|) B0 fun j hj => (h j hj).b0 s hs
    simpa [nsmul_eq_mul] using this
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul u (fun j => |F' j s|) B1 fun j hj => (h j hj).b1 s hs
    simpa [nsmul_eq_mul] using this
  · rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul u (fun j => |F' j s - F' j t|) (B2 * |s - t|)
      fun j hj => (h j hj).lip s hs t ht
    rw [nsmul_eq_mul] at this
    linarith

theorem B0_nonneg (h : C11 U φ φ' B0 B1 B2) {s : ℝ} (hs : s ∈ U) : 0 ≤ B0 :=
  (abs_nonneg _).trans (h.b0 s hs)

theorem B1_nonneg (h : C11 U φ φ' B0 B1 B2) {s : ℝ} (hs : s ∈ U) : 0 ≤ B1 :=
  (abs_nonneg _).trans (h.b1 s hs)

theorem mul (hU : Convex ℝ U) (h : C11 U φ φ' B0 B1 B2) (g : C11 U ψ ψ' C0 C1 C2) :
    C11 U (fun s => φ s * ψ s) (fun s => φ' s * ψ s + φ s * ψ' s) (B0 * C0)
      (B1 * C0 + B0 * C1) (B2 * C0 + 2 * (B1 * C1) + B0 * C2) := by
  refine ⟨fun s hs => (h.deriv s hs).mul (g.deriv s hs), fun s hs => ?_, fun s hs => ?_,
    fun s hs t ht => ?_⟩
  · rw [abs_mul]
    exact mul_le_mul (h.b0 s hs) (g.b0 s hs) (abs_nonneg _) (h.B0_nonneg hs)
  · refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul (h.b1 s hs) (g.b0 s hs) (abs_nonneg _) (h.B1_nonneg hs))
      (mul_le_mul (h.b0 s hs) (g.b1 s hs) (abs_nonneg _) (h.B0_nonneg hs))
  · have e : φ' s * ψ s + φ s * ψ' s - (φ' t * ψ t + φ t * ψ' t)
        = (φ' s - φ' t) * ψ s + φ' t * (ψ s - ψ t) + (φ s - φ t) * ψ' s
          + φ t * (ψ' s - ψ' t) := by ring
    rw [e]
    have hd : 0 ≤ |s - t| := abs_nonneg _
    have hA : |(φ' s - φ' t) * ψ s| ≤ B2 * |s - t| * C0 := by
      rw [abs_mul]
      exact mul_le_mul (h.lip s hs t ht) (g.b0 s hs) (abs_nonneg _)
        ((abs_nonneg _).trans (h.lip s hs t ht))
    have hB : |φ' t * (ψ s - ψ t)| ≤ B1 * (C1 * |s - t|) := by
      rw [abs_mul]
      exact mul_le_mul (h.b1 t ht) (g.lip0 hU hs ht) (abs_nonneg _) (h.B1_nonneg ht)
    have hC : |(φ s - φ t) * ψ' s| ≤ B1 * |s - t| * C1 := by
      rw [abs_mul]
      exact mul_le_mul (h.lip0 hU hs ht) (g.b1 s hs) (abs_nonneg _)
        (mul_nonneg (h.B1_nonneg hs) hd)
    have hD : |φ t * (ψ' s - ψ' t)| ≤ B0 * (C2 * |s - t|) := by
      rw [abs_mul]
      exact mul_le_mul (h.b0 t ht) (g.lip s hs t ht) (abs_nonneg _) (h.B0_nonneg ht)
    have t1 := abs_add_le ((φ' s - φ' t) * ψ s + φ' t * (ψ s - ψ t) + (φ s - φ t) * ψ' s)
      (φ t * (ψ' s - ψ' t))
    have t2 := abs_add_le ((φ' s - φ' t) * ψ s + φ' t * (ψ s - ψ t)) ((φ s - φ t) * ψ' s)
    have t3 := abs_add_le ((φ' s - φ' t) * ψ s) (φ' t * (ψ s - ψ t))
    nlinarith

theorem inv_sq_diff (p q : ℝ) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    -p / a ^ 2 - -q / b ^ 2 = -((p - q) / a ^ 2) - q * ((b - a) * (b + a) / (a ^ 2 * b ^ 2)) := by
  field_simp; ring

theorem inv (hU : Convex ℝ U) (h : C11 U φ φ' B0 B1 B2) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ s ∈ U, c ≤ φ s) :
    C11 U (fun s => 1 / φ s) (fun s => -(φ' s) / φ s ^ 2) (1 / c) (B1 / c ^ 2)
      (B2 / c ^ 2 + 2 * B0 * B1 ^ 2 / c ^ 4) := by
  have hpos : ∀ s ∈ U, 0 < φ s := fun s hs => lt_of_lt_of_le hc (hlow s hs)
  refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_, fun s hs t ht => ?_⟩
  · have := (h.deriv s hs).inv (hpos s hs).ne'
    simpa only [one_div] using this
  · rw [abs_of_pos (one_div_pos.2 (hpos s hs))]
    exact one_div_le_one_div_of_le hc (hlow s hs)
  · rw [abs_div, abs_neg, abs_of_pos (pow_pos (hpos s hs) 2)]
    exact div_le_div₀ (h.B1_nonneg hs) (h.b1 s hs) (pow_pos hc 2)
      (pow_le_pow_left₀ hc.le (hlow s hs) 2)
  · set a := φ s
    set b := φ t
    have ha := hpos s hs
    have hb := hpos t ht
    have hac := hlow s hs
    have hbc := hlow t ht
    have hB0 := h.B0_nonneg hs
    have hB1 := h.B1_nonneg hs
    have hd : 0 ≤ |s - t| := abs_nonneg _
    rw [inv_sq_diff (φ' s) (φ' t) ha.ne' hb.ne']
    have hX : |(φ' s - φ' t) / a ^ 2| ≤ B2 * |s - t| / c ^ 2 := by
      rw [abs_div, abs_of_pos (pow_pos ha 2)]
      exact div_le_div₀ ((abs_nonneg _).trans (h.lip s hs t ht)) (h.lip s hs t ht) (pow_pos hc 2)
        (pow_le_pow_left₀ hc.le hac 2)
    have hab : |b - a| ≤ B1 * |s - t| := by
      rw [abs_sub_comm]; exact h.lip0 hU hs ht
    have hsum : b + a ≤ 2 * B0 := by
      have := le_abs_self a; have := le_abs_self b
      have := h.b0 s hs; have := h.b0 t ht; linarith
    have hden : c ^ 4 ≤ a ^ 2 * b ^ 2 := by
      have h1 := pow_le_pow_left₀ hc.le hac 2
      have h2 := pow_le_pow_left₀ hc.le hbc 2
      calc c ^ 4 = c ^ 2 * c ^ 2 := by ring
        _ ≤ a ^ 2 * b ^ 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have hY : |(b - a) * (b + a) / (a ^ 2 * b ^ 2)| ≤ B1 * |s - t| * (2 * B0) / c ^ 4 := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < a ^ 2 * b ^ 2),
        abs_of_pos (by linarith : 0 < b + a)]
      exact div_le_div₀ (by positivity) (mul_le_mul hab hsum (by linarith) (by positivity))
        (by positivity) hden
    have hZ : |φ' t * ((b - a) * (b + a) / (a ^ 2 * b ^ 2))|
        ≤ B1 * (B1 * |s - t| * (2 * B0) / c ^ 4) := by
      rw [abs_mul]; exact mul_le_mul (h.b1 t ht) hY (abs_nonneg _) hB1
    refine (abs_sub _ _).trans ?_
    rw [abs_neg]
    have : B2 * |s - t| / c ^ 2 + B1 * (B1 * |s - t| * (2 * B0) / c ^ 4)
        = (B2 / c ^ 2 + 2 * B0 * B1 ^ 2 / c ^ 4) * |s - t| := by ring
    linarith

end C11

/-! ### Stage 2: the lattice kernel as a function of the scale -/

/-- One lattice term `gauss(r s)` and its first two derivatives in `s`. -/
def tm (r s : ℝ) : ℝ := gauss (r * s)
def t1 (r s : ℝ) : ℝ := -(r * s) * gauss (r * s) * r
def t2 (r s : ℝ) : ℝ := r ^ 2 * ((r * s) ^ 2 - 1) * gauss (r * s)

theorem tm_hasDerivAt (r s : ℝ) : HasDerivAt (tm r) (t1 r s) s := by
  have h1 := (gauss_hasDerivAt (r * s)).comp s ((hasDerivAt_id' s).const_mul r)
  unfold tm t1
  convert h1 using 1
  ring

theorem t1_hasDerivAt (r s : ℝ) : HasDerivAt (t1 r) (t2 r s) s := by
  have he : t1 r = fun y => -(r ^ 2) * (y * tm r y) := by
    funext y; unfold t1 tm; ring
  rw [he]
  have h1 := ((hasDerivAt_id' s).mul (tm_hasDerivAt r s)).const_mul (-(r ^ 2))
  convert h1 using 1
  unfold t1 t2 tm; ring

theorem t1_bound {r s b : ℝ} (hr : 0 ≤ r) (hb : 0 < b) (hbs : b ≤ s) :
    |t1 r s| ≤ 3 / b * gauss (r * b / 2) := by
  have hs : 0 < s := lt_of_lt_of_le hb hbs
  set u := r * s with hu
  have hu0 : 0 ≤ u := mul_nonneg hr hs.le
  have e : |t1 r s| = u ^ 2 * gauss u / s := by
    unfold t1
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hu0, abs_of_pos (gauss_pos _), abs_of_nonneg hr]
    field_simp
    rw [hu]; ring
  rw [e]
  have h1 := dom2 u
  have h2 : gauss (u / 2) ≤ gauss (r * b / 2) :=
    gauss_anti (by positivity) (by rw [hu]; nlinarith)
  have h3 : u ^ 2 * gauss u ≤ 3 * gauss (r * b / 2) := h1.trans (by linarith)
  calc u ^ 2 * gauss u / s ≤ 3 * gauss (r * b / 2) / s :=
        div_le_div_of_nonneg_right h3 hs.le
    _ ≤ 3 * gauss (r * b / 2) / b :=
        div_le_div_of_nonneg_left (by have := gauss_pos (r * b / 2); positivity) hb hbs
    _ = 3 / b * gauss (r * b / 2) := by ring

theorem t2_bound {r s b : ℝ} (hr : 0 ≤ r) (hb : 0 < b) (hbs : b ≤ s) :
    |t2 r s| ≤ 18 / b ^ 2 * gauss (r * b / 2) := by
  have hs : 0 < s := lt_of_lt_of_le hb hbs
  set u := r * s with hu
  have hu0 : 0 ≤ u := mul_nonneg hr hs.le
  have e : t2 r s = (u ^ 4 - u ^ 2) * gauss u / s ^ 2 := by
    unfold t2
    field_simp
    rw [hu]; ring
  rw [e, abs_div, abs_of_pos (pow_pos hs 2), abs_mul, abs_of_pos (gauss_pos _)]
  have h4 : u ^ 4 * gauss u ≤ 15 * gauss (u / 2) := dom_core _ (four_le_exp38 u)
  have h2 := dom2 u
  have h5 : gauss (u / 2) ≤ gauss (r * b / 2) :=
    gauss_anti (by positivity) (by rw [hu]; nlinarith)
  have habs : |u ^ 4 - u ^ 2| ≤ u ^ 4 + u ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [pow_nonneg hu0 4, sq_nonneg u]
  have hg := gauss_pos u
  have h6 : |u ^ 4 - u ^ 2| * gauss u ≤ 18 * gauss (r * b / 2) := by
    have := mul_le_mul_of_nonneg_right habs hg.le
    nlinarith
  calc |u ^ 4 - u ^ 2| * gauss u / s ^ 2 ≤ 18 * gauss (r * b / 2) / s ^ 2 :=
        div_le_div_of_nonneg_right h6 (by positivity)
    _ ≤ 18 * gauss (r * b / 2) / b ^ 2 :=
        div_le_div_of_nonneg_left (by have := gauss_pos (r * b / 2); positivity)
          (by positivity) (pow_le_pow_left₀ hb.le hbs 2)
    _ = 18 / b ^ 2 * gauss (r * b / 2) := by ring

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The lattice kernel at scale `ξ/s` as a function of `s`, and its derivatives. -/
def kS (S : E ≃L[ℝ] E) (ξ : ℝ) (x z : E) (s : ℝ) : ℝ := latK S (ξ / s) x z

def rr (S : E ≃L[ℝ] E) (ξ : ℝ) (x z : E) (m : Fin n → ℤ) : ℝ :=
  ‖S.symm (fr (z - x) + latV m)‖ / ξ

def kS1 (S : E ≃L[ℝ] E) (ξ : ℝ) (x z : E) (s : ℝ) : ℝ := ∑' m, t1 (rr S ξ x z m) s
def kS2 (S : E ≃L[ℝ] E) (ξ : ℝ) (x z : E) (s : ℝ) : ℝ := ∑' m, t2 (rr S ξ x z m) s

theorem arg_eq (w ξ s : ℝ) : w / (ξ / s) = w / ξ * s := by
  rw [div_div_eq_mul_div, div_mul_eq_mul_div]

theorem kS_eq (S : E ≃L[ℝ] E) (ξ : ℝ) (x z : E) (s : ℝ) :
    kS S ξ x z s = ∑' m, tm (rr S ξ x z m) s := by
  unfold kS latK tm rr
  congr 1; funext m; rw [arg_eq]

theorem rr_nonneg (S : E ≃L[ℝ] E) {ξ : ℝ} (hξ : 0 < ξ) (x z : E) (m : Fin n → ℤ) :
    0 ≤ rr S ξ x z m := by unfold rr; positivity

theorem dom_arg (S : E ≃L[ℝ] E) {ξ b : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (y : E) :
    ‖S.symm y‖ / ξ * b / 2 = ‖S.symm y‖ / (2 * ξ / b) := by
  field_simp

/-- Lattice sums of the majorants `C·gauss(r b/2)`. -/
theorem maj_sum (S : E ≃L[ℝ] E) {ξ b C : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : 0 < b) (hC : 0 ≤ C)
    (x z : E) :
    Summable (fun m : Fin n → ℤ => C * gauss (rr S ξ x z m * b / 2))
      ∧ ∑' m : Fin n → ℤ, C * gauss (rr S ξ x z m * b / 2) ≤ C * Gb n S b := by
  have hL := lat_bound S hξ hξ1 hb le_rfl hC (Φ := fun y => C * gauss (‖S.symm y‖ / (2 * ξ / b)))
    (fun y => mul_nonneg hC (gauss_pos _).le) (fun y => le_rfl) x z
  have he : ∀ m : Fin n → ℤ, C * gauss (rr S ξ x z m * b / 2)
      = C * gauss (‖S.symm (fr (z - x) + latV m)‖ / (2 * ξ / b)) := fun m => by
    unfold rr; rw [dom_arg S hξ hb]
  refine ⟨?_, ?_⟩
  · simp_rw [he]; exact hL.1
  · simp_rw [he]; exact hL.2.2

theorem kS_hasDerivAt (S : E ≃L[ℝ] E) {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : 0 < b) (x z : E)
    {s : ℝ} (hs : b < s) : HasDerivAt (kS S ξ x z) (kS1 S ξ x z s) s := by
  have hb3 : 0 ≤ 3 / b := by positivity
  obtain ⟨hsum, -⟩ := maj_sum S hξ hξ1 hb hb3 x z
  have hs0 : Summable fun m : Fin n → ℤ => tm (rr S ξ x z m) s := by
    refine Summable.of_norm_bounded ((maj_sum S hξ hξ1 hb zero_le_one x z).1) fun m => ?_
    rw [Real.norm_eq_abs, tm, abs_of_pos (gauss_pos _), one_mul]
    exact gauss_anti (by have := rr_nonneg S hξ x z m; positivity)
      (by have := rr_nonneg S hξ x z m; nlinarith)
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun m y => tm (rr S ξ x z m) y)
    (g' := fun m y => t1 (rr S ξ x z m) y) hsum isOpen_Ioi isPreconnected_Ioi
    (fun m y _ => tm_hasDerivAt _ y)
    (fun m y hy => by
      rw [Real.norm_eq_abs]
      exact t1_bound (rr_nonneg S hξ x z m) hb (le_of_lt hy))
    (mem_Ioi.2 hs) hs0 (mem_Ioi.2 hs)
  have he : kS S ξ x z = fun y => ∑' m, tm (rr S ξ x z m) y := funext fun y => kS_eq S ξ x z y
  rw [he]; exact key

theorem kS1_hasDerivAt (S : E ≃L[ℝ] E) {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : 0 < b)
    (x z : E) {s : ℝ} (hs : b < s) : HasDerivAt (kS1 S ξ x z) (kS2 S ξ x z s) s := by
  have hb3 : 0 ≤ 18 / b ^ 2 := by positivity
  obtain ⟨hsum, -⟩ := maj_sum S hξ hξ1 hb hb3 x z
  have hs0 : Summable fun m : Fin n → ℤ => t1 (rr S ξ x z m) s := by
    refine Summable.of_norm_bounded ((maj_sum S hξ hξ1 hb (by positivity : (0:ℝ) ≤ 3 / b) x z).1)
      fun m => ?_
    rw [Real.norm_eq_abs]
    exact t1_bound (rr_nonneg S hξ x z m) hb hs.le
  exact hasDerivAt_tsum_of_isPreconnected (g := fun m y => t1 (rr S ξ x z m) y)
    (g' := fun m y => t2 (rr S ξ x z m) y) hsum isOpen_Ioi isPreconnected_Ioi
    (fun m y _ => t1_hasDerivAt _ y)
    (fun m y hy => by
      rw [Real.norm_eq_abs]
      exact t2_bound (rr_nonneg S hξ x z m) hb (le_of_lt hy))
    (mem_Ioi.2 hs) hs0 (mem_Ioi.2 hs)

theorem kS1_bound (S : E ≃L[ℝ] E) {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : 0 < b) (x z : E)
    {s : ℝ} (hs : b ≤ s) : |kS1 S ξ x z s| ≤ 3 / b * Gb n S b := by
  obtain ⟨hsum, hle⟩ := maj_sum S hξ hξ1 hb (by positivity : (0:ℝ) ≤ 3 / b) x z
  have := tsum_of_norm_bounded hsum.hasSum (f := fun m => t1 (rr S ξ x z m) s) fun m => by
    rw [Real.norm_eq_abs]; exact t1_bound (rr_nonneg S hξ x z m) hb hs
  rw [Real.norm_eq_abs] at this
  exact this.trans hle

theorem kS2_bound (S : E ≃L[ℝ] E) {ξ b : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : 0 < b) (x z : E)
    {s : ℝ} (hs : b ≤ s) : |kS2 S ξ x z s| ≤ 18 / b ^ 2 * Gb n S b := by
  obtain ⟨hsum, hle⟩ := maj_sum S hξ hξ1 hb (by positivity : (0:ℝ) ≤ 18 / b ^ 2) x z
  have := tsum_of_norm_bounded hsum.hasSum (f := fun m => t2 (rr S ξ x z m) s) fun m => by
    rw [Real.norm_eq_abs]; exact t2_bound (rr_nonneg S hξ x z m) hb hs
  rw [Real.norm_eq_abs] at this
  exact this.trans hle

/-- **The kernel is C^{1,1} in the scale on `[a₀, a₁]`.** -/
theorem kS_C11 (S : E ≃L[ℝ] E) {ξ a₀ a₁ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (x z : E) :
    C11 (Icc a₀ a₁) (kS S ξ x z) (kS1 S ξ x z) (Gb n S a₀) (3 / a₀ * Gb n S a₀)
      (18 / a₀ ^ 2 * Gb n S a₀) := by
  have hb : 0 < a₀ / 2 := by positivity
  have hd : ∀ s ∈ Icc a₀ a₁, HasDerivAt (kS S ξ x z) (kS1 S ξ x z s) s := fun s hs =>
    kS_hasDerivAt S hξ hξ1 hb x z (by linarith [hs.1])
  have hd1 : ∀ s ∈ Icc a₀ a₁, HasDerivAt (kS1 S ξ x z) (kS2 S ξ x z s) s := fun s hs =>
    kS1_hasDerivAt S hξ hξ1 hb x z (by linarith [hs.1])
  refine ⟨hd, fun s hs => ?_, fun s hs => kS1_bound S hξ hξ1 ha₀ x z hs.1, fun s hs t ht => ?_⟩
  · obtain ⟨-, h0, h1⟩ := latK_nonneg S hξ hξ1 ha₀ hs.1 x z
    unfold kS; rw [abs_of_nonneg h0]; linarith
  · have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := kS1 S ξ x z)
      (f' := kS2 S ξ x z) (fun y hy => (hd1 y hy).hasDerivWithinAt)
      (fun y hy => by rw [Real.norm_eq_abs]; exact kS2_bound S hξ hξ1 ha₀ x z hy.1)
      (convex_Icc a₀ a₁) ht hs
    simpa [Real.norm_eq_abs] using this

/-- **Self-term:** `latK(x,x) ≥ 1`. -/
theorem kS_self_ge (S : E ≃L[ℝ] E) {ξ a₀ s : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (hs : a₀ ≤ s) (x : E) : 1 ≤ kS S ξ x x s := by
  obtain ⟨hsum, -, -⟩ := latK_nonneg S hξ hξ1 ha₀ hs x x
  have h := hsum.le_tsum 0 (fun j _ => ΦK_nonneg S ξ s _)
  have hfr : fr (x - x) + latV (0 : Fin n → ℤ) = 0 := by
    rw [sub_self, latV_zero, add_zero]
    ext i; rw [fr_apply]; norm_num
  unfold kS latK
  have e : ΦK S ξ s (fr (x - x) + latV 0) = 1 := by
    unfold ΦK; rw [hfr]; simp [gauss]
  rw [e] at h
  exact h

theorem kS_nonneg (S : E ≃L[ℝ] E) {ξ a₀ s : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (hs : a₀ ≤ s) (x z : E) : 0 ≤ kS S ξ x z s :=
  (latK_nonneg S hξ hξ1 ha₀ hs x z).2.1

theorem kS_le (S : E ≃L[ℝ] E) {ξ a₀ s : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (hs : a₀ ≤ s) (x z : E) : kS S ξ x z s ≤ Gb n S a₀ := by
  have := (latK_nonneg S hξ hξ1 ha₀ hs x z).2.2; unfold kS; linarith


/-! ### Stage 3: the sample operator as a function of the scale -/

theorem C11.mul_const {U : Set ℝ} {φ φ' : ℝ → ℝ} {B0 B1 B2 : ℝ} (h : C11 U φ φ' B0 B1 B2)
    {c Bc : ℝ} (hc : |c| ≤ Bc) :
    C11 U (fun s => φ s * c) (fun s => φ' s * c) (B0 * Bc) (B1 * Bc) (B2 * Bc) := by
  have hBc : 0 ≤ Bc := (abs_nonneg _).trans hc
  refine ⟨fun s hs => (h.deriv s hs).mul_const c, fun s hs => ?_, fun s hs => ?_,
    fun s hs t ht => ?_⟩
  · rw [abs_mul]; exact mul_le_mul (h.b0 s hs) hc (abs_nonneg _) (h.B0_nonneg hs)
  · rw [abs_mul]; exact mul_le_mul (h.b1 s hs) hc (abs_nonneg _) (h.B1_nonneg hs)
  · rw [← sub_mul, abs_mul]
    calc |φ' s - φ' t| * |c| ≤ B2 * |s - t| * Bc :=
          mul_le_mul (h.lip s hs t ht) hc (abs_nonneg _) ((abs_nonneg _).trans (h.lip s hs t ht))
      _ = B2 * Bc * |s - t| := by ring

theorem avg_const {N : ℕ} (hN : 0 < N) (B : ℝ) :
    |1 / (N : ℝ)| * ((Finset.range N).card * B) = B := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [Finset.card_range, abs_of_pos (one_div_pos.2 hN')]
  field_simp

/-- Constants of one weighted summand `K g / q`. -/
def tc0 (G Bg c : ℝ) : ℝ := G * Bg * (1 / c)
def tc1 (G K1 Bg c : ℝ) : ℝ := K1 * Bg * (1 / c) + G * Bg * (K1 / c ^ 2)
def tc2 (G K1 K2 Bg c : ℝ) : ℝ :=
  K2 * Bg * (1 / c) + 2 * (K1 * Bg * (K1 / c ^ 2)) + G * Bg * (K2 / c ^ 2 + 2 * G * K1 ^ 2 / c ^ 4)

/-- Constants of `Ψ = −(2/(m₂ξ²)) 𝒩/𝒟`. -/
def psiB0 (G K1 K2 B c cD m₂ ξ : ℝ) : ℝ := 2 / (m₂ * ξ ^ 2) * (tc0 G (2 * B) c * (1 / cD))
def psiB1 (G K1 K2 B c cD m₂ ξ : ℝ) : ℝ :=
  2 / (m₂ * ξ ^ 2) * (tc1 G K1 (2 * B) c * (1 / cD) + tc0 G (2 * B) c * (tc1 G K1 1 c / cD ^ 2))
def psiB2 (G K1 K2 B c cD m₂ ξ : ℝ) : ℝ :=
  2 / (m₂ * ξ ^ 2) * (tc2 G K1 K2 (2 * B) c * (1 / cD)
    + 2 * (tc1 G K1 (2 * B) c * (tc1 G K1 1 c / cD ^ 2))
    + tc0 G (2 * B) c * (tc2 G K1 K2 1 c / cD ^ 2
        + 2 * tc0 G 1 c * tc1 G K1 1 c ^ 2 / cD ^ 4))

variable {Ω : Type*}

theorem sampAvg_C11 (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E)
    {ξ a₀ a₁ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (j : ℕ) :
    C11 (Icc a₀ a₁) (fun s => sampAvg X N (latK S (ξ / s)) j ω)
      (fun s => 1 / (N : ℝ) * ∑ l ∈ Finset.range N, kS1 S ξ (X j ω) (X l ω) s)
      (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) := by
  have h := (C11.sum (Finset.range N) (F := fun l s => kS S ξ (X j ω) (X l ω) s)
    (F' := fun l s => kS1 S ξ (X j ω) (X l ω) s)
    (fun l _ => kS_C11 S (a₁ := a₁) hξ hξ1 ha₀ (X j ω) (X l ω))).const_mul (1 / (N : ℝ))
  rw [avg_const hN, avg_const hN, avg_const hN] at h
  exact h.congr fun s => rfl

theorem sampAvg_lower (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E)
    {ξ a₀ s : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (hs : a₀ ≤ s) {j : ℕ} (hj : j < N) :
    1 / (N : ℝ) ≤ sampAvg X N (latK S (ξ / s)) j ω := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  unfold sampAvg
  have h1 : latK S (ξ / s) (X j ω) (X j ω)
      ≤ ∑ l ∈ Finset.range N, latK S (ξ / s) (X j ω) (X l ω) :=
    Finset.single_le_sum (f := fun l => latK S (ξ / s) (X j ω) (X l ω))
      (fun l _ => kS_nonneg S hξ hξ1 ha₀ hs _ _) (Finset.mem_range.2 hj)
  have h2 := kS_self_ge S hξ hξ1 ha₀ hs (X j ω)
  unfold kS at h2
  have := mul_le_mul_of_nonneg_left (h2.trans h1) (one_div_pos.2 hN').le
  simpa using this

theorem sampAvg_upper (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E)
    {ξ a₀ s : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (hs : a₀ ≤ s) (j : ℕ) :
    sampAvg X N (latK S (ξ / s)) j ω ≤ Gb n S a₀ := by
  have := (sampAvg_C11 X hN ω S (a₁ := s) hξ hξ1 ha₀ j).b0 s ⟨hs, le_rfl⟩
  exact (le_abs_self _).trans this

/-- **The weighted sample average `sampW` is C^{1,1} in the scale.** -/
theorem sampW_C11 (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E)
    {ξ a₀ a₁ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (i : ℕ) (gf : E → E → ℝ) {Bg : ℝ}
    (hg : ∀ j, |gf (X i ω) (X j ω)| ≤ Bg) :
    ∃ D : ℝ → ℝ, C11 (Icc a₀ a₁) (fun s => sampW X N (latK S (ξ / s)) gf i ω) D
      (tc0 (Gb n S a₀) Bg (1 / N)) (tc1 (Gb n S a₀) (3 / a₀ * Gb n S a₀) Bg (1 / N))
      (tc2 (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) Bg (1 / N)) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hc : (0:ℝ) < 1 / N := one_div_pos.2 hN'
  have hterm : ∀ j ∈ Finset.range N, C11 (Icc a₀ a₁)
      (fun s => latK S (ξ / s) (X i ω) (X j ω) * gf (X i ω) (X j ω)
        * (1 / sampAvg X N (latK S (ξ / s)) j ω))
      (fun s => kS1 S ξ (X i ω) (X j ω) s * gf (X i ω) (X j ω)
          * (1 / sampAvg X N (latK S (ξ / s)) j ω)
        + kS S ξ (X i ω) (X j ω) s * gf (X i ω) (X j ω)
          * (-(1 / (N : ℝ) * ∑ l ∈ Finset.range N, kS1 S ξ (X j ω) (X l ω) s)
            / sampAvg X N (latK S (ξ / s)) j ω ^ 2))
      (tc0 (Gb n S a₀) Bg (1 / N)) (tc1 (Gb n S a₀) (3 / a₀ * Gb n S a₀) Bg (1 / N))
      (tc2 (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) Bg (1 / N)) := by
    intro j hj
    have hkg := (kS_C11 S hξ hξ1 ha₀ (a₁ := a₁) (X i ω) (X j ω)).mul_const (hg j)
    have hr := (sampAvg_C11 X hN ω S (a₁ := a₁) hξ hξ1 ha₀ j).inv (convex_Icc a₀ a₁) hc
      (fun s hs => sampAvg_lower X hN ω S hξ hξ1 ha₀ hs.1 (Finset.mem_range.1 hj))
    have hm := hkg.mul (convex_Icc a₀ a₁) hr
    refine (hm.mono (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_)).congr fun s => rfl
    · unfold tc0; ring
    · unfold tc1; ring
    · unfold tc2; ring
  have h := (C11.sum (Finset.range N) hterm).const_mul (1 / (N : ℝ))
  rw [avg_const hN, avg_const hN, avg_const hN] at h
  exact ⟨_, h.congr fun s => rfl⟩

theorem sampW_one_lower (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E)
    {ξ a₀ s : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (hs : a₀ ≤ s) {i : ℕ} (hi : i < N) :
    1 / ((N : ℝ) * Gb n S a₀) ≤ sampW X N (latK S (ξ / s)) (fun _ _ => 1) i ω := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hG := Gb_pos S a₀ (n := n)
  unfold sampW avgN
  have hq : ∀ j ∈ Finset.range N, 0 < sampAvg X N (latK S (ξ / s)) j ω := fun j hj =>
    lt_of_lt_of_le (one_div_pos.2 hN') (sampAvg_lower X hN ω S hξ hξ1 ha₀ hs (Finset.mem_range.1 hj))
  have h1 : latK S (ξ / s) (X i ω) (X i ω) * 1 * (1 / sampAvg X N (latK S (ξ / s)) i ω)
      ≤ ∑ j ∈ Finset.range N, latK S (ξ / s) (X i ω) (X j ω) * 1
          * (1 / sampAvg X N (latK S (ξ / s)) j ω) :=
    Finset.single_le_sum (f := fun j => latK S (ξ / s) (X i ω) (X j ω) * 1
          * (1 / sampAvg X N (latK S (ξ / s)) j ω))
      (fun j hj => mul_nonneg (mul_nonneg (kS_nonneg S hξ hξ1 ha₀ hs _ _) zero_le_one)
        (one_div_pos.2 (hq j hj)).le) (Finset.mem_range.2 hi)
  have h2 := kS_self_ge S hξ hξ1 ha₀ hs (X i ω)
  unfold kS at h2
  have hqi := hq i (Finset.mem_range.2 hi)
  have h3 : 1 / Gb n S a₀ ≤ latK S (ξ / s) (X i ω) (X i ω) * 1
      * (1 / sampAvg X N (latK S (ξ / s)) i ω) := by
    rw [mul_one]
    calc 1 / Gb n S a₀ ≤ 1 * (1 / sampAvg X N (latK S (ξ / s)) i ω) := by
          rw [one_mul]
          exact one_div_le_one_div_of_le hqi (sampAvg_upper X hN ω S hξ hξ1 ha₀ hs i)
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (one_div_pos.2 hqi).le
  have := mul_le_mul_of_nonneg_left (h3.trans h1) (one_div_pos.2 hN').le
  calc 1 / ((N : ℝ) * Gb n S a₀) = 1 / (N : ℝ) * (1 / Gb n S a₀) := by
        rw [one_div_mul_one_div]
    _ ≤ _ := this

theorem gd_bound {f : E → ℝ} {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x y : E) : |gd f x y| ≤ 2 * B := by
  unfold gd
  have := abs_sub (f y) (f x)
  have := hB x; have := hB y; linarith

/-- **`Ψ(s) = L_N f(i)` at the scale `s` is C^{1,1} on `[a₀, a₁]`** with explicit constants
(`c = 1/N`, `c_D = 1/(N G)` from the self-term). -/
theorem psi_C11 (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E)
    {ξ a₀ a₁ m₂ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (hm₂ : 0 < m₂)
    {f : E → ℝ} (hB : ∀ y, |f y| ≤ B) {i : ℕ} (hi : i < N) :
    ∃ D : ℝ → ℝ, C11 (Icc a₀ a₁) (fun s => LNK X N (latK S (ξ / s)) m₂ ξ f i ω) D
      (psiB0 (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) B (1 / N)
        (1 / (N * Gb n S a₀)) m₂ ξ)
      (psiB1 (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) B (1 / N)
        (1 / (N * Gb n S a₀)) m₂ ξ)
      (psiB2 (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) B (1 / N)
        (1 / (N * Gb n S a₀)) m₂ ξ) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hG := Gb_pos S a₀ (n := n)
  have hcD : (0:ℝ) < 1 / (N * Gb n S a₀) := by positivity
  obtain ⟨DN, hNum⟩ := sampW_C11 X hN ω S (a₁ := a₁) hξ hξ1 ha₀ i (gd f)
    (fun j => gd_bound hB (X i ω) (X j ω))
  obtain ⟨DD, hDen⟩ := sampW_C11 X hN ω S (a₁ := a₁) hξ hξ1 ha₀ i (fun _ _ => (1:ℝ))
    (Bg := 1) (fun j => by simp)
  have hDi := hDen.inv (convex_Icc a₀ a₁) hcD
    (fun s hs => sampW_one_lower X hN ω S hξ hξ1 ha₀ hs.1 hi)
  have hm := (hNum.mul (convex_Icc a₀ a₁) hDi).const_mul (-(2 / (m₂ * ξ ^ 2)))
  have habs : |-(2 / (m₂ * ξ ^ 2))| = 2 / (m₂ * ξ ^ 2) := by
    rw [abs_neg, abs_of_pos (by positivity)]
  rw [habs] at hm
  refine ⟨_, (hm.mono (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_)).congr fun s => ?_⟩
  · unfold psiB0; ring
  · unfold psiB1; ring
  · unfold psiB2; ring
  · unfold LNK; rw [div_eq_mul_one_div (sampW X N (latK S (ξ / s)) (gd f) i ω)]

/-! ### Stage 4: composition with the conformal factor -/

theorem C11.comp {U V : Set ℝ} (hV : Convex ℝ V) {a a' φ φ' : ℝ → ℝ} {A0 A1 A2 B0 B1 B2 : ℝ}
    (ha : C11 V a a' A0 A1 A2) (hmap : ∀ τ ∈ V, a τ ∈ U) (h : C11 U φ φ' B0 B1 B2)
    (hB2' : 0 ≤ B2) :
    C11 V (fun τ => φ (a τ)) (fun τ => φ' (a τ) * a' τ) B0 (B1 * A1) (B2 * A1 * A1 + B1 * A2) := by
  refine ⟨fun τ hτ => (h.deriv (a τ) (hmap τ hτ)).comp τ (ha.deriv τ hτ), fun τ hτ =>
    h.b0 _ (hmap τ hτ), fun τ hτ => ?_, fun τ hτ σ hσ => ?_⟩
  · rw [abs_mul]
    exact mul_le_mul (h.b1 _ (hmap τ hτ)) (ha.b1 τ hτ) (abs_nonneg _) (h.B1_nonneg (hmap τ hτ))
  · have e : φ' (a τ) * a' τ - φ' (a σ) * a' σ
        = (φ' (a τ) - φ' (a σ)) * a' τ + φ' (a σ) * (a' τ - a' σ) := by ring
    rw [e]
    have hd := ha.lip0 hV hτ hσ
    have hB2 : 0 ≤ B2 * |a τ - a σ| :=
      (abs_nonneg _).trans (h.lip _ (hmap τ hτ) _ (hmap σ hσ))
    have h1 : |(φ' (a τ) - φ' (a σ)) * a' τ| ≤ B2 * (A1 * |τ - σ|) * A1 := by
      rw [abs_mul]
      refine mul_le_mul ((h.lip _ (hmap τ hτ) _ (hmap σ hσ)).trans ?_) (ha.b1 τ hτ) (abs_nonneg _)
        ?_
      · exact mul_le_mul_of_nonneg_left hd hB2'
      · exact mul_nonneg hB2' (mul_nonneg (ha.B1_nonneg hτ) (abs_nonneg _))
    have h2 : |φ' (a σ) * (a' τ - a' σ)| ≤ B1 * (A2 * |τ - σ|) := by
      rw [abs_mul]
      exact mul_le_mul (h.b1 _ (hmap σ hσ)) (ha.lip τ hτ σ hσ) (abs_nonneg _)
        (h.B1_nonneg (hmap σ hσ))
    calc _ ≤ |(φ' (a τ) - φ' (a σ)) * a' τ| + |φ' (a σ) * (a' τ - a' σ)| := abs_add_le _ _
      _ ≤ B2 * (A1 * |τ - σ|) * A1 + B1 * (A2 * |τ - σ|) := add_le_add h1 h2
      _ = (B2 * A1 * A1 + B1 * A2) * |τ - σ| := by ring


/-! ### Stage 5: derivative from the window statement; mean value step -/

/-- Mean value step: a derivative bound on `[p,q]` bounds every difference quotient. -/
theorem slope_le {F F' : ℝ → ℝ} {p q β : ℝ} (hd : ∀ τ ∈ Icc p q, HasDerivAt F (F' τ) τ)
    (hb : ∀ τ ∈ Icc p q, |F' τ| ≤ β) {τa τb : ℝ} (ha : τa ∈ Icc p q) (hb' : τb ∈ Icc p q)
    (hne : τb ≠ τa) : |(F τb - F τa) / (τb - τa)| ≤ β := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F) (f' := F')
    (fun x hx => (hd x hx).hasDerivWithinAt) (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx)
    (convex_Icc p q) ha hb'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hpos : 0 < |τb - τa| := abs_pos.2 (sub_ne_zero.2 hne)
  rw [abs_div, div_le_iff₀ hpos]; exact h

/-- **Derivative from the window statement.**  If `F'` is `M`-Lipschitz on `[p,q]` and all difference
quotients over pairs with `|τb − τa| ≥ η₀` are `≤ ε`, then `|F'(τ)| ≤ ε + M η₀` on `[p,q]`
(`2η₀ ≤ q − p`). -/
theorem deriv_from_window {F F' : ℝ → ℝ} {p q η₀ ε M : ℝ} (hη₀ : 0 < η₀) (hpq : 2 * η₀ ≤ q - p)
    (hd : ∀ τ ∈ Icc p q, HasDerivAt F (F' τ) τ)
    (hlip : ∀ s ∈ Icc p q, ∀ t ∈ Icc p q, |F' s - F' t| ≤ M * |s - t|) (hM : 0 ≤ M)
    (hwin : ∀ τa ∈ Icc p q, ∀ τb ∈ Icc p q, η₀ ≤ |τb - τa| →
      |(F τb - F τa) / (τb - τa)| ≤ ε) :
    ∀ τ ∈ Icc p q, |F' τ| ≤ ε + M * η₀ := by
  have key : ∀ u ∈ Icc p q, u + η₀ ∈ Icc p q → ∀ τ ∈ Icc u (u + η₀), |F' τ| ≤ ε + M * η₀ := by
    intro u hu hv τ hτ
    have hsub : Icc u (u + η₀) ⊆ Icc p q := Icc_subset_Icc hu.1 hv.2
    obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope F F' (by linarith : u < u + η₀)
      (fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => hd x (hsub (Ioo_subset_Icc_self hx)))
    have hw := hwin u hu (u + η₀) hv (by rw [show u + η₀ - u = η₀ by ring, abs_of_pos hη₀])
    rw [← hcs] at hw
    have hl := hlip τ (hsub hτ) c (hsub (Ioo_subset_Icc_self hc))
    have hdist : |τ - c| ≤ η₀ := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2, hc.1, hc.2]
    have htri : |F' τ| ≤ |F' c| + |F' τ - F' c| := by
      calc |F' τ| = |F' c + (F' τ - F' c)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have := mul_le_mul_of_nonneg_left hdist hM
    linarith
  intro τ hτ
  by_cases h : τ + η₀ ≤ q
  · exact key τ hτ ⟨by linarith [hτ.1], h⟩ τ ⟨le_rfl, by linarith⟩
  · push_neg at h
    exact key (τ - η₀) ⟨by linarith, by linarith [hτ.2]⟩ ⟨by linarith, by linarith [hτ.2]⟩ τ
      ⟨by linarith, by linarith⟩

/-! ### Stage 6: the time derivative of the N-point operator -/

theorem tc_nonneg {G K1 K2 Bg c : ℝ} (hG : 0 ≤ G) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hBg : 0 ≤ Bg)
    (hc : 0 < c) : 0 ≤ tc0 G Bg c ∧ 0 ≤ tc1 G K1 Bg c ∧ 0 ≤ tc2 G K1 K2 Bg c := by
  have hc' := hc.le
  refine ⟨?_, ?_, ?_⟩
  · unfold tc0; positivity
  · unfold tc1; positivity
  · unfold tc2; positivity

theorem psiB_nonneg {G K1 K2 B c cD m₂ ξ : ℝ} (hG : 0 ≤ G) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hB : 0 ≤ B) (hc : 0 < c) (hcD : 0 < cD) (hm₂ : 0 < m₂) (hξ : 0 < ξ) :
    0 ≤ psiB1 G K1 K2 B c cD m₂ ξ ∧ 0 ≤ psiB2 G K1 K2 B c cD m₂ ξ := by
  obtain ⟨a0, a1, a2⟩ := tc_nonneg hG hK1 hK2 (by linarith : (0:ℝ) ≤ 2 * B) hc
  obtain ⟨b0, b1, b2⟩ := tc_nonneg hG hK1 hK2 zero_le_one hc
  have hk : 0 ≤ 2 / (m₂ * ξ ^ 2) := by positivity
  have hcD' := hcD.le
  refine ⟨?_, ?_⟩
  · unfold psiB1; positivity
  · unfold psiB2; positivity

/-- The conformal factor as a C^{1,1} function on `ℝ` (HYPOTHESIS: `a'` is `L₂`-Lipschitz). -/
theorem a_C11 (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|) : C11 univ a a' a₁ La L₂ :=
  ⟨fun τ _ => hda τ, fun τ _ => by rw [abs_of_pos (lt_of_lt_of_le ha₀ (ha τ))]; exact ha₁ τ,
    fun τ _ => hLa τ, fun s _ t _ => hL2 s t⟩

/-- Constants of `τ ↦ L/a(τ)²`. -/
def popB0 (a₀ G₂ : ℝ) : ℝ := G₂ * (1 / (a₀ * a₀))
def popB1 (a₀ a₁ La G₂ : ℝ) : ℝ := G₂ * ((La * a₁ + a₁ * La) / (a₀ * a₀) ^ 2)
def popB2 (a₀ a₁ La L₂ G₂ : ℝ) : ℝ :=
  G₂ * ((L₂ * a₁ + 2 * (La * La) + a₁ * L₂) / (a₀ * a₀) ^ 2
    + 2 * (a₁ * a₁) * (La * a₁ + a₁ * La) ^ 2 / (a₀ * a₀) ^ 4)

theorem pop_C11 (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|) {L G₂ : ℝ} (hL : |L| ≤ G₂) :
    C11 univ (fun τ => L / a τ ^ 2)
      (fun τ => L * (-(a' τ * a τ + a τ * a' τ) / (a τ * a τ) ^ 2))
      (popB0 a₀ G₂) (popB1 a₀ a₁ La G₂) (popB2 a₀ a₁ La L₂ G₂) := by
  have haC := a_C11 a a' hda ha₀ ha ha₁ hLa hL2
  have hc : 0 < a₀ * a₀ := mul_pos ha₀ ha₀
  have hi := (haC.mul convex_univ haC).inv convex_univ hc
    (fun τ _ => mul_le_mul (ha τ) (ha τ) ha₀.le (ha₀.le.trans (ha τ)))
  have hm := hi.const_mul L
  have h0 := hi.B0_nonneg (mem_univ 0)
  have h1 := hi.B1_nonneg (mem_univ 0)
  have hL₂ : 0 ≤ L₂ := by
    have := hL2 1 0; simp at this; exact le_trans (abs_nonneg _) this
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 ≤ a₁ := ha₀.le.trans ((ha 0).trans (ha₁ 0))
  have h2 : 0 ≤ (L₂ * a₁ + 2 * (La * La) + a₁ * L₂) / (a₀ * a₀) ^ 2
      + 2 * (a₁ * a₁) * (La * a₁ + a₁ * La) ^ 2 / (a₀ * a₀) ^ 4 := by positivity
  refine (hm.mono ?_ ?_ ?_).congr fun τ => ?_
  · unfold popB0; exact mul_le_mul_of_nonneg_right hL h0
  · unfold popB1; exact mul_le_mul_of_nonneg_right hL h1
  · unfold popB2; exact mul_le_mul_of_nonneg_right hL h2
  · ring

/-- The total Lipschitz constant of the derivative of `τ ↦ L_N(τ) f(i) + lapG/a²`. -/
def Mtot (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a₀ a₁ La L₂ G₂ B ξ : ℝ) (N : ℕ) : ℝ :=
  psiB2 (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) B (1 / N)
      (1 / (N * Gb n S a₀)) (gam₂ n) ξ * La * La
    + psiB1 (Gb n S a₀) (3 / a₀ * Gb n S a₀) (18 / a₀ ^ 2 * Gb n S a₀) B (1 / N)
      (1 / (N * Gb n S a₀)) (gam₂ n) ξ * L₂
    + popB2 a₀ a₁ La L₂ G₂

/-- The conclusion for one index `i` and one sample point `ω`. -/
def DerivGood (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (p q BII C : ℝ) (i : ℕ) (ω : Ω) : Prop :=
  (∀ τ ∈ Icc p q, ∃ D, HasDerivAt (fun t => LNK X N (latK S (ξ / a t)) (gam₂ n) ξ f i ω) D τ
      ∧ |D - 2 * a' τ * lapG S f (X i ω) / a τ ^ 3| ≤ BII
      ∧ ∃ DL, HasDerivAt (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) DL τ
        ∧ |D - DL| ≤ BII + ξ ^ 2 * C)
  ∧ (∀ τa ∈ Icc p q, ∀ τb ∈ Icc p q, τb ≠ τa →
      |dqIK X N S a ξ f τa τb i ω| ≤ BII + ξ ^ 2 * C
      ∧ |dqIIK X N S a ξ f τa τb i ω| ≤ BII)

set_option maxHeartbeats 1600000 in
/-- **Deterministic core.**  Fix `ω`, `i < N`.  If the window inequalities hold for all pairs of
`[p,q]` with `|τb − τa| ≥ η₀`, then (1) `τ ↦ L_N(τ) f(i)` is differentiable at every `τ ∈ [p,q]`, its
derivative is within `BII = 2Er + 2ξ²C₂ + Mtot·η₀` of `2a'Δ_{g₀}f/a³ = −∂_τ(Δ_{g_τ} f)` and within
`BII + ξ²C₂` of `∂_τ L^τ_ξ f(X_i)`; (2) both difference-quotient inequalities hold for ALL pairs
`τa ≠ τb` of `[p,q]` with these bounds. -/
theorem deriv_det (hn : 1 ≤ n) (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) {i : ℕ} (hi : i < N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ B G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (hper : Per f)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    {p q η₀ Er : ℝ} (hη₀ : 0 < η₀) (hpq : 2 * η₀ ≤ q - p)
    (hwin : ∀ τa ∈ Icc p q, ∀ τb ∈ Icc p q, η₀ ≤ |τb - τa| →
      |dqIK X N S a ξ f τa τb i ω| ≤ 2 * Er
      ∧ |dqIIK X N S a ξ f τa τb i ω|
        ≤ 2 * Er + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
            (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (τb - τa)) :
    DerivGood X N S a a' ξ f p q
      (2 * Er + 2 * (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S)
        + Mtot n S a₀ a₁ La L₂ G₂ B ξ N * η₀)
      (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) i ω := by
  have hm₂ := gam₂_pos hn
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hG := Gb_pos S a₀ (n := n)
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have ha01 : a₀ ≤ a₁ := (ha 0).trans (ha₁ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hL₂ : 0 ≤ L₂ := by
    have := hL2 1 0; simp at this; exact le_trans (abs_nonneg _) this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hG₂0 : 0 ≤ G₂ := le_trans (abs_nonneg _) (hG₂ 0)
  have hk := radK_gauss (n := n)
  have hμ₄ : 0 ≤ gaμ₄ n := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hK₀ := hk.kern.mass_pos
  set C₂ := Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S with hC₂
  have hC2 : 0 ≤ C₂ := by rw [hC₂]; unfold Ctwo; positivity
  set Mt := Mtot n S a₀ a₁ La L₂ G₂ B ξ N with hMt
  set L := lapG S f (X i ω) with hLdef
  -- the sample operator in the scale and in time
  obtain ⟨Ψ', hΨ⟩ := psi_C11 X hN ω S (a₁ := a₁) hξ hξ1 ha₀ hm₂ hB hi
  obtain ⟨hp1, hp2⟩ := psiB_nonneg (G := Gb n S a₀) (K1 := 3 / a₀ * Gb n S a₀)
    (K2 := 18 / a₀ ^ 2 * Gb n S a₀) (B := B) (c := 1 / N) (cD := 1 / (N * Gb n S a₀))
    (m₂ := gam₂ n) (ξ := ξ) hG.le (by positivity) (by positivity) hB0 (by positivity)
    (by positivity) hm₂ hξ
  have haC := a_C11 a a' hda ha₀ ha ha₁ hLa hL2
  have hcomp := haC.comp (U := Icc a₀ a₁) convex_univ (fun τ _ => ⟨ha τ, ha₁ τ⟩) hΨ hp2
  have hpop := pop_C11 a a' hda ha₀ ha ha₁ hLa hL2 (L := L) (hG₂ _)
  have hF := hcomp.add hpop
  have hMt0 : 0 ≤ Mt := by
    have : 0 ≤ popB2 a₀ a₁ La L₂ G₂ := by
      have ha₁0 : 0 ≤ a₁ := ha₀.le.trans ha01
      unfold popB2; positivity
    rw [hMt]; unfold Mtot
    have := mul_nonneg (mul_nonneg hp2 hLa0) hLa0
    have := mul_nonneg hp1 hL₂
    linarith
  -- the window statement for `F_II`
  have hwinII : ∀ τa ∈ Icc p q, ∀ τb ∈ Icc p q, η₀ ≤ |τb - τa| →
      |((LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω + L / a τb ^ 2)
          - (LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω + L / a τa ^ 2)) / (τb - τa)|
        ≤ 2 * Er + 2 * (ξ ^ 2 * C₂) := by
    intro τa hτa τb hτb hη
    have h := (hwin τa hτa τb hτb hη).2
    rw [dqIIK_eq] at h
    have hpe : popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S) C₂ (τb - τa) ≤ ξ ^ 2 * C₂ := by
      unfold popErr; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg ξ)
    exact h.trans (by linarith)
  have hderII := deriv_from_window hη₀ hpq (fun τ _ => hF.deriv τ (mem_univ τ))
    (fun s _ t _ => hF.lip s (mem_univ s) t (mem_univ t)) hMt0 hwinII
  -- identification of the derivative of the population part
  have hpopd : ∀ τ, L * (-(a' τ * a τ + a τ * a' τ) / (a τ * a τ) ^ 2)
      = -(2 * a' τ * L / a τ ^ 3) := fun τ => by
    have := (hpos τ).ne'; field_simp; ring
  have hD1 : ∀ τ ∈ Icc p q, |Ψ' (a τ) * a' τ - 2 * a' τ * L / a τ ^ 3|
      ≤ 2 * Er + 2 * (ξ ^ 2 * C₂) + Mt * η₀ := fun τ hτ => by
    have := hderII τ hτ
    rw [hpopd τ] at this
    rwa [show Ψ' (a τ) * a' τ + -(2 * a' τ * L / a τ ^ 3)
      = Ψ' (a τ) * a' τ - 2 * a' τ * L / a τ ^ 3 by ring] at this
  -- the population derivative
  have hdot : ∀ τ, ∃ DL, HasDerivAt (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) DL τ
      ∧ |DL - 2 * a' τ * L / a τ ^ 3| ≤ ξ ^ 2 * C₂ := fun τ =>
    dotL_flat_full hk hm₂ hf hper hM hM₄ S a a' hda ha₀ ha hLa hξ (X i ω) τ
  have hDI : ∀ τ ∈ Icc p q, ∀ DL, |DL - 2 * a' τ * L / a τ ^ 3| ≤ ξ ^ 2 * C₂ →
      |Ψ' (a τ) * a' τ - DL| ≤ 2 * Er + 2 * (ξ ^ 2 * C₂) + Mt * η₀ + ξ ^ 2 * C₂ := by
    intro τ hτ DL hDL
    have h1 := hD1 τ hτ
    calc |Ψ' (a τ) * a' τ - DL|
        = |(Ψ' (a τ) * a' τ - 2 * a' τ * L / a τ ^ 3) - (DL - 2 * a' τ * L / a τ ^ 3)| := by
          congr 1; ring
      _ ≤ |Ψ' (a τ) * a' τ - 2 * a' τ * L / a τ ^ 3| + |DL - 2 * a' τ * L / a τ ^ 3| :=
          abs_sub _ _
      _ ≤ _ := add_le_add h1 hDL
  refine ⟨fun τ hτ => ⟨Ψ' (a τ) * a' τ, hcomp.deriv τ (mem_univ τ), hD1 τ hτ, ?_⟩,
    fun τa hτa τb hτb hne => ⟨?_, ?_⟩⟩
  · obtain ⟨DL, hDL, hb⟩ := hdot τ
    exact ⟨DL, hDL, hDI τ hτ DL hb⟩
  · rw [dqIK_eq]
    refine slope_le (F := fun τ => LNK X N (latK S (ξ / a τ)) (gam₂ n) ξ f i ω
        - Lmet gauss (gam₂ n) S (a τ) ξ f (X i ω))
      (F' := fun τ => Ψ' (a τ) * a' τ
        - deriv (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) τ)
      (fun τ hτ => ?_) (fun τ hτ => ?_) hτa hτb hne
    · obtain ⟨DL, hDL, -⟩ := hdot τ
      show HasDerivAt _ (Ψ' (a τ) * a' τ
        - deriv (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) τ) τ
      rw [hDL.deriv]
      exact (hcomp.deriv τ (mem_univ τ)).sub hDL
    · obtain ⟨DL, hDL, hb⟩ := hdot τ
      show |Ψ' (a τ) * a' τ - deriv (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) τ| ≤ _
      rw [hDL.deriv]
      exact hDI τ hτ DL hb
  · rw [dqIIK_eq]
    refine slope_le (F := fun τ => LNK X N (latK S (ξ / a τ)) (gam₂ n) ξ f i ω + L / a τ ^ 2)
      (fun τ hτ => hF.deriv τ (mem_univ τ)) (fun τ hτ => ?_) hτa hτb hne
    exact hderII τ hτ

/-- **The time derivative of the flat N-point operator for the periodised Gaussian kernel, on one
event for a whole window, and all pairs of times.**  Hypotheses as in `flat_npoint_lattice_window`,
and in addition (HYPOTHESIS) `a'` is `L₂`-Lipschitz and `2η₀ ≤ q − p`.  Outside an event of probability
at most the bound of `flat_npoint_lattice_window`, for every `i < N`: `τ ↦ L_N(τ) f(i)` is
differentiable at every `τ ∈ [p, q]` with
`|∂_τ L_N f(i) − 2a'(τ)Δ_{g₀}f(X_i)/a(τ)³| ≤ BII := 2E + 2ξ²C₂ + Mtot·η₀` and
`|∂_τ L_N f(i) − ∂_τ L^τ_ξ f(X_i)| ≤ BII + ξ²C₂`; and for ALL pairs `τa ≠ τb` of `[p, q]`
`|dqIK| ≤ BII + ξ²C₂`, `|dqIIK| ≤ BII`.  `Mtot` is explicit and contains powers of `N` and negative
powers of `ξ` (from the self-term lower bound of the normalisations). -/
theorem flat_npoint_lattice_deriv (hn : 1 ≤ n) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * L ≤ N * ξ ^ n)
    {p q w η₀ : ℝ} (hw : 0 < w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀) (hpq : 2 * η₀ ≤ q - p)
    (hwc : cIk a₀ a₁ La * Gb n S a₀ * w ≤ P0c S a₁ * ξ ^ n / 4)
    (hwE : 4 * (LsK n S a₀ a₁ La Lip ξ (P0c S a₁ * ξ ^ n / 4)
            + (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * w
          ≤ rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ * η₀) :
    μ.real {ω | ∃ i < N, ¬ DerivGood X N S a a' ξ f p q
        (2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ
          + 2 * (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S)
          + Mtot n S a₀ a₁ La L₂ G₂ B ξ N * η₀)
        (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) i ω}
      ≤ ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) * (N * (2 * Real.exp (-L)))
        + ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
  have hN0 : 0 < N := by omega
  refine (measureReal_mono ?_).trans (flat_npoint_lattice_window hn X h_indep hX hlaw N hN hf hM
    hM₄ hper hLip0 hLip hB S hG₂ a a' hda ha₀ ha ha₁ hLa hξ hξ1 hL1 hNL hw hη₀ h4 hwc hwE)
  intro ω hω
  obtain ⟨i, hi, hfail⟩ := hω
  by_contra hnot
  apply hfail
  refine deriv_det hn X hN0 ω hi hf hM hM₄ hper hB S hG₂ a a' hda ha₀ ha ha₁ hLa hL2 hξ hξ1 hη₀ hpq
    (fun τa hτa τb hτb hη => ?_)
  by_contra hc
  exact hnot ⟨τa, hτa, τb, hτb, hη, i, hi, hc⟩

end CTG.FlatNPointLatticeDeriv
