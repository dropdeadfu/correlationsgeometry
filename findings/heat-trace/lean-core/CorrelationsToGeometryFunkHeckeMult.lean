/-
Twenty-first file: multiplicity at least `2l+1` of the eigenvalue `sphS ξ l` of the population walk on `S²`.
Imports `CorrelationsToGeometryFunkHecke` (compiled module under `.tools/leanbuild`); namespace
`CTG.FunkHecke.Mult`; check with `./check_funk_hecke_mult.sh`.
The `2l+1` complex functions `(a_j·y)^l`, `a_j = e₀ + i(0, cos φ_j, sin φ_j)`, are linearly independent on the
sphere (`F_indep`, `F_linearIndependent`; Vandermonde), each is an eigenfunction of the zonal operator
(`F_eigen`), and `Pinf_multiplicity`: there are `2l+1` real functions on `S²`, linearly independent over `ℝ`,
with `Pinf (gk ξ) f = sphS ξ l · f`.
NOT formalised: the upper bound (multiplicity exactly `2l+1`), that the `s_l` are pairwise distinct,
orthogonality across degrees, completeness, the identification with spherical harmonics and the eigenvalue
`l(l+1)` of the Laplacian, the limit `N → ∞`.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHecke

/-!
# A131: multiplicity of the eigenvalue `sphS ξ l` of the population walk on `S²`

For the isotropic vectors `a_j = e₀ + i (0, cos φ_j, sin φ_j)`, `φ_j = j/(2l+1)`, `j < 2l+1`,
the functions `F_j(y) = (a_j·y)^l` on `S²` are linearly independent over `ℂ` (`F_linearIndependent`;
proof: homogeneity, two polynomial identities, Vandermonde).  From this, `2l+1` real functions in the
real span of `Re F_j, Im F_j` are linearly independent over `ℝ` (`real_extract`), and every element
of that span is an eigenfunction of `P_∞` with eigenvalue `sphS ξ l` (`Pinf_multiplicity`):
the eigenvalue `sphS ξ l` has multiplicity at least `2l+1`.

NOT in this file: the upper bound (multiplicity exactly `2l+1`), orthogonality between degrees,
completeness of the eigenfunctions in `L²(S²)`, identification of the span with the spherical
harmonics of degree `l`.
-/

open MeasureTheory Set Metric Real
open scoped RealInnerProductSpace Pointwise

namespace CTG.FunkHecke.Mult

open CTG.FunkHecke

/-! ## The family -/

noncomputable def eZero : E3 := WithLp.toLp 2 ![1, 0, 0]
noncomputable def qv (φ : ℝ) : E3 := WithLp.toLp 2 ![0, Real.cos φ, Real.sin φ]
noncomputable def pt (t a : ℝ) : E3 := WithLp.toLp 2 ![t, Real.cos a, Real.sin a]

@[simp] theorem eZero_0 : eZero 0 = 1 := rfl
@[simp] theorem eZero_1 : eZero 1 = 0 := rfl
@[simp] theorem eZero_2 : eZero 2 = 0 := rfl
@[simp] theorem qv_0 (φ : ℝ) : qv φ 0 = 0 := rfl
@[simp] theorem qv_1 (φ : ℝ) : qv φ 1 = Real.cos φ := rfl
@[simp] theorem qv_2 (φ : ℝ) : qv φ 2 = Real.sin φ := rfl
@[simp] theorem pt_0 (t a : ℝ) : pt t a 0 = t := rfl
@[simp] theorem pt_1 (t a : ℝ) : pt t a 1 = Real.cos a := rfl
@[simp] theorem pt_2 (t a : ℝ) : pt t a 2 = Real.sin a := rfl

/-- The angles `φ_j = j/(2l+1)`. -/
noncomputable def angle (l : ℕ) (j : Fin (2 * l + 1)) : ℝ := (j : ℝ) / (2 * l + 1)

/-- The complex functions `F_j(y) = (a_j·y)^l`. -/
noncomputable def F (l : ℕ) (j : Fin (2 * l + 1)) (y : S2) : ℂ :=
  cdot eZero (qv (angle l j)) y ^ l

theorem isotropic_family (φ : ℝ) : Isotropic eZero (qv φ) := by
  refine ⟨?_, ?_⟩
  · simp only [inner3, eZero_0, eZero_1, eZero_2, qv_0, qv_1, qv_2]
    nlinarith [Real.sin_sq_add_cos_sq φ]
  · simp only [inner3, eZero_0, eZero_1, eZero_2, qv_0, qv_1, qv_2]; ring

theorem cdot_pt (φ t a : ℝ) :
    cdot eZero (qv φ) (pt t a) = (t : ℂ) + Complex.I * (Real.cos (a - φ) : ℂ) := by
  simp only [cdot, inner3, eZero_0, eZero_1, eZero_2, qv_0, qv_1, qv_2, pt_0, pt_1, pt_2]
  rw [Real.cos_sub]; push_cast; ring

theorem cdot_smul (p q y : E3) (s : ℝ) : cdot p q (s • y) = (s : ℂ) * cdot p q y := by
  simp only [cdot, real_inner_smul_right]; push_cast; ring

theorem pt_norm (t a : ℝ) : ‖pt t a‖ = √(t ^ 2 + 1) := by
  have h := EuclideanSpace.real_norm_sq_eq (pt t a)
  rw [Fin.sum_univ_three, pt_0, pt_1, pt_2] at h
  rw [← Real.sqrt_sq (norm_nonneg (pt t a)), h]
  congr 1; nlinarith [Real.sin_sq_add_cos_sq a]

/-- The point `pt t a / ‖pt t a‖` of `S²`. -/
noncomputable def ptS (t a : ℝ) : S2 :=
  ⟨(√(t ^ 2 + 1))⁻¹ • pt t a, by
    rw [mem_sphere_zero_iff_norm, norm_smul, pt_norm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 (by positivity)))]
    exact inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne'⟩

theorem F_ptS (l : ℕ) (j : Fin (2 * l + 1)) (t a : ℝ) :
    F l j (ptS t a) = ((√(t ^ 2 + 1))⁻¹ : ℂ) ^ l
      * ((t : ℂ) + Complex.I * (Real.cos (a - angle l j) : ℂ)) ^ l := by
  unfold F ptS
  simp only
  rw [cdot_smul, cdot_pt, mul_pow]
  push_cast; ring

/-! ## Polynomial identities and Vandermonde -/

theorem poly_vanish {n l : ℕ} (c R : Fin n → ℂ) (h : ∀ m : ℕ, ∑ j, c j * ((m : ℂ) + R j) ^ l = 0)
    (k : ℕ) (hk : k ≤ l) : ∑ j, c j * R j ^ k = 0 := by
  set Q : Polynomial ℂ :=
    ∑ j, Polynomial.C (c j) * (Polynomial.X + Polynomial.C (R j)) ^ l with hQdef
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℂ)) Nat.cast_injective
    intro m
    show Polynomial.IsRoot Q _
    rw [Polynomial.IsRoot.def, hQdef, Polynomial.eval_finset_sum]
    simpa using h m
  have hc := congrArg (fun p => p.coeff (l - k)) hQ
  simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow, Polynomial.coeff_zero, Nat.sub_sub_self hk] at hc
  have hch : ((l.choose (l - k) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le l k)).ne'
  have h2 : (∑ j, c j * R j ^ k) * ((l.choose (l - k) : ℕ) : ℂ) = 0 := by
    rw [Finset.sum_mul, ← hc]; exact Finset.sum_congr rfl (fun j _ => by ring)
  exact (mul_eq_zero.1 h2).resolve_right hch

theorem lin_pow_coeff (z w : ℂ) (hz : z ≠ 0) (k : ℕ) :
    ((Polynomial.C z * Polynomial.X + Polynomial.C w) ^ k).coeff k = z ^ k ∧
    ((Polynomial.C z * Polynomial.X + Polynomial.C w) ^ k).coeff 0 = w ^ k := by
  have e : Polynomial.C z * Polynomial.X + Polynomial.C w
      = Polynomial.C z * (Polynomial.X + Polynomial.C (w / z)) := by
    rw [mul_add, ← Polynomial.C_mul, mul_div_cancel₀ _ hz]
  rw [e, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow, Polynomial.coeff_X_add_C_pow]
  refine ⟨?_, ?_⟩
  · simp
  · simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [← mul_pow, mul_div_cancel₀ _ hz]

theorem poly_vanish2 {n k : ℕ} (c Z : Fin n → ℂ) (hZ : ∀ j, Z j ≠ 0) (pts : ℕ → ℂ)
    (hinj : Function.Injective pts)
    (h : ∀ a, ∑ j, c j * (Z j * pts a + (Z j)⁻¹) ^ k = 0) :
    (∑ j, c j * Z j ^ k = 0) ∧ (∑ j, c j * (Z j)⁻¹ ^ k = 0) := by
  set Q : Polynomial ℂ := ∑ j, Polynomial.C (c j)
    * (Polynomial.C (Z j) * Polynomial.X + Polynomial.C (Z j)⁻¹) ^ k with hQdef
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem hinj
    intro a
    show Polynomial.IsRoot Q _
    rw [Polynomial.IsRoot.def, hQdef, Polynomial.eval_finset_sum]
    simpa using h a
  refine ⟨?_, ?_⟩
  · have hc := congrArg (fun p => p.coeff k) hQ
    simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero] at hc
    rw [← hc]
    exact Finset.sum_congr rfl (fun j _ => by rw [(lin_pow_coeff _ _ (hZ j) k).1])
  · have hc := congrArg (fun p => p.coeff 0) hQ
    simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_zero] at hc
    rw [← hc]
    exact Finset.sum_congr rfl (fun j _ => by rw [(lin_pow_coeff _ _ (hZ j) k).2])

theorem vander_zero {l : ℕ} (c Z : Fin (2 * l + 1) → ℂ) (hZ : ∀ j, Z j ≠ 0)
    (hinj : Function.Injective Z)
    (hp : ∀ k ≤ l, ∑ j, c j * Z j ^ k = 0) (hm : ∀ k ≤ l, ∑ j, c j * (Z j)⁻¹ ^ k = 0) :
    c = 0 := by
  set d : Fin (2 * l + 1) → ℂ := fun j => c j * (Z j)⁻¹ ^ l with hd_def
  have hd : Matrix.vecMul d (Matrix.vandermonde Z) = 0 := by
    funext m
    have hmlt := m.isLt
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply, hd_def]
    by_cases hml : l ≤ (m : ℕ)
    · rw [← hp ((m : ℕ) - l) (by omega)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hj := hZ j
      have e : Z j ^ (m : ℕ) = Z j ^ ((m : ℕ) - l) * Z j ^ l := by
        rw [← pow_add, Nat.sub_add_cancel hml]
      rw [e, inv_pow]; field_simp
    · rw [← hm (l - (m : ℕ)) (by omega)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hj := hZ j
      have e : (Z j)⁻¹ ^ l = (Z j)⁻¹ ^ (l - (m : ℕ)) * (Z j)⁻¹ ^ (m : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      rw [e, inv_pow, inv_pow]; field_simp
  have hdet : (Matrix.vandermonde Z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hinj
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hd
  funext j
  have := congrFun h0 j
  simp only [hd_def, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (inv_ne_zero (hZ j)))

/-! ## Linear independence of the `F_j` over `ℂ` -/

theorem exp_I_inj {x y : ℝ} (hx : x ∈ Set.Icc 0 π) (hy : y ∈ Set.Icc 0 π)
    (h : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I)) : x = y := by
  have := congrArg Complex.re h
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at this
  exact Real.injOn_cos hx hy this

theorem angle_mem (l : ℕ) (j : Fin (2 * l + 1)) : angle l j ∈ Set.Icc 0 π := by
  have hj := j.isLt
  have hpos : (0 : ℝ) < 2 * l + 1 := by positivity
  have hjl : (j : ℝ) < 2 * l + 1 := by exact_mod_cast hj
  refine ⟨div_nonneg (Nat.cast_nonneg _) hpos.le, ?_⟩
  unfold angle
  rw [div_le_iff₀ hpos]
  nlinarith [Real.pi_gt_three]

/-- The nodes `Z_j = e^{-iφ_j}`. -/
noncomputable def Zn (l : ℕ) (j : Fin (2 * l + 1)) : ℂ :=
  (Complex.exp (((angle l j : ℝ) : ℂ) * Complex.I))⁻¹

theorem Zn_ne (l : ℕ) (j : Fin (2 * l + 1)) : Zn l j ≠ 0 :=
  inv_ne_zero (Complex.exp_ne_zero _)

theorem Zn_inj (l : ℕ) : Function.Injective (Zn l) := by
  intro j k h
  unfold Zn at h
  have h' := inv_injective h
  have := exp_I_inj (angle_mem l j) (angle_mem l k) h'
  have hpos : (2 * (l : ℝ) + 1) ≠ 0 := by positivity
  unfold angle at this
  rw [div_left_inj' hpos] at this
  exact Fin.ext (by exact_mod_cast this)

/-- Evaluation angles `α_a = 1/(a+1)`. -/
noncomputable def alp (a : ℕ) : ℝ := 1 / ((a : ℝ) + 1)

noncomputable def Wn (a : ℕ) : ℂ := Complex.exp (((alp a : ℝ) : ℂ) * Complex.I)

noncomputable def pts (a : ℕ) : ℂ := Complex.exp (((2 * alp a : ℝ) : ℂ) * Complex.I)

theorem Wn_sq (a : ℕ) : Wn a ^ 2 = pts a := by
  unfold Wn pts
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

theorem pts_inj : Function.Injective pts := by
  intro a b h
  have mem : ∀ c : ℕ, 2 * alp c ∈ Set.Icc 0 π := by
    intro c
    have hc : (1 : ℝ) ≤ (c : ℝ) + 1 := by have := c.cast_nonneg (α := ℝ); linarith
    refine ⟨by unfold alp; positivity, ?_⟩
    have : alp c ≤ 1 := by unfold alp; rw [div_le_one (by linarith)]; exact hc
    nlinarith [Real.pi_gt_three]
  have := exp_I_inj (mem a) (mem b) h
  unfold alp at this
  have ha : ((a : ℝ) + 1) ≠ 0 := by positivity
  have hb : ((b : ℝ) + 1) ≠ 0 := by positivity
  field_simp at this
  exact_mod_cast (by linarith : (a : ℝ) = b)

theorem cos_eq_Z (a : ℕ) (φ : ℝ) :
    ((Real.cos (alp a - φ) : ℝ) : ℂ) =
      (Wn a * (Complex.exp ((φ : ℂ) * Complex.I))⁻¹ +
        (Wn a * (Complex.exp ((φ : ℂ) * Complex.I))⁻¹)⁻¹) / 2 := by
  have h1 : Wn a * (Complex.exp ((φ : ℂ) * Complex.I))⁻¹
      = Complex.exp (((alp a - φ : ℝ) : ℂ) * Complex.I) := by
    unfold Wn
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h1, ← Complex.exp_neg, Complex.ofReal_cos]
  have h2 := Complex.two_cos (((alp a - φ : ℝ) : ℂ))
  rw [neg_mul] at h2
  linear_combination h2 / 2

/-- **The `2l+1` functions `F_j` are linearly independent over `ℂ`** (as functions on `S²`). -/
theorem F_indep (l : ℕ) (c : Fin (2 * l + 1) → ℂ) (h : ∀ y : S2, ∑ j, c j * F l j y = 0) :
    c = 0 := by
  set R : ℕ → Fin (2 * l + 1) → ℂ := fun a j => (Wn a * Zn l j + (Wn a * Zn l j)⁻¹) / 2
    with hR
  -- step 1: homogeneity
  have h1 : ∀ a (m : ℕ), ∑ j, c j * ((m : ℂ) + Complex.I * R a j) ^ l = 0 := by
    intro a m
    have hy := h (ptS (m : ℝ) (alp a))
    simp only [F_ptS] at hy
    have hs : ((√((m : ℝ) ^ 2 + 1))⁻¹ : ℂ) ^ l ≠ 0 := by
      apply pow_ne_zero; apply inv_ne_zero
      exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
    have e : ∑ j, c j * (((√((m : ℝ) ^ 2 + 1))⁻¹ : ℂ) ^ l
        * (((m : ℝ) : ℂ) + Complex.I * (Real.cos (alp a - angle l j) : ℂ)) ^ l)
        = ((√((m : ℝ) ^ 2 + 1))⁻¹ : ℂ) ^ l
          * ∑ j, c j * ((m : ℂ) + Complex.I * R a j) ^ l := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [cos_eq_Z]; simp only [hR, Zn]; push_cast; ring
    rw [e] at hy
    exact (mul_eq_zero.1 hy).resolve_left hs
  -- step 2: polynomial in the first coordinate
  have h2 : ∀ a, ∀ k ≤ l, ∑ j, c j * R a j ^ k = 0 := by
    intro a k hk
    have := poly_vanish c (fun j => Complex.I * R a j) (h1 a) k hk
    have hIk : Complex.I ^ k ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    have e : ∑ j, c j * (Complex.I * R a j) ^ k = Complex.I ^ k * ∑ j, c j * R a j ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by rw [mul_pow]; ring)
    rw [e] at this
    exact (mul_eq_zero.1 this).resolve_left hIk
  -- step 3: polynomial on the circle
  have h3 : ∀ k ≤ l, ∀ a, ∑ j, c j * (Zn l j * pts a + (Zn l j)⁻¹) ^ k = 0 := by
    intro k hk a
    have hW : Wn a ≠ 0 := Complex.exp_ne_zero _
    have e : ∑ j, c j * (Zn l j * pts a + (Zn l j)⁻¹) ^ k
        = (2 * Wn a) ^ k * ∑ j, c j * R a j ^ k := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_)
      have hZ := Zn_ne l j
      have e2 : Zn l j * pts a + (Zn l j)⁻¹ = 2 * Wn a * R a j := by
        simp only [hR, ← Wn_sq]; field_simp
      rw [e2, mul_pow]; ring
    rw [e, h2 a k hk, mul_zero]
  have h4 : ∀ k ≤ l, (∑ j, c j * Zn l j ^ k = 0) ∧ (∑ j, c j * (Zn l j)⁻¹ ^ k = 0) :=
    fun k hk => poly_vanish2 c (Zn l) (Zn_ne l) pts pts_inj (h3 k hk)
  exact vander_zero c (Zn l) (Zn_ne l) (Zn_inj l) (fun k hk => (h4 k hk).1)
    (fun k hk => (h4 k hk).2)

theorem F_linearIndependent (l : ℕ) : LinearIndependent ℂ (F l) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have := F_indep l g (fun y => by
    have := congrFun hg y
    simpa [Finset.sum_apply] using this)
  exact fun i => congrFun this i

/-! ## From complex to real independence -/

theorem real_extract {X : Type*} {n : ℕ} (u v : Fin n → X → ℝ)
    (h : ∀ c : Fin n → ℂ,
      (∀ x, ∑ j, c j * ((u j x : ℂ) + Complex.I * (v j x : ℂ)) = 0) → c = 0) :
    ∃ e : Fin n → X → ℝ, LinearIndependent ℝ e ∧
      ∀ i, e i ∈ Submodule.span ℝ (Set.range (Sum.elim u v)) := by
  set W := Submodule.span ℝ (Set.range (Sum.elim u v)) with hW
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hu : ∀ j, u j ∈ W := fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hv : ∀ j, v j ∈ W := fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  let φ1 : (Fin n → ℂ) →ₗ[ℝ] (X → ℝ) := ∑ j, ((Complex.reLm.comp (LinearMap.proj j)).smulRight
      (u j) - (Complex.imLm.comp (LinearMap.proj j)).smulRight (v j))
  let φ2 : (Fin n → ℂ) →ₗ[ℝ] (X → ℝ) := ∑ j, ((Complex.reLm.comp (LinearMap.proj j)).smulRight
      (v j) + (Complex.imLm.comp (LinearMap.proj j)).smulRight (u j))
  have e1 : ∀ c, φ1 c = ∑ j, ((c j).re • u j - (c j).im • v j) := by
    intro c; simp [φ1]
  have e2 : ∀ c, φ2 c = ∑ j, ((c j).re • v j + (c j).im • u j) := by
    intro c; simp [φ2]
  have m1 : ∀ c, φ1 c ∈ W := fun c => by
    rw [e1]
    exact Submodule.sum_mem _ (fun j _ => Submodule.sub_mem _ (Submodule.smul_mem _ _ (hu j))
      (Submodule.smul_mem _ _ (hv j)))
  have m2 : ∀ c, φ2 c ∈ W := fun c => by
    rw [e2]
    exact Submodule.sum_mem _ (fun j _ => Submodule.add_mem _ (Submodule.smul_mem _ _ (hv j))
      (Submodule.smul_mem _ _ (hu j)))
  let Φ : (Fin n → ℂ) →ₗ[ℝ] W × W :=
    (LinearMap.codRestrict W φ1 m1).prod (LinearMap.codRestrict W φ2 m2)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : φ1 c = 0 := by
      have := congrArg (fun p => ((p.1 : W) : X → ℝ)) hc
      simpa [Φ] using this
    have h2 : φ2 c = 0 := by
      have := congrArg (fun p => ((p.2 : W) : X → ℝ)) hc
      simpa [Φ] using this
    apply h; intro x
    have hx1 := congrFun h1 x
    have hx2 := congrFun h2 x
    rw [e1] at hx1; rw [e2] at hx2
    simp only [Finset.sum_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hx1 hx2
    apply Complex.ext
    · simp only [Complex.re_sum, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.zero_re]
      convert hx1 using 1; exact Finset.sum_congr rfl (fun j _ => by ring)
    · simp only [Complex.im_sum, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.zero_im]
      convert hx2 using 1; exact Finset.sum_congr rfl (fun j _ => by ring)
  have hfin : Module.finrank ℝ (Fin n → ℂ) ≤ Module.finrank ℝ (W × W) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_pi_fintype] at hfin
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hfin
  have hn : n ≤ Module.finrank ℝ W := by omega
  let b := Module.finBasis ℝ W
  refine ⟨fun i => ((b (Fin.castLE hn i) : W) : X → ℝ), ?_, fun i => (b _).2⟩
  exact (b.linearIndependent.comp _ (Fin.castLE_injective hn)).map' W.subtype
    (Submodule.ker_subtype W)

/-! ## Eigenfunctions -/

theorem integrable_cont (f : S2 → ℝ) (hf : Continuous f) : Integrable f sigma := by
  haveI : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => hC y (Set.mem_univ y))

/-- Imaginary-part form of `zonalOp_harmonic`. -/
theorem zonalOp_harmonic_im (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ t, |g t| ≤ C)
    (p q : E3) (h : Isotropic p q) (l : ℕ) (x : S2) :
    zonalOp g (fun y => (cdot p q y ^ l).im) x
      = ((1/2) * ∫ t in (-1:ℝ)..1, g t * legP l t) * (cdot p q x ^ l).im := by
  unfold zonalOp
  have hint : Integrable (fun y : S2 => (g ⟪(x : E3), (y : E3)⟫ : ℂ) * cdot p q y ^ l) sigma := by
    refine Integrable.of_bound ?_ (C * (‖p‖ + ‖q‖) ^ l) (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Complex.measurable_ofReal.comp (hg.comp
        (continuous_const.inner continuous_subtype_val).measurable)).mul
        (((continuous_cdot p q).comp continuous_subtype_val).measurable.pow_const l)).aestronglyMeasurable
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hC ⟪(x : E3), (y : E3)⟫
      have h2 : ‖cdot p q y‖ ≤ ‖p‖ + ‖q‖ := norm_cdot_le p q _ (mem_sphere_zero_iff_norm.1 y.2)
      exact mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) h2 l) (by positivity)
        (le_trans (abs_nonneg _) h1)
  have e : ∀ y : S2, g ⟪(x : E3), (y : E3)⟫ * (cdot p q y ^ l).im
      = RCLike.im ((g ⟪(x : E3), (y : E3)⟫ : ℂ) * cdot p q y ^ l) := by
    intro y; rw [RCLike.im_to_complex, Complex.im_ofReal_mul]
  calc ∫ y, g ⟪(x : E3), (y : E3)⟫ * (cdot p q y ^ l).im ∂sigma
      = (∫ y, (g ⟪(x : E3), (y : E3)⟫ : ℂ) * cdot p q y ^ l ∂sigma).im := by
        simp_rw [e]; exact integral_im hint
    _ = _ := by rw [funk_hecke g hg C hC p q h l x, Complex.im_mul_ofReal]; ring

/-- From the eigen-equation of `T_g` to that of `P_∞`. -/
theorem Pinf_of_eigen (ξ : ℝ) (l : ℕ) (f : S2 → ℝ) (x : S2)
    (hf : zonalOp (gk ξ) f x = ((1/2) * ∫ t in (-1:ℝ)..1, gk ξ t * legP l t) * f x) :
    Pinf (gk ξ) f x = sphS ξ l * f x := by
  have h0 : ∫ t in (-1:ℝ)..1, gk ξ t = sphZ ξ := by
    have := zonal_weight ξ (fun _ => 1) continuous_const
    simpa only [mul_one] using this
  have hl : ∫ t in (-1:ℝ)..1, gk ξ t * legP l t = sphI ξ (fun θ => legP l (Real.cos θ)) :=
    zonal_weight ξ (legP l) (legP_continuous l)
  have hZ := sphZ_pos ξ
  unfold Pinf
  rw [hf, zonalOp_const _ (gk_continuous ξ).measurable, h0, hl]
  unfold sphS sphE
  field_simp

/-- **Multiplicity at least `2l+1`.**  For every `l` and `ξ` there are `2l+1` real functions on `S²`,
linearly independent over `ℝ`, each an eigenfunction of the population walk `P_∞` (angular Gaussian
kernel) with eigenvalue `sphS ξ l`. -/
theorem Pinf_multiplicity (ξ : ℝ) (l : ℕ) :
    ∃ e : Fin (2 * l + 1) → (S2 → ℝ), LinearIndependent ℝ e ∧
      ∀ i x, Pinf (gk ξ) (e i) x = sphS ξ l * e i x := by
  set u : Fin (2 * l + 1) → S2 → ℝ := fun j y => (cdot eZero (qv (angle l j)) y ^ l).re with hu
  set v : Fin (2 * l + 1) → S2 → ℝ := fun j y => (cdot eZero (qv (angle l j)) y ^ l).im with hv
  obtain ⟨e, he, hspan⟩ := real_extract u v (fun c hc => F_indep l c (fun y => by
    have := hc y
    rw [← this]; refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    simp only [hu, hv, F]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm))
  set μ := (1/2) * ∫ t in (-1:ℝ)..1, gk ξ t * legP l t with hμ
  have hint : ∀ f : S2 → ℝ, Continuous f → ∀ x : S2,
      Integrable (fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫ * f y) sigma := fun f hf x =>
    integrable_cont _ (((gk_continuous ξ).comp
      (continuous_const.inner continuous_subtype_val)).mul hf)
  have key : ∀ f ∈ Submodule.span ℝ (Set.range (Sum.elim u v)),
      Continuous f ∧ ∀ x, zonalOp (gk ξ) f x = μ * f x := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨s, rfl⟩ := hg
      rcases s with j | j
      · refine ⟨Complex.continuous_re.comp
          (((continuous_cdot _ _).comp continuous_subtype_val).pow l), fun x => ?_⟩
        exact zonalOp_harmonic _ (gk_continuous ξ).measurable 1 (abs_gk_le ξ) _ _
          (isotropic_family _) l x
      · refine ⟨Complex.continuous_im.comp
          (((continuous_cdot _ _).comp continuous_subtype_val).pow l), fun x => ?_⟩
        exact zonalOp_harmonic_im _ (gk_continuous ξ).measurable 1 (abs_gk_le ξ) _ _
          (isotropic_family _) l x
    | zero => exact ⟨continuous_const, fun x => by simp [zonalOp]⟩
    | add f h _ _ ihf ihh =>
      refine ⟨ihf.1.add ihh.1, fun x => ?_⟩
      have e1 := ihf.2 x
      have e2 := ihh.2 x
      unfold zonalOp at e1 e2 ⊢
      simp only [Pi.add_apply, mul_add]
      rw [integral_add (hint _ ihf.1 x) (hint _ ihh.1 x), e1, e2]
    | smul a f _ ihf =>
      refine ⟨ihf.1.const_smul a, fun x => ?_⟩
      have e1 := ihf.2 x
      unfold zonalOp at e1 ⊢
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ a]
      rw [integral_const_mul, e1]
  exact ⟨e, he, fun i x => Pinf_of_eigen ξ l (e i) x ((key _ (hspan i)).2 x)⟩

/-- The complex eigen-equation for the `F_j` (from `funk_hecke`). -/
theorem F_eigen (ξ : ℝ) (l : ℕ) (j : Fin (2 * l + 1)) (x : S2) :
    ∫ y, (gk ξ ⟪(x : E3), (y : E3)⟫ : ℂ) * F l j y ∂sigma
      = F l j x * (((1/2) * ∫ t in (-1:ℝ)..1, gk ξ t * legP l t : ℝ) : ℂ) :=
  funk_hecke _ (gk_continuous ξ).measurable 1 (abs_gk_le ξ) _ _ (isotropic_family _) l x

end CTG.FunkHecke.Mult
