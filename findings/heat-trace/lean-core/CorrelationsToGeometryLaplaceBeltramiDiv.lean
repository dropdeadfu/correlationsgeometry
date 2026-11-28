/-
Seventy-eighth Lean file (after version 4). The coordinate Laplace–Beltrami operator `lapB` of
`CorrelationsToGeometryLaplaceBeltrami` equals the divergence form. Written by a subagent of the author-side
session (task A192), checked here.

`fderiv_detP`, `hasFDerivAt_det` (Jacobi's formula d det = det · tr(g⁻¹ dg), proved here), `fderiv_inv_entry`
(d(g⁻¹) = −g⁻¹ (dg) g⁻¹), `key_alg` (contraction of the Christoffel symbols), `lapB_divFree`
(lapB = Σ ∂_i V^i + (Σ ∂_i(det g) V^i)/(2 det g), V^i = g^{ij}∂_j u; needs only det g ≠ 0), `lapB_div`
(lapB = (1/√det g) Σ ∂_i(√det g V^i) for det g > 0), `divSqrt_gRound` (round metric; via `lapB_div` and
`lapB_gRound`, not an independent computation).

NOT shown: the literal form (1/sin θ)∂_θ(sin θ ∂_θ u) with `deriv` of partial functions; positivity of the metric
is not used; pointwise statements in ℝⁿ, no manifold object, no integral form, no integration by parts.
No sorry, no axiom, no native_decide.
-/
import CorrelationsToGeometryLaplaceBeltrami

open Filter Topology

noncomputable section

namespace CTG.LaplaceBeltrami.Divergence

open CTG.LaplaceBeltrami

variable {n : ℕ}

/-- Square arrays as a normed space (sup norm). -/
abbrev P (n : ℕ) := Fin n → Fin n → ℝ

/-- Determinant on arrays. -/
def detP (M : P n) : ℝ := (Matrix.of M).det

theorem detP_eq (M : P n) : detP M = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * ∏ i, M (σ i) i := by
  unfold detP; rw [Matrix.det_apply']; rfl

theorem differentiable_detP : Differentiable ℝ (detP : P n → ℝ) := by
  have : (detP : P n → ℝ) = fun M => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * ∏ i, M (σ i) i := by
    funext M; exact detP_eq M
  rw [this]
  fun_prop


/-! ### Jacobi formula on arrays -/

theorem hasDerivAt_detP_line (M H : P n) (hM : detP M ≠ 0) :
    HasDerivAt (fun t : ℝ => detP (M + t • H))
      (detP M * ((Matrix.of M)⁻¹ * Matrix.of H).trace) 0 := by
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of M with hAdef
  set K : Matrix (Fin n) (Fin n) ℝ := A⁻¹ * Matrix.of H with hK
  set q : Polynomial ℝ :=
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • K.map Polynomial.C)).divX.divX with hq
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hM
  have hfun : (fun t : ℝ => detP (M + t • H)) = fun t => A.det * (1 + K.trace * t + q.eval t * t ^ 2) := by
    funext t
    have e : Matrix.of (M + t • H) = A * (1 + t • K) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hK, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
      rfl
    unfold detP
    rw [e, Matrix.det_mul, Matrix.det_one_add_smul]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => 1 + K.trace * t + q.eval t * t ^ 2) K.trace 0 := by
    have := ((hasDerivAt_const (0:ℝ) (1:ℝ)).add ((hasDerivAt_id (0:ℝ)).const_mul K.trace)).add
      ((q.hasDerivAt 0).mul ((hasDerivAt_id (0:ℝ)).pow 2))
    convert this using 1
    simp
  have := h1.const_mul A.det
  simpa [detP, hAdef] using this

theorem fderiv_detP (M H : P n) (hM : detP M ≠ 0) :
    fderiv ℝ (detP : P n → ℝ) M H = detP M * ((Matrix.of M)⁻¹ * Matrix.of H).trace := by
  have hl : HasDerivAt (fun t : ℝ => M + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const H).const_add M
  have h0 : M + (0:ℝ) • H = M := by simp
  have hd := (differentiable_detP (M + (0:ℝ) • H)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hl
  rw [h0] at hd
  exact hd.unique (hasDerivAt_detP_line M H hM)

/-! ### Entries of a metric field -/

/-- Evaluation `B ↦ B v w`. -/
def evalL (v w : E n) : Bil n →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (E n →L[ℝ] ℝ) v)

@[simp] theorem evalL_apply (v w : E n) (B : Bil n) : evalL v w B = B v w := rfl

/-- Gram array map. -/
def Lam : Bil n →L[ℝ] P n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j => evalL (ev i) (ev j)

@[simp] theorem Lam_apply (B : Bil n) (i j : Fin n) : Lam B i j = B (ev i) (ev j) := rfl

theorem of_Lam (B : Bil n) : Matrix.of (Lam B) = mat B := rfl

theorem DG_expand (DG : E n →L[ℝ] Bil n) (z v w : E n) :
    DG z v w = ∑ k, z k * DG (ev k) v w := by
  have := lin_expand ((evalL v w).comp DG) z
  simpa using this

theorem DG_expand3 (DG : E n →L[ℝ] Bil n) (v w z : E n) :
    DG v w z = ∑ k, z k * DG v w (ev k) := lin_expand (DG v w) z

theorem koszul_expand (DG : E n →L[ℝ] Bil n) (v w z : E n) :
    koszul DG v w z = ((∑ k, z k * DG v w (ev k)) + (∑ k, z k * DG w v (ev k))
      - ∑ k, z k * DG (ev k) v w) / 2 := by
  unfold koszul; rw [DG_expand3 DG v w z, DG_expand3 DG w v z, DG_expand DG z v w]

/-- Derivative of the determinant of the Gram matrix (Jacobi formula along a metric field). -/
theorem hasFDerivAt_det {G : E n → Bil n} {DG : E n →L[ℝ] Bil n} {x : E n} (hG : HasFDerivAt G DG x)
    (hdet : (mat (G x)).det ≠ 0) :
    HasFDerivAt (fun y => (mat (G y)).det) ((fderiv ℝ detP (Lam (G x))).comp (Lam.comp DG)) x ∧
    ∀ a, ((fderiv ℝ detP (Lam (G x))).comp (Lam.comp DG)) a
      = (mat (G x)).det * ((mat (G x))⁻¹ * mat (DG a)).trace := by
  have hL : HasFDerivAt (fun y => Lam (G y)) (Lam.comp DG) x := by
    have := HasFDerivAt.comp (𝕜 := ℝ) (E := E n) (F := Bil n) (G := P n) x
      (Lam : Bil n →L[ℝ] P n).hasFDerivAt hG
    exact this
  refine ⟨?_, fun a => ?_⟩
  · have := HasFDerivAt.comp (𝕜 := ℝ) (E := E n) (F := P n) (G := ℝ) x
      (differentiable_detP (Lam (G x))).hasFDerivAt hL
    exact this
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact fderiv_detP (Lam (G x)) (Lam (DG a)) hdet

/-- The entries of the inverse Gram matrix are differentiable. -/
theorem differentiableAt_inv_entry {G : E n → Bil n} {x : E n} (hG : DifferentiableAt ℝ G x)
    (hdet : (mat (G x)).det ≠ 0) (i j : Fin n) :
    DifferentiableAt ℝ (fun y => (mat (G y))⁻¹ i j) x := by
  have hL : DifferentiableAt ℝ (fun y => Lam (G y)) x := by
    have := DifferentiableAt.comp (𝕜 := ℝ) (E := E n) (F := Bil n) (G := P n) x
      (Lam : Bil n →L[ℝ] P n).differentiableAt hG
    exact this
  have hD : DifferentiableAt ℝ (fun y => (mat (G y)).det) x := by
    have := DifferentiableAt.comp (𝕜 := ℝ) (E := E n) (F := P n) (G := ℝ) x
      (differentiable_detP (Lam (G x))) hL
    exact this
  have hentry : ∀ k l, DifferentiableAt ℝ (fun y => Lam (G y) k l) x := fun k l => by
    have : (fun y => Lam (G y) k l) = (fun Q : P n => Q k l) ∘ (fun y => Lam (G y)) := rfl
    rw [this]
    exact DifferentiableAt.comp (𝕜 := ℝ) (E := E n) (F := P n) (G := ℝ) x
      ((by fun_prop : Differentiable ℝ (fun Q : P n => Q k l)) _) hL
  have hU : DifferentiableAt ℝ
      (fun y => detP (fun k l => if k = j then (Pi.single i (1:ℝ) : Fin n → ℝ) l else Lam (G y) k l)) x := by
    refine DifferentiableAt.comp (𝕜 := ℝ) (E := E n) (F := P n) (G := ℝ) x
      (differentiable_detP _) ?_
    rw [differentiableAt_pi]; intro k
    rw [differentiableAt_pi]; intro l
    by_cases hk : k = j
    · simp [hk]
    · simpa [hk] using hentry k l
  have heq : (fun y => (mat (G y))⁻¹ i j) = fun y => ((mat (G y)).det)⁻¹ *
      detP (fun k l => if k = j then (Pi.single i (1:ℝ) : Fin n → ℝ) l else Lam (G y) k l) := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
    congr 1
    unfold detP
    congr 1
    ext k l
    simp [Matrix.updateRow_apply, mat]
  rw [heq]
  exact (hD.inv hdet).mul hU

/-! ### Derivative of the inverse matrix -/

/-- `∂_a (g⁻¹) = −g⁻¹ (∂_a g) g⁻¹`, entrywise. -/
theorem fderiv_inv_entry {G : E n → Bil n} {DG : E n →L[ℝ] Bil n} {x : E n} (hG : HasFDerivAt G DG x)
    (hdet : (mat (G x)).det ≠ 0) (a : E n) :
    Matrix.of (fun i j => fderiv ℝ (fun y => (mat (G y))⁻¹ i j) x a)
      = -((mat (G x))⁻¹ * mat (DG a) * (mat (G x))⁻¹) := by
  set g := mat (G x) with hg
  set H' : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => fderiv ℝ (fun y => (mat (G y))⁻¹ i j) x a)
    with hH'
  have hDc : ContinuousAt (fun y => (mat (G y)).det) x := (hasFDerivAt_det hG hdet).1.continuousAt
  have hev : ∀ᶠ y in 𝓝 x, (mat (G y)).det ≠ 0 := hDc.eventually_ne hdet
  have hrel : g * H' + mat (DG a) * g⁻¹ = 0 := by
    ext i j
    have hF : HasFDerivAt (fun y => ∑ k, (evalL (ev i) (ev k)) (G y) * (mat (G y))⁻¹ k j)
        (∑ k, ((evalL (ev i) (ev k)) (G x) • fderiv ℝ (fun y => (mat (G y))⁻¹ k j) x
           + (mat (G x))⁻¹ k j • (evalL (ev i) (ev k)).comp DG)) x := by
      apply HasFDerivAt.fun_sum; intro k _
      have h1 : HasFDerivAt (fun y => (evalL (ev i) (ev k)) (G y)) ((evalL (ev i) (ev k)).comp DG) x := by
        have := HasFDerivAt.comp (𝕜 := ℝ) (E := E n) (F := Bil n) (G := ℝ) x
          (evalL (ev i) (ev k)).hasFDerivAt hG
        exact this
      exact h1.mul (differentiableAt_inv_entry hG.differentiableAt hdet k j).hasFDerivAt
    have hconst : HasFDerivAt (fun y => ∑ k, (evalL (ev i) (ev k)) (G y) * (mat (G y))⁻¹ k j)
        (0 : E n →L[ℝ] ℝ) x := by
      apply (hasFDerivAt_const ((1 : Matrix (Fin n) (Fin n) ℝ) i j) x).congr_of_eventuallyEq
      filter_upwards [hev] with y hy
      have := congrFun (congrFun (Matrix.mul_nonsing_inv (mat (G y)) (isUnit_iff_ne_zero.mpr hy)) i) j
      rw [Matrix.mul_apply] at this
      simpa [mat] using this
    have h0 := congrArg (fun L : E n →L[ℝ] ℝ => L a) (hF.unique hconst)
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, evalL_apply,
      smul_eq_mul, ContinuousLinearMap.zero_apply] at h0
    simp only [Matrix.add_apply, Matrix.mul_apply, hH', Matrix.of_apply, hg, mat, Matrix.zero_apply]
    rw [← Finset.sum_add_distrib]
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mat]; ring
  have hu : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.mpr hdet)
  calc H' = g⁻¹ * (g * H') := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
    _ = g⁻¹ * (-(mat (DG a) * g⁻¹)) := by rw [eq_neg_of_add_eq_zero_left hrel]
    _ = _ := by rw [Matrix.mul_neg, Matrix.mul_assoc]

/-! ### The vector field `V^i = Σ_j g^{ij} ∂_j u` -/

/-- Components of the gradient field. -/
def Vf (G : E n → Bil n) (u : E n → ℝ) (i : Fin n) (y : E n) : ℝ :=
  ∑ j, (mat (G y))⁻¹ i j * fderiv ℝ u y (ev j)

theorem fderiv_Vf {G : E n → Bil n} {DG : E n →L[ℝ] Bil n} {x : E n} {u : E n → ℝ}
    (hG : HasFDerivAt G DG x) (hdet : (mat (G x)).det ≠ 0) (hu : DifferentiableAt ℝ (fderiv ℝ u) x)
    (i : Fin n) (a : E n) :
    HasFDerivAt (Vf G u i) (∑ j, ((mat (G x))⁻¹ i j •
        (ContinuousLinearMap.apply ℝ ℝ (ev j)).comp (fderiv ℝ (fderiv ℝ u) x)
        + fderiv ℝ u x (ev j) • fderiv ℝ (fun y => (mat (G y))⁻¹ i j) x)) x ∧
    fderiv ℝ (Vf G u i) x a = ∑ j, ((mat (G x))⁻¹ i j * fderiv ℝ (fderiv ℝ u) x a (ev j)
        - fderiv ℝ u x (ev j) * ((mat (G x))⁻¹ * mat (DG a) * (mat (G x))⁻¹) i j) := by
  have hV : HasFDerivAt (Vf G u i) (∑ j, ((mat (G x))⁻¹ i j •
        (ContinuousLinearMap.apply ℝ ℝ (ev j)).comp (fderiv ℝ (fderiv ℝ u) x)
        + fderiv ℝ u x (ev j) • fderiv ℝ (fun y => (mat (G y))⁻¹ i j) x)) x := by
    unfold Vf
    apply HasFDerivAt.fun_sum; intro j _
    have h1 : HasFDerivAt (fun y => fderiv ℝ u y (ev j))
        ((ContinuousLinearMap.apply ℝ ℝ (ev j)).comp (fderiv ℝ (fderiv ℝ u) x)) x := by
      have := HasFDerivAt.comp (𝕜 := ℝ) (E := E n) (F := E n →L[ℝ] ℝ) (G := ℝ) x
        (ContinuousLinearMap.apply ℝ ℝ (ev j) : (E n →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt hu.hasFDerivAt
      exact this
    exact (differentiableAt_inv_entry hG.differentiableAt hdet i j).hasFDerivAt.mul h1
  refine ⟨hV, ?_⟩
  rw [hV.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.apply_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun (fderiv_inv_entry hG hdet a) i) j
  simp only [Matrix.of_apply, Matrix.neg_apply] at this
  rw [this]; ring

/-! ### Algebra: contraction of the Christoffel symbols -/

theorem T1 (h : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → Fin n → Fin n → ℝ) (du z : Fin n → ℝ)
    (hz : ∀ k, z k = ∑ l, h k l * du l) :
    ∑ i, ∑ j, h i j * ∑ k, z k * c i j k
      = ∑ i, ∑ j, du j * (h * Matrix.of (c i) * h) i j := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hz, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem T2 (h : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, h i j = h j i) (c : Fin n → Fin n → Fin n → ℝ)
    (z : Fin n → ℝ) :
    ∑ i, ∑ j, h i j * ∑ k, z k * c j i k = ∑ i, ∑ j, h i j * ∑ k, z k * c i j k := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hs]

theorem T3 (h : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, h i j = h j i) (c : Fin n → Fin n → Fin n → ℝ)
    (z : Fin n → ℝ) :
    ∑ i, ∑ j, h i j * ∑ k, z k * c k i j = ∑ k, (h * Matrix.of (c k)).trace * z k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hs i j]; ring

theorem key_alg (h : Matrix (Fin n) (Fin n) ℝ) (hs : ∀ i j, h i j = h j i) (c : Fin n → Fin n → Fin n → ℝ)
    (D2 : Fin n → Fin n → ℝ) (du z : Fin n → ℝ) (hz : ∀ k, z k = ∑ l, h k l * du l) (d : ℝ) (hd : d ≠ 0) :
    ∑ i, ∑ j, h i j * (D2 i j - ((∑ k, z k * c i j k) + (∑ k, z k * c j i k) - (∑ k, z k * c k i j)) / 2)
      = ∑ i, ∑ j, (h i j * D2 i j - du j * (h * Matrix.of (c i) * h) i j)
        + (∑ i, d * (h * Matrix.of (c i)).trace * z i) / (2 * d) := by
  have e1 : ∀ i j, h i j * (D2 i j - ((∑ k, z k * c i j k) + (∑ k, z k * c j i k) - (∑ k, z k * c k i j)) / 2)
      = h i j * D2 i j - (h i j * (∑ k, z k * c i j k) + h i j * (∑ k, z k * c j i k)
        - h i j * (∑ k, z k * c k i j)) / 2 := fun i j => by ring
  have e2 : (∑ i, d * (h * Matrix.of (c i)).trace * z i) / (2 * d)
      = (∑ i, (h * Matrix.of (c i)).trace * z i) / 2 := by
    rw [show (∑ i, d * (h * Matrix.of (c i)).trace * z i) = d * ∑ i, (h * Matrix.of (c i)).trace * z i by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring]
    field_simp
  simp only [e1, e2, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [T1 h c du z hz, T2 h hs c z, T1 h c du z hz, T3 h hs c z]
  ring

/-! ### The divergence forms and the main theorem -/

/-- Divergence form without the square root:
`Σ_i ∂_i V^i + (1/(2 det g)) Σ_i (∂_i det g) V^i`, `V^i = Σ_j g^{ij} ∂_j u`. -/
def divFree (G : E n → Bil n) (u : E n → ℝ) (x : E n) : ℝ :=
  ∑ i, fderiv ℝ (Vf G u i) x (ev i)
    + (∑ i, fderiv ℝ (fun y => (mat (G y)).det) x (ev i) * Vf G u i x) / (2 * (mat (G x)).det)

/-- Divergence form `(1/√det g) Σ_i ∂_i (√det g · Σ_j g^{ij} ∂_j u)`. -/
def divSqrt (G : E n → Bil n) (u : E n → ℝ) (x : E n) : ℝ :=
  (∑ i, fderiv ℝ (fun y => Real.sqrt (mat (G y)).det * Vf G u i y) x (ev i)) / Real.sqrt (mat (G x)).det

theorem inv_symm {g : Matrix (Fin n) (Fin n) ℝ} (hs : ∀ i j, g i j = g j i) (i j : Fin n) :
    g⁻¹ i j = g⁻¹ j i := by
  have hT : Matrix.transpose g = g := by ext a b; exact hs b a
  have := congrFun (congrFun (Matrix.transpose_nonsing_inv g) j) i
  rw [hT] at this
  simpa [Matrix.transpose_apply] using this

/-- **Christoffel form = divergence form (without root).** -/
theorem lapB_divFree {G : E n → Bil n} {u : E n → ℝ} {x : E n} (hG : DifferentiableAt ℝ G x)
    (hsym : ∀ v w, G x v w = G x w v) (hdet : (mat (G x)).det ≠ 0)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    lapB G u x = divFree G u x := by
  have hG' : HasFDerivAt G (fderiv ℝ G x) x := hG.hasFDerivAt
  have hs : ∀ i j, (mat (G x))⁻¹ i j = (mat (G x))⁻¹ j i := inv_symm (fun i j => hsym (ev i) (ev j))
  have hdetD := hasFDerivAt_det hG' hdet
  unfold divFree
  rw [hdetD.1.fderiv]
  simp only [hdetD.2, fun i => (fderiv_Vf hG' hdet hu i (ev i)).2]
  unfold lapB LB hessG
  simp only [koszul_expand]
  have hz : ∀ k, grad (G x) (fderiv ℝ u x) k = ∑ l, (mat (G x))⁻¹ k l * dvec (fderiv ℝ u x) l :=
    fun k => rfl
  have key := key_alg (mat (G x))⁻¹ hs (fun k i j => fderiv ℝ G x (ev k) (ev i) (ev j))
    (fun i j => fderiv ℝ (fderiv ℝ u) x (ev i) (ev j)) (dvec (fderiv ℝ u x))
    (grad (G x) (fderiv ℝ u x)) hz ((mat (G x)).det) hdet
  have hV : ∀ i, Vf G u i x = grad (G x) (fderiv ℝ u x) i := fun i => rfl
  simp only [hV]
  exact key

theorem weight_rule {ρ V : E n → ℝ} {ρ' : E n →L[ℝ] ℝ} {x : E n} (hρ : HasFDerivAt ρ ρ' x)
    (hV : DifferentiableAt ℝ V x) (h0 : ρ x ≠ 0) (a : E n) :
    fderiv ℝ (fun y => ρ y * V y) x a / ρ x = fderiv ℝ V x a + ρ' a / ρ x * V x := by
  have hm : HasFDerivAt (fun y => ρ y * V y) (ρ x • fderiv ℝ V x + V x • ρ') x := hρ.mul hV.hasFDerivAt
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- **Christoffel form = divergence form with `√det g`**, at a point where `det g > 0`. -/
theorem lapB_div {G : E n → Bil n} {u : E n → ℝ} {x : E n} (hG : DifferentiableAt ℝ G x)
    (hsym : ∀ v w, G x v w = G x w v) (hdet : 0 < (mat (G x)).det)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    lapB G u x = divSqrt G u x := by
  rw [lapB_divFree hG hsym hdet.ne' hu]
  have hG' := hG.hasFDerivAt
  have hdetD := hasFDerivAt_det hG' hdet.ne'
  set D := (fderiv ℝ detP (Lam (G x))).comp (Lam.comp (fderiv ℝ G x)) with hD
  have hsq : HasFDerivAt (fun y => Real.sqrt (mat (G y)).det)
      ((1 / (2 * Real.sqrt (mat (G x)).det)) • D) x := by
    have := (Real.hasDerivAt_sqrt hdet.ne').comp_hasFDerivAt x hdetD.1
    convert this using 1
  have hr : 0 < Real.sqrt (mat (G x)).det := Real.sqrt_pos.mpr hdet
  have hrr : Real.sqrt (mat (G x)).det * Real.sqrt (mat (G x)).det = (mat (G x)).det :=
    Real.mul_self_sqrt hdet.le
  unfold divFree divSqrt
  rw [Finset.sum_div]
  simp only [fun i => weight_rule hsq (fderiv_Vf hG' hdet.ne' hu i (ev i)).1.differentiableAt hr.ne' (ev i),
    hdetD.1.fderiv, Finset.sum_add_distrib, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  set d := (mat (G x)).det
  set r := Real.sqrt d
  rw [← hrr]
  ring

/-! ### Check: the round metric -/

theorem differentiableAt_const_add_smul {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {s : E 2 → ℝ} {x : E 2} (hs : DifferentiableAt ℝ s x) (C B : W) :
    DifferentiableAt ℝ (fun x => C + s x • B) x :=
  (differentiableAt_const C).add (hs.smul_const B)

theorem gRound_differentiableAt (x : E 2) : DifferentiableAt ℝ gRound x := by
  unfold gRound gDiag
  have hs : DifferentiableAt ℝ (fun x : E 2 => Real.sin (x 0) ^ 2) x := by fun_prop
  exact differentiableAt_const_add_smul (W := Bil 2) hs (sq 0) (sq 1)

theorem gRound_symm (x : E 2) (v w : E 2) : gRound x v w = gRound x w v := by
  simp [gRound, gDiag, sq, mul_comm]

theorem gRound_det (x : E 2) : (mat (gRound x)).det = Real.sin (x 0) ^ 2 := by
  unfold gRound; rw [mat_gDiag]; simp [Matrix.det_fin_two]

/-- **Round metric in divergence form.** For `sin θ ≠ 0` and `u` with differentiable `fderiv u`, the
divergence form `(1/√det g) Σ ∂_i(√det g g^{ij}∂_j u)` (here `√det g = |sin θ|`) gives the classical formula
`∂_θ²u + (cos θ/sin θ)∂_θ u + (1/sin²θ)∂_φ²u`. -/
theorem divSqrt_gRound (u : E 2 → ℝ) {x : E 2} (h0 : Real.sin (x 0) ≠ 0)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    divSqrt gRound u x =
      fderiv ℝ (fderiv ℝ u) x (ev 0) (ev 0)
        + Real.cos (x 0) / Real.sin (x 0) * fderiv ℝ u x (ev 0)
        + 1 / Real.sin (x 0) ^ 2 * fderiv ℝ (fderiv ℝ u) x (ev 1) (ev 1) := by
  have hpos : 0 < (mat (gRound x)).det := by rw [gRound_det]; positivity
  rw [← lapB_div (gRound_differentiableAt x) (gRound_symm x) hpos hu, lapB_gRound u h0]

theorem sqrt_det_gRound (x : E 2) : Real.sqrt (mat (gRound x)).det = |Real.sin (x 0)| := by
  rw [gRound_det, Real.sqrt_sq_eq_abs]
end CTG.LaplaceBeltrami.Divergence
