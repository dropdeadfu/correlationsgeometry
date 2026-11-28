/-
Seventy-sixth Lean file (after version 4). A Laplace–Beltrami operator defined in coordinates, in the Christoffel
form written with the Koszul formula (g^{ij}(∂_i∂_j u − Γ^k_ij ∂_k u), no determinant), and its invariance under
C² changes of coordinates. Only Mathlib. Written by a subagent of the author-side session (task A189), checked here.

Main statements: `hessG_comp` (the covariant Hessian is a tensor, pointwise and algebraic), `LB_comp`,
`lapB_pullback` (lapB (ψ*G) (u∘ψ) y = lapB G u (ψ y) for ψ C² at y with invertible derivative, u C² at ψ y,
G differentiable at ψ y, symmetric and nondegenerate there; any dimension), `lapB_isometry` (two coordinate
expressions related by an isometry give the same value), `lapB_gDiag`, `lapB_gRound` (for the round metric
dθ² + sin²θ dφ² with sin θ ≠ 0 the operator is ∂_θ²u + (cos θ/sin θ)∂_θu + (1/sin²θ)∂_φ²u).

NOT proved here: that the change between the two charts of the sphere file is an isometry of the round metric
(so `sphLapS_coord`/`sphLapS_atlas` are not yet formally connected to `lapB`); the bridge between `deriv` of
partial functions and `fderiv` on `Fin 2 → ℝ`; the divergence form with √det g; any global object
"Riemannian manifold" (the invariance is local in ℝⁿ); positive definiteness is not used.
-/
import Mathlib

open Filter Topology

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace CTG.LaplaceBeltrami

variable {n : ℕ}

/-- Coordinate space. -/
abbrev E (n : ℕ) := Fin n → ℝ

/-- A bilinear form on `E n`. -/
abbrev Bil (n : ℕ) := E n →L[ℝ] E n →L[ℝ] ℝ

/-- Standard basis vector. -/
def ev (i : Fin n) : E n := Pi.single i 1

/-- Gram matrix of a bilinear form. -/
def mat (B : Bil n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => B (ev i) (ev j)

/-- Matrix of a linear map. -/
def amat (J : E n →L[ℝ] E n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => J (ev j) i

/-- Coordinate vector of a linear form. -/
def dvec (du : E n →L[ℝ] ℝ) : E n := fun j => du (ev j)

/-- Gradient `G⁻¹ du`. -/
noncomputable def grad (G : Bil n) (du : E n →L[ℝ] ℝ) : E n := Matrix.mulVec (mat G)⁻¹ (dvec du)

/-- Lowered Christoffel symbols (Koszul formula) from the derivative `DG` of the metric. -/
noncomputable def koszul (DG : E n →L[ℝ] Bil n) (v w z : E n) : ℝ :=
  (DG v w z + DG w v z - DG z v w) / 2

/-- Covariant Hessian `D²u(v,w) − du(Γ(v,w))`. -/
noncomputable def hessG (G : Bil n) (DG : E n →L[ℝ] Bil n) (du : E n →L[ℝ] ℝ)
    (D2u : E n →L[ℝ] E n →L[ℝ] ℝ) (v w : E n) : ℝ :=
  D2u v w - koszul DG v w (grad G du)

/-- Pointwise Laplace–Beltrami: `g^{ij}(∂_i∂_j u − Γ^k_{ij}∂_k u)`. -/
noncomputable def LB (G : Bil n) (DG : E n →L[ℝ] Bil n) (du : E n →L[ℝ] ℝ)
    (D2u : E n →L[ℝ] E n →L[ℝ] ℝ) : ℝ :=
  ∑ i, ∑ j, (mat G)⁻¹ i j * hessG G DG du D2u (ev i) (ev j)

/-- The Laplace–Beltrami operator of a metric field `G` applied to `u` at `x`. -/
noncomputable def lapB (G : E n → Bil n) (u : E n → ℝ) (x : E n) : ℝ :=
  LB (G x) (fderiv ℝ G x) (fderiv ℝ u x) (fderiv ℝ (fderiv ℝ u) x)

/-- Pulled-back metric `ψ*G = Dψᵀ (G∘ψ) Dψ`. -/
noncomputable def pullback {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (ψ : V → V)
    (G : V → V →L[ℝ] V →L[ℝ] ℝ) (y : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  (G (ψ y)).bilinearComp (fderiv ℝ ψ y) (fderiv ℝ ψ y)

section LA
open Matrix

/-! ### Linear algebra -/

theorem vec_expand (v : E n) : v = ∑ i, v i • (ev i : E n) := by
  ext k; simp [ev, Pi.single_apply]

theorem lin_expand (L : E n →L[ℝ] ℝ) (v : E n) : L v = ∑ i, v i * L (ev i) := by
  conv_lhs => rw [vec_expand v]
  simp [map_sum, map_smul]

theorem bil_expand (B : Bil n) (v w : E n) : B v w = v ⬝ᵥ (mat B *ᵥ w) := by
  conv_lhs => rw [vec_expand v, vec_expand w]
  simp [map_sum, map_smul, dotProduct, Matrix.mulVec, mat, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc]
  rw [Finset.sum_comm]

theorem lin_apply (J : E n →L[ℝ] E n) (v : E n) : J v = amat J *ᵥ v := by
  conv_lhs => rw [vec_expand v]
  ext k
  simp [map_sum, map_smul, Matrix.mulVec, dotProduct, amat, mul_comm]

theorem mat_comp (B : Bil n) (J : E n →L[ℝ] E n) :
    mat (B.bilinearComp J J) = (amat J)ᵀ * mat B * amat J := by
  ext i j
  have : (B.bilinearComp J J) (ev i) (ev j) = B (J (ev i)) (J (ev j)) := rfl
  rw [show mat (B.bilinearComp J J) i j = B (J (ev i)) (J (ev j)) from this, bil_expand]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, amat, Finset.mul_sum, Finset.sum_mul,
    mul_comm, mul_left_comm, mul_assoc]
  rw [Finset.sum_comm]

theorem dvec_comp (du : E n →L[ℝ] ℝ) (J : E n →L[ℝ] E n) :
    dvec (du.comp J) = (amat J)ᵀ *ᵥ dvec du := by
  ext j
  simp only [dvec, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [lin_expand]
  simp [Matrix.mulVec, dotProduct, amat, mul_comm, dvec]

theorem grad_spec (G : Bil n) (du : E n →L[ℝ] ℝ) (hG : (mat G).det ≠ 0) (a : E n) :
    G a (grad G du) = du a := by
  rw [bil_expand, grad, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hG),
    Matrix.one_mulVec, lin_expand]
  simp [dotProduct, dvec]

theorem grad_comp (G : Bil n) (du : E n →L[ℝ] ℝ) (J : E n →L[ℝ] E n) (hG : (mat G).det ≠ 0)
    (hJ : (amat J).det ≠ 0) : J (grad (G.bilinearComp J J) (du.comp J)) = grad G du := by
  have hJt : (amat J)ᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  rw [lin_apply, grad, grad, mat_comp, dvec_comp, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hJt), Matrix.mul_one]

theorem sum_entries (X Y : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, ∑ j, X i j * Y i j = (X * Yᵀ).trace := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trace_comp (G B : Bil n) (J : E n →L[ℝ] E n) (hJ : (amat J).det ≠ 0) :
    ∑ i, ∑ j, (mat (G.bilinearComp J J))⁻¹ i j * B (J (ev i)) (J (ev j))
      = ∑ i, ∑ j, (mat G)⁻¹ i j * B (ev i) (ev j) := by
  have hJt : (amat J)ᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have h1 : ∀ i j, B (J (ev i)) (J (ev j)) = mat (B.bilinearComp J J) i j := fun _ _ => rfl
  have h2 : ∀ i j, B (ev i) (ev j) = mat B i j := fun _ _ => rfl
  simp only [h1, h2, sum_entries, mat_comp, Matrix.mul_inv_rev, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((amat J)ᵀ)⁻¹ (amat J)ᵀ, Matrix.nonsing_inv_mul _ (Ne.isUnit hJt), Matrix.one_mul,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ),
    Matrix.mul_one]

/-! ### Stage 1: pointwise invariance -/

/-- The covariant Hessian is a tensor: under the chain-rule formulas for the pulled-back data it transforms by `J`. -/
theorem hessG_comp (G : Bil n) (DG : E n →L[ℝ] Bil n) (du : E n →L[ℝ] ℝ) (D2u : E n →L[ℝ] E n →L[ℝ] ℝ)
    (J : E n →L[ℝ] E n) (H2 : E n →L[ℝ] E n →L[ℝ] E n)
    (DG' : E n →L[ℝ] Bil n) (D2u' : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hG : (mat G).det ≠ 0) (hJ : (amat J).det ≠ 0)
    (hsym : ∀ v w, G v w = G w v) (hH : ∀ a b, H2 a b = H2 b a)
    (hDG' : ∀ a b c, DG' a b c = DG (J a) (J b) (J c) + G (H2 a b) (J c) + G (J b) (H2 a c))
    (hD2' : ∀ a b, D2u' a b = D2u (J a) (J b) + du (H2 a b)) (v w : E n) :
    hessG (G.bilinearComp J J) DG' (du.comp J) D2u' v w = hessG G DG du D2u (J v) (J w) := by
  have hg := grad_comp G du J hG hJ
  have hs := grad_spec G du hG (H2 v w)
  simp only [hessG, koszul, hDG', hD2']
  generalize grad (G.bilinearComp J J) (du.comp J) = z at hg ⊢
  rw [hg, hH z v, hH z w, hH w v]
  have e1 := hsym (J w) (H2 v z)
  have e2 := hsym (J v) (H2 w z)
  linarith

/-- The covariant Hessian is given by a bilinear form. -/
theorem hessG_eq (G : Bil n) (DG : E n →L[ℝ] Bil n) (du : E n →L[ℝ] ℝ) (D2u : E n →L[ℝ] E n →L[ℝ] ℝ) :
    ∃ Hb : Bil n, ∀ v w, hessG G DG du D2u v w = Hb v w := by
  let B2 : Bil n := (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) ℝ
    (ContinuousLinearMap.apply ℝ ℝ (grad G du))).comp DG
  refine ⟨D2u - (1/2 : ℝ) • ((B2 + B2.flip - DG (grad G du) : Bil n)), fun v w => ?_⟩
  simp [hessG, koszul, B2]
  ring

theorem LB_comp (G : Bil n) (DG : E n →L[ℝ] Bil n) (du : E n →L[ℝ] ℝ) (D2u : E n →L[ℝ] E n →L[ℝ] ℝ)
    (J : E n →L[ℝ] E n) (H2 : E n →L[ℝ] E n →L[ℝ] E n)
    (DG' : E n →L[ℝ] Bil n) (D2u' : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hG : (mat G).det ≠ 0) (hJ : (amat J).det ≠ 0)
    (hsym : ∀ v w, G v w = G w v) (hH : ∀ a b, H2 a b = H2 b a)
    (hDG' : ∀ a b c, DG' a b c = DG (J a) (J b) (J c) + G (H2 a b) (J c) + G (J b) (H2 a c))
    (hD2' : ∀ a b, D2u' a b = D2u (J a) (J b) + du (H2 a b)) :
    LB (G.bilinearComp J J) DG' (du.comp J) D2u' = LB G DG du D2u := by
  unfold LB
  simp only [hessG_comp G DG du D2u J H2 DG' D2u' hG hJ hsym hH hDG' hD2']
  obtain ⟨Hb, hHb⟩ := hessG_eq G DG du D2u
  simp only [hHb]
  exact trace_comp G Hb J hJ


end LA

/-! ### Stage 2: invariance under C² changes of coordinates -/

section Analytic
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Derivative of the pulled-back metric (chain and product rule), on any normed space. -/
theorem pullback_deriv {ψ : V → V} {G : V → V →L[ℝ] V →L[ℝ] ℝ} {y : V} (hψd : DifferentiableAt ℝ ψ y)
    (hJd : DifferentiableAt ℝ (fderiv ℝ ψ) y) (hGd : DifferentiableAt ℝ G (ψ y)) (a b c : V) :
    fderiv ℝ (pullback ψ G) y a b c
      = fderiv ℝ G (ψ y) (fderiv ℝ ψ y a) (fderiv ℝ ψ y b) (fderiv ℝ ψ y c)
        + G (ψ y) (fderiv ℝ (fderiv ℝ ψ) y a b) (fderiv ℝ ψ y c)
        + G (ψ y) (fderiv ℝ ψ y b) (fderiv ℝ (fderiv ℝ ψ) y a c) := by
  have hpb : pullback ψ G = fun z => ((ContinuousLinearMap.compL ℝ V V ℝ).flip (fderiv ℝ ψ z)).comp
      ((G (ψ z)).comp (fderiv ℝ ψ z)) := by
    funext z; ext a b; rfl
  have hr := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := V →L[ℝ] V)
    (F := (V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ)) (x := fderiv ℝ ψ y) ((ContinuousLinearMap.compL ℝ V V ℝ).flip)
  have h1 := HasFDerivAt.comp (𝕜 := ℝ) (E := V) (F := V →L[ℝ] V)
    (G := (V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ)) y hr hJd.hasFDerivAt
  have h2 := HasFDerivAt.comp (𝕜 := ℝ) (E := V) (F := V) (G := V →L[ℝ] V →L[ℝ] ℝ) y
    hGd.hasFDerivAt hψd.hasFDerivAt
  have h3 := HasFDerivAt.clm_comp (𝕜 := ℝ) (E := V) (F := V) (G := V) (H := V →L[ℝ] ℝ) h2
    hJd.hasFDerivAt
  have h4 := HasFDerivAt.clm_comp (𝕜 := ℝ) (E := V) (F := V) (G := V →L[ℝ] ℝ) (H := V →L[ℝ] ℝ) h1 h3
  have h5 : HasFDerivAt (pullback ψ G) _ y :=
    h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by rw [hpb]; rfl)
  rw [h5.fderiv]
  simp
  ring

/-- Second derivative of `u ∘ ψ` (chain rule of second order), on any normed space. -/
theorem comp_deriv2 {ψ : V → V} {u : V → ℝ} {y : V}
    (hψd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ ψ z) (hud : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ u (ψ z))
    (hJd : DifferentiableAt ℝ (fderiv ℝ ψ) y) (hDud : DifferentiableAt ℝ (fderiv ℝ u) (ψ y)) (a b : V) :
    fderiv ℝ (fderiv ℝ (u ∘ ψ)) y a b
      = fderiv ℝ (fderiv ℝ u) (ψ y) (fderiv ℝ ψ y a) (fderiv ℝ ψ y b)
        + fderiv ℝ u (ψ y) (fderiv ℝ (fderiv ℝ ψ) y a b) := by
  have hev : fderiv ℝ (u ∘ ψ) =ᶠ[𝓝 y] fun z => (fderiv ℝ u (ψ z)).comp (fderiv ℝ ψ z) := by
    filter_upwards [hψd, hud] with z h1 h2
    exact fderiv_comp z h2 h1
  have h2 := hDud.hasFDerivAt.comp y hψd.self_of_nhds.hasFDerivAt
  have hD2 : HasFDerivAt (fun z => (fderiv ℝ u (ψ z)).comp (fderiv ℝ ψ z)) _ y :=
    h2.clm_comp hJd.hasFDerivAt
  rw [hev.fderiv_eq, hD2.fderiv]
  simp
  ring

/-- Derivative of `x ↦ C + s x • B`. -/
theorem fderiv_const_add_smul {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {s : V → ℝ}
    {s' : V →L[ℝ] ℝ} {x : V} (hs : HasFDerivAt s s' x) (C B : W) (a : V) :
    fderiv ℝ (fun x => C + s x • B) x a = s' a • B := by
  have h : HasFDerivAt (fun x => C + s x • B) _ x := (hasFDerivAt_const C x).add (hs.smul_const B)
  rw [h.fderiv]
  simp

end Analytic

/-- **Invariance of the Laplace–Beltrami operator.** For a change of coordinates `ψ` that is C² at `y` with invertible
derivative, a metric field `G` differentiable at `ψ y` (symmetric, nondegenerate there) and a function `u` that is C² at
`ψ y`: `Δ_{ψ*G}(u∘ψ)(y) = (Δ_G u)(ψ y)`. -/
theorem lapB_pullback {ψ : E n → E n} {G : E n → Bil n} {u : E n → ℝ} {y : E n}
    (hψ : ContDiffAt ℝ 2 ψ y) (hJ : (amat (fderiv ℝ ψ y)).det ≠ 0)
    (hu : ContDiffAt ℝ 2 u (ψ y)) (hGd : DifferentiableAt ℝ G (ψ y))
    (hsym : ∀ v w, G (ψ y) v w = G (ψ y) w v) (hdet : (mat (G (ψ y))).det ≠ 0) :
    lapB (pullback ψ G) (u ∘ ψ) y = lapB G u (ψ y) := by
  have hψd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ ψ z :=
    (hψ.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hud : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ u (ψ z) :=
    hψ.continuousAt.tendsto.eventually
      ((hu.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num))
  have hJd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDud : DifferentiableAt ℝ (fderiv ℝ u) (ψ y) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hHs : ∀ a b, fderiv ℝ (fderiv ℝ ψ) y a b = fderiv ℝ (fderiv ℝ ψ) y b a :=
    fun a b => (hψ.isSymmSndFDerivAt (by simp)) a b
  have hdu' : fderiv ℝ (u ∘ ψ) y = (fderiv ℝ u (ψ y)).comp (fderiv ℝ ψ y) :=
    fderiv_comp y hud.self_of_nhds hψd.self_of_nhds
  unfold lapB
  rw [hdu']
  exact LB_comp (G (ψ y)) (fderiv ℝ G (ψ y)) (fderiv ℝ u (ψ y)) (fderiv ℝ (fderiv ℝ u) (ψ y))
    (fderiv ℝ ψ y) (fderiv ℝ (fderiv ℝ ψ) y) (fderiv ℝ (pullback ψ G) y) (fderiv ℝ (fderiv ℝ (u ∘ ψ)) y)
    hdet hJ hsym hHs (pullback_deriv hψd.self_of_nhds hJd hGd) (comp_deriv2 hψd hud hJd hDud)

/-- **Isometries.** If `ψ` pulls `G` back to `H` near `y` (e.g. a change between two charts in which the metric has the
same coordinate expression), then the two coordinate expressions of the Laplace–Beltrami operator agree:
`Δ_H(u∘ψ)(y) = (Δ_G u)(ψ y)`. -/
theorem lapB_isometry {ψ : E n → E n} {G H : E n → Bil n} {u : E n → ℝ} {y : E n}
    (hψ : ContDiffAt ℝ 2 ψ y) (hJ : (amat (fderiv ℝ ψ y)).det ≠ 0)
    (hu : ContDiffAt ℝ 2 u (ψ y)) (hGd : DifferentiableAt ℝ G (ψ y))
    (hsym : ∀ v w, G (ψ y) v w = G (ψ y) w v) (hdet : (mat (G (ψ y))).det ≠ 0)
    (hiso : pullback ψ G =ᶠ[𝓝 y] H) :
    lapB H (u ∘ ψ) y = lapB G u (ψ y) := by
  have h := lapB_pullback hψ hJ hu hGd hsym hdet
  unfold lapB at h ⊢
  rwa [hiso.eq_of_nhds, hiso.fderiv_eq] at h

/-! ### Stage 3: the round metric of S² in spherical coordinates -/

/-- `v ↦ w ↦ v k * w k`. -/
noncomputable def sq (k : Fin 2) : Bil 2 :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k)

/-- A diagonal metric `dθ² + s(θ,φ) dφ²` on coordinates `(x 0, x 1) = (θ, φ)`. -/
noncomputable def gDiag (s : E 2 → ℝ) (x : E 2) : Bil 2 := sq 0 + s x • sq 1

/-- The round metric `dθ² + sin²θ dφ²`. -/
noncomputable def gRound : E 2 → Bil 2 := gDiag fun x => Real.sin (x 0) ^ 2

open Matrix in
theorem mat_gDiag (s : E 2 → ℝ) (x : E 2) :
    mat (gDiag s x) = Matrix.diagonal ![1, s x] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mat, gDiag, sq, ev]

theorem fderiv_gDiag {s : E 2 → ℝ} {s' : E 2 →L[ℝ] ℝ} {x : E 2} (hs : HasFDerivAt s s' x) (a : E 2) :
    fderiv ℝ (gDiag s) x a = s' a • sq 1 :=
  fderiv_const_add_smul hs (sq 0) (sq 1) a

open Matrix in
/-- The Laplace–Beltrami operator of a diagonal metric `dθ² + s dφ²` at a point where `s ≠ 0`, `s'` the derivative of
`s`: `u₀₀ + (u₁₁ + ½ s'(e₀) u₀ − s'(e₁)/(2s) u₁)/s`. -/
theorem lapB_gDiag {s : E 2 → ℝ} {s' : E 2 →L[ℝ] ℝ} {x : E 2} (hs : HasFDerivAt s s' x) (h0 : s x ≠ 0)
    (u : E 2 → ℝ) :
    lapB (gDiag s) u x =
      fderiv ℝ (fderiv ℝ u) x (ev 0) (ev 0)
        + (fderiv ℝ (fderiv ℝ u) x (ev 1) (ev 1) + s' (ev 0) / 2 * fderiv ℝ u x (ev 0)
          - s' (ev 1) / (2 * s x) * fderiv ℝ u x (ev 1)) / s x := by
  unfold lapB LB hessG koszul grad
  have hinv : (Matrix.diagonal ![1, s x])⁻¹ = Matrix.diagonal ![1, (s x)⁻¹] := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; fin_cases i <;> simp [h0]
  rw [mat_gDiag, hinv]
  simp only [fderiv_gDiag hs]
  rw [lin_expand s' (Matrix.diagonal ![1, (s x)⁻¹] *ᵥ dvec (fderiv ℝ u x))]
  simp [Fin.sum_univ_two, Matrix.mulVec_diagonal, dvec, sq, ev, Matrix.diagonal_apply]
  field_simp
  ring

/-- **The round metric.** At `x = (θ, φ)` with `sin θ ≠ 0`:
`Δ u = ∂_θ²u + (cos θ / sin θ) ∂_θ u + (1/sin²θ) ∂_φ²u`, the formula of `sphLapS_coord'`. -/
theorem lapB_gRound (u : E 2 → ℝ) {x : E 2} (h0 : Real.sin (x 0) ≠ 0) :
    lapB gRound u x =
      fderiv ℝ (fderiv ℝ u) x (ev 0) (ev 0)
        + Real.cos (x 0) / Real.sin (x 0) * fderiv ℝ u x (ev 0)
        + 1 / Real.sin (x 0) ^ 2 * fderiv ℝ (fderiv ℝ u) x (ev 1) (ev 1) := by
  have hp : HasFDerivAt (fun x : E 2 => x 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt
  have hs : HasFDerivAt (fun x : E 2 => Real.sin (x 0) ^ 2)
      ((2 * Real.sin (x 0) * Real.cos (x 0)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x := by
    have h := ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x hp).pow 2
    convert h using 1
    ext v; simp; ring
  unfold gRound
  rw [lapB_gDiag hs (pow_ne_zero 2 h0)]
  simp [ev]
  field_simp
  ring

end CTG.LaplaceBeltrami

end


