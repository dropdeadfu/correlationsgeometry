import Mathlib

/-!
# Classical eigenfunctions of the Laplacian on the flat torus (Mathlib only)

Fourth Lean file of the project "From Correlations to Geometry"; it imports only Mathlib (tag v4.29.0)
and none of the other project files. Check with `cd lean && ./check_spectrum.sh`.

Content: for `C²`, `ℤ^d`-periodic functions `f : EuclideanSpace ℝ (Fin d) → ℂ` and Mathlib's Laplacian,
the equation `Δ f = -λ f` has a non-zero solution iff `λ = 4π²|n|²` for some `n ∈ ℤ^d`; the solution
space for `4π² q` is the span of the characters `e_n` with `|n|² = q`, and its dimension is the number
of lattice points of that shell (`eigenvalue_mem_lattice`, `eigenspace_ne_bot_iff`, `eigenspace_eq_span`,
`finrank_eigenspace`, `finrank_eigenspace_enum`).

What this is NOT: a statement on an unbounded self-adjoint operator on `L²`, on its spectrum, or on weak
eigenfunctions; "function on the torus" means a periodic function on `ℝ^d`. The eigenvalue statements of
the other files are not linked to these statements in one theorem.
No `sorry`, no `axiom`, no `native_decide`.
-/

open MeasureTheory UnitAddTorus

noncomputable section

namespace CTG.TorusSpectrum

/-! As in `Mathlib.Analysis.Fourier.AddCircleMulti` (where these instances are local), the measure
on `ℝ/ℤ` is the Haar probability measure. -/
attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (AddCircle.haarAddCircle (T := (1 : ℝ))))

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := (1 : ℝ))))

/-- ℝ^d with the Euclidean inner product. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The torus ℝ^d/ℤ^d. -/
abbrev T (d : ℕ) := UnitAddTorus (Fin d)

/-- The integer vector `k` as a point of ℝ^d. -/
def intVec (d : ℕ) (k : Fin d → ℤ) : E d := WithLp.toLp 2 (fun i => (k i : ℝ))

/-- ℤ^d-periodicity. -/
def ZPeriodic (d : ℕ) (g : E d → ℂ) : Prop := ∀ (x : E d) (k : Fin d → ℤ), g (x + intVec d k) = g x

/-- The projection ℝ^d → ℝ^d/ℤ^d. -/
def proj (d : ℕ) (x : E d) : T d := fun i => ((x i : ℝ) : UnitAddCircle)

theorem proj_add (d : ℕ) (x y : E d) : proj d (x + y) = proj d x + proj d y := by
  funext i
  show (((x + y) i : ℝ) : UnitAddCircle) = ((x i : ℝ) : UnitAddCircle) + ((y i : ℝ) : UnitAddCircle)
  rw [PiLp.add_apply]
  rfl

theorem proj_zero (d : ℕ) : proj d 0 = 0 := by
  have h := proj_add d 0 0
  rw [add_zero] at h
  have h2 : proj d 0 + proj d 0 = proj d 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem proj_intVec (d : ℕ) (k : Fin d → ℤ) : proj d (intVec d k) = 0 := by
  funext i
  show (((k i : ℤ) : ℝ) : UnitAddCircle) = 0
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩

theorem proj_surjective (d : ℕ) : Function.Surjective (proj d) := fun t =>
  ⟨WithLp.toLp 2 (fun i => (QuotientAddGroup.mk_surjective (t i)).choose),
    funext fun i => (QuotientAddGroup.mk_surjective (t i)).choose_spec⟩

theorem proj_continuous (d : ℕ) : Continuous (proj d) := by
  have h : Continuous (fun y : Fin d → ℝ => fun i => ((y i : ℝ) : UnitAddCircle)) :=
    continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
  exact h.comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))

theorem proj_isOpenMap (d : ℕ) : IsOpenMap (proj d) := by
  have h1 : IsOpenMap (Pi.map (fun (_ : Fin d) (y : ℝ) => (y : UnitAddCircle))) :=
    IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)
  exact h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenMap

theorem proj_eq_imp (d : ℕ) {x y : E d} (h : proj d x = proj d y) :
    ∃ k : Fin d → ℤ, y = x + intVec d k := by
  have h1 : ∀ i, ∃ k : ℤ, (k : ℝ) = y i - x i := by
    intro i
    have hi : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
    have h0 : (((y i - x i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr hi.symm
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
    exact ⟨k, by simpa using hk⟩
  choose k hk using h1
  refine ⟨k, PiLp.ext fun i => ?_⟩
  show y i = x i + ((k i : ℤ) : ℝ)
  rw [hk i]
  ring

theorem periodic_comp_proj (d : ℕ) (G : T d → ℂ) : ZPeriodic d (fun x => G (proj d x)) := by
  intro x k
  show G (proj d (x + intVec d k)) = G (proj d x)
  rw [proj_add, proj_intVec, add_zero]

/-- Descent of a function on ℝ^d to the torus (meaningful for periodic functions). -/
def desc (d : ℕ) (g : E d → ℂ) (t : T d) : ℂ := g (Function.surjInv (proj_surjective d) t)

theorem desc_proj (d : ℕ) {g : E d → ℂ} (hg : ZPeriodic d g) (x : E d) :
    desc d g (proj d x) = g x := by
  have hs : proj d (Function.surjInv (proj_surjective d) (proj d x)) = proj d x :=
    Function.surjInv_eq _ _
  obtain ⟨k, hk⟩ := proj_eq_imp d hs.symm
  show g (Function.surjInv (proj_surjective d) (proj d x)) = g x
  rw [hk, hg]

theorem desc_continuous (d : ℕ) {g : E d → ℂ} (hg : Continuous g) (hper : ZPeriodic d g) :
    Continuous (desc d g) := by
  have hq : Topology.IsQuotientMap (proj d) :=
    (proj_isOpenMap d).isQuotientMap (proj_continuous d) (proj_surjective d)
  rw [hq.continuous_iff]
  have h : desc d g ∘ proj d = g := funext fun x => desc_proj d hper x
  rw [h]
  exact hg

theorem integrable_of_cont {d : ℕ} {φ : T d → ℂ} (h : Continuous φ) :
    Integrable φ (volume : Measure (T d)) := by
  refine Integrable.mono' (integrable_const ‖(⟨φ, h⟩ : C(T d, ℂ))‖) h.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  exact ContinuousMap.norm_coe_le_norm (⟨φ, h⟩ : C(T d, ℂ)) t

theorem coeff_eq {d : ℕ} (G : T d → ℂ) (n : Fin d → ℤ) :
    mFourierCoeff G n = ∫ t, mFourier (-n) t * G t := by
  simp only [mFourierCoeff, smul_eq_mul]

/-! ## The characters -/

/-- `2πi⟨n,v⟩`. -/
def cc (d : ℕ) (n : Fin d → ℤ) (v : E d) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * ∑ i, (n i : ℂ) * ((v i : ℝ) : ℂ)

theorem cc_add (d : ℕ) (n : Fin d → ℤ) (x y : E d) : cc d n (x + y) = cc d n x + cc d n y := by
  simp only [cc, PiLp.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

theorem cc_smul (d : ℕ) (n : Fin d → ℤ) (h : ℝ) (v : E d) :
    cc d n (h • v) = (h : ℂ) * cc d n v := by
  have h1 : ∀ i, (n i : ℂ) * (((h • v) i : ℝ) : ℂ) = (h : ℂ) * ((n i : ℂ) * ((v i : ℝ) : ℂ)) := by
    intro i
    rw [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  unfold cc
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum]
  ring

theorem cc_single (d : ℕ) (n : Fin d → ℤ) (j : Fin d) :
    cc d n (EuclideanSpace.single j (1 : ℝ)) = 2 * (Real.pi : ℂ) * Complex.I * (n j : ℂ) := by
  unfold cc
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem cc_contDiff (d : ℕ) (n : Fin d → ℤ) {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun x : E d => cc d n x) := by
  unfold cc
  refine contDiff_const.mul (ContDiff.sum fun i _ => contDiff_const.mul ?_)
  exact Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply (p := 2))

/-- The character `e_n(x) = exp(2πi⟨n,x⟩)`, as the pull-back of Mathlib's `mFourier n`. -/
def e (d : ℕ) (n : Fin d → ℤ) (x : E d) : ℂ := mFourier n (proj d x)

theorem e_apply (d : ℕ) (n : Fin d → ℤ) (x : E d) : e d n x = Complex.exp (cc d n x) := by
  show ∏ i, fourier (n i) ((x i : ℝ) : UnitAddCircle) = Complex.exp (cc d n x)
  unfold cc
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem e_add (d : ℕ) (n : Fin d → ℤ) (x y : E d) : e d n (x + y) = e d n x * e d n y := by
  rw [e_apply, e_apply, e_apply, cc_add, Complex.exp_add]

theorem mFourier_add_arg {d : ℕ} (n : Fin d → ℤ) (s t : T d) :
    mFourier n (s + t) = mFourier n s * mFourier n t := by
  obtain ⟨x, rfl⟩ := proj_surjective d s
  obtain ⟨y, rfl⟩ := proj_surjective d t
  rw [← proj_add]
  exact e_add d n x y

theorem e_periodic (d : ℕ) (n : Fin d → ℤ) : ZPeriodic d (e d n) :=
  periodic_comp_proj d (fun t => mFourier n t)

theorem e_contDiff (d : ℕ) (n : Fin d → ℤ) {m : WithTop ℕ∞} : ContDiff ℝ m (e d n) := by
  have h : e d n = fun x => Complex.exp (cc d n x) := funext fun x => e_apply d n x
  rw [h]
  exact Complex.contDiff_exp.comp (cc_contDiff d n)

theorem e_differentiable (d : ℕ) (n : Fin d → ℤ) : Differentiable ℝ (e d n) :=
  (e_contDiff d n (m := 1)).differentiable one_ne_zero

/-! ## Directional derivatives -/

/-- Directional derivative. -/
def dir {d : ℕ} (v : E d) (g : E d → ℂ) : E d → ℂ := fun x => fderiv ℝ g x v

theorem line_hasDerivAt {d : ℕ} {g : E d → ℂ} (hg : Differentiable ℝ g) (x v : E d) (h : ℝ) :
    HasDerivAt (fun s : ℝ => g (x + s • v)) (fderiv ℝ g (x + h • v) v) h := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v h := by
    simpa using ((hasDerivAt_id h).smul_const v).const_add x
  exact (hg (x + h • v)).hasFDerivAt.comp_hasDerivAt h h1

theorem exp_line_hasDerivAt (c K : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c) * K)
      (Complex.exp (((0 : ℝ) : ℂ) * c) * (1 * c) * K) 0 := by
  have h4 : HasDerivAt (fun z : ℂ => Complex.exp (z * c))
      (Complex.exp (((0 : ℝ) : ℂ) * c) * (1 * c)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const c).cexp
  exact (h4.comp_ofReal).mul_const K

theorem fderiv_e (d : ℕ) (n : Fin d → ℤ) (x v : E d) :
    fderiv ℝ (e d n) x v = cc d n v * e d n x := by
  have h1 := line_hasDerivAt (e_differentiable d n) x v 0
  have h5 : (fun s : ℝ => e d n (x + s • v))
      = fun s : ℝ => Complex.exp ((s : ℂ) * cc d n v) * e d n x := by
    funext s
    rw [e_add, e_apply d n (s • v), cc_smul, mul_comm]
  rw [h5] at h1
  have h6 := h1.unique (exp_line_hasDerivAt (cc d n v) (e d n x))
  rw [zero_smul, add_zero] at h6
  rw [h6, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, one_mul]

theorem dir_contDiff {d : ℕ} {g : E d → ℂ} (hg : ContDiff ℝ 2 g) (v : E d) :
    ContDiff ℝ 1 (dir v g) :=
  (hg.fderiv_right (m := 1) one_add_one_eq_two.le).clm_apply contDiff_const

theorem dir_continuous {d : ℕ} {g : E d → ℂ} (hg : ContDiff ℝ 1 g) (v : E d) :
    Continuous (dir v g) :=
  (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem dir_periodic {d : ℕ} {g : E d → ℂ} (hg : ZPeriodic d g) (v : E d) :
    ZPeriodic d (dir v g) := by
  intro x k
  show fderiv ℝ g (x + intVec d k) v = fderiv ℝ g x v
  rw [← fderiv_comp_add_right]
  have h : (fun y => g (y + intVec d k)) = g := funext fun y => hg y k
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The Laplacian as the sum of the second directional derivatives along the coordinate axes. -/
theorem laplacian_eq_sum {d : ℕ} {f : E d → ℂ} (hf : ContDiff ℝ 2 f) (x : E d) :
    Laplacian.laplacian f x
      = ∑ j, dir (EuclideanSpace.single j (1 : ℝ)) (dir (EuclideanSpace.single j (1 : ℝ)) f) x := by
  show Laplacian.laplacian f x = ∑ j, fderiv ℝ (fun y => fderiv ℝ f y
    (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single j (1 : ℝ))
  have h0 := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin d) ℝ)) x
  refine h0.trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) one_add_one_eq_two.le).differentiable one_ne_zero) x
  have h2 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  have h9 : fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ))) x
      = (fderiv ℝ f x).comp (0 : E d →L[ℝ] E d)
        + (fderiv ℝ (fderiv ℝ f) x).flip (EuclideanSpace.single j (1 : ℝ)) := h2.fderiv
  rw [h9]
  simp [EuclideanSpace.basisFun_apply]

set_option backward.isDefEq.respectTransparency false in
theorem dir_const_mul {d : ℕ} {g : E d → ℂ} (hg : Differentiable ℝ g) (c : ℂ) (v : E d) :
    dir v (fun y => c * g y) = fun y => c * dir v g y := by
  funext y
  have h8 : fderiv ℝ (fun z => c * g z) y = c • fderiv ℝ g y := fderiv_const_mul (hg y) c
  show fderiv ℝ (fun z => c * g z) y v = c * fderiv ℝ g y v
  rw [h8]
  rfl

theorem laplacian_const_mul {d : ℕ} {f : E d → ℂ} (hf : ContDiff ℝ 2 f) (c : ℂ) (x : E d) :
    Laplacian.laplacian (fun y => c * f y) x = c * Laplacian.laplacian f x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  rw [laplacian_eq_sum (contDiff_const.mul hf) x, laplacian_eq_sum hf x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have a1 := dir_const_mul (hf1.differentiable one_ne_zero) c (EuclideanSpace.single j (1 : ℝ))
  have a2 := dir_const_mul ((dir_contDiff hf (EuclideanSpace.single j (1 : ℝ))).differentiable
    one_ne_zero) c (EuclideanSpace.single j (1 : ℝ))
  rw [a1]
  exact congrFun a2 x

/-! ## Stage 1: the characters are eigenfunctions -/

theorem laplacian_e (d : ℕ) (n : Fin d → ℤ) (x : E d) :
    Laplacian.laplacian (e d n) x
      = -(4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2) * e d n x := by
  rw [laplacian_eq_sum (e_contDiff d n) x]
  have h1 : ∀ v : E d, dir v (e d n) = fun y => cc d n v * e d n y :=
    fun v => funext fun y => fderiv_e d n y v
  have h2 : ∀ v : E d, dir v (dir v (e d n)) x = cc d n v * (cc d n v * e d n x) := by
    intro v
    have a : dir v (dir v (e d n)) = dir v (fun y => cc d n v * e d n y) := by rw [h1 v]
    rw [a, dir_const_mul (e_differentiable d n) (cc d n v) v]
    exact congrArg (fun z => cc d n v * z) (fderiv_e d n x v)
  rw [show (-(4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2) * e d n x)
      = ∑ j, (-(4 * (Real.pi : ℂ) ^ 2) * (n j : ℂ) ^ 2 * e d n x) by
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2, cc_single]
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * (n j : ℂ) ^ 2 * e d n x) * Complex.I_sq

/-! ## Stage 2: Fourier coefficients of derivatives -/

theorem integral_shift {d : ℕ} (n : Fin d → ℤ) (G : T d → ℂ) (a : T d) :
    ∫ t, mFourier (-n) t * G (t + a) = mFourier n a * ∫ t, mFourier (-n) t * G t := by
  have hpt : ∀ t, mFourier (-n) t * G (t + a)
      = mFourier n a * (mFourier (-n) (t + a) * G (t + a)) := by
    intro t
    have h1 : mFourier (-n) (t + a) * mFourier n a = mFourier (-n) t := by
      rw [mFourier_add_arg, mul_assoc, ← mFourier_add, neg_add_cancel, mFourier_zero]
      simp
    rw [← h1]
    ring
  calc ∫ t, mFourier (-n) t * G (t + a)
      = ∫ t, mFourier n a * (mFourier (-n) (t + a) * G (t + a)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = mFourier n a * ∫ t, mFourier (-n) (t + a) * G (t + a) := integral_const_mul _ _
    _ = mFourier n a * ∫ t, mFourier (-n) t * G t := by
        rw [integral_add_right_eq_self (fun t => mFourier (-n) t * G t) a]

/-- **First-order core lemma.** The Fourier coefficient of a directional derivative. -/
theorem coeff_dir {d : ℕ} {g : E d → ℂ} (hg : ContDiff ℝ 1 g) (hper : ZPeriodic d g)
    (v : E d) (n : Fin d → ℤ) :
    mFourierCoeff (desc d (dir v g)) n = cc d n v * mFourierCoeff (desc d g) n := by
  have hG : Continuous (desc d g) := desc_continuous d hg.continuous hper
  have hDper : ZPeriodic d (dir v g) := dir_periodic hper v
  have hD : Continuous (desc d (dir v g)) := desc_continuous d (dir_continuous hg v) hDper
  have hC : ∀ t, ‖desc d (dir v g) t‖ ≤ ‖(⟨desc d (dir v g), hD⟩ : C(T d, ℂ))‖ :=
    fun t => ContinuousMap.norm_coe_le_norm (⟨desc d (dir v g), hD⟩ : C(T d, ℂ)) t
  have hm1 : ∀ (m : Fin d → ℤ) (t : T d), ‖mFourier m t‖ ≤ 1 := fun m t => by
    have h := ContinuousMap.norm_coe_le_norm (mFourier m) t
    rwa [mFourier_norm] at h
  have hFc : ∀ h : ℝ, Continuous (fun t : T d => mFourier (-n) t * desc d g (t + proj d (h • v))) :=
    fun h => (map_continuous (mFourier (-n))).mul (hG.comp (continuous_add_right _))
  have hF'c : Continuous (fun t : T d =>
      mFourier (-n) t * desc d (dir v g) (t + proj d ((0 : ℝ) • v))) :=
    (map_continuous (mFourier (-n))).mul (hD.comp (continuous_add_right _))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (T d)))
    (F := fun (h : ℝ) (t : T d) => mFourier (-n) t * desc d g (t + proj d (h • v)))
    (F' := fun (h : ℝ) (t : T d) => mFourier (-n) t * desc d (dir v g) (t + proj d (h • v)))
    (x₀ := (0 : ℝ)) (bound := fun _ => ‖(⟨desc d (dir v g), hD⟩ : C(T d, ℂ))‖)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun h => (hFc h).aestronglyMeasurable)
    (integrable_of_cont (hFc 0))
    hF'c.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t h _ => by
      show ‖mFourier (-n) t * desc d (dir v g) (t + proj d (h • v))‖ ≤ _
      rw [norm_mul]
      calc ‖mFourier (-n) t‖ * ‖desc d (dir v g) (t + proj d (h • v))‖
          ≤ 1 * ‖(⟨desc d (dir v g), hD⟩ : C(T d, ℂ))‖ :=
            mul_le_mul (hm1 _ _) (hC _) (norm_nonneg _) zero_le_one
        _ = ‖(⟨desc d (dir v g), hD⟩ : C(T d, ℂ))‖ := one_mul _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun t h _ => by
      obtain ⟨x, rfl⟩ := proj_surjective d t
      have e1 : ∀ s : ℝ, desc d g (proj d x + proj d (s • v)) = g (x + s • v) := fun s => by
        rw [← proj_add]
        exact desc_proj d hper _
      have e2 : desc d (dir v g) (proj d x + proj d (h • v)) = fderiv ℝ g (x + h • v) v := by
        rw [← proj_add]
        exact desc_proj d hDper _
      have h3 := (line_hasDerivAt (hg.differentiable one_ne_zero) x v h).const_mul
        (mFourier (-n) (proj d x))
      show HasDerivAt (fun s : ℝ => mFourier (-n) (proj d x) * desc d g (proj d x + proj d (s • v)))
        (mFourier (-n) (proj d x) * desc d (dir v g) (proj d x + proj d (h • v))) h
      rw [e2]
      simp only [e1]
      exact h3)
  have hd1 : HasDerivAt (fun h : ℝ => ∫ t, mFourier (-n) t * desc d g (t + proj d (h • v)))
      (∫ t, mFourier (-n) t * desc d (dir v g) (t + proj d ((0 : ℝ) • v))) 0 := key.2
  have hfun : (fun h : ℝ => ∫ t, mFourier (-n) t * desc d g (t + proj d (h • v)))
      = fun h : ℝ => Complex.exp ((h : ℂ) * cc d n v) * ∫ t, mFourier (-n) t * desc d g t := by
    funext h
    rw [integral_shift n (desc d g) (proj d (h • v))]
    show e d n (h • v) * _ = _
    rw [e_apply, cc_smul]
  rw [hfun] at hd1
  have h6 := hd1.unique (exp_line_hasDerivAt (cc d n v) (∫ t, mFourier (-n) t * desc d g t))
  rw [coeff_eq, coeff_eq]
  have h7 : (∫ t, mFourier (-n) t * desc d (dir v g) (t + proj d ((0 : ℝ) • v)))
      = ∫ t, mFourier (-n) t * desc d (dir v g) t := by
    simp only [zero_smul, proj_zero, add_zero]
  rw [← h7, h6, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, one_mul]

/-- **Second-order core lemma.** The Fourier coefficients of the Laplacian of a `C²`,
ℤ^d-periodic function. -/
theorem coeff_laplacian {d : ℕ} {f : E d → ℂ} (hf : ContDiff ℝ 2 f) (hper : ZPeriodic d f)
    (n : Fin d → ℤ) :
    mFourierCoeff (desc d (Laplacian.laplacian f)) n
      = -(4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2) * mFourierCoeff (desc d f) n := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hΔ : Laplacian.laplacian f = fun x => ∑ j, dir (EuclideanSpace.single j (1 : ℝ))
      (dir (EuclideanSpace.single j (1 : ℝ)) f) x := funext fun x => laplacian_eq_sum hf x
  have hdesc : desc d (Laplacian.laplacian f) = fun t => ∑ j, desc d
      (dir (EuclideanSpace.single j (1 : ℝ)) (dir (EuclideanSpace.single j (1 : ℝ)) f)) t := by
    rw [hΔ]
    rfl
  have hint : ∀ j : Fin d, Integrable (fun t : T d => mFourier (-n) t * desc d
      (dir (EuclideanSpace.single j (1 : ℝ)) (dir (EuclideanSpace.single j (1 : ℝ)) f)) t) :=
    fun j => integrable_of_cont ((map_continuous (mFourier (-n))).mul
      (desc_continuous d (dir_continuous (dir_contDiff hf _) _)
        (dir_periodic (dir_periodic hper _) _)))
  have hj : ∀ j : Fin d, ∫ t, mFourier (-n) t * desc d
      (dir (EuclideanSpace.single j (1 : ℝ)) (dir (EuclideanSpace.single j (1 : ℝ)) f)) t
      = -(4 * (Real.pi : ℂ) ^ 2) * (n j : ℂ) ^ 2 * mFourierCoeff (desc d f) n := by
    intro j
    rw [← coeff_eq (desc d (dir (EuclideanSpace.single j (1 : ℝ))
      (dir (EuclideanSpace.single j (1 : ℝ)) f))) n,
      coeff_dir (dir_contDiff hf _) (dir_periodic hper _), coeff_dir hf1 hper, cc_single]
    linear_combination (4 * (Real.pi : ℂ) ^ 2 * (n j : ℂ) ^ 2 * mFourierCoeff (desc d f) n)
      * Complex.I_sq
  have hI : mFourierCoeff (fun t => ∑ j, desc d
      (dir (EuclideanSpace.single j (1 : ℝ)) (dir (EuclideanSpace.single j (1 : ℝ)) f)) t) n
      = ∑ j, ∫ t, mFourier (-n) t * desc d
      (dir (EuclideanSpace.single j (1 : ℝ)) (dir (EuclideanSpace.single j (1 : ℝ)) f)) t := by
    refine (coeff_eq _ n).trans ?_
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
      (integral_finset_sum _ fun j _ => hint j)
    simp only [Finset.mul_sum]
  have hs : ∑ j, -(4 * (Real.pi : ℂ) ^ 2) * (n j : ℂ) ^ 2 * mFourierCoeff (desc d f) n
      = -(4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2) * mFourierCoeff (desc d f) n := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [hdesc, hI, Finset.sum_congr rfl fun j _ => hj j, hs]

/-! ## Stages 3 and 4: eigenspaces -/

/-- The space of classical eigenfunctions: `C²`, ℤ^d-periodic, `Δ f = -lam • f`. -/
def eigenspace (d : ℕ) (lam : ℂ) : Submodule ℂ (E d → ℂ) where
  carrier := {f | ContDiff ℝ 2 f ∧ ZPeriodic d f ∧ ∀ x, Laplacian.laplacian f x = -lam * f x}
  zero_mem' := by
    refine ⟨contDiff_const, fun _ _ => rfl, fun x => ?_⟩
    have h : Laplacian.laplacian (fun _ : E d => (0 : ℂ)) = 0 := InnerProductSpace.laplacian_const
    show Laplacian.laplacian (fun _ : E d => (0 : ℂ)) x = -lam * 0
    rw [h]
    simp
  add_mem' := by
    rintro f g ⟨hf, hpf, hΔf⟩ ⟨hg, hpg, hΔg⟩
    refine ⟨hf.add hg, fun x k => ?_, fun x => ?_⟩
    · show f (x + intVec d k) + g (x + intVec d k) = f x + g x
      rw [hpf, hpg]
    · rw [hf.contDiffAt.laplacian_add hg.contDiffAt, hΔf, hΔg]
      show _ = -lam * (f x + g x)
      ring
  smul_mem' := by
    rintro c f ⟨hf, hpf, hΔf⟩
    refine ⟨hf.const_smul c, fun x k => ?_, fun x => ?_⟩
    · show c • f (x + intVec d k) = c • f x
      rw [hpf]
    · show Laplacian.laplacian (fun y => c * f y) x = -lam * (c * f x)
      rw [laplacian_const_mul hf c x, hΔf]
      ring

theorem mem_eigenspace {d : ℕ} {lam : ℂ} {f : E d → ℂ} :
    f ∈ eigenspace d lam ↔
      ContDiff ℝ 2 f ∧ ZPeriodic d f ∧ ∀ x, Laplacian.laplacian f x = -lam * f x := Iff.rfl

theorem e_mem (d : ℕ) (n : Fin d → ℤ) :
    e d n ∈ eigenspace d (4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2) :=
  ⟨e_contDiff d n, e_periodic d n, fun x => laplacian_e d n x⟩

theorem coeff_eigen {d : ℕ} {lam : ℂ} {f : E d → ℂ} (hf : f ∈ eigenspace d lam)
    (n : Fin d → ℤ) :
    (lam - 4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2) * mFourierCoeff (desc d f) n = 0 := by
  obtain ⟨hc, hper, hΔ⟩ := hf
  have h1 := coeff_laplacian hc hper n
  have h2 : desc d (Laplacian.laplacian f) = fun t => -lam * desc d f t := by
    have h : Laplacian.laplacian f = fun x => -lam * f x := funext hΔ
    rw [h]
    rfl
  have h3 : mFourierCoeff (fun t => -lam * desc d f t) n = -lam * mFourierCoeff (desc d f) n := by
    have h4 : ∫ t, -lam * (mFourier (-n) t * desc d f t)
        = -lam * ∫ t, mFourier (-n) t * desc d f t := integral_const_mul _ _
    rw [coeff_eq, coeff_eq (desc d f) n, ← h4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show mFourier (-n) t * (-lam * desc d f t) = -lam * (mFourier (-n) t * desc d f t)
    ring
  rw [h2, h3] at h1
  linear_combination -h1

/-- A classical eigenfunction is the finite sum of its Fourier modes on the shell. -/
theorem eigen_repr {d : ℕ} {lam : ℂ} {f : E d → ℂ} (hf : f ∈ eigenspace d lam)
    (S : Finset (Fin d → ℤ))
    (hS : ∀ n : Fin d → ℤ, lam = 4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2 → n ∈ S) (x : E d) :
    f x = ∑ n ∈ S, mFourierCoeff (desc d f) n * e d n x := by
  have hper : ZPeriodic d f := hf.2.1
  have hcont : Continuous (desc d f) := desc_continuous d hf.1.continuous hper
  have hzero : ∀ n ∉ S, mFourierCoeff (⇑(⟨desc d f, hcont⟩ : C(T d, ℂ))) n = 0 := by
    intro n hn
    rcases mul_eq_zero.mp (coeff_eigen hf n) with h | h
    · exact absurd (hS n (sub_eq_zero.mp h)) hn
    · exact h
  have hsum : Summable (mFourierCoeff (⇑(⟨desc d f, hcont⟩ : C(T d, ℂ)))) :=
    summable_of_ne_finset_zero hzero
  have h1 := hasSum_mFourier_series_apply_of_summable hsum (proj d x)
  have h2 : HasSum (fun i => mFourierCoeff (⇑(⟨desc d f, hcont⟩ : C(T d, ℂ))) i
      • mFourier i (proj d x))
      (∑ n ∈ S, mFourierCoeff (⇑(⟨desc d f, hcont⟩ : C(T d, ℂ))) n • mFourier n (proj d x)) :=
    hasSum_sum_of_ne_finset_zero fun n hn => by rw [hzero n hn, zero_smul]
  have h3 := h1.unique h2
  have h4 : (⟨desc d f, hcont⟩ : C(T d, ℂ)) (proj d x) = f x := desc_proj d hper x
  rw [← h4, h3]
  exact Finset.sum_congr rfl fun n _ => rfl

/-- **Stage 3.** The eigenvalue of a nonzero classical eigenfunction is `4π²|n|²` for some
lattice point `n`. -/
theorem eigenvalue_mem_lattice {d : ℕ} {lam : ℂ} {f : E d → ℂ} (hf : f ∈ eigenspace d lam)
    (hne : f ≠ 0) : ∃ n : Fin d → ℤ, lam = 4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2 := by
  by_contra hcon
  apply hne
  funext x
  have h := eigen_repr hf ∅ (fun n hn => absurd ⟨n, hn⟩ hcon) x
  simpa using h

theorem e_ne_zero (d : ℕ) (n : Fin d → ℤ) : e d n ≠ 0 := by
  intro h0
  have h := congrFun h0 0
  rw [e_apply] at h
  exact Complex.exp_ne_zero _ h

theorem eigenspace_ne_bot_iff (d : ℕ) (lam : ℂ) :
    eigenspace d lam ≠ ⊥ ↔ ∃ n : Fin d → ℤ, lam = 4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2 := by
  constructor
  · intro h
    obtain ⟨f, hf, hne⟩ := (Submodule.ne_bot_iff _).mp h
    exact eigenvalue_mem_lattice hf hne
  · rintro ⟨n, rfl⟩
    exact (Submodule.ne_bot_iff _).mpr ⟨e d n, e_mem d n, e_ne_zero d n⟩

/-- The lattice points with `|n|² = q`. -/
def shell (d : ℕ) (q : ℤ) : Set (Fin d → ℤ) := {n | ∑ i, n i ^ 2 = q}

theorem int_le_sq (a : ℤ) : a ≤ a ^ 2 := by
  rcases le_or_gt a 0 with h | h
  · exact le_trans h (sq_nonneg a)
  · nlinarith [mul_nonneg (le_of_lt h) (by omega : (0 : ℤ) ≤ a - 1)]

theorem shell_finite (d : ℕ) (q : ℤ) : (shell d q).Finite := by
  refine (Set.finite_Icc (fun _ : Fin d => -q) (fun _ => q)).subset fun n hn => ?_
  have hn' : ∑ i, n i ^ 2 = q := hn
  have hi : ∀ i, n i ^ 2 ≤ q := fun i => by
    rw [← hn']
    exact Finset.single_le_sum (f := fun j => n j ^ 2) (fun j _ => sq_nonneg (n j))
      (Finset.mem_univ i)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := int_le_sq (-n i)
    rw [neg_sq] at h1
    have h2 := hi i
    show -q ≤ n i
    linarith
  · have h1 := int_le_sq (n i)
    have h2 := hi i
    show n i ≤ q
    linarith

theorem shell_iff (d : ℕ) (q : ℤ) (n : Fin d → ℤ) :
    (4 * (Real.pi : ℂ) ^ 2 * (q : ℂ) = 4 * (Real.pi : ℂ) ^ 2 * ∑ i, (n i : ℂ) ^ 2)
      ↔ n ∈ shell d q := by
  have hpi : (4 * (Real.pi : ℂ) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  constructor
  · intro h
    have h1 : (q : ℂ) = ∑ i, (n i : ℂ) ^ 2 := mul_left_cancel₀ hpi h
    have h3 : q = ∑ i, n i ^ 2 := by exact_mod_cast h1
    exact h3.symm
  · intro h
    have h' : ∑ i, n i ^ 2 = q := h
    have h1 : (q : ℂ) = ∑ i, (n i : ℂ) ^ 2 := by exact_mod_cast h'.symm
    rw [h1]

/-- **Stage 4.** The eigenspace for `4π²q` is the span of the characters of the shell. -/
theorem eigenspace_eq_span (d : ℕ) (q : ℤ) :
    eigenspace d (4 * (Real.pi : ℂ) ^ 2 * (q : ℂ))
      = Submodule.span ℂ (Set.range fun n : shell d q => e d (n : Fin d → ℤ)) := by
  apply le_antisymm
  · intro f hf
    have hrep : f = ∑ n ∈ (shell_finite d q).toFinset, mFourierCoeff (desc d f) n • e d n := by
      funext x
      refine (eigen_repr hf (shell_finite d q).toFinset
        (fun n hn => (shell_finite d q).mem_toFinset.mpr ((shell_iff d q n).mp hn)) x).trans ?_
      rw [Finset.sum_apply]
      rfl
    rw [hrep]
    exact Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨n, (shell_finite d q).mem_toFinset.mp hn⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    show e d (n : Fin d → ℤ) ∈ eigenspace d (4 * (Real.pi : ℂ) ^ 2 * (q : ℂ))
    rw [(shell_iff d q n).mpr n.2]
    exact e_mem d (n : Fin d → ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem e_linearIndependent (d : ℕ) : LinearIndependent ℂ (fun n : Fin d → ℤ => e d n) := by
  have h1 : LinearIndependent ℂ (fun n : Fin d → ℤ => (mFourier n : C(T d, ℂ))) := by
    have h0 : LinearIndependent ℂ (mFourierLp (d := Fin d) 2) :=
      (orthonormal_mFourier (d := Fin d)).linearIndependent
    exact LinearIndependent.of_comp
      ((ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (T d)) ℂ :
        C(T d, ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure (T d))) :
        C(T d, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (T d))) h0
  let P : C(T d, ℂ) →ₗ[ℂ] (E d → ℂ) :=
    { toFun := fun G x => G (proj d x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker P = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro G hG
    ext t
    obtain ⟨x, rfl⟩ := proj_surjective d t
    exact congrFun hG x
  exact h1.map' P hker

/-- **Stage 4, multiplicity.** The dimension of the eigenspace for `4π²q` is the number of
lattice points with `|n|² = q`. -/
theorem finrank_eigenspace (d : ℕ) (q : ℤ) :
    Module.finrank ℂ (eigenspace d (4 * (Real.pi : ℂ) ^ 2 * (q : ℂ))) = Nat.card (shell d q) := by
  haveI : Fintype (shell d q) := (shell_finite d q).fintype
  rw [eigenspace_eq_span, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card ((e_linearIndependent d).comp _ Subtype.val_injective)

/-- **Multiplicity along an enumeration of the lattice.** For any bijection `ε : ℕ → ℤ^d`, the
dimension of the eigenspace for `4π²q` is the number of positions `j` with `|ε j|² = q`. -/
theorem finrank_eigenspace_enum (d : ℕ) (ε : ℕ → (Fin d → ℤ)) (hε : Function.Bijective ε)
    (q : ℤ) :
    Module.finrank ℂ (eigenspace d (4 * (Real.pi : ℂ) ^ 2 * (q : ℂ)))
      = Nat.card {j : ℕ // ∑ i, ε j i ^ 2 = q} := by
  rw [finrank_eigenspace]
  exact (Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective ε hε) (fun _ => Iff.rfl))).symm

end CTG.TorusSpectrum
