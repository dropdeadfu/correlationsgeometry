# Stage-2 shortlist: statements rated 3 (general, squarely on a need), with the source wording

398 statements in 253 files. Mechanical check of those files (comments stripped): 253 clean, 0 flagged.


## N1

### AlgebraicGeometry/ComplexMultiplication/LatticeGaussian [3] lattice_gaussian_poly_summable  (general; file: clean)
Reader: For a > 0: the family |l|^k exp(-a |l|^2 + b |l|) over all vectors l of a discrete lattice L is summable.  Caveat: summability only, no explicit bound on the sum; L and ambient space are file variables not shown

```lean
-- /-- Gaussian decay is summable on the actual lattice in its ambient norm. -/
theorem lattice_gaussian_poly_summable (a b : ℝ) (ha : 0 < a) (k : ℕ) :
 Summable (fun l : L => ‖l‖ ^ k * Real.exp (-a * ‖l‖ ^ 2 + b * ‖l‖))
```

### AlgebraicGeometry/ComplexMultiplication/LatticeGaussian [4] lattice_gaussian_summable  (general; file: clean)
Reader: For a > 0: exp(-a |l|^2 + b |l|) is summable over all vectors l of a discrete lattice L.  Caveat: summability only, no explicit bound; L and ambient space are file variables not shown

```lean
theorem lattice_gaussian_summable (a b : ℝ) (ha : 0 < a) :
 Summable (fun l : L => Real.exp (-a * ‖l‖ ^ 2 + b * ‖l‖))
```

### Analysis/Fourier/WavePackets/Poisson [14] poisson_of_continuous_periodization  (special; file: clean)
Reader: Poisson summation on ℝ^n for integrable f with continuous periodization and summable Fourier samples: Σ f(k+x) = Σ sample(k) · character_k(x).  Caveat: lattice ℤ^n only, every dimension n (other lattices need a linear change of variables); scored 3 despite that

```lean
-- /-- Multidimensional Poisson summation for an integrable function whose periodization is continuous and whose dual-lattice samples are summable. -/
theorem poisson_of_continuous_periodization {n : ℕ}
 {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : Integrable f)
 (F : C(UnitAddTorus (Fin n), ℂ))
 (hF : ∀ x, F (torusProjection x) = ∑' k : Fin n → ℤ, f (integerVector k + x))
 (hs : Summable (latticeFourierSample f)) (x : EuclideanSpace ℝ (Fin n)) :
 (∑' k : Fin n → ℤ, f (integerVector k + x)) =
 ∑' k : Fin n → ℤ, latticeFourierSample f k *
 UnitAddTorus.mFourier k (torusProjection x)
```

### Analysis/Fourier/WavePackets/Poisson [27] schwartz_poisson  (special; file: clean)
Reader: Poisson summation for Schwartz f on ℝ^n: Σ_k f(k+x) = Σ_k 𝓕f(k) · mFourier k (projection of x), in every finite dimension.  Caveat: lattice ℤ^n only (other lattices need a linear change of variables); a Gaussian must be supplied as a SchwartzMap; scored 3 despite that

```lean
-- /-- Poisson summation on the full Euclidean integer lattice, in every finite dimension. -/
theorem schwartz_poisson {n : ℕ} (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
 (x : EuclideanSpace ℝ (Fin n)) :
 (∑' k : Fin n → ℤ, f (integerVector k + x)) =
 ∑' k : Fin n → ℤ, 𝓕 f (integerVector k) *
 UnitAddTorus.mFourier k (torusProjection x)
```

### Analysis/PlanarPacking/GaussianSeries [1] gaussian_shift_poisson  (general; file: clean)
Reader: For Re a > 0 and real d: sum over n in Z of exp(-pi a (n+d)^2) = a^(-1/2) * sum over n in Z of exp(-pi n^2/a + 2 pi i n d).  Caveat: one-dimensional; complex a with complex power a^(1/2); compare Mathlib's Jacobi theta results before copying

```lean
lemma gaussian_shift_poisson {a : ℂ} (ha : 0 < a.re) (d : ℝ) :
 (∑' n : ℤ, Complex.exp (-(Real.pi:ℂ)*a*((n:ℂ)+d)^2)) =
 1/a^(1/2:ℂ) * ∑' n : ℤ,
 Complex.exp (-(Real.pi:ℂ)/a*(n:ℂ)^2+2*(Real.pi:ℂ)*Complex.I*n*d)
```

### Analysis/Theta/GaussianConvergenceGaussian [19] shifted_gaussian_summable  (general; file: clean)
Reader: For any discrete ℤ-submodule L of ι → ℝ, C ≥ 0, c > 0, any b, d: x ↦ C(1+‖x‖)^d · exp(−c‖x‖² + b‖x‖) is summable over L.  Caveat: summability only, no explicit bound; norm is that of the function space ι → ℝ (sup norm), not Euclidean; ι instances not shown

```lean
lemma shifted_gaussian_summable (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
 (C c b : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (d : ℕ) :
 Summable (fun x : L => C * (1 + ‖(x : ι → ℝ)‖) ^ d *
 Real.exp (-c * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖))
```

### Combinatorics/Progressions/Fourier/LatticeGaussianMeanFourier [3] normalizedLatticeGaussian_zero_eq_dual  (general; file: clean)
Reader: For t > 0: normalised lattice Gaussian of Lambda at 0 equals the Gaussian mass of the dual lattice at parameter 1/t at 0.  Caveat: theta inversion at the origin only; both definitions and the hypotheses on Lambda hidden

```lean
theorem normalizedLatticeGaussian_zero_eq_dual {t : ℝ} (ht : 0 < t) :
 normalizedLatticeGaussian Λ t 0 = latticeGaussianMass (euclideanDualLattice Λ) t⁻¹ 0
```

### Combinatorics/Progressions/Fourier/LatticeGaussianMeanFourier [4] normalizedLatticeGaussian_le_origin  (general; file: clean)
Reader: For t > 0 and every x: normalised lattice Gaussian at x is at most its value at 0.  Caveat: definition hidden

```lean
theorem normalizedLatticeGaussian_le_origin {t : ℝ} (ht : 0 < t) (x : E) :
 normalizedLatticeGaussian Λ t x ≤ normalizedLatticeGaussian Λ t 0
```

### Combinatorics/Progressions/Fourier/LatticeTorusFourierCoefficient [5] latticeGaussianTorus_coefficient  (general; file: clean)
Reader: covolume(Lambda) times the n-th Fourier coefficient of the lattice Gaussian on the unit torus equals t^(-dim/2) * exp(-pi ||dual point of n||^2 / t).  Caveat: latticeGaussianTorus and latticeDualPoint bodies hidden; coefficients only, the series identity is not stated here

```lean
theorem latticeGaussianTorus_coefficient (b : Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) (n : ι → ℤ) :
 (ZLattice.covolume Λ : ℂ) * UnitAddTorus.mFourierCoeff (latticeGaussianTorus Λ b ht) n =
 ((((Real.sqrt t) ^ Module.finrank ℝ E)⁻¹ *
 Real.exp (-Real.pi / t * ‖latticeDualPoint Λ b n‖ ^ 2) : ℝ) : ℂ)
```

### Combinatorics/Progressions/Lattices/GaussianLatticeDistance [4] latticeGaussianTail_bound  (general; file: clean)
Reader: For t > 0, R >= 0: latticeGaussianTail Lambda t R <= exp(-pi t R^2 / 2) * 2^dim * latticeGaussianMass Lambda t 0.  Caveat: bodies of latticeGaussianTail and latticeGaussianMass hidden ([3] shows the summand)

```lean
theorem latticeGaussianTail_bound {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R) :
 latticeGaussianTail Λ t R ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
 (2 : ℝ) ^ Module.finrank ℝ E * latticeGaussianMass Λ t 0
```

### Combinatorics/Progressions/Lattices/GaussianLatticeDistance [5] latticeGaussianMass_le_origin  (general; file: clean)
Reader: For t > 0 and every x: latticeGaussianMass Lambda t x <= latticeGaussianMass Lambda t 0.  Caveat: definition hidden

```lean
theorem latticeGaussianMass_le_origin {t : ℝ} (ht : 0 < t) (x : E) :
 latticeGaussianMass Λ t x ≤ latticeGaussianMass Λ t 0
```

### Combinatorics/Progressions/Lattices/GaussianLatticeDistance [6] normalizedLatticeGaussian_le_of_far  (general; file: clean)
Reader: If x is at distance >= R from every lattice point, normalised lattice Gaussian at x <= exp(-pi t R^2 / 2) * 2^dim * its value at 0.  Caveat: definition hidden; factor 1/2 in the exponent

```lean
theorem normalizedLatticeGaussian_le_of_far {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
 (x : E) (hfar : ∀ m : Λ, R ≤ ‖x - (m : E)‖) :
 normalizedLatticeGaussian Λ t x ≤ Real.exp (-Real.pi * t * R ^ 2 / 2) *
 (2 : ℝ) ^ Module.finrank ℝ E * normalizedLatticeGaussian Λ t 0
```

### Combinatorics/Progressions/Lattices/LatticeDualCoordinates [12] latticeDualPoint_character  (general; file: clean)
Reader: euclideanCharacter of the dual point of n, at the point with basis coordinates x, equals Mathlib's UnitAddTorus.mFourier n at x reduced to the unit torus.  Caveat: euclideanCharacter body hidden (presumably exp(2πi⟨ξ,x⟩)); bridges a general lattice to UnitAddTorus Fourier theory

```lean
theorem latticeDualPoint_character (b : Basis ι ℤ Λ) (n : ι → ℤ) (x : ι → ℝ) :
 euclideanCharacter (latticeDualPoint Λ b n) ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) =
 UnitAddTorus.mFourier n (fun i => (x i : UnitAddCircle))
```

### Combinatorics/Progressions/Lattices/LatticeGaussianCoefficient [1] lattice_periodization_integral  (general; file: clean)
Reader: For continuous integrable f with summable bounds C m on the translates over a finite-measure fundamental domain S, the integral over S of the Λ-periodisation of f equals the integral of f.  Caveat: any Haar measure μ; needs the uniform bound ‖f (x - m)‖ ≤ C m on S

```lean
theorem lattice_periodization_integral (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] (μ : Measure E) [μ.IsAddHaarMeasure]
 (S : Set E) (hS : MeasurableSet S) (hfinite : μ S < ⊤)
 (hfund : IsAddFundamentalDomain Λ S μ) (f : E → ℂ)
 (hf : Continuous f) (hint : Integrable f μ) (C : Λ → ℝ) (hC : Summable C)
 (hbound : ∀ m : Λ, ∀ x ∈ S, ‖f (x - m)‖ ≤ C m) :
 (∫ x in S, ∑' m : Λ, f (x - m) ∂μ) = ∫ x, f x ∂μ
```

### Combinatorics/Progressions/Lattices/LatticeGaussianCoefficient [2] latticeGaussian_integral_character  (general; file: clean)
Reader: For t > 0 and ξ in the dual lattice: integral over a bounded fundamental domain of character(-ξ) times latticeGaussianMass Λ t equals (sqrt t ^ dim)⁻¹ * exp(-π ‖ξ‖² / t).  Caveat: latticeGaussianMass and euclideanCharacter bodies hidden; Fourier coefficients of the periodised Gaussian, unnormalised by covolume

```lean
theorem latticeGaussian_integral_character (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] (S : Set E) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
 (hfund : IsAddFundamentalDomain Λ S volume) {t : ℝ} (ht : 0 < t)
 (ξ : E) (hξ : ξ ∈ euclideanDualLattice Λ) :
 (∫ x in S, euclideanCharacter (-ξ) x * (latticeGaussianMass Λ t x : ℂ)) =
 ((((Real.sqrt t) ^ Module.finrank ℝ E)⁻¹ *
 Real.exp (-Real.pi / t * ‖ξ‖ ^ 2) : ℝ) : ℂ)
```

### Combinatorics/Progressions/Lattices/LatticeGaussianPoisson [4] normalizedLatticeGaussian_poisson  (general; file: clean)
Reader: Poisson summation: for t > 0 and all x, normalizedLatticeGaussian Λ t x equals the sum over dual-lattice ξ of exp(-π ‖ξ‖² / t) times euclideanCharacter ξ x.  Caveat: normalisation is inside the hidden def normalizedLatticeGaussian (LatticeSheetHaar [9]); hypotheses on Λ and E file-level; [3] is the same with an explicit basis

```lean
theorem normalizedLatticeGaussian_poisson {t : ℝ} (ht : 0 < t) (x : E) :
 (normalizedLatticeGaussian Λ t x : ℂ) =
 ∑' ξ : euclideanDualLattice Λ,
 (Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2) : ℂ) * euclideanCharacter (ξ : E) x
```

### Combinatorics/Progressions/Lattices/LatticeHyperplaneBasis [18] lattice_gaussian_summable  (general; file: clean)
Reader: For a discrete Λ, t > 0 and any x, the family m ↦ exp(-π t ‖x - m‖²) over m in Λ is summable.  Caveat: hypotheses on E file-level, not shown; no explicit bound, summability only

```lean
theorem lattice_gaussian_summable (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 {t : ℝ} (ht : 0 < t) (x : E) :
 Summable (fun m : Λ => Real.exp (-Real.pi * t * ‖x - (m : E)‖ ^ 2))
```

### Combinatorics/Progressions/Lattices/LatticeSheetHaar [7] latticeBasis_integral_cube  (general; file: clean)
Reader: covolume Λ times the integral over the unit cube [0,1)^ι of f at the point with basis coordinates x equals the integral of f over the ZSpan fundamental domain.  Caveat: f complex-valued, no integrability hypothesis visible

```lean
theorem latticeBasis_integral_cube (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) (f : E → ℂ) :
 (ZLattice.covolume Λ : ℂ) *
 (∫ x : ι → ℝ in Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1),
 f ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x)) =
 ∫ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), f x
```

### Combinatorics/Progressions/Lattices/StandardLatticeGaussianBound [1] standardLatticeGaussian_mass_bound  (special; file: clean)
Reader: For t > 0: latticeGaussianMass of the standard integer lattice at parameter t⁻¹ and point 0 is at most (1 + 2 t) ^ card ι.  Caveat: Z^ι only, any dimension; body of latticeGaussianMass hidden (LatticeHyperplaneBasis [18] suggests summand exp(-π s ‖m‖²), here s = t⁻¹)

```lean
theorem standardLatticeGaussian_mass_bound {t : ℝ} (ht : 0 < t) :
 latticeGaussianMass (standardEuclideanLattice ι) t⁻¹ 0 ≤ (1 + 2 * t) ^ Fintype.card ι
```

### Geometry/LatticeCovering/CircuitLattices [32] tsum_ennreal_fin_prod  (general; file: clean)
Reader: Sum over Z^r of a product of one-variable terms f(a_j) equals the r-th power of the sum of f over Z.  Caveat: values in ENNReal; index type Fin r -> Z

```lean
lemma tsum_ennreal_fin_prod (r : ℕ) (f : ℤ → ℝ≥0∞) :
 (∑' a : Fin r → ℤ, ∏ j, f (a j)) = (∑' z, f z)^r
```

### Geometry/NodalSets/Waves/GaussianTailBound [1] finite_gaussian_tail  (general; file: clean)
Reader: If f_i <= R exp(-2a d_i^2) and sum_i exp(-a d_i^2) <= B over a finite index set, then the sum of f_i over indices with d_i > r is at most R B exp(-a r^2).  Caveat: finite index type; the bound B on the Gaussian sum must be supplied

```lean
lemma finite_gaussian_tail {ι : Type*} [Fintype ι] (d f : ι → ℝ)
 {a R B r : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (hr : 0 ≤ r)
 (hd : ∀ i, 0 ≤ d i) (hf : ∀ i, f i ≤ R*Real.exp (-2*a*(d i)^2))
 (hs : ∑ i, Real.exp (-a*(d i)^2) ≤ B) :
 ∑ i ∈ Finset.univ.filter (fun i ↦ r < d i), f i ≤
 R*B*Real.exp (-a*r^2)
```

### Geometry/NodalSets/Waves/ShiftedGaussianSum [4] finite_shifted_gaussian_sum_pi  (general; file: clean)
Reader: For a>0 and any d there is C>0 with sum over z in any finite subset of Z^d of exp(-a*|x-z|^2) <= C, uniformly in the shift x in R^d.  Caveat: C only existential (depends on a, d), not explicit; standard lattice Z^d only; finite sums, no tsum statement

```lean
theorem finite_shifted_gaussian_sum_pi {d : ℕ} {a : ℝ} (ha : 0 < a) :
 ∃ C > 0, ∀ (x : Fin d → ℝ) (s : Finset (Fin d → ℤ)),
 ∑ z ∈ s, Real.exp (-a*∑ i, (x i-(z i:ℝ))^2) ≤ C
```

### Geometry/TranslativeCovering/LatticeAveraging [4] one_coset  (general; file: clean)
Reader: Unfolding: for a discrete ℤ-submodule Λ with fundamental domain F and measurable f ≥ 0, ∫ over F of Σ_{l∈Λ} f(y−p−l) = ∫ f.  Caveat: ℝ≥0∞-valued (lintegral) form; abbrev Space n not shown

```lean
lemma one_coset {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
 {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
 (p : Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
 ∫⁻ y in F,∑' l : Λ,f (y-p-l.val) = ∫⁻ x,f x
```

### MathematicalPhysics/NavierStokes/ForcedComputation/Scalar/TorusHeatGaussianBound [1] gaussian_nat_tsum_le  (general; file: clean)
Reader: For b > 0, the sum over natural numbers n of exp(-b n^2) is at most 1 + sqrt(pi/b).  Caveat: one-dimensional and over N, not Z or Z^d; a lattice version has to be assembled from products

```lean
theorem gaussian_nat_tsum_le {b : ℝ} (hb : 0 < b) :
 (∑' n : ℕ, Real.exp (-b * (n : ℝ) ^ 2)) ≤ 1 + Real.sqrt (Real.pi / b)
```

### NumberTheory/CubicGauss/LaplaceBounds [13] finite_laplace_power_bound  (general; file: clean)
Reader: If the partial sums of f over {n_h < Y} are at most C*Y^p for all Y>0 (p>-1, n_h>=0), then sum exp(-n_h/X)*f_h <= C*X^p*Gamma(p+1).  Caveat: finite index set only; turns a counting bound into a heat-trace bound; no sign hypothesis on f is visible

```lean
theorem finite_laplace_power_bound {ι : Type*} (H : Finset ι) (n f : ι → ℝ)
 {X C p : ℝ} (hX : 0 < X) (hp : -1 < p) (hn : ∀ h ∈ H, 0 ≤ n h)
 (hcut : ∀ Y : ℝ, 0 < Y → ∑ h ∈ H with n h < Y, f h ≤ C * Y^p) :
 ∑ h ∈ H, Real.exp (-n h/X) * f h ≤ C * X^p * Real.Gamma (p+1)
```

### NumberTheory/CubicGram/Periodization [1] schwartz_summable_lattice  (general; file: clean)
Reader: A Schwartz function on E is summable over any Z-submodule L of E with the discrete topology.  Caveat: E is a file variable (its hypotheses are not shown); Schwartz functions only

```lean
lemma schwartz_summable_lattice (L : Submodule ℤ E) [DiscreteTopology L]
 (f : 𝓢(E, ℂ)) : Summable (fun z : L => f z)
```

### NumberTheory/CubicGram/Periodization [4] periodization_apply  (general; file: clean)
Reader: The periodization of a Schwartz f over a discrete Z-submodule L, a continuous function, equals the sum over z in L of f(x+z) at every x.  Caveat: periodization body not shown ([3]); [5] gives L-periodicity

```lean
lemma periodization_apply (L : Submodule ℤ E) [DiscreteTopology L]
 (f : 𝓢(E, ℂ)) (x : E) :
 periodization L f x = ∑' z : L, f (x + (z : E))
```

### NumberTheory/PrimePackets/LatticeTheta [17] normalizedTheta_inversion  (general; file: clean)
Reader: Theta inversion for an arbitrary lattice basis B in any finite dimension, t>0: normalizedTheta B t = |det B|^(-1) * t^(-d/2) * normalizedTheta (adjointEquiv B.symm) (1/t).  Caveat: normalizedTheta and adjointEquiv bodies not shown (exponent normalisation unseen); value at the lattice origin only, no shift

```lean
lemma normalizedTheta_inversion (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
 (t : ℝ) (ht : 0 < t) :
 normalizedTheta B t = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
 (t:ℂ)^(-((Fintype.card d:ℂ)/2)) * normalizedTheta (adjointEquiv B.symm) t⁻¹
```

### RepresentationTheory/Theta/PoissonAutomorphyNormalizationData [86] schwartz_lattice_summable  (general; file: clean)
Reader: For a discrete ℤ-submodule L of V and a Schwartz function f, the norms ‖f x‖ are summable over x in L.  Caveat: V and its instances are file variables (not shown); no explicit bound on the sum

```lean
theorem schwartz_lattice_summable (L : Submodule ℤ V) [DiscreteTopology L]
 (f : SchwartzMap V ℂ) : Summable (fun x : L => ‖f x.val‖)
```

### RepresentationTheory/Theta/PoissonAutomorphyNormalizationData [97] latticePeriodization_apply  (general; file: clean)
Reader: The periodisation of a Schwartz f over a discrete ℤ-submodule L, built as a continuous map on V, equals the sum over a in L of f (x + a).  Caveat: latticePeriodization is the project's def [96] of type C(V, ℂ); V is a file variable

```lean
theorem latticePeriodization_apply (L : Submodule ℤ V) [DiscreteTopology L]
 (f : SchwartzMap V ℂ) (x : V) :
 latticePeriodization L f x = ∑' a : L, f (x + a.val)
```

### RepresentationTheory/Weil/AdelicSplitting/LatticePoisson [6] real_lattice_poisson_positive  (general; file: clean)
Reader: Poisson summation for the lattice spanned by a basis b of E: sum of the B-Fourier transform over dual-lattice points equals basisHaarFactor times the sum of f over lattice points.  Caveat: hypothesis B.SeparatingLeft; E, b, B, μ file variables; basisHaarFactor (covolume-type factor) and latticeDualCoordinates bodies hidden

```lean
theorem real_lattice_poisson_positive (hB : B.SeparatingLeft)
 (f : SchwartzMap E ℂ) :
 (∑' n : ι → ℤ, realBilinearFourier B μ f
 ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ)))) =
 (basisHaarFactor b μ : ℂ) *
 ∑' n : ι → ℤ, f (b.equivFunL.symm (fun i => (n i : ℝ)))
```

### RepresentationTheory/Weil/AdelicSplitting/LatticePoisson [7] real_lattice_poisson_shift_positive  (general; file: clean)
Reader: Same with shift a: sum over dual-lattice points of the B-Fourier transform times the character of B(dual point, a) equals basisHaarFactor times sum of f (a + lattice point).  Caveat: as [6]; realCharacter 1 is the project's character (elsewhere stated as exp(2πi t)); sign conventions to check in source

```lean
theorem real_lattice_poisson_shift_positive (hB : B.SeparatingLeft)
 (f : SchwartzMap E ℂ) (a : E) :
 (∑' n : ι → ℤ, realBilinearFourier B μ f
 ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) *
 RealCharacters.LocalAnalysis.realCharacter 1 (B ((LatticeDualCoordinates.LocalAnalysis.latticeDualCoordinates b B hB).symm (fun i => (n i : ℝ))) a)) =
 (basisHaarFactor b μ : ℂ) *
 ∑' n : ι → ℤ, f (a + b.equivFunL.symm (fun i => (n i : ℝ)))
```

## N2

### Analysis/RieszRectifiability/Packing/EuclideanPackingBound [2] euclidean_separated_card_le  (general; file: clean)
Reader: A finite set in Ambient k with all norms <= R and pairwise distances >= 2r (r>0) has at most ((R+r)/r)^k points.  Caveat: Ambient k is a project abbreviation not shown (presumably Euclidean k-space); bounds lattice points only through the minimal distance, no covolume

```lean
theorem euclidean_separated_card_le {k : ℕ}
 (s : Finset (Ambient k)) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
 (hs : ∀ x ∈ s, ‖x‖ ≤ R)
 (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * r ≤ dist x y) :
 (s.card : ℝ) ≤ ((R + r) / r) ^ k
```

### Combinatorics/Progressions/Estimates/GramCovolume [1] zspan_covolume_sq_eq_det_gram  (general; file: clean)
Reader: For a real basis b of a finite-dimensional inner product space, covolume of its Z-span squared equals the determinant of the Gram matrix of b.  Caveat: basis indexed by Fin r

```lean
theorem zspan_covolume_sq_eq_det_gram {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 {r : ℕ} (b : Basis (Fin r) ℝ E) :
 ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det
```

### Combinatorics/Progressions/Lattices/EuclideanShortLatticeBasis [9] exists_short_euclidean_lattice_basis  (general; file: clean)
Reader: Full lattice in n-dim Euclidean E spanned over R by lattice vectors of norm <= R: a Z-basis b with prod ||b i|| <= n^n c_n covolume and ||b i|| <= n n! c_n R.  Caveat: c_n = minkowskiSecondConstant n, body hidden

```lean
theorem exists_short_euclidean_lattice_basis {E A : Type*} {n : ℕ}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [MeasurableSpace E] [BorelSpace E]
 (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
 (o : OrthonormalBasis (Fin n) ℝ E) (v : A → E) {R : ℝ}
 (hspan : span ℝ (Set.range v) = ⊤) (hmem : ∀ a, v a ∈ Λ)
 (hnorm : ∀ a, ‖v a‖ ≤ R) :
 ∃ b : Basis (Fin n) ℝ E,
 span ℤ (Set.range b) = Λ ∧
 (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * minkowskiSecondConstant n * ZLattice.covolume Λ ∧
 ∀ i, ‖b i‖ ≤ (n : ℝ) * n.factorial * minkowskiSecondConstant n * R
```

### Combinatorics/Progressions/Lattices/LatticeDualCoordinates [2] euclideanDualLattice_eq_span  (general; file: clean)
Reader: For a ℤ-basis b of Λ, the dual lattice equals the ℤ-span of the vectors latticeDualBasis Λ b.  Caveat: euclideanDualLattice and latticeDualBasis are project defs (dual lattice characterised in NormalizedLatticeSheet [6]); ambient hypotheses not shown

```lean
theorem euclideanDualLattice_eq_span (b : Basis ι ℤ Λ) :
 euclideanDualLattice Λ = Submodule.span ℤ (Set.range (latticeDualBasis Λ b))
```

### Combinatorics/Progressions/Lattices/LatticeDualCoordinates [9] latticeDualEquiv  (general; file: clean)
Reader: Definition: a bijection between ι → ℤ and the dual lattice of Λ, built from a ℤ-basis b of Λ.  Caveat: def, body hidden; [10] says its value is latticeDualPoint Λ b n

```lean
noncomputable def latticeDualEquiv (b : Basis ι ℤ Λ) : (ι → ℤ) ≃ euclideanDualLattice Λ
```

### Combinatorics/Progressions/Lattices/LatticeSheetHaar [1] zspan_covolume_sq_eq_det_gram_fintype  (general; file: clean)
Reader: For a real basis b of a finite-dimensional inner product space, the squared covolume of its ℤ-span equals the determinant of the Gram matrix of b.

```lean
theorem zspan_covolume_sq_eq_det_gram_fintype
 {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : Basis ι ℝ E) :
 ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det
```

### Combinatorics/Progressions/Lattices/LatticeSheetHaar [2] lattice_covolume_sq_eq_gram  (general; file: clean)
Reader: For a full lattice Λ with ℤ-basis b, covolume Λ squared equals the determinant of the Gram matrix of b viewed as a real basis.

```lean
theorem lattice_covolume_sq_eq_gram
 {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
 ZLattice.covolume Λ ^ 2 = (Matrix.gram ℝ (b.ofZLatticeBasis ℝ Λ)).det
```

### Combinatorics/Progressions/Lattices/LatticeVoronoiPacking [5] latticeVoronoi_isAddFundamentalDomain  (general; file: clean)
Reader: For a discrete Λ and any additive Haar measure μ, latticeVoronoi Λ is an additive fundamental domain of Λ.  Caveat: latticeVoronoi body hidden; file-level hypotheses on E and Λ not shown

```lean
theorem latticeVoronoi_isAddFundamentalDomain [DiscreteTopology Λ]
 [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
 IsAddFundamentalDomain Λ (latticeVoronoi Λ) μ where
```

### Combinatorics/Progressions/Lattices/LatticeVoronoiPacking [13] lattice_points_mul_covolume_le_closedBall  (general; file: clean)
Reader: If every point is within B of the full lattice Λ, any finite set P of lattice points of norm ≤ R satisfies card P * covolume Λ μ ≤ μ(closed ball of radius R + B).  Caveat: upper bound for the lattice point count only; any Haar measure μ

```lean
theorem lattice_points_mul_covolume_le_closedBall
 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
 (μ : Measure E) [Measure.IsAddHaarMeasure μ]
 (B R : ℝ) (hcover : ∀ x : E, ∃ z : Λ, ‖x - z.val‖ ≤ B)
 (P : Finset Λ) (hP : ∀ p ∈ P, ‖(p : E)‖ ≤ R) :
 (P.card : ℝ) * ZLattice.covolume Λ μ ≤ μ.real (Metric.closedBall 0 (R + B))
```

### Combinatorics/Progressions/Lattices/NormalizedLatticeSheet [6] mem_euclideanDualLattice  (general; file: clean)
Reader: ξ lies in euclideanDualLattice Λ iff the inner product of ξ with every x in Λ is an integer.  Caveat: characterises the project def [5]; holds for any ℤ-submodule Λ

```lean
theorem mem_euclideanDualLattice (Λ : Submodule ℤ E) (ξ : E) :
 ξ ∈ euclideanDualLattice Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ)
```

### Combinatorics/Progressions/Lattices/NormalizedLatticeSheet [8] euclideanDualLattice_eq_span_dualBasis  (general; file: clean)
Reader: For a full lattice Λ the dual lattice is the ℤ-span of Mathlib's BilinForm.dualBasis (for the inner product) of a chosen ℤ-basis of Λ.  Caveat: uses Module.Free.chooseBasis; LatticeDualCoordinates [2] is the version for a given basis

```lean
theorem euclideanDualLattice_eq_span_dualBasis (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] :
 euclideanDualLattice Λ = Submodule.span ℤ (Set.range
 (LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate
 ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)))
```

### Combinatorics/Progressions/Lattices/NormalizedLatticeSheet [10] euclideanDualLattice_isZLattice  (general; file: clean)
Reader: Instance: the dual lattice of a full discrete lattice Λ is again a full lattice (IsZLattice).  Caveat: discreteness is the separate instance [9]

```lean
instance euclideanDualLattice_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] : IsZLattice ℝ (euclideanDualLattice Λ)
```

### Combinatorics/Progressions/Lattices/NormalizedLatticeSheet [11] euclideanDualLattice_involutive  (general; file: clean)
Reader: For a full discrete lattice Λ, the dual of the dual lattice is Λ.

```lean
theorem euclideanDualLattice_involutive (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] : euclideanDualLattice (euclideanDualLattice Λ) = Λ
```

### Combinatorics/Progressions/Linear/ShortGeneratingBasisBound [3] abs_det_eq_of_same_integer_span  (general; file: clean)
Reader: Two real bases of R^n with the same integer span have equal |det|: the covolume does not depend on the lattice basis.  Caveat: stated for Basis (Fin n) R (Fin n -> R) and Matrix.of, not for Mathlib's ZLattice covolume

```lean
theorem abs_det_eq_of_same_integer_span {n : ℕ}
 (b c : Basis (Fin n) ℝ (Fin n → ℝ))
 (hspan : span ℤ (Set.range b) = span ℤ (Set.range c)) :
 |(Matrix.of b).det| = |(Matrix.of c).det|
```

### Geometry/HeilbronnTriangle/LatticeLowerProduct [3] covolume_mono_reverse  (general; file: clean)
Reader: If lattice L1 is contained in lattice L2 then covolume(L2) is at most covolume(L1).  Caveat: ambient space E is a file variable not shown

```lean
theorem covolume_mono_reverse (L₁ L₂ : Submodule ℤ E)
 [DiscreteTopology L₁] [IsZLattice ℝ L₁]
 [DiscreteTopology L₂] [IsZLattice ℝ L₂] (hL : L₁ ≤ L₂) :
 ZLattice.covolume L₂ ≤ ZLattice.covolume L₁
```

### Geometry/HeilbronnTriangle/LatticeLowerProduct [4] covolume_le_prod_norm  (general; file: clean)
Reader: For a lattice L and any real basis consisting of vectors of L, covolume(L) is at most the product of the norms of the basis vectors.  Caveat: ambient space E and n are file variables not shown

```lean
theorem covolume_le_prod_norm (L : Submodule ℤ E)
 [DiscreteTopology L] [IsZLattice ℝ L]
 (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L) :
 ZLattice.covolume L ≤ ∏ i, ‖b i‖
```

### Geometry/HeilbronnTriangle/LatticePacking [1] card_mul_measure_le  (general; file: clean)
Reader: If translates a+F of a fundamental domain F, for a in a finite set A of the group, all lie in T, then card(A)*mu(F) is at most mu(T).

```lean
theorem card_mul_measure_le {G E : Type*} [AddGroup G]
 [MeasurableSpace G] [MeasurableSpace E] [AddAction G E]
 [MeasurableVAdd G E] (μ : Measure E) [VAddInvariantMeasure G E μ]
 {F T : Set E} (hF : IsAddFundamentalDomain G F μ)
 (A : Finset G) (hAT : ∀ a ∈ A, a +ᵥ F ⊆ T) :
 (A.card : ℝ≥0∞) * μ F ≤ μ T
```

### Geometry/HeilbronnTriangle/LatticePacking [2] card_mul_measure_le_closedBall  (general; file: clean)
Reader: For an additive subgroup L with fundamental domain F inside the ball of radius D: (number of chosen points of L in closedBall c R)*mu(F) is at most mu(closedBall c (R+D)).  Caveat: upper bound only; Haar measure

```lean
theorem card_mul_measure_le_closedBall {E : Type*} [NormedAddCommGroup E]
 [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
 (L : AddSubgroup E) {F : Set E} (hF : IsAddFundamentalDomain L F μ)
 (A : Finset L) (c : E) (R D : ℝ)
 (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
 (hFD : F ⊆ Metric.closedBall 0 D) :
 (A.card : ℝ≥0∞) * μ F ≤ μ (Metric.closedBall c (R + D))
```

### Geometry/HeilbronnTriangle/LatticePacking [3] fundamentalDomain_subset_closedBall  (general; file: clean)
Reader: The ZSpan fundamental domain of a real basis b lies in the closed ball around 0 of radius the sum of the norms of the b i.

```lean
theorem fundamentalDomain_subset_closedBall {E ι : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
 (b : Module.Basis ι ℝ E) :
 ZSpan.fundamentalDomain b ⊆ Metric.closedBall 0 (∑ i, ‖b i‖)
```

### Geometry/HeilbronnTriangle/LatticePacking [4] card_mul_measure_le_basis  (general; file: clean)
Reader: For the Z-span of a real basis b: (number of chosen span points in closedBall c R)*mu(fundamental domain) is at most mu(closedBall c (R + sum of norms of b i)).  Caveat: upper bound only; Haar measure

```lean
theorem card_mul_measure_le_basis {E ι : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
 [Fintype ι] (μ : Measure E) [IsAddHaarMeasure μ]
 (b : Module.Basis ι ℝ E)
 (A : Finset (Submodule.span ℤ (Set.range b))) (c : E) (R : ℝ)
 (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R) :
 (A.card : ℝ≥0∞) * μ (ZSpan.fundamentalDomain b) ≤
 μ (Metric.closedBall c (R + ∑ i, ‖b i‖))
```

### Geometry/HeilbronnTriangle/PlaneCovolume [1] covolume_sq_eq_det_gram  (general; file: clean)
Reader: For a lattice L in a finite-dimensional real inner product space with Z-basis b: covolume(L)^2 equals the determinant of the Gram matrix of b.  Caveat: takes an orthonormal basis with the same index type, so full-rank lattice

```lean
theorem covolume_sq_eq_det_gram
 {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 [Fintype ι] [DecidableEq ι]
 (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ E) :
 ZLattice.covolume L ^ 2 = (Matrix.gram ℝ (fun i => (b i : E))).det
```

### Geometry/HeilbronnTriangle/PlaneCovolume [2] covolume_eq_sqrt_det_gram  (general; file: clean)
Reader: Same setting: covolume(L) equals the square root of the Gram determinant of a Z-basis of L.  Caveat: takes an orthonormal basis with the same index type, so full-rank lattice

```lean
theorem covolume_eq_sqrt_det_gram
 {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 [Fintype ι] [DecidableEq ι]
 (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 (b : Basis ι ℤ L) (o : OrthonormalBasis ι ℝ E) :
 ZLattice.covolume L = Real.sqrt (Matrix.gram ℝ (fun i => (b i : E))).det
```

### Geometry/HeilbronnTriangle/PlaneCovolume [11] euclidean_covolume_eq_det  (general; file: clean)
Reader: For a lattice L in EuclideanSpace R iota with Z-basis b: covolume(L) equals the absolute determinant of the matrix whose rows are the basis vectors.

```lean
theorem euclidean_covolume_eq_det
 {ι : Type*} [Fintype ι] [DecidableEq ι]
 (L : Submodule ℤ (EuclideanSpace ℝ ι)) [DiscreteTopology L] [IsZLattice ℝ L]
 (b : Basis ι ℤ L) :
 ZLattice.covolume L = |(Matrix.of (fun i => (b i : EuclideanSpace ℝ ι).ofLp)).det|
```

### Geometry/HeilbronnTriangle/SuccessiveBox [2] width_product_le  (general; file: clean)
Reader: For an additive subgroup L of R^iota with fundamental domain F of finite volume: if no nonzero point of L has all coordinates below w i in absolute value, then the product of the w i is at most vol(F).  Caveat: box version of Minkowski's first theorem; coordinate space only

```lean
theorem width_product_le {ι : Type*} [Fintype ι]
 (L : AddSubgroup (ι → ℝ)) [Countable L] (F : Set (ι → ℝ))
 (hF : IsAddFundamentalDomain L F volume) (hfinite : volume F ≠ ⊤)
 (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
 (hempty : ∀ x : L, (∀ i, |(x : ι → ℝ) i| < w i) → x = 0) :
 (∏ i, w i) ≤ volume.real F
```

### Geometry/HeilbronnTriangle/SuccessiveEstimates [2] successive_basis_estimates  (general; file: clean)
Reader: For a real basis of lattice vectors, each shortest outside the span of the earlier ones: covolume <= product of norms <= sqrt(n)^n * covolume, and index of its Z-span in L <= sqrt(n)^n.  Caveat: ambient space E and n are file variables not shown

```lean
theorem successive_basis_estimates (hn : 0 < n) (L : Submodule ℤ E)
 [DiscreteTopology L] [IsZLattice ℝ L]
 (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L)
 (hmin : ∀ j (x : E), x ∈ L → x ∉ Submodule.span ℝ (b '' Set.Iio j) →
 ‖b j‖ ≤ ‖x‖) :
 ZLattice.covolume L ≤ ∏ i, ‖b i‖ ∧
 (∏ i, ‖b i‖) ≤ Real.sqrt n ^ n * ZLattice.covolume L ∧
 ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
 Real.sqrt n ^ n
```

### Geometry/HeilbronnTriangle/SuccessiveEstimates [3] exists_successive_basis_estimates  (general; file: clean)
Reader: Every lattice in positive dimension has a successive basis with covolume <= product of norms <= sqrt(dim)^dim * covolume and index of its Z-span <= sqrt(dim)^dim.  Caveat: ambient space E is a file variable not shown; IsSuccessive is defined in SuccessiveVectors

```lean
theorem exists_successive_basis_estimates (hdim : 0 < Module.finrank ℝ E)
 (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
 ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E,
 SuccessiveVectors.IsSuccessive L b ∧
 ZLattice.covolume L ≤ ∏ i, ‖b i‖ ∧
 (∏ i, ‖b i‖) ≤ Real.sqrt (Module.finrank ℝ E) ^ Module.finrank ℝ E *
 ZLattice.covolume L ∧
 ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
 Real.sqrt (Module.finrank ℝ E) ^ Module.finrank ℝ E
```

### Geometry/HeilbronnTriangle/SuccessiveMinima [1] exists_basis_product_bound  (general; file: clean)
Reader: Every lattice L in a finite-dimensional real inner product space of positive dimension has a successive basis whose product of norms is at most sqrt(dim)^dim * covolume(L).  Caveat: IsSuccessive is defined in SuccessiveVectors

```lean
theorem exists_basis_product_bound
 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 (hn : 0 < finrank ℝ E)
 (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
 ∃ b : Basis (Fin (finrank ℝ E)) ℝ E,
 SuccessiveVectors.IsSuccessive L b ∧
 (∏ i, ‖b i‖) ≤ Real.sqrt (finrank ℝ E) ^ finrank ℝ E * ZLattice.covolume L
```

### Geometry/HeilbronnTriangle/SuccessiveMinima [2] product_bound_of_successive  (general; file: clean)
Reader: For any successive basis b (indexed by Fin n, n>0) of a lattice L, the product of the norms of the b i is at most sqrt(n)^n * covolume(L).  Caveat: IsSuccessive is defined in SuccessiveVectors

```lean
theorem product_bound_of_successive
 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 {n : ℕ} (hn : 0 < n)
 (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 (b : Basis (Fin n) ℝ E) (hb : SuccessiveVectors.IsSuccessive L b) :
 (∏ i, ‖b i‖) ≤ Real.sqrt n ^ n * ZLattice.covolume L
```

### Geometry/HeilbronnTriangle/SuccessiveVectors [2] exists_shortest_outside  (general; file: clean)
Reader: For a lattice L and a proper real subspace W there is a vector of L outside W, of positive norm, shortest among all vectors of L outside W.  Caveat: ambient space E is a file variable not shown

```lean
theorem exists_shortest_outside (L : Submodule ℤ E) [DiscreteTopology L]
 [IsZLattice ℝ L] (W : Submodule ℝ E) (hW : W ≠ ⊤) :
 ∃ v ∈ L, v ∉ W ∧ 0 < ‖v‖ ∧
 ∀ w ∈ L, w ∉ W → ‖v‖ ≤ ‖w‖
```

### Geometry/HeilbronnTriangle/SuccessiveVectors [8] exists_successive_basis  (general; file: clean)
Reader: Every lattice in a finite-dimensional real space has a real basis that is successive (successive-minima vectors).  Caveat: ambient space E is a file variable not shown

```lean
theorem exists_successive_basis (L : Submodule ℤ E) [DiscreteTopology L]
 [IsZLattice ℝ L] [FiniteDimensional ℝ E] :
 ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, IsSuccessive L b
```

### Geometry/LatticeCovering/GridCounts [2] tendsto_real_grid_count  (general; file: clean)
Reader: For a full lattice L in R^iota and bounded measurable S with null frontier and monotone dilations, card(S meet t^-1 L) / t^dim tends to vol(S)/covol(L).  Caveat: limit only, no error term

```lean
theorem tendsto_real_grid_count (L : Submodule ℤ (ι → ℝ))
 [DiscreteTopology L] [IsZLattice ℝ L] {S : Set (ι → ℝ)}
 (hSb : IsBounded S) (hSm : MeasurableSet S)
 (hSf : volume (frontier S) = 0)
 (hSd : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • S ⊆ y • S) :
 Tendsto (fun t : ℝ => (Nat.card ↥(S ∩ t⁻¹ • (L : Set (ι → ℝ))) : ℝ) /
 t ^ Fintype.card ι) atTop (𝓝 (volume.real S / ZLattice.covolume L))
```

### Geometry/LatticeCovering/GridCounts [3] tendsto_convex_grid_count  (general; file: clean)
Reader: For a full lattice L and compact convex S containing 0, card(S meet t^-1 L) / t^dim tends to vol(S)/covol(L) as t -> infinity.  Caveat: limit only, no error term; ambient space is iota -> R, a Euclidean ball has to be supplied as the set S

```lean
theorem tendsto_convex_grid_count (L : Submodule ℤ (ι → ℝ))
 [DiscreteTopology L] [IsZLattice ℝ L] {S : Set (ι → ℝ)}
 (hSc : IsCompact S) (hSv : Convex ℝ S) (h0 : 0 ∈ S) :
 Tendsto (fun t : ℝ => (Nat.card ↥(S ∩ t⁻¹ • (L : Set (ι → ℝ))) : ℝ) /
 t ^ Fintype.card ι) atTop (𝓝 (volume.real S / ZLattice.covolume L))
```

### NumberTheory/ArithmeticGroups/Lattices/CovolumeTransport [1] covolume_of_linear_lattice_image  (general; file: clean)
Reader: If a linear automorphism e maps a Z-lattice Lambda onto Omega, then covolume(Omega) = |det e| * covolume(Lambda), for any additive Haar measure.

```lean
theorem covolume_of_linear_lattice_image
 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [MeasurableSpace E] [BorelSpace E]
 (Λ Ω : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
 [DiscreteTopology Ω] [IsZLattice ℝ Ω]
 (μ : Measure E) [Measure.IsAddHaarMeasure μ] (e : E ≃ₗ[ℝ] E)
 (he : Λ.map (e.toLinearMap.restrictScalars ℤ) = Ω) :
 ZLattice.covolume Ω μ = |e.toLinearMap.det| * ZLattice.covolume Λ μ
```

### NumberTheory/ArithmeticGroups/Lattices/Minkowski/Ellipsoid [1] minkowski_of_covolume_lt_measure  (general; file: clean)
Reader: Minkowski convex body theorem in covolume form: a symmetric convex set with Haar measure > covolume * 2^dim contains a nonzero vector of the Z-lattice.  Caveat: instances on the ambient space E are file variables and not shown

```lean
theorem minkowski_of_covolume_lt_measure
 (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
 (μ : Measure E) [Measure.IsAddHaarMeasure μ] {S : Set E}
 (hsym : ∀ x ∈ S, -x ∈ S) (hconv : Convex ℝ S)
 (hvol : ENNReal.ofReal (ZLattice.covolume Λ μ) * 2 ^ finrank ℝ E < μ S) :
 ∃ x ∈ Λ, x ≠ 0 ∧ x ∈ S
```

### NumberTheory/ArithmeticGroups/Lattices/ShortestVector [1] exists_shortest_lattice_vector  (general; file: clean)
Reader: A discrete Z-submodule of a proper normed space containing a nonzero vector has a nonzero vector of minimal norm (first successive minimum is attained).

```lean
theorem exists_shortest_lattice_vector
 {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
 (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 (y : E) (hy : y ∈ Λ) (hy0 : y ≠ 0) :
 ∃ v ∈ Λ, v ≠ 0 ∧ ∀ x ∈ Λ, x ≠ 0 → ‖v‖ ≤ ‖x‖
```

### Probability/GaussianRegression/Nets [3] card_le_volume_ratio  (general; file: clean)
Reader: A finite set of points of norm <= R that are pairwise at distance >= r has at most ((R + r/2)/(r/2))^(finrank E) elements (volume packing bound).  Caveat: ambient assumptions on E not shown; upper bound only; gives a lattice-point count when r is the shortest vector length

```lean
theorem card_le_volume_ratio (s : Finset E) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
 (hs : ∀ x ∈ s, ‖x‖ ≤ R)
 (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
 (s.card : ℝ) ≤ ((R + r / 2) / (r / 2)) ^ Module.finrank ℝ E
```

### RepresentationTheory/Theta/Geometric/CompactLattice [2] isZLattice_of_compact_quotient  (general; file: clean)
Reader: A discrete Z-submodule L of a finite-dimensional real normed space V with compact quotient V/L is a full lattice (IsZLattice R L).

```lean
theorem isZLattice_of_compact_quotient
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
 (L : Submodule ℤ V) [DiscreteTopology L] [CompactSpace (V ⧸ L.toAddSubgroup)] :
 IsZLattice ℝ L
```

### RepresentationTheory/Theta/Geometric/CompactLattice [1] span_top_of_compact_quotient  (general; file: clean)
Reader: A Z-submodule L of a finite-dimensional real normed space with compact quotient V/L spans V over R.  Caveat: no discreteness assumed

```lean
theorem span_top_of_compact_quotient
 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
 (L : Submodule ℤ V) [CompactSpace (V ⧸ L.toAddSubgroup)] :
 Submodule.span ℝ (L : Set V) = ⊤
```

## N3

### Analysis/CoulombIonization/Localization/SubGaussianMoments [3] subGaussian_even_moment_le  (general; file: clean)
Reader: If X has a sub-Gaussian moment generating function with parameter v, then E[X^(2k)] ≤ (8·e·k·v)^k for k > 0.  Caveat: uses Mathlib's HasSubgaussianMGF; integrability is [2]

```lean
theorem subGaussian_even_moment_le {Ω : Type*} [MeasurableSpace Ω]
 {μ : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
 (h : HasSubgaussianMGF X v μ) {k : ℕ} (hk : 0 < k) :
 (∫ sample, X sample ^ (2 * k) ∂μ) ≤ (8 * Real.exp 1 * k * (v : ℝ)) ^ k
```

### Analysis/IrrationalRotation/Sampling/SamplingAlmostSure [1] ae_summable_of_lintegral_tsum_ne_top  (general; file: clean)
Reader: Nonnegative e n whose expectations have a finite sum: almost surely the series over n of e n omega is summable.  Caveat: Omega and mu are file variables; their assumptions are not visible

```lean
theorem ae_summable_of_lintegral_tsum_ne_top {e : ℕ → Ω → ℝ}
 (he : ∀ n ω, 0 ≤ e n ω)
 (hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (e n ω)) μ)
 (hsum : (∑' n, ∫⁻ ω, ENNReal.ofReal (e n ω) ∂μ) ≠ ∞) :
 ∀ᵐ ω ∂μ, Summable (fun n => e n ω)
```

### Analysis/IrrationalRotation/Sampling/SamplingAlmostSure [3] ae_tendsto_zero_of_summable_expected_norm_sq_bound  (general; file: clean)
Reader: If the expected squared norm of F n is at most b n with b summable, then F n tends to 0 almost surely.  Caveat: Omega and mu are file variables; expectation written as lintegral of ENNReal.ofReal

```lean
theorem ae_tendsto_zero_of_summable_expected_norm_sq_bound
 {E : Type*} [NormedAddCommGroup E] {F : ℕ → Ω → E} {b : ℕ → ℝ}
 (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
 (hbound : ∀ n, (∫⁻ ω, ENNReal.ofReal (‖F n ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal (b n))
 (hb : Summable b) :
 ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 0)
```

### Analysis/IrrationalRotation/Sampling/SamplingAlmostSure [4] ae_all_tendsto_zero_of_summable_expected_norm_sq_bound  (general; file: clean)
Reader: Same for a countable family F i n with summable bounds b i: almost surely all sequences tend to 0 simultaneously.  Caveat: Omega and mu are file variables

```lean
theorem ae_all_tendsto_zero_of_summable_expected_norm_sq_bound
 {ι E : Type*} [Countable ι] [NormedAddCommGroup E]
 {F : ι → ℕ → Ω → E} {b : ι → ℕ → ℝ}
 (hmeas : ∀ i n, AEStronglyMeasurable (F i n) μ)
 (hbound : ∀ i n,
 (∫⁻ ω, ENNReal.ofReal (‖F i n ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal (b i n))
 (hb : ∀ i, Summable (b i)) :
 ∀ᵐ ω ∂μ, ∀ i, Tendsto (fun n => F i n ω) atTop (𝓝 0)
```

### Combinatorics/BalancedRyser/Probability/BoundedDriftCore [3] subGaussian_sum_of_bounded_differences  (general; file: clean)
Reader: Probability measure, filtration ℱ: if Y_j is ℱ(j+1)-measurable, |Y_j| ≤ a a.s. and E[Y_j | ℱ j] = 0 for j < n, then Σ_{j<n} Y_j has HasSubgaussianMGF with parameter n·a².  Caveat: Ω, μ are file variables; conclusion is Mathlib's HasSubgaussianMGF, tail follows from [4]

```lean
lemma subGaussian_sum_of_bounded_differences [IsProbabilityMeasure μ]
 {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {a : ℝ} (ha : 0 < a)
 (n : ℕ)
 (hY : ∀ j < n, StronglyMeasurable[ℱ (j + 1)] (Y j))
 (hb : ∀ j < n, ∀ᵐ ω ∂μ, |Y j ω| ≤ a)
 (hzero : ∀ j < n, μ[Y j | ℱ j] =ᵐ[μ] 0) :
 HasSubgaussianMGF (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω)
 ((n : ℝ≥0) * NNReal.mk (a ^ 2) (sq_nonneg a)) μ
```

### Combinatorics/BalancedRyser/Probability/BoundedDriftCore [1] condExp_exp_le_of_abs_le  (general; file: clean)
Reader: Conditional Hoeffding lemma: if |Y| ≤ a a.s. (a > 0) and E[Y | m] = 0 a.s., then E[exp(θY) | m] ≤ exp(a²θ²/2) a.s. for every θ.  Caveat: Ω, μ are file variables

```lean
lemma condExp_exp_le_of_abs_le [IsProbabilityMeasure μ]
 {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Y : Ω → ℝ} {a : ℝ}
 (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
 (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) (θ : ℝ) :
 μ[fun ω ↦ exp (θ * Y ω) | m] ≤ᵐ[μ]
 fun _ ↦ exp (a ^ 2 * θ ^ 2 / 2)
```

### Combinatorics/BalancedRyser/Probability/BoundedDriftCore [4] measure_abs_ge_le_of_subGaussian  (general; file: clean)
Reader: If Y has HasSubgaussianMGF with parameter c under a probability measure, then P(|Y| ≥ u) ≤ 2 exp(−u²/(2c)) for u ≥ 0.  Caveat: Ω, μ are file variables

```lean
lemma measure_abs_ge_le_of_subGaussian [IsProbabilityMeasure μ]
 {Y : Ω → ℝ} {c : ℝ≥0} (hY : HasSubgaussianMGF Y c μ)
 {u : ℝ} (hu : 0 ≤ u) :
 μ.real {ω | u ≤ |Y ω|} ≤ 2 * exp (-u ^ 2 / (2 * c))
```

### Combinatorics/BalancedRyser/Probability/DriftUnionBound [6] simultaneous_abs_tail_of_drift_bound  (general; file: clean)
Reader: Finite family of adapted processes, increments ≤ L, accumulated conditional drift ≤ D_{i,t} in absolute value: P(∃ i, t ≤ T: D_{i,t}+u ≤ |X_{i,t}−X_{i,0}|) ≤ 2·|ι|·(T+1)·exp(−u²/(8TL²)).  Caveat: μ, filtration ℱ are file variables (instances not shown)

```lean
theorem simultaneous_abs_tail_of_drift_bound
 {ι : Type*} [Fintype ι] (X : ι → ℕ → Ω → ℝ)
 (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
 (hX : ∀ i j, j ≤ T → StronglyMeasurable[ℱ j] (X i j))
 (hbound : ∀ i j, j < T → ∀ᵐ ω ∂μ, |X i (j + 1) ω - X i j ω| ≤ L)
 (u : ℝ) (hu : 0 < u) (D : ι → ℕ → ℝ)
 (hD : ∀ i t, t ≤ T → ∀ᵐ ω ∂μ, |∑ j ∈ Finset.range t,
 μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω| ≤ D i t) :
 μ.real {ω | ∃ i t, t ≤ T ∧ D i t + u ≤ |X i t ω - X i 0 ω|} ≤
 2 * Fintype.card ι * (T + 1 : ℕ) * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2))
```

### Combinatorics/BalancedRyser/Probability/DriftUnionBound [4] abs_tail_of_accumulated_drift_bound  (general; file: clean)
Reader: Adapted process with increments bounded by L a.s. and accumulated conditional drift at most D in absolute value: P(D+u ≤ |X_t − X_0|) ≤ 2 exp(−u²/(8TL²)) for t ≤ T, u > 0.  Caveat: μ, filtration ℱ are file variables (instances not shown)

```lean
theorem abs_tail_of_accumulated_drift_bound
 (X : ℕ → Ω → ℝ) (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L)
 (hX : ∀ j ≤ T, StronglyMeasurable[ℱ j] (X j))
 (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |X (j + 1) ω - X j ω| ≤ L)
 (u : ℝ) (hu : 0 < u) (t : ℕ) (ht : t ≤ T) (D : ℝ)
 (hD : ∀ᵐ ω ∂μ, |∑ j ∈ Finset.range t,
 μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω| ≤ D) :
 μ.real {ω | D + u ≤ |X t ω - X 0 ω|} ≤
 2 * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2))
```

### Combinatorics/BalancedRyser/Probability/IndependentTrials2 [1] martingale_abs_tail  (general; file: clean)
Reader: Azuma-Hoeffding: martingale with increments a.s. bounded by L for j < T gives P(|D_T - D_0| >= u) <= 2 exp(-u^2/(8 T L^2)).  Caveat: constant 8, not the sharp 2; one uniform bound L; assumptions on the measure sit in hidden section variables

```lean
theorem martingale_abs_tail (hD : Martingale D ℱ μ)
 {T : ℕ} {L u : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hu : 0 < u)
 (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |D (j + 1) ω - D j ω| ≤ L) :
 μ.real {ω | u ≤ |D T ω - D 0 ω|} ≤
 2 * Real.exp (-(u ^ 2) / (8 * (T : ℝ) * L ^ 2))
```

### Combinatorics/BalancedRyser/Probability/PatternCancellation [5] integral_centered_pattern_prod_eq_zero  (general; file: clean)
Reader: Independent family, factors F_b depending on coordinate sets C_b: if C_a is disjoint from every other C_b, the product of the centred factors has expectation 0.  Caveat: the cancellation step for second moments over distinct indices; real-valued factors; family types in hidden variables

```lean
theorem integral_centered_pattern_prod_eq_zero [IsProbabilityMeasure μ]
 {A : Type*} [DecidableEq A] [DecidableEq I]
 (hξ : iIndepFun ξ μ) (hξm : ∀ i, Measurable (ξ i))
 (C : A → Finset I)
 (F : (a : A) → ((i : C a) → E i) → ℝ)
 (hF : ∀ a, Measurable (F a))
 (hFi : ∀ a, Integrable (fun ω => F a (fun i => ξ i ω)) μ)
 (s : Finset A) {a : A} (ha : a ∈ s)
 (hdisj : ∀ b ∈ s.erase a, Disjoint (C a) (C b)) :
 (∫ ω, ∏ b ∈ s,
 (F b (fun i => ξ i ω) - ∫ w, F b (fun i => ξ i w) ∂μ) ∂μ) = 0
```

### Combinatorics/BalancedRyser/Probability/SimultaneousDrift [1] simultaneous_bounded_drift  (general; file: clean)
Reader: Finite family of adapted processes with increments bounded by L: P(some i, some t <= T deviates by u from its predictable drift) <= 2 |family| (T+1) exp(-u^2/(8 T L^2)).  Caveat: constant 8; union over the family and over times is built in

```lean
theorem simultaneous_bounded_drift [IsProbabilityMeasure μ]
 {ι : Type*} [Fintype ι] (ℱ : Filtration ℕ mΩ) (X : ι → ℕ → Ω → ℝ)
 {T : ℕ} {L u : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hu : 0 < u)
 (hX : ∀ i j, j ≤ T → StronglyMeasurable[ℱ j] (X i j))
 (hb : ∀ i j, j < T → ∀ᵐ ω ∂μ, |X i (j + 1) ω - X i j ω| ≤ L) :
 μ.real {ω | ∃ i, ∃ t ≤ T,
 u ≤ |X i t ω - X i 0 ω - ∑ j ∈ Finset.range t,
 μ[fun ω ↦ X i (j + 1) ω - X i j ω | ℱ j] ω|} ≤
 2 * (Fintype.card ι : ℝ) * (T + 1 : ℕ) * exp (-u ^ 2 / (8 * (T : ℝ) * L ^ 2))
```

### Combinatorics/BalancedRyser/Probability/SubGaussianTail [1] subGaussian_abs_tail  (general; file: clean)
Reader: Probability measure, Mathlib HasSubgaussianMGF X c: P(|X| >= u) <= 2 exp(-u^2/(2c)) for u >= 0.  Caveat: input is Mathlib's HasSubgaussianMGF; X, c, mu in hidden variables

```lean
lemma subGaussian_abs_tail [IsProbabilityMeasure μ]
 (h : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
 μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * c))
```

### Combinatorics/EditApproximation/Probability/BernsteinFinite [2] finite_bernstein_upper  (general; file: clean)
Reader: One-sided Bernstein: independent, centred, a.e. |X_i| <= b, sum of second moments <= v, then P(sum X_i >= d) <= exp(-d^2 / (2v + (2/3) b d)).  Caveat: index type Fin n; needs Measurable and Integrable for each X_i; b, v, d strictly positive; one-sided only

```lean
theorem finite_bernstein_upper {Ω : Type*} [MeasurableSpace Ω]
 (μ : Measure Ω) [IsProbabilityMeasure μ]
 {n : ℕ} (X : Fin n → Ω → ℝ) (b v d : ℝ)
 (hb : 0 < b) (hv : 0 < v) (hd : 0 < d)
 (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
 (hi : ∀ i, Integrable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
 (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
 (hvar : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ v) :
 μ.real {ω | d ≤ ∑ i, X i ω} ≤
 Real.exp (-d ^ 2 / (2 * v + (2 / 3 : ℝ) * b * d))
```

### Combinatorics/EditApproximation/Probability/BernsteinMGF [2] bounded_centered_mgf  (general; file: clean)
Reader: Centred X with |X| <= b a.e., 0 <= t, t*b < 3: mgf X mu t <= exp( t^2 / (2(1 - t b/3)) * integral of X^2 ).  Caveat: Omega and mu are file variables; assumptions on mu not visible

```lean
theorem bounded_centered_mgf (X : Ω → ℝ) (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t)
 (htb : t * b < 3) (hm : Measurable X) (hi : Integrable X μ)
 (hmean : (∫ ω, X ω ∂μ) = 0) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
 mgf X μ t ≤ Real.exp ((t ^ 2 / (2 * (1 - t * b / 3))) * ∫ ω, (X ω) ^ 2 ∂μ)
```

### Combinatorics/EditApproximation/Probability/BernsteinMGF [3] bounded_centered_sum_mgf  (general; file: clean)
Reader: Independent centred X_i bounded by b with summed second moments <= v: mgf of the sum at t is at most exp( t^2 v / (2(1 - t b/3)) ).  Caveat: index type Fin n; Omega and mu are file variables; assumptions on mu not visible

```lean
theorem bounded_centered_sum_mgf {n : ℕ} (X : Fin n → Ω → ℝ)
 (b v t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) (htb : t * b < 3)
 (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
 (hi : ∀ i, Integrable (X i) μ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
 (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
 (hvar : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ v) :
 mgf (fun ω => ∑ i, X i ω) μ t ≤ Real.exp (t ^ 2 * v / (2 * (1 - t * b / 3)))
```

### Combinatorics/Progressions/Lattices/LatticeSheetHaar [18] lattice_quotient_scaled_haar  (general; file: clean)
Reader: For a translation-invariant probability measure μ on E ⧸ Λ: covolume Λ • μ equals the image under the quotient map of volume restricted to the fundamental domain.  Caveat: identifies the uniform law on the torus with normalised Lebesgue measure on a fundamental domain

```lean
theorem lattice_quotient_scaled_haar (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
 (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
 ENNReal.ofReal (ZLattice.covolume Λ) • μ =
 Measure.map (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup)
 (volume.restrict (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)))
```

### Combinatorics/Progressions/Lattices/LatticeSheetHaar [23] lattice_quotient_haar_image  (general; file: clean)
Reader: For measurable A on which the quotient map is injective, the invariant probability measure of the image of A in E ⧸ Λ equals volume A / covolume Λ.  Caveat: [24] and [25] are the translated and countable-union versions

```lean
theorem lattice_quotient_haar_image (Λ : Submodule ℤ E) [DiscreteTopology Λ]
 [IsZLattice ℝ Λ] (b : Basis I ℤ Λ)
 (μ : Measure (E ⧸ Λ.toAddSubgroup)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
 {A : Set E} (hAm : MeasurableSet A)
 (hA : InjOn (QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) A) :
 μ ((QuotientAddGroup.mk : E → E ⧸ Λ.toAddSubgroup) '' A) =
 volume A / ENNReal.ofReal (ZLattice.covolume Λ)
```

### Combinatorics/Ryser/Probability/Exponential [7] bernstein_scalar_optimization  (general; file: clean)
Reader: Pure real lemma: if P <= exp(t^2 V - t u) for all 0 < t <= 1/M, then P <= exp(-min(u^2/V, u/M)/4).

```lean
lemma bernstein_scalar_optimization
 (M V u P : ℝ)
 (hM : 0 < M) (hV : 0 < V) (hu : 0 < u)
 (h : ∀ t : ℝ, 0 < t → t ≤ 1 / M →
 P ≤ Real.exp (t ^ 2 * V - t * u)) :
 P ≤ Real.exp (-(1 / 4 : ℝ) * min (u ^ 2 / V) (u / M))
```

### Combinatorics/SparsestCut/Directions [9] finite_union_bound  (general; file: clean)
Reader: Under a probability measure, a finite union of events each of probability <= p has probability <= (number of events)*p.  Caveat: elementary; stated with Measure.real

```lean
lemma finite_union_bound {Ω : Type u4} {I : Type u5} [MeasurableSpace Ω] [Fintype I]
 {ν : Measure Ω} [IsProbabilityMeasure ν] (A : I → Set Ω) {p : ℝ}
 (hA : ∀ i, (ν).real (A i) ≤ p) :
 (ν).real {x | ∃ i, x ∈ A i} ≤ (Fintype.card I : ℝ)*p
```

### Combinatorics/SparsestCut/GaussianTools [2] bounded_concentration  (general; file: clean)
Reader: Hoeffding: for independent real variables with |X_i| <= B almost surely, the centred average exceeds u in absolute value with probability <= 2exp(-n u^2/(2B^2)).  Caveat: Omega and mu are file variables (presumably any probability space)

```lean
theorem bounded_concentration {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
 (hmeas : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
 {B : ℝ} (hB : 0 < B) (hbound : ∀ i, ∀ᵐ sample ∂μ, |X i sample| ≤ B)
 {u : ℝ} (hu : 0 ≤ u) :
 μ.real {sample | u < |(∑ i, (X i sample - ∫ z, X i z ∂μ)) / (n : ℝ)|} ≤
 2 * Real.exp (-(n : ℝ) * u^2 / (2 * B^2))
```

### Combinatorics/SparsestCut/GaussianTools [1] subgaussian_abs_tail  (general; file: clean)
Reader: A variable with HasSubgaussianMGF X c mu satisfies P(|X| > u) <= 2exp(-u^2/(2c)) for u >= 0.  Caveat: Omega and mu are file variables

```lean
lemma subgaussian_abs_tail {X : Ω → ℝ} {c : ℝ≥0}
 (hX : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
 μ.real {sample | u < |X sample|} ≤ 2 * Real.exp (-u^2 / (2 * c))
```

### Computability/VertexCover/Analysis/VarianceCoordinateSum [1] update_right_measurePreserving  (general; file: clean)
Reader: For a probability measure mu on E, finite iota and coordinate j: (s,x) -> update s j x is measure preserving from (product of mu over iota) x mu to the product of mu over iota.

```lean
theorem update_right_measurePreserving {ι E : Type*} [Fintype ι] [DecidableEq ι]
 [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
 MeasurePreserving (fun p : (ι → E) × E => Function.update p.1 j p.2)
 ((Measure.pi (fun _ : ι => μ)).prod μ) (Measure.pi (fun _ : ι => μ))
```

### Computability/VertexCover/Analysis/VarianceCoordinateSum [3] integral_update_right  (general; file: clean)
Reader: For f integrable against the iota-fold product of a probability measure mu: integrating f(update s j x) in x then in s gives the integral of f.

```lean
theorem integral_update_right {ι E : Type*} [Fintype ι] [DecidableEq ι]
 [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
 {f : (ι → E) → ℝ} (hf : Integrable f (Measure.pi (fun _ : ι => μ))) :
 (∫ s, ∫ x, f (Function.update s j x) ∂μ ∂Measure.pi (fun _ : ι => μ)) =
 ∫ s, f s ∂Measure.pi (fun _ : ι => μ)
```

### Computability/VertexCover/Analysis/VariancePi [6] variance_pi_le  (general; file: clean)
Reader: Efron–Stein type bound: for bounded measurable f on n independent coordinates of law μ, variance(f) ≤ Σ_j ∫ coordinateVariance μ f j.  Caveat: coordinateVariance definition hidden (presumably the variance in coordinate j with the others fixed); assumptions on μ not shown; f must be uniformly bounded

```lean
theorem variance_pi_le (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
 {C : ℝ} (hb : ∀ s, ‖f s‖ ≤ C) :
 variance f (Measure.pi (fun _ : Fin n => μ)) ≤
 ∑ j, ∫ s, coordinateVariance μ f j s ∂Measure.pi (fun _ : Fin n => μ)
```

### Computability/VertexCover/Analysis/VarianceProduct [8] variance_product_le  (general; file: clean)
Reader: For jointly measurable bounded f: variance under mu x nu is at most the integral of the nu-variances of the sections plus the integral of the mu-variances of the sections.  Caveat: two-factor Efron-Stein; mu, nu and their assumptions on a hidden variable line; bounded f only

```lean
theorem variance_product_le (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
 (hb : ∀ x y, ‖f x y‖ ≤ C) :
 variance (Function.uncurry f) (μ.prod ν) ≤
 (∫ x, variance (f x) ν ∂μ) + ∫ y, variance (fun x => f x y) μ ∂ν
```

### GroupTheory/SimpleAmenable/RandomFields/FiniteFieldConcentration [2] finite_weighted_noise_tail  (general; file: clean)
Reader: Hoeffding bound: independent centred X_i with values in [-1,1], sum of b_i^2 <= V: P(|sum b_i X_i| >= eps) <= 2 exp(-eps^2/(2V)).

```lean
theorem finite_weighted_noise_tail {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
 [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (hind : iIndepFun X μ)
 (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
 (hc : ∀i,∫ω,X i ω ∂μ=0) (S : Finset ι) (b : ι → ℝ)
 {V ε : ℝ} (hV : 0≤V) (he : ∑i∈S,(b i)^2 ≤ V) (hε : 0≤ε) :
 μ.real {ω | ε ≤ |∑i∈S,b i*X i ω|} ≤ 2*Real.exp (-ε^2/(2*V))
```

### GroupTheory/SimpleAmenable/RandomFields/FiniteFieldConcentration [3] finite_matrix_noise_tail  (general; file: clean)
Reader: Hoeffding plus union bound over a finite set T of rows: P(some row z in T has |sum_i B_zi X_i| >= eps) <= 2 |T| exp(-eps^2/(2V)).

```lean
theorem finite_matrix_noise_tail {Ω ι ζ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
 [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (hind : iIndepFun X μ)
 (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
 (hc : ∀i,∫ω,X i ω ∂μ=0) (S : Finset ι) (T : Finset ζ) (B : ζ → ι → ℝ)
 {V ε : ℝ} (hV : 0≤V) (he : ∀z∈T,∑i∈S,(B z i)^2 ≤ V) (hε : 0≤ε) :
 μ.real {ω | ∃z∈T,ε ≤ |∑i∈S,B z i*X i ω|} ≤
 2*(T.card:ℝ)*Real.exp (-ε^2/(2*V))
```

### GroupTheory/SimpleAmenable/RandomFields/FiniteOrthogonalEnergy [3] finite_overlap_energy  (general; file: clean)
Reader: If F_i and F_j are orthogonal whenever their labels differ and each label class has at most k members, then integral of (sum F_i)^2 <= k * sum of integrals of F_i^2.

```lean
theorem finite_overlap_energy {I X S : Type*} [Fintype I] [MeasurableSpace X]
 (μ : Measure X) (F : I → X → ℝ) (s : I → S)
 (h : ∀i j,Integrable (fun x => F i x*F j x) μ)
 (ho : ∀i j,s i≠s j → (∫x,F i x*F j x ∂μ)=0)
 (k : ℕ) (hcard : ∀i,(Finset.univ.filter (fun j => s i=s j)).card≤k) :
 (∫x,(∑i,F i x)^2 ∂μ)≤(k:ℝ)*∑i,∫x,F i x^2 ∂μ
```

### MathematicalPhysics/CriticalSK/GaussianConcentration [35] centered_mgf_from_exp_square  (general; file: clean)
Reader: On a probability space, X integrable with mean zero and ∫exp(X^2/8) ≤ B implies ∫exp(t·X) ≤ exp((16B+4)·t^2) for every real t.

```lean
lemma centered_mgf_from_exp_square {Ω : Type*} [MeasurableSpace Ω]
 {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {B : ℝ}
 (hX : Integrable X μ) (hzero : ∫ x, X x ∂μ = 0)
 (hexp : Integrable (fun x => Real.exp (X x ^ 2 / 8)) μ)
 (hB : (∫ x, Real.exp (X x ^ 2 / 8) ∂μ) ≤ B) (hB0 : 0 ≤ B) (t : ℝ) :
 (∫ x, Real.exp (t * X x) ∂μ) ≤ Real.exp ((16 * B + 4) * t ^ 2)
```

### MathematicalPhysics/CriticalSK/GaussianConcentration [67] partial_sum_maximal_tail  (general; file: clean)
Reader: Independent mean-zero X_i with sub-Gaussian MGF parameter c > 0, a ≥ 0: probability that some partial sum X_0+…+X_k, k ≤ m, reaches a is at most exp(-a^2/(2(m+1)c)).  Caveat: Ω and μ are section variables not shown; needs HasSubgaussianMGF, not boundedness

```lean
lemma partial_sum_maximal_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
 (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
 (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
 (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
 (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
 μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
 Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ)))
```

### MathematicalPhysics/CriticalSK/GaussianConcentration [68] partial_sum_abs_maximal_tail  (general; file: clean)
Reader: Same hypotheses as [67]: probability that some |X_0+…+X_k|, k ≤ m, reaches a is at most 2·exp(-a^2/(2(m+1)c)).  Caveat: Ω and μ are section variables not shown; needs HasSubgaussianMGF, not boundedness

```lean
lemma partial_sum_abs_maximal_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
 (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
 (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
 (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
 (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
 μ.real {ω | ∃ k ≤ m, a ≤ |∑ i ∈ Finset.range (k + 1), X i ω|} ≤
 2 * Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ)))
```

### MathematicalPhysics/DefocusingNLS/Nonlinear/RandomSeries [1] ae_tsum_lt_top_of_summable_expectations  (general; file: clean)
Reader: Countably many measurable nonnegative F_i with expectations bounded by a summable w: the sum of the F_i is finite almost everywhere; no independence needed.  Caveat: Borel-Cantelli-type, qualitative (no rate); arbitrary measure

```lean
-- /-- Summable bounds on the expectations of nonnegative terms imply almost sure finiteness of their sum. Independence is not needed for this step. -/
theorem ae_tsum_lt_top_of_summable_expectations
 {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] {μ : Measure Ω}
 (F : ι → Ω → ℝ≥0∞) (hF : ∀ i, Measurable (F i))
 (w : ι → ℝ) (hw : Summable w)
 (hbound : ∀ i, ∫⁻ ω, F i ω ∂μ ≤ ENNReal.ofReal (w i)) :
 ∀ᵐ ω ∂μ, (∑' i, F i ω) < ∞
```

### MeasureTheory/Falconer/Estimates/IidSampling [7] iid_finite_cells_tail  (general; file: clean)
Reader: For n i.i.d. draws from any probability measure and finitely many measurable cells with mass <= p_j: P(some count >= n(e-1)p_j + L) <= (number of cells)*exp(-L).  Caveat: iidLaw and iidCount bodies not shown (presumably product law and count of sample points in a cell)

```lean
-- /-- Counts are simultaneously controlled on every prescribed measurable cell, with an exponentially small failure probability. -/
theorem iid_finite_cells_tail {X κ : Type*} [MeasurableSpace X] [DecidableEq κ]
 (ν : ProbabilityMeasure X) (n : ℕ) (B : Finset κ) (A : κ → Set X)
 (hA : ∀ j, MeasurableSet (A j)) (p T : κ → ℝ) (L : ℝ)
 (hp : ∀ j ∈ B, 0 ≤ p j)
 (hprob : ∀ j ∈ B, (ν : Measure X).real (A j) ≤ p j)
 (hT : ∀ j ∈ B, (n : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
 iidLaw ν n (⋃ j ∈ B, {ω | T j ≤ iidCount (A j) ω}) ≤
 ENNReal.ofReal ((B.card : ℝ) * exp (-L))
```

### MeasureTheory/Falconer/Estimates/SamplingTail [3] independent_indicator_sum_tail  (general; file: clean)
Reader: Chernoff bound: for independent indicators with mu(A_i) <= p, mu(sum over S >= T) <= exp(|S|(e-1)p - T).  Caveat: upper tail only; exponential-moment parameter fixed at 1

```lean
-- /-- The tail bound retains the actual small mean of each indicator. -/
theorem independent_indicator_sum_tail {Ω ι : Type*} [MeasurableSpace Ω]
 [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
 (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
 (hindep : iIndepFun (fun i => (A i).indicator (fun _ => (1 : ℝ))) μ)
 (S : Finset ι) {p T : ℝ} (_hp : 0 ≤ p) (hprob : ∀ i ∈ S, μ.real (A i) ≤ p) :
 μ.real {ω | T ≤ ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
 exp ((S.card : ℝ) * (exp 1 - 1) * p - T)
```

### MeasureTheory/Falconer/Estimates/SamplingTail [5] finite_sample_count_failure  (general; file: clean)
Reader: Union bound over a finite family of cells: probability that any cell count reaches T_j >= |S|(e-1)p_j + L is at most |B|*exp(-L).  Caveat: independence required within each cell's indicators

```lean
-- /-- Simultaneous sample-count bounds over any fixed finite collection of cells. Independence is required only among the draws for each cell. -/
theorem finite_sample_count_failure {Ω ι κ : Type*} [MeasurableSpace Ω]
 [DecidableEq ι] [DecidableEq κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
 (B : Finset κ) (S : Finset ι) (A : κ → ι → Set Ω)
 (hA : ∀ j i, MeasurableSet (A j i))
 (hindep : ∀ j ∈ B,
 iIndepFun (fun i => (A j i).indicator (fun _ => (1 : ℝ))) μ)
 (p T : κ → ℝ) (L : ℝ) (hp : ∀ j ∈ B, 0 ≤ p j)
 (hprob : ∀ j ∈ B, ∀ i ∈ S, μ.real (A j i) ≤ p j)
 (hT : ∀ j ∈ B, (S.card : ℝ) * (exp 1 - 1) * p j + L ≤ T j) :
 μ (⋃ j ∈ B, {ω | T j ≤ ∑ i ∈ S, (A j i).indicator (fun _ => (1 : ℝ)) ω}) ≤
 ENNReal.ofReal ((B.card : ℝ) * exp (-L))
```

### Probability/FreeIsing/Estimates/BoundedAverageConcentration [1] measureReal_average_ge_le  (general; file: clean)
Reader: Independent variables with values in [0,1] and means at most tau/2: probability that their average over a finite set is at least tau is at most exp(-n tau^2/2).  Caveat: one-sided; threshold tied to twice the mean bound

```lean
theorem measureReal_average_ge_le
 {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
 (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
 (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
 (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
 (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
 μ.real {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
 Real.exp (-(s.card : ℝ) * τ ^ 2 / 2)
```

### Probability/FreeIsing/Estimates/BoundedAverageConcentration [2] measure_average_ge_le  (general; file: clean)
Reader: Same bound as [1], stated for the measure itself with ENNReal.ofReal of the exponential.  Caveat: ENNReal form of [1]

```lean
theorem measure_average_ge_le
 {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
 (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
 (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
 (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
 (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
 μ {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
 ENNReal.ofReal (Real.exp (-(s.card : ℝ) * τ ^ 2 / 2))
```

### Probability/InvariantIsing/Gaussian/GaussianPatternEigenvalueMeasurability [2] continuous_hermitian_eigenvalues  (general; file: clean)
Reader: For a continuous family of real symmetric N by N matrices on a sequential space, the map to the eigenvalue vector is continuous.  Caveat: real matrices indexed by Fin N; parameter space must be sequential

```lean
lemma continuous_hermitian_eigenvalues {X : Type*} [TopologicalSpace X] [SequentialSpace X]
 {N : ℕ} (A : X → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ x, (A x).IsHermitian)
 (hc : Continuous A) : Continuous (fun x => (hA x).eigenvalues)
```

### Probability/InvariantIsing/Pressure/AlmostSure [1] ae_tendsto_zero_of_exponential_tail  (general; file: clean)
Reader: If for each eps > 0 there are C >= 0, a > 0 with P(|f_n| >= eps) <= C exp(-a n) for all n, then f_n tends to 0 almost surely.  Caveat: exponential-in-n tails only; no independence needed; conclusion carries no rate

```lean
-- /-- Summable exponential tails imply almost-sure convergence to zero. No independence between the random variables is required. -/
lemma ae_tendsto_zero_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
 (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → ℝ)
 (htail : ∀ ε : ℝ, 0 < ε → ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
 ∀ n, μ.real {ω | ε ≤ |f n ω|} ≤ C * Real.exp (-a * (n : ℝ))) :
 ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0)
```

### Probability/IsingPerceptron/NodalGaussianLipschitz [26] variance_pi_bounded_differences  (general; file: clean)
Reader: Bounded differences: a bounded measurable F on a product of n probability measures that changes by at most c_i when only coordinate i changes has variance <= sum of c_i^2.  Caveat: all factors live on one type A; a variance bound, not an exponential tail; constant not sharp

```lean
theorem variance_pi_bounded_differences [Nonempty A] {n : ℕ}
 (μ : Fin n → Measure A) [∀i,IsProbabilityMeasure (μ i)]
 {F : (Fin n → A) → ℝ} (hF : Measurable F) {M : ℝ}
 (hM : ∀x,|F x|≤M) (c : Fin n → ℝ)
 (hc : ∀i x y,(∀j,j≠i → x j=y j) → |F x-F y|≤c i) :
 variance F (Measure.pi μ) ≤ ∑i,c i ^2
```

### Probability/LatticePassage/BoundedEfronStein [2] bounded_efron_stein  (general; file: clean)
Reader: Efron-Stein for bounded measurable f on an i.i.d. product: variance f <= sum over i of integral of (f(z1 with coordinate i from z2) - f(z1))^2.  Caveat: f bounded; constant 1 instead of 1/2; assumptions on mu and the index type are in hidden variables

```lean
theorem bounded_efron_stein {f : (ι → α) → ℝ} (hf : Measurable f)
 {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
 variance f (Measure.pi (fun _ : ι => μ)) ≤
 ∑ i : ι, ∫ z : (ι → α) × (ι → α),
 (f (Function.update z.1 i (z.2 i)) - f z.1)^2
 ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))
```

### Probability/LatticePassage/EfronStein [7] centered_square_lintegral_le_resampling  (general; file: clean)
Reader: Efron-Stein: for integrable measurable f on a finite i.i.d. product, E(f - Ef)^2 <= sum over i of E(f with coordinate i resampled - f)^2.  Caveat: lintegral/ENNReal form; constant 1 instead of 1/2; identical factors mu

```lean
theorem centered_square_lintegral_le_resampling {ι α : Type*} [Fintype ι] [DecidableEq ι]
 [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
 {f : (ι → α) → ℝ} (hf : Measurable f)
 (hfi : Integrable f (Measure.pi (fun _ : ι => μ))) :
 (∫⁻ v : ι → α, ENNReal.ofReal ((f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2)
 ∂Measure.pi (fun _ : ι => μ)) ≤
 ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
 ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2)
 ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))
```

### Probability/Perceptron/Sphere/GaussianRotation [10] integral_independent_difference_square  (general; file: clean)
Reader: For F in L2 of a probability measure mu: the integral of (F(x) - F(y))^2 over mu x mu equals 2 * variance of F.

```lean
lemma integral_independent_difference_square {Ω : Type*} [MeasurableSpace Ω]
 (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
 (∫ p : Ω×Ω, (F p.1-F p.2)^2 ∂μ.prod μ) = 2*variance F μ
```

### Probability/SKGap/Gaussian/IndependentBoundedAverageTailLaw [1] independent_bounded_average_tail_law  (general; file: clean)
Reader: Hoeffding-type bound: independent X_i with common law tau, measurable f_i with |f_i| <= B; P(|average of f_i(X_i) minus its mean| >= eps) <= 2 exp(-eps^2 n/(2 B^2)).  Caveat: constant 1/(2B^2), not the sharp Hoeffding 2/(2B)^2; fixed functions f_i only (no sup over a class)

```lean
lemma independent_bounded_average_tail_law {Ω : Type*} [MeasurableSpace Ω]
 {μ : Measure Ω} [IsProbabilityMeasure μ]
 {F : Type*} [MeasurableSpace F] (τ : Measure F) {n : ℕ} (hn : 0 < n)
 (X : Fin n → Ω → F) (hXi : iIndepFun X μ)
 (hX : ∀ i, HasLaw (X i) τ μ) (f : Fin n → F → ℝ)
 (hf : ∀ i, Measurable (f i)) (B : ℝ) (hB : 0 ≤ B)
 (hbound : ∀ i z, |f i z| ≤ B) (ε : ℝ) (hε : 0 ≤ ε) :
 μ {g | ε ≤ |((∑ i, f i (X i g)) - ∑ i, ∫ z, f i z ∂τ)/(n:ℝ)|} ≤
 2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(2*B^2)))
```

### Probability/SKGap/Gaussian/SquareTail2 [2] iid_upper_deviation_of_log_mgf  (general; file: clean)
Reader: Chernoff bound: independent real X_i with common law nu, t > 0, exp(t x) integrable; P(average >= a) <= exp(-(t a - cgf(t)) n).  Caveat: upper tail only; one-dimensional; user optimises t (route to Bernstein)

```lean
lemma iid_upper_deviation_of_log_mgf {Ω : Type*} [MeasurableSpace Ω]
 {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
 (X : Fin n → Ω → ℝ) (hXi : iIndepFun X μ)
 (hXm : ∀ i, Measurable (X i)) (ν : Measure ℝ)
 (hLaw : ∀ i, HasLaw (X i) ν μ) {t : ℝ} (ht : 0 < t)
 (hi : Integrable (fun x : ℝ => Real.exp (t*x)) ν) (a : ℝ) :
 μ {ω | a ≤ (∑ i, X i ω)/(n:ℝ)} ≤
 ENNReal.ofReal (Real.exp (-((t*a-cgf id ν t)*(n:ℝ))))
```

### Probability/SKGap/Gaussian/SubgaussianAbsTail [1] subgaussian_abs_tail  (general; file: clean)
Reader: If X has sub-Gaussian MGF with parameter c (Mathlib HasSubgaussianMGF) under a finite measure, then mu{|X| >= eps} <= 2 exp(-eps^2/(2c)).

```lean
lemma subgaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
 [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
 (ε : ℝ) (hε : 0 ≤ ε) :
 μ {ω | ε ≤ |X ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-ε^2/(2*(c:ℝ))))
```

### Probability/SphericalField/Gaussian/Integration [9] integral_independent_difference_square  (general; file: clean)
Reader: For a probability measure mu and F in L2: the integral of (F(x)-F(y))^2 over mu x mu equals 2 * variance of F.

```lean
lemma integral_independent_difference_square {Ω : Type*} [MeasurableSpace Ω]
 (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
 (∫ p : Ω×Ω, (F p.1-F p.2)^2 ∂μ.prod μ) = 2*variance F μ
```

### Probability/SphericalField/Perceptron/Variance [8] variance_pi_le_of_bounded_differences  (general; file: clean)
Reader: For continuous bounded F on n i.i.d. coordinates with |F(update x i y) - F x| <= c: variance of F under the n-fold product of mu is at most n c^2.  Caveat: variance bound only (no exponential tail); F continuous and bounded; mu, X from file variables not shown

```lean
theorem variance_pi_le_of_bounded_differences (n : ℕ) {F : (Fin n → X) → ℝ}
 (hF : Continuous F) {K c : ℝ} (hK : ∀ x, |F x| ≤ K)
 (hdiff : ∀ x i y, |F (Function.update x i y) - F x| ≤ c) :
 variance F (Measure.pi fun _ : Fin n => μ) ≤ (n : ℝ) * c ^ 2
```

## N4

### Algebra/DepthFive/TraceRank [2] hermitian_trace_sq_eq_sum_eigenvalues_sq  (general; file: clean)
Reader: For a Hermitian complex matrix A on a finite index type, trace(A^2) equals the sum of the squared eigenvalues.  Caveat: second power only; complex finite matrices

```lean
-- /-- The second spectral moment of a Hermitian matrix. -/
theorem hermitian_trace_sq_eq_sum_eigenvalues_sq {ι : Type*} [Fintype ι]
 [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
 (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2)
```

### Analysis/BiholderTransport/LinearAlgebra/CongruenceSpectrum [1] ordered_eigenvalues_bounded_congruence  (general; file: clean)
Reader: Ostrowski-type: if <A v, v> = <B P v, P v> with P bijective and l|v| <= |P v| <= u|v|, then lambda_i(A) <= u^2 lambda_i(B) and lambda_i(B) <= l^(-2) lambda_i(A) for every i.  Caveat: A, B positive operators on finite-dimensional real inner product spaces of equal dimension

```lean
lemma ordered_eigenvalues_bounded_congruence {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
 (hA : A.IsPositive) (hB : B.IsPositive) (P : E →ₗ[ℝ] F)
 (hP : Function.Bijective P) {l u : ℝ} (hl : 0 < l) (hu : 0 ≤ u)
 (hPn : ∀ v, l*‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ u*‖v‖)
 (h : ∀ v, inner ℝ (A v) v = inner ℝ (B (P v)) (P v))
 {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
 hA.isSymmetric.eigenvalues hnE i ≤ u^2 * hB.isSymmetric.eigenvalues hnF i ∧
 hB.isSymmetric.eigenvalues hnF i ≤ (1/l)^2 * hA.isSymmetric.eigenvalues hnE i
```

### Analysis/BiholderTransport/LinearAlgebra/SchurBackground [6] ordered_eigenvalues_of_diagonal_basis  (general; file: clean)
Reader: If symmetric A is diagonal in an orthonormal basis with antitone values mu, then Mathlib's ordered eigenvalues of A are exactly mu i.  Caveat: finite dimension; mu must already be sorted decreasingly

```lean
lemma ordered_eigenvalues_of_diagonal_basis {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
 {n : ℕ} (hn : Module.finrank ℝ E=n) (b : OrthonormalBasis (Fin n) ℝ E)
 (μ : Fin n → ℝ) (hμ : ∀ j, A (b j)=μ j • b j) (hm : Antitone μ) (i : Fin n) :
 hA.eigenvalues hn i=μ i
```

### Analysis/BiholderTransport/LinearAlgebra/SpectralContinuity [1] ordered_eigenvalues_positive_crossing  (general; file: clean)
Reader: Weyl-type: if c|v|^2 <= <B v, v> - <A v, v> <= C|v|^2 for all v, then lambda_i(A) + c <= lambda_i(B) <= lambda_i(A) + C for every ordered index i.  Caveat: A, B symmetric continuous linear maps on a finite-dimensional space E (file variable)

```lean
lemma ordered_eigenvalues_positive_crossing {A B : E →L[ℝ] E}
 (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
 {c C : ℝ}
 (h : ∀ v, c*‖v‖^2 ≤ inner ℝ (B v) v-inner ℝ (A v) v ∧
 inner ℝ (B v) v-inner ℝ (A v) v ≤ C*‖v‖^2)
 {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
 hA.eigenvalues hn i+c ≤ hB.eigenvalues hn i ∧
 hB.eigenvalues hn i ≤ hA.eigenvalues hn i+C
```

### Analysis/BiholderTransport/Regularity/NormMinMax [2] quadratic_lower_spectral_slice  (general; file: clean)
Reader: For symmetric A, if v has zero coordinates on eigenvectors with index above i, then eigenvalue_i * |v|^2 <= <A v, v>.  Caveat: indices follow Mathlib's eigenvalue ordering; instance assumptions on E not shown

```lean
lemma quadratic_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
 {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
 (hv : ∀ j : Fin n, i < j → (hA.eigenvectorBasis hn).repr v j = 0) :
 hA.eigenvalues hn i * ‖v‖^2 ≤ inner ℝ (A v) v
```

### Analysis/BiholderTransport/Regularity/NormMinMax [3] quadratic_upper_spectral_slice  (general; file: clean)
Reader: For symmetric A, if v has zero coordinates on eigenvectors with index below i, then <A v, v> <= eigenvalue_i * |v|^2.  Caveat: indices follow Mathlib's eigenvalue ordering; instance assumptions on E not shown

```lean
lemma quadratic_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
 {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) (v : E)
 (hv : ∀ j : Fin n, j < i → (hA.eigenvectorBasis hn).repr v j = 0) :
 inner ℝ (A v) v ≤ hA.eigenvalues hn i * ‖v‖^2
```

### Analysis/BiholderTransport/Regularity/NormMinMax [4] ordered_eigenvalue_pullback_comparison  (general; file: clean)
Reader: If <Av,v> <= a<B(Kv),Kv> + b|v|^2 and |Kv| <= c|v|, then the i-th eigenvalue of A is <= a*c^2 times the i-th eigenvalue of B, plus b.  Caveat: A symmetric, B positive, real spaces E and F of the same finite dimension; instance assumptions not shown

```lean
lemma ordered_eigenvalue_pullback_comparison {A : E →ₗ[ℝ] E} {B : F →ₗ[ℝ] F}
 (hA : A.IsSymmetric) (hB : B.IsPositive) (K : E →ₗ[ℝ] F)
 {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
 (hK : ∀ v, ‖K v‖ ≤ c * ‖v‖)
 (h : ∀ v, inner ℝ (A v) v ≤ a * inner ℝ (B (K v)) (K v) + b * ‖v‖^2)
 {n : ℕ} (hnE : Module.finrank ℝ E = n) (hnF : Module.finrank ℝ F = n) (i : Fin n) :
 hA.eigenvalues hnE i ≤ a * c^2 * hB.isSymmetric.eigenvalues hnF i + b
```

### Analysis/DirectCrouzeix/CircleFourier [3] markov_kernel_contraction  (general; file: clean)
Reader: A continuous nonnegative kernel whose row and column integrals all equal 1 is an L2 contraction: ∫‖∫K(x,y)u(x)dμ‖²dν ≤ ∫‖u‖²dμ.  Caveat: compact second-countable metric spaces, finite measures, K and u continuous, u valued in a real Hilbert space

```lean
theorem markov_kernel_contraction {α : Type u_52} {β : Type u_53} {E : Type u_54}
 [MetricSpace α] [MeasurableSpace α] [BorelSpace α] [CompactSpace α]
 [SecondCountableTopology α]
 [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [CompactSpace β]
 [SecondCountableTopology β]
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
 (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
 (K : α → β → ℝ) (u : α → E)
 (hK : Continuous K.uncurry) (hu : Continuous u)
 (hpos : ∀ x y, 0 ≤ K x y)
 (hcol : ∀ y, ∫ x, K x y ∂μ = 1)
 (hrow : ∀ x, ∫ y, K x y ∂ν = 1) :
 (∫ y, ‖∫ x, K x y • u x ∂μ‖ ^ 2 ∂ν) ≤ ∫ x, ‖u x‖ ^ 2 ∂μ
```

### Analysis/DirectCrouzeix/HilbertSchmidt [9] hsSq_mul_le  (general; file: clean)
Reader: hsSq(F·G) ≤ ‖F‖² · hsSq(G) for complex rectangular matrices F, G.  Caveat: which matrix norm ‖F‖ denotes (the instance in scope) is not visible

```lean
theorem hsSq_mul_le {ι : Type u_24} {κ : Type u_25} {τ : Type u_26} [Fintype ι] [Fintype κ]
 [Fintype τ]
 [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
 hsSq (F * G) ≤ ‖F‖ ^ 2 * hsSq G
```

### Analysis/DirectCrouzeix/PositiveBlocks [3] re_trace_mul_nonneg  (general; file: clean)
Reader: For positive semidefinite complex matrices A and B, the real part of trace(A·B) is ≥ 0.

```lean
theorem re_trace_mul_nonneg {ι : Type u_5} [Fintype ι] [DecidableEq ι]
 {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
 0 ≤ (Matrix.trace (A * B)).re
```

### Analysis/Fourier/Restriction/Schur [1] schur_quadratic_bound  (general; file: clean)
Reader: Schur test, positive form: if a nonnegative measurable kernel has row and column integrals ≤ A, then ∫∫ a(x)a(z)k(x,z) ≤ A·∫a².  Caveat: s-finite μ, one space, a ≥ 0 measurable; stated with lintegral in ℝ≥0∞

```lean
-- /-- The positive-kernel quadratic form of Schur's test. Both integrals are allowed to be infinite, so the lemma does not presuppose the bound that it proves. -/
theorem schur_quadratic_bound
 {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
 {k : X × X → ℝ≥0∞} (hk : Measurable k)
 {a : X → ℝ} (ha : Measurable a) (han : ∀ x, 0 ≤ a x)
 {A : ℝ≥0∞} (hrow : ∀ x, (∫⁻ z, k (x, z) ∂μ) ≤ A)
 (hcol : ∀ z, (∫⁻ x, k (x, z) ∂μ) ≤ A) :
 (∫⁻ w, ENNReal.ofReal (a w.1) * ENNReal.ofReal (a w.2) * k w ∂μ.prod μ) ≤
 A * ∫⁻ x, ENNReal.ofReal (a x) ^ (2 : ℝ) ∂μ
```

### Analysis/Fourier/Restriction/Schur [2] schur_complex_quadratic_bound  (general; file: clean)
Reader: Schur test for a complex measurable kernel: row and column integrals of |K| ≤ A imply ‖∫∫ f(x)·conj f(z)·K(x,z)‖ ≤ A·∫|f|².  Caveat: s-finite μ; extended-norm (ℝ≥0∞) form; quadratic form, not operator-norm, statement

```lean
theorem schur_complex_quadratic_bound
 {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
 {K : X × X → ℂ} (hK : Measurable K)
 {f : X → ℂ} (hf : Measurable f)
 {A : ℝ≥0∞} (hrow : ∀ x, (∫⁻ z, ‖K (x, z)‖ₑ ∂μ) ≤ A)
 (hcol : ∀ z, (∫⁻ x, ‖K (x, z)‖ₑ ∂μ) ≤ A) :
 ‖∫ w, f w.1 * star (f w.2) * K w ∂μ.prod μ‖ₑ ≤
 A * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ
```

### Analysis/HardSphere/Geometry/HeatScalar [15] strong_pow_tendsto  (general; file: clean)
Reader: If operators T_n of norm ≤ 1 converge strongly to T₀, then T_n^k converges strongly to T₀^k for every k.  Caveat: complex normed space; pointwise convergence only, no rate

```lean
lemma strong_pow_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 (T : ℕ → E →L[ℂ] E) (T₀ : E →L[ℂ] E)
 (hC : ∀ n, ‖T n‖ ≤ 1) (hT : ∀ u, Tendsto (fun n ↦ T n u) atTop (𝓝 (T₀ u)))
 (k : ℕ) (u : E) : Tendsto (fun n ↦ (T n ^ k) u) atTop (𝓝 ((T₀^k) u))
```

### Analysis/KadisonKastler/ExponentialRemainder [1] norm_pow_succ_sub_pow_succ_le  (general; file: clean)
Reader: If the norms of x, y are at most r, then norm(x^(n+1) - y^(n+1)) <= (n+1) r^n norm(x - y); no commutation assumed.  Caveat: typeclass of the algebra A is a file variable not shown

```lean
-- /-- A bound independent of the algebra and of commutation of the two elements. -/
theorem norm_pow_succ_sub_pow_succ_le (x y : A) {r : ℝ} (hr : 0 ≤ r)
 (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
 ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (n + 1 : ℝ) * r ^ n * ‖x - y‖
```

### Analysis/Laughlin/Operators/SpectralKernelDistance [1] spectral_kernel_distance  (general; file: clean)
Reader: For symmetric T on a finite-dimensional complex inner product space with eigenvalues 0 or at least c, each x has y in ker T with c|x-y|^2 <= Re<Tx,x>.  Caveat: finite dimension only

```lean
theorem spectral_kernel_distance {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
 (T : Module.End ℂ E) (hT : T.IsSymmetric) (c : ℝ) (hc : 0 ≤ c)
 (hgap : ∀ v : E, v≠0 → ∀ a : ℝ, T v=(a : ℂ) • v → a=0 ∨ c≤a)
 (x : E) : ∃ y : E, T y=0 ∧ c*‖x-y‖^2 ≤ (inner ℂ (T x) x).re
```

### Analysis/LiebThirring/MatrixOrder [30] hsSquared_cfc_sub  (general; file: clean)
Reader: Hermitian A, B: if |f(a_i) - f(b_j)| <= L |a_i - b_j| for all eigenvalue pairs, then hsSquared(f(A) - f(B)) <= L^2 hsSquared(A - B).  Caveat: complex matrices; hsSquared is a project def (see [28])

```lean
-- /-- The finite-dimensional Hilbert--Schmidt calculus estimate, proved in mixed eigenbases. -/
lemma hsSquared_cfc_sub {A B : Matrix n n ℂ}
 (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
 (hf : ∀ i j, |f (hA.eigenvalues i) - f (hB.eigenvalues j)| ≤
 L * |hA.eigenvalues i - hB.eigenvalues j|) :
 hsSquared (hA.cfc f - hB.cfc f) ≤ L ^ 2 * hsSquared (A - B)
```

### Analysis/LipschitzHilbert/Estimates/FiniteSchur [1] finite_schur_bound  (general; file: clean)
Reader: Schur test on finite sets: nonnegative K with row and column sums at most M and nonnegative a, b give sum K a b <= M sqrt(sum a^2) sqrt(sum b^2).  Caveat: nonnegative kernel and vectors only

```lean
theorem finite_schur_bound {ι κ : Type*} (I : Finset ι) (J : Finset κ)
 (K : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ) (M : ℝ)
 (hM : 0≤M) (hK : ∀ i∈I, ∀ j∈J, 0≤K i j)
 (ha : ∀ i∈I, 0≤a i) (hb : ∀ j∈J, 0≤b j)
 (hrow : ∀ i∈I, (∑ j∈J, K i j)≤M)
 (hcol : ∀ j∈J, (∑ i∈I, K i j)≤M) :
 (∑ i∈I, ∑ j∈J, K i j*a i*b j)≤
 M*Real.sqrt (∑ i∈I, (a i)^2)*Real.sqrt (∑ j∈J, (b j)^2)
```

### Analysis/LipschitzHilbert/Trees/SourceGramSchur [1] symmetric_matrix_energy  (general; file: clean)
Reader: Symmetric entrywise nonnegative finite matrix G with row sums at most C: sum G_ij a_i a_j is at most C times the sum of a_i^2.  Caveat: real entries, finite index type; Schur test in quadratic-form shape

```lean
theorem symmetric_matrix_energy {ι : Type*} [Fintype ι]
 (a : ι → ℝ) (G : ι → ι → ℝ) (C : ℝ)
 (hG : ∀ i j, 0≤G i j) (hsym : ∀ i j, G i j=G j i)
 (hrow : ∀ i, ∑ j, G i j≤C) :
 (∑ i, ∑ j, G i j*a i*a j)≤C*∑ i, (a i)^2
```

### Analysis/LpDimension/HeatKernel [8] matrix_exp_spectral  (general; file: clean)
Reader: For a Hermitian real matrix S: exp(t S) = U diagonal(exp(t lambda_k)) star U, with Mathlib's eigenvectorUnitary and eigenvalues.  Caveat: exp as written in the file (presumably the matrix exponential); V is a file variable

```lean
lemma matrix_exp_spectral (S : Matrix V V ℝ) (hS : S.IsHermitian) (t : ℝ) :
 exp (t • S) = (hS.eigenvectorUnitary : Matrix V V ℝ) *
 Matrix.diagonal (fun k => Real.exp (t * hS.eigenvalues k)) *
 star (hS.eigenvectorUnitary : Matrix V V ℝ)
```

### Analysis/Matrix/Holder [49] matrix_trace_holder  (general; file: clean)
Reader: Trace Hoelder: norm of tr(A_1 ... A_m) is at most the product over j of schatten m (A_j), for m complex n x n matrices.  Caveat: schatten is a project def; [50] identifies the even ones

```lean
theorem matrix_trace_holder [Nonempty n] {m : ℕ} (hm : 0 < m) (A : Fin m → Matrix n n ℂ) :
 ‖Matrix.trace (List.ofFn A).prod‖ ≤ ∏ j, schatten m (A j)
```

### Analysis/Matrix/Holder [51] trace_mul_pow_comm  (general; file: clean)
Reader: tr((AB)^q) = tr((BA)^q) for complex square matrices of the same size.  Caveat: complex entries; square factors only

```lean
lemma trace_mul_pow_comm (A B : Matrix n n ℂ) (q : ℕ) :
 Matrix.trace ((A*B)^q) = Matrix.trace ((B*A)^q)
```

### Analysis/MatrixScaling/Spectrum [6] symmetric_eigenvalues_mono  (general; file: clean)
Reader: Symmetric T, S on a finite-dimensional complex inner product space with Re<x,Tx> <= Re<x,Sx> for all x: each ordered eigenvalue of T is at most that of S.  Caveat: complex scalars only; E is a file variable

```lean
-- /-- Eigenvalue monotonicity for symmetric operators from quadratic-form order. -/
theorem symmetric_eigenvalues_mono [FiniteDimensional ℂ E]
 {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
 (hn : Module.finrank ℂ E = r)
 (horder : ∀ x, (inner ℂ x (T x)).re ≤ (inner ℂ x (S x)).re) (k : Fin r) :
 hT.eigenvalues hn k ≤ hS.eigenvalues hn k
```

### Analysis/MatrixScaling/Spectrum [12] symmetric_eigenvalue_le_add_norm  (general; file: clean)
Reader: Weyl: the k-th eigenvalue of T is at most the k-th eigenvalue of S plus the operator norm of T - S, for symmetric T, S (Mathlib's eigenvalues).  Caveat: complex scalars only; finite dimension

```lean
theorem symmetric_eigenvalue_le_add_norm [FiniteDimensional ℂ E]
 {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
 (hn : Module.finrank ℂ E = r) (k : Fin r) :
 hT.eigenvalues hn k ≤ hS.eigenvalues hn k + ‖(T-S).toContinuousLinearMap‖
```

### Analysis/MatrixScaling/Spectrum [13] decreasingEigenvalues_sub_le_norm  (general; file: clean)
Reader: Hermitian complex r x r matrices: |lambda_k(A) - lambda_k(B)| <= norm(A - B) for every k.  Caveat: decreasingEigenvalues is a project def; doc comment says the norm is the operator norm

```lean
-- /-- Ordered eigenvalues are 1-Lipschitz in the actual operator norm. -/
theorem decreasingEigenvalues_sub_le_norm {A B : Matrix (Fin r) (Fin r) ℂ}
 (hA : A.IsHermitian) (hB : B.IsHermitian) (k : Fin r) :
 |decreasingEigenvalues hA k - decreasingEigenvalues hB k| ≤ ‖A-B‖
```

### Analysis/NumericalRange/HilbertSchmidt [2] trace_mul_nonneg  (general; file: clean)
Reader: The real part of tr(A B) is nonnegative for positive semidefinite complex matrices A, B.

```lean
theorem trace_mul_nonneg {A B : Matrix m m ℂ}
 (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (Matrix.trace (A * B)).re
```

### Analysis/NumericalRange/MarkovOperator [25] toCLM_norm_le  (general; file: clean)
Reader: The integral operator of a MarkovKernel on L2(mu; E) has operator norm at most 1.  Caveat: needs row AND column integrals 1, bounded kernel, finite measure, complex Hilbert-valued L2; `toCLM` body hidden

```lean
lemma toCLM_norm_le : ‖(K.toCLM : Lp E 2 μ →L[ℂ] Lp E 2 μ)‖ ≤ 1
```

### Analysis/RieszRectifiability/Packing/FiniteWeightedSchur [2] finite_weighted_schur_quadratic  (general; file: clean)
Reader: Finite weighted Schur test: nonnegative symmetric k on a Finset, positive weights w with sum_j k_ij w_j <= C w_i, gives sum_ij |a_i||a_j| k_ij <= C sum a_i^2.  Caveat: symmetric kernel only; real entries

```lean
theorem finite_weighted_schur_quadratic {ι : Type*} (s : Finset ι)
 (k : ι → ι → ℝ) (w a : ι → ℝ) (C : ℝ)
 (hw : ∀ i ∈ s, 0 < w i) (hk : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ k i j)
 (hsymm : ∀ i ∈ s, ∀ j ∈ s, k j i = k i j)
 (hrow : ∀ i ∈ s, ∑ j ∈ s, k i j * w j ≤ C * w i) :
 (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * k i j) ≤ C * ∑ i ∈ s, a i ^ 2
```

### Analysis/RieszRectifiability/Packing/SchurBilinear [1] schur_bilinear_integrable_and_sq_bound  (general; file: clean)
Reader: Schur test: measurable nonnegative symmetric kernel k with row integrals at most B gives integrability of f(x)g(y)k(x,y) and (double integral)^2 <= B^2 * int f^2 * int g^2.  Caveat: finite measure only; kernel must be symmetric; row bound required for every x; f, g measurable and in L2; typeclasses on X hidden in variables

```lean
theorem schur_bilinear_integrable_and_sq_bound
 (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
 (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q) (hsymm : ∀ x y, k (y, x) = k (x, y))
 (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
 (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
 (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g)
 (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
 Integrable (fun q : X × X => f q.1 * g q.2 * k q) (μ.prod μ) ∧
 (∫ q : X × X, f q.1 * g q.2 * k q ∂μ.prod μ) ^ 2 ≤
 B ^ 2 * (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ)
```

### Analysis/Steinitz/HeatL2 [98] selfAdjoint_norm_pow  (general; file: clean)
Reader: In a C*-ring (NormedRing, StarRing, CStarRing) a self-adjoint element a satisfies ‖a^n‖ = ‖a‖^n for every n ≠ 0.

```lean
lemma selfAdjoint_norm_pow {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
 (a : A) (ha : IsSelfAdjoint a) (n : ℕ) (hn : n ≠ 0) : ‖a^n‖ = ‖a‖^n
```

### Analysis/Steinitz/HeatL2 [55] positive_norm_le_iff  (general; file: clean)
Reader: For a positive bounded operator T on a complex Hilbert space H and C ≥ 0: ‖T‖ ≤ C iff Re⟨f, T f⟩ ≤ C‖f‖² for all f.  Caveat: H is a file variable, its instances are not shown

```lean
lemma positive_norm_le_iff (T : H →L[ℂ] H) (hT : T.IsPositive) {C : ℝ} (hC : 0 ≤ C) :
 ‖T‖ ≤ C ↔ ∀ f, (⟪f, T f⟫).re ≤ C * ‖f‖^2
```

### Combinatorics/GotsmanLinial/ProjectionTrace [2] trace_starProjection  (general; file: clean)
Reader: The linear-map trace of the orthogonal projection onto a submodule K equals finrank K.  Caveat: scalar field and space E are file variables (not shown; presumably finite-dimensional inner product space)

```lean
-- /-- The trace of the actual orthogonal projection is the dimension of its range. -/
theorem trace_starProjection (K : Submodule 𝕜 E) :
 LinearMap.trace 𝕜 E K.starProjection.toLinearMap = (Module.finrank 𝕜 K : 𝕜)
```

### Combinatorics/MatchingEntropy/WeightedSpectrum [1] spectral_diagonal  (general; file: clean)
Reader: For a real Hermitian matrix C, the diagonal entry C e e equals the sum over i of eigenvalue i times the square of the e-th entry of eigenvector i.  Caveat: real matrices only; short consequence of Mathlib's spectral theorem

```lean
theorem spectral_diagonal {I : Type uI} [Fintype I] [DecidableEq I]
 {C : Matrix I I ℝ} (hC : C.IsHermitian) (e : I) :
 C e e = ∑ i, hC.eigenvalues i * (hC.eigenvectorBasis i e)^2
```

### Combinatorics/MatchingPSD/IncidenceKernels [6] trace_normalized_kernel_sq  (general; file: clean)
Reader: For a symmetric real matrix K on finite X: trace((K/card X)^2) = (sum over x,y of K x y ^2) / (card X)^2.  Caveat: X is a file variable (Fintype presumably)

```lean
lemma trace_normalized_kernel_sq (K : Matrix X X ℝ) (hs : ∀ x y, K x y = K y x) :
 Matrix.trace ((Matrix.of fun x y => K x y / Fintype.card X) *
 (Matrix.of fun x y => K x y / Fintype.card X)) =
 (∑ x, ∑ y, K x y ^ 2) / (Fintype.card X : ℝ) ^ 2
```

### Combinatorics/MatchingPSD/MatrixBounds [2] le_card_entry_bound  (general; file: clean)
Reader: A real Hermitian matrix E with all |E i j| <= b satisfies E <= (card R * b) * 1 in the matrix order.  Caveat: upper bound only; factor card R; order instance on matrices is the one in scope (not shown)

```lean
lemma le_card_entry_bound {E : Matrix R R ℝ} (hE : E.IsHermitian)
 {b : ℝ} (hb : 0 ≤ b) (hbound : ∀ i j, |E i j| ≤ b) :
 E ≤ ((Fintype.card R : ℝ)*b) • (1 : Matrix R R ℝ)
```

### Combinatorics/MatchingPSD/SpectralContraction [4] trace_square_eq_sum_norm_sq  (general; file: clean)
Reader: For a symmetric real endomorphism A and an orthonormal basis b: trace(A * A) = sum over i of norm(A (b i))^2.  Caveat: E is a file variable (finite-dimensional real inner product space presumably)

```lean
lemma trace_square_eq_sum_norm_sq (A : Module.End ℝ E) (hA : A.IsSymmetric)
 {ι : Type u_2} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
 LinearMap.trace ℝ E (A * A) = ∑ i, ‖A (b i)‖ ^ 2
```

### Combinatorics/MatchingPSD/SpectralMultiplicity [1] trace_square_eq_sum_eigenvalue_sq  (general; file: clean)
Reader: For a symmetric real endomorphism B, trace(B * B) equals a finite sum of terms built from hB.eigenvalues.  Caveat: statement cut (the summand is not visible)

```lean
lemma trace_square_eq_sum_eigenvalue_sq (B : Module.End ℝ E) (hB : B.IsSymmetric) :
 LinearMap.trace ℝ E (B * B) =
 ∑ i, (hB.eigenvalues (n
```

### Combinatorics/MatchingPSD/SpectralMultiplicity [2] eigenspace_dim_mul_sq_le_trace_square  (general; file: clean)
Reader: For a symmetric real endomorphism B and any real c: finrank(eigenspace B c) * c^2 <= trace(B * B).  Caveat: E is a file variable (finite-dimensional real inner product space presumably)

```lean
lemma eigenspace_dim_mul_sq_le_trace_square (B : Module.End ℝ E) (hB : B.IsSymmetric)
 (c : ℝ) :
 (Module.finrank ℝ (Module.End.eigenspace B c) : ℝ) * c ^ 2 ≤
 LinearMap.trace ℝ E (B * B)
```

### Combinatorics/MatchingPSD/SquareRootDisturbance [9] posSemidef_le_trace  (general; file: clean)
Reader: A real positive semidefinite matrix A satisfies A <= trace(A) * 1 in the matrix order.

```lean
lemma posSemidef_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) :
 A ≤ A.trace • (1 : Matrix R R ℝ)
```

### Combinatorics/MatchingPSD/TensorBounds [1] abs_eigenvalue_le_one_stochastic  (general; file: clean)
Reader: Real matrix with nonnegative entries and all row sums 1: every real eigenvalue c of its linear map has |c| <= 1.  Caveat: real eigenvalues only; instances on index type C come from hidden variable lines

```lean
lemma abs_eigenvalue_le_one_stochastic (W : Matrix C C ℝ)
 (hn : ∀ i j, 0 ≤ W i j) (hs : ∀ i, ∑ j, W i j = 1)
 (c : ℝ) (hc : Module.End.HasEigenvalue (Matrix.toLin' W) c) : |c| ≤ 1
```

### Combinatorics/MatchingPSD/TensorBounds [2] abs_eigenvalue_le_one_positive_fixed  (general; file: clean)
Reader: Entrywise nonnegative real matrix A with a strictly positive vector v, A v = v: every real eigenvalue c has |c| <= 1.  Caveat: real eigenvalues only; covers D^(-1)K (v = 1) and the symmetric normalisation (v = sqrt degree)

```lean
lemma abs_eigenvalue_le_one_positive_fixed (A : Matrix C C ℝ)
 (hn : ∀ i j, 0 ≤ A i j) (v : C → ℝ) (hv : ∀ i, 0 < v i)
 (hf : A *ᵥ v = v) (c : ℝ)
 (hc : Module.End.HasEigenvalue (Matrix.toLin' A) c) : |c| ≤ 1
```

### Combinatorics/MatchingPSD/TensorBounds [3] exists_orthogonal_diagonalization_bounded  (general; file: clean)
Reader: Symmetric entrywise nonnegative real matrix with a positive fixed vector: A = U diag(d) U^T with U^T U = 1 and all |d i| <= 1.  Caveat: existence only, no ordering of d

```lean
lemma exists_orthogonal_diagonalization_bounded (A : Matrix C C ℝ)
 (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
 (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
 ∃ U : Matrix C C ℝ, ∃ d : C → ℝ,
 U.transpose * U = 1 ∧ (∀ i, |d i| ≤ 1) ∧ A = U * diagonal d * U.transpose
```

### Combinatorics/SparsestCut/PositiveKernels [7] gaussian_posSemidef  (general; file: clean)
Reader: The Gaussian kernel matrix exp(-|x_i - x_j|^2/l), l > 0, of finitely many points in a real inner product space is positive semidefinite.  Caveat: Euclidean distance, not torus distance; the periodised kernel needs an extra sum or limit

```lean
lemma gaussian_posSemidef {H : Type u4} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
 (x : ι → H) {l : ℝ} (hl : 0 < l) :
 Matrix.PosSemidef (fun i j => Real.exp (-‖x i - x j‖ ^ 2 / l))
```

### Combinatorics/ThinTrees/SpectralPacking [11] projection_trace  (general; file: clean)
Reader: The trace of the orthogonal projection onto a subspace K equals finrank K.  Caveat: finite-dimensional real inner product space

```lean
lemma projection_trace (K : Submodule ℝ E) :
 LinearMap.trace ℝ E K.starProjection.toLinearMap = (Module.finrank ℝ K : ℝ)
```

### Combinatorics/ThinTrees/SpectralPacking [19] rank_approximation  (general; file: clean)
Reader: Eckart–Young lower bound: if range C has dimension ≤ k, then Σ_{i ≥ k} of squared singular values of T.adjoint is at most frobSq(T − C).  Caveat: finite-dimensional real; frobSq definition hidden; singular values taken of the adjoint

```lean
lemma rank_approximation (T C : E →ₗ[ℝ] E) {k : ℕ}
 (hk : k ≤ Module.finrank ℝ E) (hC : Module.finrank ℝ (LinearMap.range C) ≤ k) :
 (∑i : Fin (Module.finrank ℝ E) with k ≤ i.val, T.adjoint.singularValues i ^ 2) ≤
 frobSq (T - C)
```

### Combinatorics/TriangleRemoval/Process/EigenProjector [1] hermitian_trace_pow  (general; file: clean)
Reader: For a real Hermitian matrix A and natural r, the trace of A^r equals the sum of the r-th powers of its eigenvalues.  Caveat: real entries only; index type instances on a hidden variable line

```lean
theorem hermitian_trace_pow (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (r : ℕ) :
 (A ^ r).trace = ∑ i, hA.eigenvalues i ^ r
```

### Combinatorics/TriangleRemoval/Process/EigenProjector [2] eigenvalue_tail_of_trace  (general; file: clean)
Reader: Real Hermitian A, r even and nonzero, 0 <= a <= eigenvalue i0, trace(A^r) <= a^r + theta^r: every other eigenvalue has absolute value at most theta.  Caveat: real entries only

```lean
theorem eigenvalue_tail_of_trace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
 (i₀ : ι) (r : ℕ) (hr : Even r) (hr0 : r ≠ 0) (a θ : ℝ)
 (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hlead : a ≤ hA.eigenvalues i₀)
 (htrace : (A ^ r).trace ≤ a ^ r + θ ^ r) :
 ∀ i, i ≠ i₀ → |hA.eigenvalues i| ≤ θ
```

### Combinatorics/TriangleRemoval/Process/EigenvalueAbsRowsum [1] eigenvalue_abs_le_rowsum  (general; file: clean)
Reader: Real Hermitian A whose absolute row sums are all at most a (a >= 0): every eigenvalue has absolute value at most a.  Caveat: real entries only

```lean
theorem eigenvalue_abs_le_rowsum (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
 (a : ℝ) (ha : 0 ≤ a) (hrow : ∀ i, ∑ j, |A i j| ≤ a) (i : ι) :
 |hA.eigenvalues i| ≤ a
```

### Combinatorics/TriangleRemoval/Process/EigenvalueAbsRowsum [3] exists_leading_of_rowsums  (general; file: clean)
Reader: Real Hermitian A with all row sums >= a and all absolute row sums <= b: there is a largest eigenvalue, it is >= a and has absolute value <= b.  Caveat: real entries only

```lean
theorem exists_leading_of_rowsums (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
 (a b : ℝ) (hb : 0 ≤ b)
 (hlower : ∀ i, a ≤ ∑ j, A i j) (hupper : ∀ i, ∑ j, |A i j| ≤ b) :
 ∃ i₀, a ≤ hA.eigenvalues i₀ ∧ |hA.eigenvalues i₀| ≤ b ∧
 ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀
```

### Combinatorics/TriangleRemoval/Spectral/MatrixExpL2Bound [1] matrix_exp_l2_bound  (general; file: clean)
Reader: Self-adjoint real matrix A whose real spectrum lies above -r, and s >= 0: the norm of exp(-s A) is at most exp(s r).  Caveat: matrix norm instance not visible (name says l2); real entries only

```lean
theorem matrix_exp_l2_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
 (A : Matrix ι ι ℝ) (hA : IsSelfAdjoint A) (r s : ℝ) (hs : 0 ≤ s)
 (hlower : ∀ x ∈ spectrum ℝ A, -r ≤ x) :
 ‖NormedSpace.exp ((-s) • A)‖ ≤ Real.exp (s * r)
```

### Combinatorics/TriangleRemoval/Spectral/MatrixExpL2Bound [2] matrix_posSemidef_exp_l2_le_one  (general; file: clean)
Reader: Positive semidefinite real matrix P and s >= 0: the norm of exp(-s P) is at most 1.  Caveat: matrix norm instance not visible (name says l2); real entries only

```lean
theorem matrix_posSemidef_exp_l2_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
 (P : Matrix ι ι ℝ) (hP : P.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
 ‖NormedSpace.exp ((-s) • P)‖ ≤ 1
```

### Combinatorics/TriangleRemoval/Spectral/MatrixExpL2Bound [3] matrix_perturbed_exp_l2_bound  (general; file: clean)
Reader: P positive semidefinite, R self-adjoint, s >= 0 (real matrices, nonempty index): the norm of exp(-s(P+R)) is at most exp(s * norm R).  Caveat: matrix norm instance not visible (name says l2); real entries only

```lean
theorem matrix_perturbed_exp_l2_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
 [Nonempty ι]
 (P R : Matrix ι ι ℝ) (hP : P.PosSemidef) (hR : IsSelfAdjoint R)
 (s : ℝ) (hs : 0 ≤ s) :
 ‖NormedSpace.exp ((-s) • (P + R))‖ ≤ Real.exp (s * ‖R‖)
```

### Combinatorics/TriangleRemoval/Spectral/StarInclusion [6] hermitian_norm_le_of_quadratic  (general; file: clean)
Reader: Real Hermitian M with |x . (M x)| <= a times the sum of x_e^2 for every vector x (a >= 0): norm M <= a.  Caveat: matrix norm instance not visible (must be checked to be the l2 operator norm)

```lean
theorem hermitian_norm_le_of_quadratic (M : Matrix E E ℝ) (hM : M.IsHermitian)
 (a : ℝ) (ha : 0 ≤ a)
 (hquad : ∀ x : E → ℝ, |x ⬝ᵥ (M *ᵥ x)| ≤ a * ∑ e, (x e)^2) : ‖M‖ ≤ a
```

### Dynamics/TriangleBilliards/KernelBounds [4] kernel_schur_sq  (general; file: clean)
Reader: Schur test: measurable K >= 0 with row integrals <= A and column integrals <= B (s-finite measures): integral of (integral of K x y f y)^2 <= A B times the integral of f^2.  Caveat: nonnegative extended-real kernel and f; pointwise (every x, every y) row and column bounds required

```lean
-- /-- Schur's L² bound. Bounds for the absolute kernel integral in each variable control the squared L² seminorm of its positive majorant. -/
lemma kernel_schur_sq {α : Type uAlpha} {β : Type uBeta} [MeasurableSpace α] [MeasurableSpace β]
 (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
 {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
 {f : β → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
 (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
 (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B) :
 ∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℕ) ∂μ ≤
 A * B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν
```

### Dynamics/TriangleBilliards/KernelBounds [5] kernel_integral_schur_sq  (general; file: clean)
Reader: Schur test for vector-valued F with |F x y| <= K x y f y: the integral of the squared norm of the y-integral of F is at most A B times the integral of f^2.  Caveat: pointwise row and column bounds on the majorant K required

```lean
-- /-- The Schur bound for a vector-valued integral with a scalar kernel majorant. It also covers norm-preserving parallel transports between fibers. -/
lemma kernel_integral_schur_sq {α : Type uAlpha} {β : Type uBeta} {E : Type uE}
 [MeasurableSpace α] [MeasurableSpace β]
 [NormedAddCommGroup E] [NormedSpace ℝ E]
 (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
 {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
 {f : β → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
 (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
 (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
 {F : α → β → E} (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * f y) :
 ∫⁻ x, ‖∫ y, F x y ∂ν‖ₑ ^ (2 : ℕ) ∂μ ≤
 A * B * ∫⁻ y, f y ^ (2 : ℕ) ∂ν
```

### Geometry/EinsteinFour/JacobiLogDetSeries [3] trace_pow_eq_sum_eigenvalues  (general; file: clean)
Reader: For a real Hermitian matrix A, trace(A^k) equals the sum over i of the k-th powers of the eigenvalues.  Caveat: real matrices only; index type is a file variable not shown

```lean
theorem trace_pow_eq_sum_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
 (k : ℕ) : (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k
```

### Geometry/NodalSets/Spectral/FiniteEigenframeMinMax [3] finite_eigenframe_minmax  (general; file: clean)
Reader: Min-max for an orthonormal eigenframe with antitone eigenvalues and successive-maximum property: some (N+1)-dimensional V has <Tx,x> >= mu_N |x|^2, and every (N+1)-dimensional V contains nonzero x with <Tx,x> <= mu_N |x|^2.  Caveat: real scalars; successive-maximum property is a hypothesis (supplied by FiniteVariationalEigenframe [3])

```lean
theorem finite_eigenframe_minmax {E : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
 (T : E →L[ℝ] E) (e : Fin (N+1) → E) (mu : Fin (N+1) → ℝ)
 (he : Orthonormal ℝ e) (heig : ∀ i, T (e i) = mu i • e i)
 (hanti : Antitone mu)
 (hmax : ∀ i x, (∀ j, j < i → inner ℝ (e j) x = 0) →
 inner ℝ (T x) x ≤ mu i * ‖x‖^2) :
 (∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧ Module.finrank ℝ V = N+1 ∧
 ∀ x ∈ V, mu (Fin.last N) * ‖x‖^2 ≤ inner ℝ (T x) x) ∧
 (∀ V : Submodule ℝ E, FiniteDimensional ℝ V → Module.finrank ℝ V = N+1 →
 ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ inner ℝ (T x) x ≤ mu (Fin.last N) * ‖x‖^2)
```

### GroupTheory/PolycyclicRecognition/Geometry/ExponentialDuhamel [3] exponential_sub_eq_integral  (general; file: clean)
Reader: Duhamel formula: exp b - exp a = integral over t in [0,1] of exp((1-t) a) (b - a) exp(t b).  Caveat: the algebra A is a file variable whose assumptions are not shown (a Banach algebra, judging by NormedSpace.exp)

```lean
theorem exponential_sub_eq_integral (a b : A) :
 NormedSpace.exp b - NormedSpace.exp a =
 ∫ t in (0 : ℝ)..1,
 NormedSpace.exp ((1 - t) • a) * (b - a) * NormedSpace.exp (t • b)
```

### GroupTheory/SimpleAmenable/PolygonGeometry/TentMatrixPositivity [1] integral_posSemidef  (general; file: clean)
Reader: An entrywise integral of almost-everywhere positive semidefinite real matrices A(omega) with integrable entries is positive semidefinite.  Caveat: real matrices; assumptions on the index type iota not shown; route to positive semidefinite kernel matrices

```lean
theorem integral_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
 (A : Ω → Matrix ι ι ℝ) (hA : ∀ᵐ ω∂μ,(A ω).PosSemidef)
 (hi : ∀i j,Integrable (fun ω => A ω i j) μ) :
 Matrix.PosSemidef (fun i j => ∫ω,A ω i j ∂μ)
```

### InformationTheory/AmplitudeDamping/SpectralEntropy [2] trace_cfc_eq  (general; file: clean)
Reader: For a Hermitian matrix A and any real function f: trace of f(A) (continuous functional calculus) equals the sum of f over the eigenvalues.  Caveat: finite-dimensional

```lean
-- /-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
 (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ)
```

### LinearAlgebra/MatrixState/HilbertSchmidt [2] hsVector_inner  (general; file: clean)
Reader: For complex matrices M, N of the same shape: inner product of hsVector M and hsVector N equals trace(M^H * N).  Caveat: hsVector body not shown ([11] fixes its norm); finite index types

```lean
lemma hsVector_inner (M N : Matrix I J ℂ) :
 inner ℂ (hsVector M) (hsVector N) = (M.conjTranspose*N).trace
```

### LinearAlgebra/MatrixState/HilbertSchmidt [3] hsVector_norm_sq  (general; file: clean)
Reader: ||hsVector M||^2 equals the real part of trace(M^H * M).

```lean
lemma hsVector_norm_sq (M : Matrix I J ℂ) :
 ‖hsVector M‖^2 = (M.conjTranspose*M).trace.re
```

### LinearAlgebra/MatrixState/HilbertSchmidt [4] trace_mH_mul_le  (general; file: clean)
Reader: Cauchy-Schwarz for the trace pairing: Re trace(M^H N) <= sqrt(Re trace(M^H M)) * sqrt(Re trace(N^H N)).  Caveat: complex rectangular matrices; one-sided (no absolute value)

```lean
lemma trace_mH_mul_le (M N : Matrix I J ℂ) :
 (M.conjTranspose*N).trace.re ≤ Real.sqrt ((M.conjTranspose*M).trace.re) *
 Real.sqrt ((N.conjTranspose*N).trace.re)
```

### LinearAlgebra/MatrixState/HilbertSchmidt [5] trace_mul_psd_nonneg  (general; file: clean)
Reader: For positive semidefinite square complex matrices A and B: 0 <= Re trace(A * B).

```lean
lemma trace_mul_psd_nonneg (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
 0 ≤ (A*B).trace.re
```

### LinearAlgebra/MatrixState/HilbertSchmidt [6] trace_mul_mono  (general; file: clean)
Reader: If A <= B (Loewner order) and T is positive semidefinite then Re trace(A*T) <= Re trace(B*T).

```lean
lemma trace_mul_mono (A B T : Matrix I I ℂ) (h : A ≤ B) (hT : T.PosSemidef) :
 (A*T).trace.re ≤ (B*T).trace.re
```

### LinearAlgebra/MatrixState/HilbertSchmidt [11] hsVector_norm_sq_sum  (general; file: clean)
Reader: ||hsVector M||^2 equals the double sum over i, j of ||M i j||^2.

```lean
lemma hsVector_norm_sq_sum (M : Matrix I J ℂ) :
 ‖hsVector M‖^2 = ∑ i, ∑ j, ‖M i j‖^2
```

### MathematicalPhysics/ContinuumCoulomb/ManyBody/GramCorrection [2] eigenvalue_bounds  (general; file: clean)
Reader: Hermitian m×m matrix G with unit diagonal and off-diagonal entries bounded by delta has every eigenvalue in [1 − m·delta, 1 + m·delta].  Caveat: type of G comes from a variable line not shown; real matrix over Fin m inferred from the neighbouring declarations

```lean
lemma eigenvalue_bounds (hG : G.IsHermitian) {delta : ℝ} (hdelta : 0 ≤ delta)
 (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → |G i j| ≤ delta) (i : Fin m) :
 1 - m * delta ≤ hG.eigenvalues i ∧ hG.eigenvalues i ≤ 1 + m * delta
```

### MathematicalPhysics/CriticalSK/Covariance [1] euclideanMatrix_norm_le_frobenius  (general; file: clean)
Reader: For a real n x n matrix A: the operator norm of A on Euclidean space is at most sqrt of the sum of A i j^2.  Caveat: real matrices indexed by Fin n

```lean
lemma euclideanMatrix_norm_le_frobenius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
 ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ Real.sqrt (∑ i, ∑ j, A i j^2)
```

### MathematicalPhysics/CriticalSK/GOESpectrum [1] symmetric_eigenvalue_norm_bound  (general; file: clean)
Reader: For symmetric continuous linear maps A, B on a finite-dimensional real inner product space, |i-th eigenvalue of A - i-th eigenvalue of B| ≤ operator norm of A - B.  Caveat: eigenvalues are Mathlib's ordered IsSymmetric.eigenvalues hn

```lean
lemma symmetric_eigenvalue_norm_bound {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 (A B : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
 {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
 |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ ‖A-B‖
```

### MathematicalPhysics/CriticalSK/GapMixing [17] kernel_pow_reversible  (general; file: clean)
Reader: If μ_x·K_xy = μ_y·K_yx for a real square matrix K on a finite index type, then μ_x·(K^k)_xy = μ_y·(K^k)_yx for every k.  Caveat: elementary

```lean
lemma kernel_pow_reversible {ι : Type*} [Fintype ι] [DecidableEq ι]
 {K : Matrix ι ι ℝ} {μ : ι → ℝ} (h : ∀ x y, μ x*K x y=μ y*K y x)
 (k : ℕ) (x y : ι) : μ x*(K^k) x y=μ y*(K^k) y x
```

### MathematicalPhysics/CriticalSK/HeatBath [30] kernel_pow_nonneg  (general; file: clean)
Reader: If all entries of a real square matrix K are nonnegative, all entries of K^k are nonnegative.  Caveat: elementary; index type and instances are section variables

```lean
lemma kernel_pow_nonneg {K : Matrix ι ι ℝ}
 (hK : ∀ x y, 0 ≤ K x y) (k : ℕ) (x y : ι) : 0 ≤ (K ^ k) x y
```

### MathematicalPhysics/CriticalSK/HeatBath [31] kernel_pow_sum  (general; file: clean)
Reader: If every row of a real square matrix K sums to 1, every row of K^k sums to 1.  Caveat: elementary; index type and instances are section variables

```lean
lemma kernel_pow_sum {K : Matrix ι ι ℝ}
 (hK : ∀ x, ∑ y, K x y = 1) (k : ℕ) (x : ι) : ∑ y, (K ^ k) x y = 1
```

### MathematicalPhysics/CriticalSK/MinMax [12] eigenvalue_form_comparison  (general; file: clean)
Reader: Visible hypotheses: symmetric A, B; e + Φ(e) and e - Φ(e) monotone on S; eigenvalues and unit-vector forms of B in S; |⟨x,Ax⟩ - ⟨x,Bx⟩| ≤ Φ(⟨x,Bx⟩) for unit x.  Caveat: statement cut: the conclusion is not visible; E is a section variable

```lean
lemma eigenvalue_form_comparison {A B : E →ₗ[ℝ] E}
 (hA : A.IsSymmetric) (hB : B.IsSymmetric)
 {n : ℕ} (hn : finrank ℝ E = n) {S : Set ℝ} {Φ : ℝ → ℝ}
 (hplus : MonotoneOn (fun e => e + Φ e) S)
 (hminus : MonotoneOn (fun e => e - Φ e) S)
 (hBS : ∀ i, hB.eigenvalues hn i ∈ S)
 (hqS : ∀ x : E, ‖x‖ = 1 → inner ℝ x (B x) ∈ S)
 (hform : ∀ x : E, ‖x‖ = 1 →
 |inner ℝ x (A x) - inner ℝ x (B x)| ≤ Φ (inner ℝ x (B x)))
```

### MathematicalPhysics/CriticalSK/PathSpectra [32] eigenvalue_lower_of_subspace  (general; file: clean)
Reader: Symmetric T on a finite-dimensional real inner product space, subspace S with i < dim S and a ≤ ⟨x, T x⟩ for all unit x in S: then a ≤ i-th eigenvalue of T.  Caveat: indexing is Mathlib's IsSymmetric.eigenvalues hn

```lean
lemma eigenvalue_lower_of_subspace {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {n : ℕ} (hn : finrank ℝ E = n)
 (S : Submodule ℝ E) (i : Fin n) {a : ℝ}
 (hdim : i.val < finrank ℝ S)
 (hquad : ∀ x : E, x ∈ S → ‖x‖ = 1 → a ≤ inner ℝ x (T x)) :
 a ≤ hT.eigenvalues hn i
```

### MathematicalPhysics/Heisenberg/KilledContractions [14] contraction  (general; file: clean)
Reader: Matrix U with nonnegative entries and all row and column sums ≤ 1 satisfies Σ_i ((U f)_i)^2 ≤ Σ_i (f_i)^2 for every real vector f.  Caveat: Schur test only in the case bound 1; finite index type; DoublySubstochastic is the structure [10] of that file

```lean
theorem contraction {U : Matrix V V ℝ} (hU : DoublySubstochastic U) (f : V → ℝ) :
 ∑ i, ((U.mulVec f) i) ^ 2 ≤ ∑ i, (f i) ^ 2
```

### MathematicalPhysics/PEPSMove/EntropyHolder [6] diagonal_rpow_le  (general; file: clean)
Reader: For a positive semidefinite matrix A and p >= 1: the sum of (Re A i i)^p is at most the sum of the p-th powers of the eigenvalues.  Caveat: finite-dimensional complex matrices; identical statement in MathematicalPhysics/PEPSSubvolume/EntropyHolder [6]

```lean
theorem diagonal_rpow_le (A : Matrix n n ℂ) (hA : A.PosSemidef)
 (p : ℝ) (hp : 1 ≤ p) :
 (∑ i, (A i i).re ^ p) ≤ ∑ i, hA.isHermitian.eigenvalues i ^ p
```

### MathematicalPhysics/PEPSMove/Interpolation [6] trace_mul_sq_le  (general; file: clean)
Reader: For square complex matrices A, B: |tr(A B)|^2 <= hsSquare A * hsSquare B.  Caveat: hsSquare body hidden; by [3] of the same file it equals Re tr(A A*), i.e. the squared Hilbert-Schmidt norm

```lean
theorem trace_mul_sq_le (A B : Matrix ι ι ℂ) :
 ‖trace (A*B)‖^2≤hsSquare A*hsSquare B
```

### MathematicalPhysics/PEPSMove/PureEntropy [1] sum_eigen_stat_mul_comm  (general; file: clean)
Reader: For rectangular U, V with U V and V U Hermitian and f 0 = 0: the sum of f over the eigenvalues of U V equals that over the eigenvalues of V U.  Caveat: finite-dimensional complex matrices

```lean
theorem sum_eigen_stat_mul_comm (U : Matrix ι κ ℂ) (V : Matrix κ ι ℂ)
 (hUV : (U*V).IsHermitian) (hVU : (V*U).IsHermitian)
 (f : ℝ → ℝ) (hf : f 0=0) :
 ∑ i, f (hUV.eigenvalues i)=∑ j, f (hVU.eigenvalues j)
```

### NumberTheory/ArithmeticGroups/Lattices/EigenbasisTrace [1] linear_trace_eq_sum_eigenvalues  (general; file: clean)
Reader: If a finite basis consists of eigenvectors of a linear map A with eigenvalues w_i, then trace(A) = sum of the w_i.  Caveat: any field; finite basis

```lean
theorem linear_trace_eq_sum_eigenvalues
 {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
 (b : Module.Basis ι k V) (A : V →ₗ[k] V) (w : ι → k)
 (heig : ∀ i, A (b i) = w i • b i) : LinearMap.trace k V A = ∑ i, w i
```

### NumberTheory/ArithmeticGroups/Lattices/SimultaneousOrthonormalEigenbasis [1] exists_simultaneous_orthonormal_eigenbasis  (general; file: clean)
Reader: A pairwise commuting family of symmetric operators on a finite-dimensional real inner product space has a common orthonormal eigenbasis.  Caveat: real scalars, finite dimension

```lean
theorem exists_simultaneous_orthonormal_eigenbasis
 {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
 (T : ι → L →ₗ[ℝ] L) (hT : ∀ i, (T i).IsSymmetric)
 (hc : Pairwise (fun i j => Commute (T i) (T j))) :
 ∃ (b : OrthonormalBasis (Fin (Module.finrank ℝ L)) ℝ L)
 (w : Fin (Module.finrank ℝ L) → ι → ℝ), ∀ i j, T j (b i) = w i j • b i
```

### NumberTheory/CubicMoment/Estimates/GramSchur [2] complex_schur_bound  (general; file: clean)
Reader: Finite Schur test: if norms of K are symmetric and every absolute row sum is <= R, then |sum z_p*conj(z_q)*K_pq| <= R * sum |z_p|^2.  Caveat: finite index set; complex kernel

```lean
-- /-- The complex Gram quadratic form is bounded using only absolute row sums and Hermitian symmetry of their norms. -/
theorem complex_schur_bound {ι : Type*} (P : Finset ι) (z : ι → ℂ)
 (K : ι → ι → ℂ) (R : ℝ)
 (hsym : ∀ p ∈ P, ∀ q ∈ P, ‖K p q‖ = ‖K q p‖)
 (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖K p q‖ ≤ R) :
 ‖∑ p ∈ P, ∑ q ∈ P, z p * star (z q) * K p q‖ ≤
 R * ∑ p ∈ P, ‖z p‖^2
```

### NumberTheory/CubicMoment/Estimates/GramSchur [1] nonnegative_schur_bound  (general; file: clean)
Reader: Finite Schur test for a nonnegative symmetric real kernel: row sums <= R imply sum x_p*x_q*K_pq <= R * sum x_p^2.  Caveat: finite index set

```lean
theorem nonnegative_schur_bound {ι : Type*} (P : Finset ι) (x : ι → ℝ)
 (K : ι → ι → ℝ) (R : ℝ)
 (hK : ∀ p ∈ P, ∀ q ∈ P, 0 ≤ K p q)
 (hsym : ∀ p ∈ P, ∀ q ∈ P, K p q = K q p)
 (hrow : ∀ p ∈ P, ∑ q ∈ P, K p q ≤ R) :
 (∑ p ∈ P, ∑ q ∈ P, x p * x q * K p q) ≤ R * ∑ p ∈ P, (x p)^2
```

### NumberTheory/DukePrimeDegree/Geometry/MatrixPowerApproximation [2] matrix_power_approximation  (general; file: clean)
Reader: For real square matrices with norms of A and B at most exp(C/(N+1)): norm of A^(N+1) - B^(N+1) <= exp(C)*(N+1)*norm(A-B).  Caveat: which matrix norm instance is in scope is not visible (doc comment says operator norm)

```lean
-- /-- The operator norm gives a dimension-free estimate for actual matrix powers; no entrywise bound is repeatedly amplified. -/
theorem matrix_power_approximation {n : ℕ}
 (A B : Matrix (Fin n) (Fin n) ℝ) (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
 (hA : ‖A‖ ≤ Real.exp (C / (N + 1 : ℝ)))
 (hB : ‖B‖ ≤ Real.exp (C / (N + 1 : ℝ))) :
 ‖A ^ (N + 1) - B ^ (N + 1)‖ ≤ Real.exp C * ((N + 1 : ℝ) * ‖A - B‖)
```

### NumberTheory/JointDickman/Probability/FiniteKernelBilinear [3] finiteKernelBilinear_bound_of_energies  (general; file: clean)
Reader: Schur test, finite weighted form: weighted absolute row and column sums of K at most C give |B(u,v)| <= C*sqrt(U)*sqrt(V) for weighted square-sum bounds U, V.  Caveat: real kernel on a Fintype; body of finiteKernelBilinear not shown

```lean
theorem finiteKernelBilinear_bound_of_energies {A : Type*} [Fintype A]
 (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
 {C : ℝ} (hC : 0 ≤ C)
 (hrow : ∀ a, (∑ b, μ b*|K a b|) ≤ C)
 (hcol : ∀ b, (∑ a, μ a*|K a b|) ≤ C) (u v : A → ℝ)
 {U V : ℝ} (hu : (∑ a, μ a*u a^2) ≤ U) (hv : (∑ a, μ a*v a^2) ≤ V) :
 |finiteKernelBilinear μ K u v| ≤ C*Real.sqrt U*Real.sqrt V
```

### NumberTheory/OrdinaryCorrelations/AbsoluteDefect/FiniteSchur [1] finite_schur  (general; file: clean)
Reader: Schur test for a symmetric nonnegative kernel on a finset: if every row sum is <= R then sum_{m,n} a_m*a_n*K m n <= R * sum_m a_m^2.

```lean
lemma finite_schur {ι : Type*} (s : Finset ι) (a : ι → ℝ) (K : ι → ι → ℝ)
 (R : ℝ) (hK : ∀ m ∈ s, ∀ n ∈ s, 0 ≤ K m n)
 (hsym : ∀ m ∈ s, ∀ n ∈ s, K m n = K n m)
 (hrow : ∀ m ∈ s, ∑ n ∈ s, K m n ≤ R) :
 ∑ m ∈ s, ∑ n ∈ s, a m * a n * K m n ≤ R * ∑ m ∈ s, (a m)^2
```

### NumberTheory/OrdinaryCorrelations/AbsoluteDefect/NormPowLeGramTrace [1] norm_pow_le_gram_trace  (general; file: clean)
Reader: For any complex square matrix M and natural m: norm(M)^(2m) <= real part of trace((M^H * M)^m).  Caveat: which matrix norm instance is in scope is not visible in the statement

```lean
theorem norm_pow_le_gram_trace {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
 (M : Matrix ι ι ℂ) (m : ℕ) :
 ‖M‖^(2*m) ≤ ((M.conjTranspose*M)^m).trace.re
```

### Probability/BinarySweep/MatrixBounds/BlockTrace [6] trace_prod_eq_sum_cycles  (general; file: clean)
Reader: Trace of a product of n+1 square matrices equals the sum over index cycles x of the products of entries A_j (x_j) (x_{j+1}), indices rotated cyclically.  Caveat: ring and index type come from variables not shown; product written as List.ofFn

```lean
lemma trace_prod_eq_sum_cycles {n : ℕ} (A : Fin (n+1) → Matrix P P R) :
 Matrix.trace (List.ofFn A).prod =
 ∑ x : Fin (n+1) → P,
 (List.ofFn fun j => A j (x j) (x (finRotate (n+1) j))).prod
```

### Probability/EntangledGames/HilbertSchmidt [9] hsSq_cfc_sub_le  (general; file: clean)
Reader: For Hermitian A, B and f with (f s - f t)^2 <= L (s - t)^2: hsSq(f(A) - f(B)) <= L hsSq(A - B).  Caveat: finite complex matrices; hsSq project def, see [4]

```lean
lemma hsSq_cfc_sub_le [DecidableEq n] {A B : Matrix n n ℂ}
 (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ)
 (hf : ∀ s t : ℝ, (f s - f t)^2 ≤ L * (s - t)^2) :
 hsSq (cfc f A - cfc f B) ≤ L * hsSq (A - B)
```

### Probability/EntangledGames/HilbertSchmidt [21] hsSq_right_absolute_sub_le  (general; file: clean)
Reader: For rectangular complex M, N: hsSq(sqrt(M^H M) - sqrt(N^H N)) <= 2 hsSq(M - N).  Caveat: finite matrices only

```lean
theorem hsSq_right_absolute_sub_le [DecidableEq m] [DecidableEq n] (M N : Matrix m n ℂ) :
 hsSq (CFC.sqrt (Mᴴ * M) - CFC.sqrt (Nᴴ * N)) ≤ 2 * hsSq (M - N)
```

### Probability/SKGap/Matrix/GOESubmatrix [8] matrixOperator_norm_le_row  (general; file: clean)
Reader: A symmetric real matrix whose absolute row sums are all at most R (R >= 0) has operator norm at most R: Schur test, symmetric case.  Caveat: matrixOperator is a project def (body unseen); [9] of the same file relates it to Matrix.toEuclideanCLM but is cut

```lean
lemma matrixOperator_norm_le_row (M : Matrix ι ι ℝ) (hM : ∀ i k,M i k=M k i)
 {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ i,∑ k,|M i k| ≤ R) :
 ‖matrixOperator M‖ ≤ R
```

### Probability/SKGap/Matrix/RankNorm [1] real_eigenvalue_abs_le_opNorm  (general; file: clean)
Reader: Every eigenvalue of a real Hermitian (symmetric) matrix is bounded in absolute value by opNorm of the matrix.  Caveat: opNorm is a project def (OpNorm [3], body unseen)

```lean
lemma real_eigenvalue_abs_le_opNorm {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (i : ι) :
 |hM.eigenvalues i| ≤ opNorm M
```

### Probability/SKGap/Matrix/RankNorm [2] frobenius_sq_le_rank_opNorm_sq  (general; file: clean)
Reader: For a real square matrix: norm(M)^2 <= rank(M) * opNorm(M)^2.  Caveat: norm instance not visible (name says Frobenius); opNorm project def; [3] is the square-root form

```lean
lemma frobenius_sq_le_rank_opNorm_sq (M : Matrix ι ι ℝ) :
 ‖M‖^2 ≤ (M.rank:ℝ)*(opNorm M)^2
```

### Probability/SKGap/Matrix/TanhMatrixBounds [1] matrix_l2_norm_le_row  (general; file: clean)
Reader: A symmetric real matrix with all absolute row sums at most R (R >= 0) satisfies norm(A) <= R.  Caveat: which matrix norm instance is in scope is not visible; the name says l2 operator norm

```lean
lemma matrix_l2_norm_le_row (A : Matrix ι ι ℝ) (hA : ∀ i k,A i k=A k i)
 {R : ℝ} (hR : 0 ≤ R) (hrow : ∀ i,∑ k,|A i k| ≤ R) : ‖A‖ ≤ R
```

### Probability/SKRatio/Matrices/RandomMatrixNet [5] matrix_opNorm_le_schur  (general; file: clean)
Reader: Schur test hypotheses for a real n x n matrix: all absolute row sums and all absolute column sums at most R (R >= 0); conclusion is about the norm of Matrix.toEuclideanCLM.  Caveat: statement cut (the bound itself is not visible); same name with project type Interaction n in Probability/SKGap/Matrix/NormalizedInfluence [6], also cut

```lean
lemma matrix_opNorm_le_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R)
 (hr : ∀ i, ∑ j, |A i j| ≤ R) (hc : ∀ j, ∑ i, |A i j| ≤ R) :
 ‖Matrix.toEuclideanCLM (n
```

### Probability/SignedSweeps/SpectralAngle [1] trace_spectral  (general; file: clean)
Reader: For a symmetric linear map T on E: the real part of the trace equals the sum of its eigenvalues.  Caveat: E from file variables not shown (complex, finite-dimensional inner product space implied)

```lean
lemma trace_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
 (LinearMap.trace ℂ E T).re = ∑ i : Fin (Module.finrank ℂ E), hT.eigenvalues rfl i
```

### Probability/SignedSweeps/SpectralAngle [2] quadratic_spectral  (general; file: clean)
Reader: For symmetric T: Re <x, T x> equals the sum over i of eigenvalue_i times |<eigenvector_i, x>|^2.  Caveat: E from file variables not shown

```lean
lemma quadratic_spectral (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (x : E) :
 (inner ℂ x (T x)).re = ∑ i : Fin (Module.finrank ℂ E),
 hT.eigenvalues rfl i * ‖inner ℂ (hT.eigenvectorBasis rfl i) x‖ ^ 2
```

### Probability/SignedSweeps/SpectralAngle [4] trace_product_spectral  (general; file: clean)
Reader: For symmetric X and any Y: Re trace(X Y) equals the sum over i of eigenvalue_i(X) times Re <e_i, Y e_i> in X's eigenbasis.  Caveat: E from file variables not shown

```lean
lemma trace_product_spectral (X Y : E →ₗ[ℂ] E) (hX : X.IsSymmetric) :
 (LinearMap.trace ℂ E (X * Y)).re =
 ∑ i : Fin (Module.finrank ℂ E), hX.eigenvalues rfl i *
 (inner ℂ (hX.eigenvectorBasis rfl i) (Y (hX.eigenvectorBasis rfl i))).re
```

### Probability/SignedSweeps/SpectralAngle [5] positive_trace_product_nonneg  (general; file: clean)
Reader: For positive linear maps X, Y: 0 <= Re trace(X Y).  Caveat: E from file variables not shown

```lean
lemma positive_trace_product_nonneg (X Y : E →ₗ[ℂ] E)
 (hX : X.IsPositive) (hY : Y.IsPositive) :
 0 ≤ (LinearMap.trace ℂ E (X * Y)).re
```

### Probability/SignedSweeps/SpectralAngle [10] positive_projection_trace_le  (general; file: clean)
Reader: For positive X and a symmetric idempotent P: Re trace(X P) <= Re trace X.  Caveat: E from file variables not shown

```lean
lemma positive_projection_trace_le (X P : E →ₗ[ℂ] E) (hX : X.IsPositive)
 (hP : P.IsSymmetric) (hPP : P * P = P) :
 (LinearMap.trace ℂ E (X * P)).re ≤ (LinearMap.trace ℂ E X).re
```

### Probability/SwitchChain/FiniteKernelTV [6] matrix_centered_norm_decay  (general; file: clean)
Reader: Symmetric real K with unit column sums, nonnegative quadratic form and Poincare gap gamma <= 1 on sum-zero vectors: |K^t f| <= exp(-gamma t) |f| for sum-zero f.  Caveat: symmetric K, so stationary measure is uniform; needs positive semidefiniteness

```lean
theorem matrix_centered_norm_decay (K : Matrix α α ℝ)
 (hsymm : K.IsSymm) (hcols : ∀ j, ∑ i, K i j = 1)
 {γ : ℝ} (hγ : γ ≤ 1)
 (hpos : ∀ f : α → ℝ, 0 ≤ ∑ i, f i * ∑ j, K i j * f j)
 (hgap : ∀ f : α → ℝ, (∑ i, f i) = 0 →
 γ * (∑ i, (f i) ^ 2) ≤ ∑ i, f i * (f i - ∑ j, K i j * f j))
 (t : ℕ) (f : EuclideanSpace ℝ α) (hf : ∑ i, f i = 0) :
 ‖(Matrix.toEuclideanLin K : EuclideanSpace ℝ α → EuclideanSpace ℝ α)^[t] f‖ ≤
 Real.exp (-γ * (t : ℝ)) * ‖f‖
```

### Probability/SwitchChain/FiniteKernelTV [12] matrix_pow_row_sum  (general; file: clean)
Reader: If every row of a real square matrix K sums to 1, every row of K^t sums to 1.

```lean
lemma matrix_pow_row_sum (K : Matrix α α ℝ)
 (hrows : ∀ i, ∑ j, K i j = 1) (t : ℕ) : ∀ i, ∑ j, (K ^ t) i j = 1
```

### Probability/SwitchChain/SpectralFromSquare [2] norm_apply_le_of_inner_bounds  (general; file: clean)
Reader: Symmetric nonnegative T with <x,Tx> <= r norm(x)^2 for all x (r >= 0) satisfies norm(T x) <= r norm(x).  Caveat: T is a linear map on an ambient real inner product space E whose hypotheses are not visible

```lean
theorem norm_apply_le_of_inner_bounds
 (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {r : ℝ} (hr : 0 ≤ r)
 (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
 (hbound : ∀ x : E, ⟪x, T x⟫ ≤ r * ‖x‖ ^ 2)
 (x : E) : ‖T x‖ ≤ r * ‖x‖
```

### Probability/SwitchChain/SpectralFromSquare [4] norm_iterate_le_exp_of_inner_bounds  (general; file: clean)
Reader: Symmetric nonnegative T with <x,Tx> <= (1-gamma) norm(x)^2, gamma <= 1, gives norm(T^t x) <= exp(-gamma t) norm(x) for all natural t.  Caveat: ambient space E not visible; requires T nonnegative (so applies to a lazy or squared walk, not directly to a signed spectrum)

```lean
theorem norm_iterate_le_exp_of_inner_bounds
 (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {γ : ℝ} (hγ : γ ≤ 1)
 (hpos : ∀ x : E, 0 ≤ ⟪x, T x⟫)
 (hgap : ∀ x : E, ⟪x, T x⟫ ≤ (1 - γ) * ‖x‖ ^ 2)
 (t : ℕ) (x : E) :
 ‖(T : E → E)^[t] x‖ ≤ Real.exp (-γ * (t : ℝ)) * ‖x‖
```

### Probability/ThorpRouting/TraceBound [1] trace_re_le_dimension_norm  (general; file: clean)
Reader: For a continuous linear map A on a finite-dimensional complex inner product space: Re trace A <= dim times the operator norm of A.

```lean
lemma trace_re_le_dimension_norm {V : Type*} [NormedAddCommGroup V]
 [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (A : V →L[ℂ] V) :
 (LinearMap.trace ℂ V A.toLinearMap).re ≤ (Module.finrank ℂ V : ℝ) * ‖A‖
```

### Probability/ThorpRouting/TraceBound [2] trace_power_le_dimension_norm  (general; file: clean)
Reader: Same setting, u > 0: Re trace(A^u) <= dim times the operator norm of A to the power u.

```lean
lemma trace_power_le_dimension_norm {V : Type*} [NormedAddCommGroup V]
 [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
 (A : V →L[ℂ] V) (u : ℕ) (hu : 0 < u) :
 (LinearMap.trace ℂ V (A^u).toLinearMap).re ≤
 (Module.finrank ℂ V : ℝ) * ‖A‖^u
```

### RepresentationTheory/PartialPermutation/HilbertSchmidt [9] hsNormSq_mul_le  (general; file: clean)
Reader: Submultiplicativity: hsNormSq (A * B) <= hsNormSq A * hsNormSq B for endomorphisms of V.  Caveat: complex scalars; body of hsNormSq hidden; weaker than the operator-norm times Hilbert-Schmidt bound

```lean
lemma hsNormSq_mul_le (A B : Module.End ℂ V) :
 hsNormSq (A * B) ≤ hsNormSq A * hsNormSq B
```

### RepresentationTheory/PartialPermutation/OperatorNorm [2] opNorm_sq_le_hsNormSq  (general; file: clean)
Reader: Squared operator norm of A (as a continuous linear map) is at most hsNormSq A.  Caveat: complex scalars; body of hsNormSq hidden; V ambient

```lean
lemma opNorm_sq_le_hsNormSq (A : Module.End ℂ V) :
 ‖LinearMap.toContinuousLinearMap A‖^2 ≤ hsNormSq A
```

### RepresentationTheory/Theta/PoissonAutomorphyGaussianPoisson [39] real_pair_diagonalization  (general; file: clean)
Reader: For real X symmetric and Y positive definite there are invertible L and a vector d with Lᵀ Y L = 1 and Lᵀ X L = diagonal d.  Caveat: existence only; d is not identified as eigenvalues of Y⁻¹X in the statement

```lean
theorem real_pair_diagonalization (X Y : Matrix ι ι ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
 ∃ (L : Matrix ι ι ℝ) (d : ι → ℝ), L.det ≠ 0 ∧
 L.transpose * Y * L = 1 ∧ L.transpose * X * L = Matrix.diagonal d
```

### RepresentationTheory/Unitary/Spectral [14] norm_le_trace  (general; file: clean)
Reader: For a positive semidefinite complex square matrix A: norm(A) <= Re tr A.  Caveat: which matrix norm instance is in scope is not visible in the statement

```lean
lemma norm_le_trace (A : Matrix n n ℂ) (hA : A.PosSemidef) : ‖A‖ ≤ (Matrix.trace A).re
```

### RepresentationTheory/Unitary/Spectral [15] norm_sq_le_trace  (general; file: clean)
Reader: For any complex square matrix A: norm(A)^2 <= Re tr(A^H A), i.e. norm bounded by the Frobenius/Hilbert-Schmidt norm.  Caveat: which matrix norm instance is in scope is not visible in the statement

```lean
lemma norm_sq_le_trace (A : Matrix n n ℂ) :
 ‖A‖^2 ≤ (Matrix.trace (A.conjTranspose*A)).re
```

### Topology/ArtinGroups/ParabolicIntersections/MeshSpectralUpper [1] mesh_spectral_upper  (general; file: clean)
Reader: A real Hermitian matrix all of whose eigenvalues are <= d satisfies: d*1 - A is positive semidefinite.  Caveat: index type V and its instances are file-level variables

```lean
lemma mesh_spectral_upper {A : Matrix V V ℝ} (hA : A.IsHermitian) (d : ℝ)
 (hbound : ∀ i, hA.eigenvalues i≤d) :
 (d • (1 : Matrix V V ℝ)-A).PosSemidef
```

## N5

### Analysis/CoulombIonization/FormDomain/CompactEigenbasis [8] compactSpectralBasis  (general; file: clean)
Reader: Definition: for a compact symmetric operator T on H, a Hilbert basis of H indexed by CompactSpectralIndex T.  Caveat: a def, body not shown; assumptions on H hidden; the eigenvector property is [10]

```lean
def compactSpectralBasis (T : H →L[ℂ] H)
 (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
 HilbertBasis (CompactSpectralIndex T) ℂ H
```

### Analysis/CoulombIonization/FormDomain/CompactEigenbasis [10] compactSpectralBasis_eigen  (general; file: clean)
Reader: Each vector of that basis is an eigenvector of the compact symmetric T: T(b i) = i.1 • b i.  Caveat: H file variable (complex scalars); eigenvalue is the first component of the index

```lean
lemma compactSpectralBasis_eigen (T : H →L[ℂ] H)
 (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
 (i : CompactSpectralIndex T) :
 T (compactSpectralBasis T hTc hTs i) = i.1 • compactSpectralBasis T hTc hTs i
```

### Analysis/CoulombIonization/FormDomain/CompactEigenbasis [13] hilbertBasis_frame_trace  (general; file: clean)
Reader: For a Hilbert basis b and measurable v with ∫‖v‖² finite, the sum over i of ∫|⟨b i, v x⟩|² equals ∫‖v x‖².  Caveat: countable index; H file variable; this is the step behind trace = integral of the kernel on the diagonal, not that theorem itself

```lean
lemma hilbertBasis_frame_trace {α : Type w} [MeasurableSpace α]
 (μ : Measure α) (b : HilbertBasis ι ℂ H) [Countable ι] (v : α → H)
 (hv : AEStronglyMeasurable v μ) (hn : Integrable (fun x => ‖v x‖^2) μ) :
 HasSum (fun i => ∫ x, ‖inner ℂ (b i) (v x)‖^2 ∂μ) (∫ x, ‖v x‖^2 ∂μ)
```

### Analysis/CoulombRadii/FormDomain/HilbertBasisSumSqInner [2] frameOperator_hasSum_diagonal  (general; file: clean)
Reader: For v in L2(mu; E) and any countable Hilbert basis b: the diagonal entries Re<b i, frameOperator mu v (b i)> have sum the integral of norm(v x)^2.  Caveat: `frameOperator` body hidden (presumably u -> integral of <v x, u> v x); judgement depends on it

```lean
lemma frameOperator_hasSum_diagonal {ι : Type*} [Countable ι]
 {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (b : HilbertBasis ι ℂ E) :
 HasSum (fun i => (inner ℂ (b i) (frameOperator μ v (b i))).re)
 (∫ x, ‖v x‖^2 ∂μ)
```

### Analysis/CoulombRadii/FormDomain/HilbertBasisSumSqInner [3] frameOperator_spectral_hasSum  (general; file: clean)
Reader: In separable E, for v in L2(mu; E): the eigenvalues of frameOperator mu v, counted through eigenspace bases, have sum the integral of norm(v x)^2.  Caveat: `frameOperator`, `eigenspaceBasisSet` bodies hidden

```lean
lemma frameOperator_spectral_hasSum [SeparableSpace E]
 {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) :
 HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z => i.1.re)
 (∫ x, ‖v x‖^2 ∂μ)
```

### Analysis/CoulombRadii/FormDomain/HilbertBasisSumSqInner [4] compactSpectralBasis_quadratic_hasSum  (general; file: clean)
Reader: For compact symmetric T and any u: sum over the spectral basis of eigenvalue * norm(<e_i, u>)^2 equals Re<u, T u>.  Caveat: complex scalars; class hypotheses on E hidden

```lean
lemma compactSpectralBasis_quadratic_hasSum (T : E →L[ℂ] E)
 (hc : IsCompactOperator T) (hT : T.IsSymmetric) (u : E) :
 HasSum (fun i : Σ z, eigenspaceBasisSet T z =>
 i.1.re * ‖inner ℂ (compactSpectralBasis T hc hT i) u‖^2)
 (inner ℂ u (T u)).re
```

### Analysis/CoulombRadii/SpectralTheory/EigenspaceBasisSet [7] compactSpectralBasis  (general; file: clean)
Reader: Definition: for compact symmetric T on E, a Hilbert basis of E indexed by pairs (eigenvalue z, basis vector of the z-eigenspace).  Caveat: a `def`, body hidden; eigenvector property is [8]; complex scalars

```lean
noncomputable def compactSpectralBasis (T : E →L[ℂ] E)
 (hc : IsCompactOperator T) (hT : T.IsSymmetric) :
 HilbertBasis (Σ z, eigenspaceBasisSet T z) ℂ E
```

### Analysis/CoulombRadii/SpectralTheory/EigenspaceBasisSet [8] compactSpectralBasis_eigen  (general; file: clean)
Reader: Each vector of compactSpectralBasis is an eigenvector: T e_i = (its eigenvalue) * e_i.  Caveat: complex scalars; class hypotheses on E hidden

```lean
lemma compactSpectralBasis_eigen (T : E →L[ℂ] E)
 (hc : IsCompactOperator T) (hT : T.IsSymmetric) (i : Σ z, eigenspaceBasisSet T z) :
 T (compactSpectralBasis T hc hT i) = i.1 • compactSpectralBasis T hc hT i
```

### Analysis/QuantumTrace/Basic [10] norm_le_trace  (general; file: clean)
Reader: A positive T whose diagonal sum re<b_i, T b_i> over a Hilbert basis is tau satisfies ||T|| <= tau.  Caveat: complex Hilbert space; assumptions on E not shown

```lean
theorem norm_le_trace (b : HilbertBasis ι ℂ E)
 {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
 (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) : ‖T‖ ≤ τ
```

### Analysis/QuantumTrace/Basic [12] norm_le_sqrt_basis_sum  (general; file: clean)
Reader: For T : E -> F, if the sum of ||T b_i||^2 over a Hilbert basis is tau then ||T|| <= sqrt(tau).  Caveat: assumptions on E, F not shown

```lean
theorem norm_le_sqrt_basis_sum (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
 {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) :
 ‖T‖ ≤ Real.sqrt τ
```

### Analysis/QuantumTrace/Basic [17] compact_of_summable_basis_norm_sq  (general; file: clean)
Reader: If ||T b_i||^2 is summable over a Hilbert basis then T is a compact operator.  Caveat: assumptions on E, F not shown

```lean
theorem compact_of_summable_basis_norm_sq (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
 (ht : Summable (fun i => ‖T (b i)‖ ^ 2)) : IsCompactOperator T
```

### Analysis/QuantumTrace/Basic [18] compact_of_positive_finite_trace  (general; file: clean)
Reader: A positive T with summable diagonal re<b_i, T b_i> over a Hilbert basis is a compact operator.

```lean
theorem compact_of_positive_finite_trace (b : HilbertBasis ι ℂ E)
 {T : E →L[ℂ] E} (hT : T.IsPositive)
 (ht : Summable (fun i => (inner ℂ (b i) (T (b i))).re)) : IsCompactOperator T
```

### Analysis/QuantumTrace/Basic [19] exists_eigenbasis  (general; file: clean)
Reader: A compact symmetric T on E has a Hilbert basis b with T (b j) = e j • b j for complex numbers e j.  Caveat: no ordering, multiplicity or realness of e j in the statement; index type in universe u; assumptions on E not shown

```lean
theorem exists_eigenbasis {T : E →L[ℂ] E} (hc : IsCompactOperator T)
 (hs : T.IsSymmetric) :
 ∃ (J : Type u) (b : HilbertBasis J ℂ E) (e : J → ℂ),
 ∀ j, T (b j) = e j • b j
```

### Analysis/QuantumTrace/Basic [20] cfc_apply_eigenvector  (general; file: clean)
Reader: For symmetric T with T x = mu • x and f continuous on the spectrum: cfc f T x = f mu • x.  Caveat: complex functional calculus

```lean
theorem cfc_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
 {x : E} {μ : ℂ} (he : T x = μ • x) (f : ℂ → ℂ)
 (hf : ContinuousOn f (spectrum ℂ T)) : cfc f T x = f μ • x
```

### Analysis/QuantumTrace/Basic [24] hasSum_trace_basis  (general; file: clean)
Reader: For positive T, if the diagonal sum re<b_i, T b_i> is tau in one Hilbert basis, it is tau in every other Hilbert basis.  Caveat: positive operators only

```lean
theorem hasSum_trace_basis (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
 {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
 (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
 HasSum (fun i => (inner ℂ (c i) (T (c i))).re) τ
```

### Analysis/QuantumTrace/Basic [25] exists_positive_eigenbasis  (general; file: clean)
Reader: A positive T with diagonal sum tau has a Hilbert basis of eigenvectors with eigenvalues p_j >= 0 and sum of p_j equal to tau.  Caveat: index type in universe u

```lean
theorem exists_positive_eigenbasis (b : HilbertBasis ι ℂ E)
 {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
 (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
 ∃ (J : Type u) (c : HilbertBasis J ℂ E) (p : J → ℝ),
 (∀ j, 0 ≤ p j) ∧ HasSum p τ ∧ ∀ j, T (c j) = (p j : ℂ) • c j
```

### Dynamics/TriangleBilliards/KernelBounds [7] memLp_kernel_integral  (general; file: clean)
Reader: If |F x y| <= K x y |f y| with f in L2(nu) and finite Schur constants A, B for K, then x -> integral of F x y d nu is in L2(mu).  Caveat: membership only (no norm bound in this statement); pointwise row and column bounds required

```lean
-- /-- In particular, genuine strongly measurable kernel integrals map L² to L² whenever both Schur constants are finite. -/
lemma memLp_kernel_integral {α : Type uAlpha} {β : Type uBeta} {E : Type uE} {G : Type uG}
 [MeasurableSpace α] [MeasurableSpace β]
 [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup G]
 (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
 {K : α → β → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
 {f : β → G} (hf : StronglyMeasurable f) (hf₂ : MemLp f 2 ν)
 {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
 (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ A)
 (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
 {F : α → β → E} (hFm : StronglyMeasurable (Function.uncurry F))
 (hF : ∀ x y, ‖F x y‖ₑ ≤ K x y * ‖f y‖ₑ) :
 MemLp (fun x => ∫ y, F x y ∂ν) 2 μ
```

### Geometry/NodalSets/Spectral/CompactEigenframeCardBound [1] compact_eigenframe_card_bound  (general; file: clean)
Reader: For a compact operator T and c > 0 there is K such that every orthonormal family of eigenvectors with eigenvalues >= c has at most K members.  Caveat: real inner product space; K not explicit

```lean
theorem compact_eigenframe_card_bound {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (hT : IsCompactOperator T)
 (c : ℝ) (hc : 0 < c) :
 ∃ K : ℕ, ∀ (N : ℕ) (e : Fin N → E) (mu : Fin N → ℝ),
 Orthonormal ℝ e → (∀ i, T (e i)=mu i • e i) →
 (∀ i, c ≤ mu i) → N ≤ K
```

### Geometry/NodalSets/Spectral/CompactPositiveMaxEigenvector [1] compact_positive_max_eigenvector  (general; file: clean)
Reader: A nonzero compact symmetric positive semidefinite T on a real Hilbert space has a unit eigenvector with eigenvalue ||T||, and <Tx,x> <= ||T|| |x|^2 for all x.  Caveat: real scalars

```lean
theorem compact_positive_max_eigenvector {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [CompleteSpace E] [Nontrivial E]
 (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
 (hp : ∀ x, 0 ≤ inner ℝ (T x) x) (hT : T ≠ 0) :
 ∃ v : E, ‖v‖=1 ∧ T v=‖T‖ • v ∧
 inner ℝ (T v) v=‖T‖ ∧ ∀ x : E, inner ℝ (T x) x ≤ ‖T‖*‖x‖^2
```

### Geometry/NodalSets/Spectral/FiniteVariationalEigenframe [3] compact_positive_finite_variational_eigenframe  (general; file: clean)
Reader: Compact symmetric strictly positive T on an infinite-dimensional real Hilbert space has, for every N, N orthonormal eigenvectors with positive antitone eigenvalues and the successive-maximum Rayleigh property.  Caveat: real scalars; strict positivity and infinite dimension required; finite frames only, no full eigenbasis statement

```lean
theorem compact_positive_finite_variational_eigenframe {E : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
 (hE : ¬FiniteDimensional ℝ E)
 (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
 (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x) (N : ℕ) :
 ∃ (e : Fin N → E) (mu : Fin N → ℝ),
 Orthonormal ℝ e ∧ (∀ i, 0 < mu i ∧ T (e i) = mu i • e i) ∧
 Antitone mu ∧ ∀ i x,
 (∀ j, j < i → inner ℝ (e j) x = 0) →
 inner ℝ (T x) x ≤ mu i * ‖x‖^2
```

### GroupTheory/Kervaire/SpectralMeasures [9] integral_vectorMeasure  (general; file: clean)
Reader: For a normal operator U and continuous real f on its spectrum: integral of f against the spectral measure of xi equals Re <xi, f(U) xi>.  Caveat: bounded normal operators on a complex Hilbert space only; Operator H body not shown

```lean
-- /-- The defining integration identity for the scalar spectral measure. -/
theorem integral_vectorMeasure (U : Operator H) [hU : IsStarNormal U] (ξ : H)
 (f : C(spectrum ℂ U, ℝ)) :
 ∫ z, f z ∂vectorMeasure U ξ = (inner ℂ ξ (cfcHom hU (complexify f) ξ)).re
```

### GroupTheory/Kervaire/SpectralMeasures [43] tendsto_calculus  (general; file: clean)
Reader: Uniformly bounded continuous f_n converging pointwise on the spectrum to a continuous g give strong convergence f_n(U) xi -> g(U) xi for normal U.  Caveat: bounded normal operators only; continuous functional calculus cfcHom

```lean
-- /-- An already continuous pointwise limit is identified by the scalar measures. -/
theorem tendsto_calculus (U : Operator H) [hU : IsStarNormal U]
 (f : ℕ → C(spectrum ℂ U, ℂ)) (g : C(spectrum ℂ U, ℂ))
 (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n z, ‖f n z‖ ≤ C)
 (ht : ∀ z, Tendsto (fun n => f n z) atTop (𝓝 (g z))) (ξ : H) :
 Tendsto (fun n => cfcHom hU (f n) ξ) atTop (𝓝 (cfcHom hU g ξ))
```

### InformationTheory/Entanglement/HilbertTrace [7] positiveTrace_change_basis  (general; file: clean)
Reader: A positive operator with finite trace in Hilbert basis b has finite trace in any other Hilbert basis c, and the two traces agree.  Caveat: hilbertTrace and HasFinitePositiveTrace are project definitions, bodies not shown

```lean
lemma positiveTrace_change_basis (b : HilbertBasis ι ℂ H) (c : HilbertBasis κ ℂ H)
 {T : H →L[ℂ] H} (hT : HasFinitePositiveTrace b T) :
 HasFinitePositiveTrace c T ∧ hilbertTrace c T=hilbertTrace b T
```

### InformationTheory/Entanglement/HilbertTrace [5] symmetric_finite_compression_trace  (general; file: clean)
Reader: For symmetric bounded S with sum of ‖S b_i‖^2 summable over a Hilbert basis, any finite orthonormal family v has sum ‖S v_j‖^2 ≤ tsum ‖S b_i‖^2.  Caveat: symmetric S only; inequality for finite subfamilies, not equality of Hilbert-Schmidt norms

```lean
lemma symmetric_finite_compression_trace
 (b : HilbertBasis ι ℂ H) (S : H →L[ℂ] H) (hS : S.IsSymmetric)
 (hi : Summable (fun i => ‖S (b i)‖^2))
 (v : κ → H) (hv : Orthonormal ℂ v) (s : Finset κ) :
 ∑ j ∈ s, ‖S (v j)‖^2 ≤ ∑' i, ‖S (b i)‖^2
```

### InformationTheory/PhotonNumber/SpectralLog [50] log_apply_eigenvector  (general; file: clean)
Reader: For strictly positive bounded T and eigenvector x with real eigenvalue p: CFC.log T x = (log p) • x.  Caveat: class assumptions on E come from a variable line not shown

```lean
theorem log_apply_eigenvector {T : E →L[ℂ] E} (hT : IsStrictlyPositive T)
 {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
 CFC.log T x = (Real.log p : ℂ) • x
```

### MathematicalPhysics/PEPSMove/PartialTrace [16] trace_cfc  (general; file: clean)
Reader: For a Hermitian matrix A and a real function f: the trace of cfc f A equals the sum over i of f(eigenvalue i).  Caveat: finite-dimensional matrices only

```lean
theorem trace_cfc (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
 (cfc f A).trace=∑ i, (f (hA.eigenvalues i) : ℂ)
```

### MathematicalPhysics/PEPSSubvolume/QuantumSSA [1] cfc_intertwine  (general; file: clean)
Reader: If Hermitian matrices A, B satisfy A V = V B for a rectangular V, then f(A) V = V f(B) for every real function f (continuous functional calculus).  Caveat: finite complex matrices

```lean
lemma cfc_intertwine {A : Matrix m m ℂ} {B : Matrix n n ℂ}
 (hA : A.IsHermitian) (hB : B.IsHermitian) (V : Matrix m n ℂ)
 (hV : A*V=V*B) (f : ℝ → ℝ) : cfc f A*V=V*cfc f B
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [16] trace_cfc  (general; file: clean)
Reader: For a Hermitian matrix A and real f: tr(f(A)) equals the sum of f over the eigenvalues of A.  Caveat: finite complex matrices

```lean
theorem trace_cfc (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
 (cfc f A).trace=∑ i, (f (hA.eigenvalues i) : ℂ)
```

### Probability/SKRatio/Matrices/ExpDuhamel [1] exp_duhamel  (general; file: clean)
Reader: Duhamel formula: exp a - exp b equals the integral over u in [0,1] of exp((1-u)a) * (a-b) * exp(u b).  Caveat: assumptions on the algebra A and the exp used sit in an unseen variable line

```lean
lemma exp_duhamel (a b : A) :
 exp a - exp b = ∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b)
```

## N7

### Analysis/QuantumTrace/Basic [31] entropy_summable_and_le_crossEntropy  (general; file: clean)
Reader: Countable weights p >= 0, q > 0, both summing to 1, with summable cross entropy: negMulLog(p_i) is summable and its sum is <= sum of p_i * (-log q_i).  Caveat: classical (commuting) relative-entropy nonnegativity only

```lean
theorem entropy_summable_and_le_crossEntropy {ι : Type*} (p q : ι → ℝ)
 (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
 (hp1 : HasSum p 1) (hq1 : HasSum q 1)
 (hcross : Summable (fun i => p i * (-Real.log (q i)))) :
 Summable (fun i => Real.negMulLog (p i)) ∧
 (∑' i, Real.negMulLog (p i)) ≤ ∑' i, p i * (-Real.log (q i))
```

### Analysis/QuantumTrace/Basic [40] entropy_le_thermal_crossEntropy  (general; file: clean)
Reader: Positive T with diagonal sum 1 and finite number-energy E in a basis indexed by Fin n -> N: sum of re<b_k, entropyOperator T b_k> <= n*log(r+1) + E*log((r+1)/r), any r > 0.  Caveat: entropy and energy are diagonal sums in the given basis; entropyOperator body hidden; the choice r = E/n is not made here

```lean
theorem entropy_le_thermal_crossEntropy {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ E)
 {T : E →L[ℂ] E} (hp : T.IsPositive)
 (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1)
 (hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re))
 {r : ℝ} (hr : 0 < r) :
 (∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re) ≤
 n * Real.log (r + 1) +
 (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) * Real.log ((r + 1) / r)
```

### InformationTheory/AmplitudeDamping/EntropyContinuity [13] shannon_le_log_card  (general; file: clean)
Reader: For a probability vector p on a finite type: sum of -p_i log p_i <= log of the number of points.

```lean
theorem shannon_le_log_card [Nonempty ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
 (hs : ∑ i, p i = 1) : (∑ i, Real.negMulLog (p i)) ≤ Real.log (Fintype.card ι)
```

### InformationTheory/AmplitudeDamping/EntropyContinuity [14] entropy_le_log_card  (general; file: clean)
Reader: For a state A (density matrix) on a finite index type: entropy A <= log of the dimension.  Caveat: finite-dimensional; entropy and IsState are project definitions (Model [3], [4])

```lean
theorem entropy_le_log_card [Nonempty ι] {A : Matrix ι ι ℂ} (hA : IsState A) :
 entropy A ≤ Real.log (Fintype.card ι)
```

### InformationTheory/AmplitudeDamping/EntropyContinuity [16] entropy_coupling_bound  (general; file: clean)
Reader: Entropy continuity: states A, B with A + U = B + V, U and V positive semidefinite of trace t > 0: entropy A - entropy B <= t log(dim) + (1+t) binEntropy(t/(1+t)).  Caveat: finite-dimensional; one-sided bound

```lean
-- /-- Entropy continuity from a positive common-mixture coupling. -/
theorem entropy_coupling_bound [Nonempty ι] {A B U V : Matrix ι ι ℂ}
 (hA : IsState A) (hB : IsState B) (hU : U.PosSemidef) (hV : V.PosSemidef)
 {t : ℝ} (ht : 0 < t) (htrU : U.trace=(t:ℂ)) (htrV : V.trace=(t:ℂ))
 (heq : A+U=B+V) :
 entropy A-entropy B ≤ t*Real.log (Fintype.card ι)+(1+t)*Real.binEntropy (t/(1+t))
```

### InformationTheory/AmplitudeDamping/LogDetEntropy [12] entropy_mul_conjTranspose  (general; file: clean)
Reader: For a rectangular complex matrix A: entropy(A A^H) = entropy(A^H A).  Caveat: finite-dimensional; entropy is the project definition

```lean
-- /-- Nonzero spectra, including their entropy, agree for both rectangular Gram matrices. -/
theorem entropy_mul_conjTranspose {κ : Type u_5} [Fintype κ] [DecidableEq κ]
 (A : Matrix ι κ ℂ) : entropy (A * Aᴴ) = entropy (Aᴴ * A)
```

### InformationTheory/AmplitudeDamping/SpectralEntropy [3] entropy_eq_sum  (general; file: clean)
Reader: For a Hermitian matrix A: entropy A equals the sum of -x log x over its eigenvalues.  Caveat: finite-dimensional; entropy is the project definition

```lean
theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
 entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i)
```

### InformationTheory/AmplitudeDamping/SpectralEntropy [8] entropy_le_diagonal  (general; file: clean)
Reader: For positive semidefinite A: entropy A <= sum of -x log x over the real parts of the diagonal entries (pinching increases entropy).  Caveat: finite-dimensional

```lean
-- /-- Pinching in any fixed orthonormal coordinate basis increases entropy. -/
theorem entropy_le_diagonal {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
 entropy A ≤ ∑ i, Real.negMulLog (A i i).re
```

### InformationTheory/AmplitudeDamping/SpectralEntropy [10] concaveOn_entropy  (general; file: clean)
Reader: The matrix entropy is concave on the set of positive semidefinite matrices.  Caveat: finite-dimensional; entropy is the project definition

```lean
-- /-- The full matrix entropy, not just normalized-state entropy, is concave on positive semidefinite matrices. -/
theorem concaveOn_entropy :
 ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosSemidef} entropy
```

### InformationTheory/AmplitudeDamping/StateEntropy [16] entropy_mixture_upper  (general; file: clean)
Reader: For states A_a and weights w_a >= 0: entropy(sum w_a A_a) <= sum of (w_a entropy(A_a) - w_a log w_a).  Caveat: finite-dimensional

```lean
theorem entropy_mixture_upper (w : α → ℝ) (A : α → Matrix ι ι ℂ)
 (hw : ∀ a, 0 ≤ w a) (hA : ∀ a, IsState (A a)) :
 entropy (∑ a, w a • A a) ≤ ∑ a, (w a*entropy (A a)+Real.negMulLog (w a))
```

### InformationTheory/AmplitudeDamping/TensorEntropy [7] entropy_kronecker  (general; file: clean)
Reader: For Hermitian A, B: entropy(A tensor B) = Re tr(B) * entropy A + Re tr(A) * entropy B.  Caveat: finite-dimensional; Kronecker product of matrices

```lean
theorem entropy_kronecker {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
 (hA : A.IsHermitian) (hB : B.IsHermitian) :
 entropy (A ⊗ₖ B) = B.trace.re * entropy A + A.trace.re * entropy B
```

### InformationTheory/AmplitudeDamping/TensorEntropy [8] entropy_kronecker_state  (general; file: clean)
Reader: Additivity: for states A, B: entropy(A tensor B) = entropy A + entropy B.  Caveat: finite-dimensional

```lean
theorem entropy_kronecker_state {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
 (hA : IsState A) (hB : IsState B) : entropy (A ⊗ₖ B) = entropy A + entropy B
```

### InformationTheory/PhotonNumber/GibbsVariational [12] quantum_klein  (general; file: clean)
Reader: Klein inequality: T diagonal in basis b (eigenvalues p), symmetric S diagonal in c (eigenvalues q>0), sums 1: sum negMulLog p ≤ −sum Re⟨c_j,T c_j⟩ log q_j; equality gives T=S.  Caveat: both operators need a diagonalising Hilbert basis; sums supplied as HasSum hypotheses

```lean
theorem quantum_klein (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
 {T S : E →L[ℂ] E} (hs : S.IsSymmetric)
 {p : I → ℝ} {q : J → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
 (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
 (heT : ∀ i, T (b i) = (p i : ℂ) • b i)
 (heS : ∀ j, S (c j) = (q j : ℂ) • c j)
 {H C : ℝ} (hh : HasSum (fun i => Real.negMulLog (p i)) H)
 (hc : HasSum (fun j => (inner ℂ (c j) (T (c j))).re * (-Real.log (q j))) C) :
 H ≤ C ∧ (H = C → T = S)
```

### InformationTheory/PhotonNumber/GibbsVariational [1] negMulLog_lt_crossEntropy  (general; file: clean)
Reader: Strict scalar Gibbs inequality: for p ≥ 0, q > 0, p ≠ q, negMulLog p < q − p + p·(−log q).

```lean
theorem negMulLog_lt_crossEntropy {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hne : p ≠ q) :
 Real.negMulLog p < q - p + p * (-Real.log q)
```

### InformationTheory/PhotonNumber/Inequality [8] hasDerivAt_g  (general; file: clean)
Reader: For t > 0, g has derivative log(t+1) − log t at t.  Caveat: g is defined in Basic [9], body not shown

```lean
theorem hasDerivAt_g {t : ℝ} (ht : 0 < t) :
 HasDerivAt g (Real.log (t + 1) - Real.log t) t
```

### InformationTheory/PhotonNumber/Inequality [9] strictMonoOn_g  (general; file: clean)
Reader: g is strictly increasing on [0, ∞).  Caveat: g body not shown

```lean
theorem strictMonoOn_g : StrictMonoOn g (Ici 0)
```

### MathematicalPhysics/PEPSMove/EntropyBounds [24] entropy_subadditive  (general; file: clean)
Reader: For PSD A indexed by m×n: traceEntropy A + negMulLog(Re tr A) ≤ traceEntropy(ptrR A) + traceEntropy(ptrL A); subadditivity, i.e. nonnegative mutual information, unnormalised form.  Caveat: finite matrices only; traceEntropy, ptrL, ptrR are project definitions with hidden bodies

```lean
theorem entropy_subadditive [Nonempty m] [Nonempty n]
 {A : Matrix (m×n) (m×n) ℂ} (hA : A.PosSemidef) :
 traceEntropy A+Real.negMulLog A.trace.re≤traceEntropy (ptrR A)+traceEntropy (ptrL A)
```

### MathematicalPhysics/PEPSMove/EntropyBounds [10] conditional_superadditive  (general; file: clean)
Reader: For PSD A, B indexed by m×n: (S(A) − S(ptrL A)) + (S(B) − S(ptrL B)) ≤ S(A+B) − S(ptrL(A+B)), S = traceEntropy.  Caveat: finite matrices only; traceEntropy and ptrL hidden; which factor ptrL traces out must be checked

```lean
theorem conditional_superadditive [Nonempty m]
 {A B : Matrix (m×n) (m×n) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
 (traceEntropy A-traceEntropy (ptrL A))+(traceEntropy B-traceEntropy (ptrL B))≤
 traceEntropy (A+B)-traceEntropy (ptrL (A+B))
```

### MathematicalPhysics/PEPSMove/EntropyBounds [25] entropy_density_upper  (general; file: clean)
Reader: PSD matrix A with Re trace 1 has traceEntropy A ≤ log(card n).  Caveat: finite matrices only; traceEntropy hidden definition

```lean
theorem entropy_density_upper [Nonempty n] {A : Matrix n n ℂ}
 (hA : A.PosSemidef) (htr : A.trace.re=1) :
 traceEntropy A≤Real.log (Fintype.card n:ℝ)
```

### MathematicalPhysics/PEPSMove/LogCompression [4] log_compression  (general; file: clean)
Reader: For positive definite A and V with V* V = 1: V* (log A) V <= log(V* A V) in the matrix order.  Caveat: finite-dimensional matrices; log is CFC.log

```lean
theorem log_compression (A : Matrix m m ℂ) (hA : A.PosDef)
 (V : Matrix m n ℂ) (hV : V.conjTranspose*V=1) :
 V.conjTranspose*CFC.log A*V ≤ CFC.log (V.conjTranspose*A*V)
```

### MathematicalPhysics/PEPSMove/LogCompression [8] log_kronecker  (general; file: clean)
Reader: For positive definite A, B: log(A kron B) = (log A) kron 1 + 1 kron (log B).  Caveat: finite-dimensional matrices; gives additivity of entropy on product states

```lean
lemma log_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
 (hA : A.PosDef) (hB : B.PosDef) :
 CFC.log (A ⊗ₖ B) = (CFC.log A ⊗ₖ (1 : Matrix n n ℂ))+
 ((1 : Matrix m m ℂ) ⊗ₖ CFC.log B)
```

### MathematicalPhysics/PEPSMove/LogCompression [34] relative_entropy_mono_posDef  (general; file: clean)
Reader: Positive definite A, B, a, b and a star-homomorphism phi with tr(A phi X) = tr(a X), tr(B phi X) = tr(b X) for all X: Re tr a(log a - log b) <= Re tr A(log A - log B).  Caveat: finite-dimensional, strictly positive definite only; the map is the adjoint of a star-homomorphism (covers partial trace), not an arbitrary channel

```lean
theorem relative_entropy_mono_posDef (φ : Matrix n n ℂ →⋆ₐ[ℂ] Matrix m m ℂ)
 {A B : Matrix m m ℂ} {a b : Matrix n n ℂ}
 (hA : A.PosDef) (hB : B.PosDef) (ha : a.PosDef) (hb : b.PosDef)
 (hdualA : ∀ X, (A*φ X).trace=(a*X).trace)
 (hdualB : ∀ X, (B*φ X).trace=(b*X).trace) :
 (a*(CFC.log a-CFC.log b)).trace.re ≤ (A*(CFC.log A-CFC.log B)).trace.re
```

### MathematicalPhysics/PEPSMove/PartialTrace [8] trace_ptrR  (general; file: clean)
Reader: For A on the index type m x n: the trace of ptrR A equals the trace of A.  Caveat: ptrR body hidden; finite-dimensional

```lean
theorem trace_ptrR (A : Matrix (m×n) (m×n) ℂ) : (ptrR A).trace=A.trace
```

### MathematicalPhysics/PEPSMove/PartialTrace [9] ptrR_dual  (general; file: clean)
Reader: For A on m x n and X on m: tr(A * tensorLeftHom X) = tr(ptrR A * X).  Caveat: tensorLeftHom body hidden (presumably X kron 1); [10] is the ptrL version

```lean
theorem ptrR_dual (A : Matrix (m×n) (m×n) ℂ) (X : Matrix m m ℂ) :
 (A*tensorLeftHom X).trace=(ptrR A*X).trace
```

### MathematicalPhysics/PEPSMove/PartialTrace [17] traceEntropy_spectral  (general; file: clean)
Reader: For a Hermitian matrix A: traceEntropy A equals the sum over i of negMulLog(eigenvalue i).  Caveat: traceEntropy body hidden; this identifies it with the von Neumann entropy; finite-dimensional

```lean
theorem traceEntropy_spectral (A : Matrix n n ℂ) (hA : A.IsHermitian) :
 traceEntropy A=∑ i, Real.negMulLog (hA.eigenvalues i)
```

### MathematicalPhysics/PEPSMove/PartialTrace [18] traceEntropy_log  (general; file: clean)
Reader: For a positive definite matrix A: traceEntropy A = -Re tr(A log A).  Caveat: finite-dimensional; positive definite only

```lean
theorem traceEntropy_log {A : Matrix n n ℂ} (hA : A.PosDef) :
 traceEntropy A= -(A*CFC.log A).trace.re
```

### MathematicalPhysics/PEPSMove/PureEntropy [4] traceEntropy_gram  (general; file: clean)
Reader: For any rectangular complex matrix C: traceEntropy(C C*) = traceEntropy(C* C).  Caveat: equal entropies of the two marginals of a pure state; finite-dimensional

```lean
theorem traceEntropy_gram (C : Matrix m n ℂ) :
 traceEntropy (C*C.conjTranspose)=traceEntropy (C.conjTranspose*C)
```

### MathematicalPhysics/PEPSMove/PureEntropy [9] entropy_triangle  (general; file: clean)
Reader: For positive semidefinite A on m x n: traceEntropy(ptrL A) + negMulLog(Re tr A) <= traceEntropy(ptrR A) + traceEntropy A.  Caveat: Araki-Lieb type inequality; ptrL, ptrR bodies hidden; finite-dimensional

```lean
theorem entropy_triangle [Nonempty m] [Nonempty n]
 {A : Matrix (m×n) (m×n) ℂ} (hA : A.PosSemidef) :
 traceEntropy (ptrL A)+Real.negMulLog A.trace.re≤
 traceEntropy (ptrR A)+traceEntropy A
```

### MathematicalPhysics/PEPSMove/StrongSubadditivity [13] strong_subadditivity  (general; file: clean)
Reader: Strong subadditivity for positive semidefinite A on (m x n) x p: S(A) + S(n-marginal) <= S(mn-marginal) + S(np-marginal), with S = traceEntropy.  Caveat: finite-dimensional; marginals are written ptrR A, ptrL (assocMatrix A), ptrR (ptrL (assocMatrix A)), my reading follows their types, bodies hidden; no trace normalisation; [10] is the positive definite case

```lean
theorem strong_subadditivity [Nonempty m] [Nonempty p]
 {A : Matrix ((m×n)×p) ((m×n)×p) ℂ} (hA : A.PosSemidef) :
 traceEntropy A+traceEntropy (ptrR (ptrL (assocMatrix A))) ≤
 traceEntropy (ptrR A)+traceEntropy (ptrL (assocMatrix A))
```

### MathematicalPhysics/PEPSSubvolume/PinnedCosts [15] entropy_concave_mixture  (general; file: clean)
Reader: Concavity of matrix entropy: for probabilities p_k and positive semidefinite A_k, sum p_k*entropy(A_k) <= entropy(sum p_k A_k).  Caveat: `entropy` is a project definition (body not shown); finite matrices, no trace-one hypothesis

```lean
theorem entropy_concave_mixture {s : Type*} [Fintype s]
 (p : s → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
 (A : s → Matrix n n ℂ) (hA : ∀ k, (A k).PosSemidef) :
 ∑ k, p k * entropy (A k) (hA k).isHermitian ≤
 entropy (∑ k, p k • A k)
 (Matrix.posSemidef_sum _ (fun k _ => (hA k).smul (hp k))).isHermitian
```

### MathematicalPhysics/PEPSSubvolume/QuantumSSA [8] log_kronecker  (general; file: clean)
Reader: For positive definite A, B: log(A kron B) = log(A) kron 1 + 1 kron log(B).  Caveat: finite matrices, positive definite only

```lean
lemma log_kronecker {A : Matrix m m ℂ} {B : Matrix n n ℂ}
 (hA : A.PosDef) (hB : B.PosDef) :
 CFC.log (A ⊗ₖ B) = (CFC.log A ⊗ₖ (1 : Matrix n n ℂ))+
 ((1 : Matrix m m ℂ) ⊗ₖ CFC.log B)
```

### MathematicalPhysics/PEPSSubvolume/QuantumSSA [34] relative_entropy_mono_posDef  (general; file: clean)
Reader: Monotonicity of relative entropy: if a, b are the pullbacks of A, B along a star-algebra hom phi (trace duality), then Re tr(a(log a - log b)) <= Re tr(A(log A - log B)).  Caveat: all four matrices positive definite (full rank); finite dimension; phi is a star-hom, so covers partial trace/restriction, not arbitrary channels

```lean
theorem relative_entropy_mono_posDef (φ : Matrix n n ℂ →⋆ₐ[ℂ] Matrix m m ℂ)
 {A B : Matrix m m ℂ} {a b : Matrix n n ℂ}
 (hA : A.PosDef) (hB : B.PosDef) (ha : a.PosDef) (hb : b.PosDef)
 (hdualA : ∀ X, (A*φ X).trace=(a*X).trace)
 (hdualB : ∀ X, (B*φ X).trace=(b*X).trace) :
 (a*(CFC.log a-CFC.log b)).trace.re ≤ (A*(CFC.log A-CFC.log B)).trace.re
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [6] ptrR_posSemidef  (general; file: clean)
Reader: The partial trace ptrR over the second tensor factor of a positive semidefinite matrix on m x n is positive semidefinite.  Caveat: ptrR body not shown; [27] is the ptrL version

```lean
theorem ptrR_posSemidef {A : Matrix (m×n) (m×n) ℂ} (hA : A.PosSemidef) :
 (ptrR A).PosSemidef
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [8] trace_ptrR  (general; file: clean)
Reader: Partial trace preserves the trace: tr(ptrR A) = tr A.  Caveat: ptrR body not shown

```lean
theorem trace_ptrR (A : Matrix (m×n) (m×n) ℂ) : (ptrR A).trace=A.trace
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [9] ptrR_dual  (general; file: clean)
Reader: Duality characterising the partial trace: tr(A * tensorLeftHom X) = tr(ptrR A * X) for all X.  Caveat: tensorLeftHom is defined in QuantumSSA [5] (body not shown, presumably X kron 1); [10] is the ptrL version

```lean
theorem ptrR_dual (A : Matrix (m×n) (m×n) ℂ) (X : Matrix m m ℂ) :
 (A*tensorLeftHom X).trace=(ptrR A*X).trace
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [11] ptrR_kronecker  (general; file: clean)
Reader: Partial trace of a product: ptrR(A kron B) = tr(B) * A.  Caveat: ptrR body not shown

```lean
theorem ptrR_kronecker (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
 ptrR (A ⊗ₖ B) = B.trace • A
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [17] traceEntropy_spectral  (general; file: clean)
Reader: For Hermitian A, traceEntropy A equals the sum of negMulLog (-x log x) over the eigenvalues of A.  Caveat: traceEntropy body not shown

```lean
theorem traceEntropy_spectral (A : Matrix n n ℂ) (hA : A.IsHermitian) :
 traceEntropy A=∑ i, Real.negMulLog (hA.eigenvalues i)
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [18] traceEntropy_log  (general; file: clean)
Reader: For positive definite A: traceEntropy A = -Re tr(A log A).  Caveat: traceEntropy body not shown

```lean
theorem traceEntropy_log {A : Matrix n n ℂ} (hA : A.PosDef) :
 traceEntropy A= -(A*CFC.log A).trace.re
```

### MathematicalPhysics/PEPSSubvolume/SSARegularized [44] strong_subadditivity  (general; file: clean)
Reader: Strong subadditivity for a positive semidefinite matrix on (m x n) x p: S(ABC) + S(B) <= S(AB) + S(BC), with marginals given by ptrR, ptrL.  Caveat: finite dimension; no trace-one hypothesis; traceEntropy, ptrR, ptrL, assocMatrix bodies not shown; [41] is the positive definite case

```lean
theorem strong_subadditivity [Nonempty m] [Nonempty p]
 {A : Matrix ((m×n)×p) ((m×n)×p) ℂ} (hA : A.PosSemidef) :
 traceEntropy A+traceEntropy (ptrR (ptrL (assocMatrix A))) ≤
 traceEntropy (ptrR A)+traceEntropy (ptrL (assocMatrix A))
```

## N8

### Analysis/BiholderTransport/Geodesics/GaussLemma [10] coordinate_gauss_variation  (general; file: clean)
Reader: Gauss lemma in coordinates: for geodesics A(t,s) from x with initial velocities nu(s), g(velocity, dA/ds) at (t,s) equals t * g_x(nu s, nu'(s)).  Caveat: coordinate metric on an open set of E; coordinateChristoffel and directionalDerivative are project definitions

```lean
lemma coordinate_gauss_variation
 {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
 (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
 (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
 {A V : ℝ × ℝ → E} {a b c d : ℝ}
 (hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ Ioo c d))
 (hV : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ Ioo c d))
 (himg : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c d, A (t,s) ∈ S)
 (hode : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c d,
 HasDerivAt (fun q => A (q,s)) (V (t,s)) t ∧
 HasDerivAt (fun q => V (q,s))
 (-coordinateChristoffel g (A (t,s)) (V (t,s)) (V (t,s))) t)
 {x : E} {ν : ℝ → E}
 (h0 : 0 ∈ Ioo a b) (hA0 : ∀ s ∈ Ioo c d, A (0,s) = x)
 (hV0 : ∀ s ∈ Ioo c d, V (0,s) = ν s)
 {s t : ℝ} {w : E} (ht : t ∈ Ioo a b) (hs : s ∈ Ioo c d)
 (hν : HasDerivAt ν w s) :
 g (A (t,s)) (V (t,s)) (directionalDerivative A (0,1) (t,s)) =
 t * g x (ν s) w
```

### Analysis/BiholderTransport/Geodesics/IntegratedGauss [2] sprayFlow_gauss  (general; file: clean)
Reader: Gauss lemma on the manifold: inner product of the geodesic velocity at time t with the variation field from initial vectors v + s w equals t * <v, w>.  Caveat: sprayFlow is the project's geodesic flow (body hidden); M's hypotheses are file variables not shown

```lean
lemma sprayFlow_gauss (x : M) (v w : TangentSpace 𝓘(ℝ,E) x) (t : ℝ) :
 inner ℝ (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).2
 (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
 (fun s : ℝ => (sprayFlow t (⟨x,v+s • w⟩ : TangentBundle 𝓘(ℝ,E) M)).1) 0 1) =
 t*inner ℝ v w
```

### Analysis/BiholderTransport/Geodesics/ShortGradient [1] exists_local_spray_cost_gradient  (general; file: clean)
Reader: First variation, locally: y -> dist(z, y)^2 / 2 has derivative <t * velocity, .> at the endpoint of a minimizing geodesic of time t from z.  Caveat: local (ball of unspecified radius delta); sprayFlow project definition; M's hypotheses not shown; [3] is the derivative at the starting point

```lean
lemma exists_local_spray_cost_gradient (a : M) :
 ∃ δ : ℝ, 0 < δ ∧ ∀ z : TangentBundle 𝓘(ℝ,E) M, ∀ t : ℝ, 0 < t →
 z.1 ∈ Metric.ball a δ → (sprayFlow t z).1 ∈ Metric.ball a δ →
 dist z.1 (sprayFlow t z).1 = t*‖z.2‖ →
 HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun y => dist z.1 y^2/2)
 (sprayFlow t z).1 (innerSL ℝ (t • (sprayFlow t z).2))
```

### Analysis/BiholderTransport/Geodesics/SprayMinimizing [2] sprayFlow_locally_minimizing  (general; file: clean)
Reader: Geodesics realise distance locally: around every time t0 there is eps with dist(gamma s, gamma u) = |s-u| * speed for s, u within eps of t0.  Caveat: eps not explicit or uniform; sprayFlow project definition; M's hypotheses not shown

```lean
lemma sprayFlow_locally_minimizing (z : TangentBundle 𝓘(ℝ,E) M) (t₀ : ℝ) :
 ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ, |s-t₀| < ε → |u-t₀| < ε →
 dist (sprayFlow s z).1 (sprayFlow u z).1 = |s-u| * ‖z.2‖
```

### Analysis/BiholderTransport/Regularity/RiemannianMetricSegment [1] riemannian_exists_metric_segment  (general; file: clean)
Reader: On a compact Riemannian manifold (Mathlib IsRiemannianManifold), any two points x, y are joined by an isometry from the interval [0, dist x y].  Caveat: compact only; gives a metric segment, no smoothness or geodesic equation

```lean
lemma riemannian_exists_metric_segment
 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace H M]
 [RiemannianBundle (fun x : M => TangentSpace I x)]
 [IsRiemannianManifold I M] (x y : M) :
 ∃ γ : Icc (0:ℝ) (dist x y) → M, Isometry γ ∧
 γ ⟨0,⟨le_rfl,dist_nonneg⟩⟩ = x ∧
 γ ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩ = y
```

### Combinatorics/Progressions/Estimates/RiemannianLipschitz [4] riemannianEDist_le_mul_of_mfderiv_bound  (general; file: clean)
Reader: C^1 map phi between manifolds with ||d phi v|| <= C||v|| everywhere, C > 0: Riemannian edist(phi x, phi y) <= C * Riemannian edist(x, y).  Caveat: manifold and metric assumptions from hidden variable lines; [2] is the case C = 1

```lean
theorem riemannianEDist_le_mul_of_mfderiv_bound {φ : M → N} {C : ℝ≥0}
 (hC : 0 < C) (hφ : ContMDiff I J 1 φ)
 (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ C * ‖v‖ₑ)
 (x y : M) : riemannianEDist J (φ x) (φ y) ≤ C * riemannianEDist I x y
```

### Geometry/Riemannian/EDistMap [3] riemannianEDist_map_le  (general; file: clean)
Reader: A C1 map between manifolds whose differential has norm at most C (C > 0) satisfies riemannianEDist(f x, f y) <= C * riemannianEDist(x, y).  Caveat: manifold and model hypotheses on M, N, I, J are file variables not shown

```lean
-- /-- A positive finite differential bound controls the actual Riemannian extended distance. Positivity is necessary if the source has distinct path components. -/
theorem riemannianEDist_map_le {f : M → N} (hf : ContMDiff I J 1 f)
 {C : ℝ≥0} (hC : 0 < C) (hbound : ∀ x, ‖mfderiv I J f x‖ₑ ≤ C)
 (x y : M) :
 riemannianEDist J (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDist I x y
```

### Geometry/Riemannian/EDistMap [6] lipschitzWith_of_mfderiv_bound  (general; file: clean)
Reader: A C1 map between Riemannian manifolds with globally bounded differential (norm <= C, C > 0) is LipschitzWith C.  Caveat: manifold and model hypotheses are file variables not shown

```lean
-- /-- A globally bounded differential gives a Lipschitz map between Riemannian manifolds. -/
theorem lipschitzWith_of_mfderiv_bound
 [PseudoEMetricSpace M] [IsRiemannianManifold I M]
 [PseudoEMetricSpace N] [IsRiemannianManifold J N]
 {f : M → N} (hf : ContMDiff I J 1 f)
 {C : ℝ≥0} (hC : 0 < C) (hbound : ∀ x, ‖mfderiv I J f x‖ ≤ C) :
 LipschitzWith C f
```

### Geometry/Riemannian/LengthSpace [3] exists_intermediate_dist  (general; file: clean)
Reader: For 0 ≤ s ≤ dist x y and ε>0 there is z with dist x z = s and dist z y < dist x y − s + ε; no completeness assumed.  Caveat: assumptions on M (Riemannian distance, per the doc comment) are file variables not shown

```lean
-- /-- Real-distance intermediate-point property. In particular, Riemannian distance has approximate midpoints without any completeness or minimizing-geodesic assumption. -/
theorem exists_intermediate_dist (x y : M) {s ε : ℝ}
 (hs : 0 ≤ s) (hsd : s ≤ dist x y) (hε : 0 < ε) :
 ∃ z : M, dist x z = s ∧ dist z y < dist x y - s + ε
```

### Geometry/WeakMTW/Geodesics/GaussLemma [1] flow_gauss  (general; file: clean)
Reader: Gauss lemma: G at the endpoint of the geodesic, applied to the flow derivatives in velocity directions v and w, equals T^2 * G_x(v,w).  Caveat: stated in a chart (open set S of a vector space E, smooth symmetric positive G); the geodesic flow Phi with its ODE is a hypothesis; MetricTensor, geodesicSpray hidden

```lean
theorem flow_gauss {G : E → MetricTensor E} {S : Set E}
 (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
 (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
 (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
 {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
 (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
 (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
 (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
 HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
 {x v : E} {T : ℝ} (hT : 0 ≤ T)
 (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, v)) ∈ U) (w : E) :
 G (Φ (T, (x, v))).1
 (fderiv ℝ Φ (T, (x, v)) (0, (0, v))).1
 (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T ^ 2 * G x v w
```

### Geometry/WeakMTW/Geodesics/GeneralFirstVariation [1] geodesic_general_pairing  (general; file: clean)
Reader: First variation: along a variation through geodesics, G(velocity, variation field) at time t equals its value at t=0 plus t times (dG(variation)(V,V)/2 + G(V, d_s V)) at (0,0).  Caveat: chart level; christoffel and MetricTensor are project definitions; c is C^2, V is C^1

```lean
theorem geodesic_general_pairing {G : E → MetricTensor E} {S : Set E}
 (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
 (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
 (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
 {c V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
 (hc : ContDiffOn ℝ 2 c U) (hV : ContDiffOn ℝ 1 V U)
 (hmem : ∀ q ∈ U, c q ∈ S)
 (hct : ∀ q ∈ U, HasDerivAt (fun t => c (t, q.2)) (V q) q.1)
 (hVt : ∀ q ∈ U, HasDerivAt (fun t => V (t, q.2))
 (-christoffel G (c q) (V q) (V q)) q.1)
 {T : ℝ} (hT : 0 ≤ T) {P : Set ℝ} (hP : P ∈ 𝓝 (0 : ℝ))
 (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P, (t, s) ∈ U)
 : ∀ t ∈ Icc (0 : ℝ) T,
 G (c (t, 0)) (V (t, 0)) (fderiv ℝ c (t, 0) (0, 1)) =
 G (c (0, 0)) (V (0, 0)) (fderiv ℝ c (0, 0) (0, 1)) +
 t * (fderiv ℝ G (c (0,0)) (fderiv ℝ c (0,0) (0,1)) (V (0,0)) (V (0,0)) / 2 +
 G (c (0,0)) (V (0,0)) (fderiv ℝ V (0,0) (0,1)))
```

### Geometry/WeakMTW/Variations/FirstVariation [3] geodesic_fan_pairing  (general; file: clean)
Reader: Gauss lemma for a fan of geodesics from one point x with initial velocities v + s w: G(velocity, variation field) at time t equals t * G_x(v,w).  Caveat: chart level; the variation c and its velocity V are hypotheses (C^2 and C^1)

```lean
theorem geodesic_fan_pairing {G : E → MetricTensor E} {S : Set E}
 (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
 (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
 (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
 {c V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
 (hc : ContDiffOn ℝ 2 c U) (hV : ContDiffOn ℝ 1 V U)
 (hmem : ∀ q ∈ U, c q ∈ S)
 (hct : ∀ q ∈ U, HasDerivAt (fun t => c (t, q.2)) (V q) q.1)
 (hVt : ∀ q ∈ U, HasDerivAt (fun t => V (t, q.2))
 (-christoffel G (c q) (V q) (V q)) q.1)
 {T : ℝ} (hT : 0 ≤ T) {P : Set ℝ} (hP : P ∈ 𝓝 (0 : ℝ))
 (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P, (t, s) ∈ U)
 {x v w : E} (hc0 : ∀ s ∈ P, c (0, s) = x)
 (hV0 : ∀ s ∈ P, V (0, s) = v + s • w) :
 ∀ t ∈ Icc (0 : ℝ) T,
 G (c (t, 0)) (V (t, 0)) (fderiv ℝ c (t, 0) (0, 1)) = t * G x v w
```

## N9

### AlgebraicGeometry/PlaneCurves/GaussianBounds [3] gaussian_exp_le  (general; file: clean)
Reader: For c > 0 and all real t: exp(-c t^2 + C t) <= exp(gaussianConstant c C) * exp(-t).  Caveat: gaussianConstant is a definition whose body is hidden; [2] is the same bound on exponents

```lean
-- /-- Global explicit exponential majorant, independent of the index. -/
theorem gaussian_exp_le (c C t : ℝ) (hc : 0 < c) :
 Real.exp (-c * t ^ 2 + C * t) ≤
 Real.exp (gaussianConstant c C) * Real.exp (-t)
```

### Analysis/BiholderTransport/Calculus/TaylorBound [1] second_order_remainder_bound_on_ball  (general; file: clean)
Reader: If f is C2 on a ball around 0 and its second derivative varies by at most eps there, then |f h - f 0 - f'(0) h - f''(0) h h / 2| <= eps |h|^2.  Caveat: E is a file variable (hypotheses not shown)

```lean
lemma second_order_remainder_bound_on_ball {f : E → ℝ} {r ε : ℝ}
 (hr : 0 < r) (hε : 0 ≤ ε)
 (hf : ∀ z ∈ Metric.ball (0:E) r, ContDiffAt ℝ 2 f z)
 (hB : ∀ z ∈ Metric.ball (0:E) r,
 ‖fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ f) 0‖ ≤ ε)
 {h : E} (hh : h ∈ Metric.ball (0:E) r) :
 |f h - f 0 - fderiv ℝ f 0 h - fderiv ℝ (fderiv ℝ f) 0 h h / 2| ≤ ε * ‖h‖^2
```

### Analysis/BiholderTransport/LinearAlgebra/Calculus [1] first_order_remainder_le_of_hessian_bound  (general; file: clean)
Reader: On a convex set where f is C2 with second derivative of norm <= B: |f y - f x - f'(x)(y-x)| <= B |y-x|^2.  Caveat: constant B, not B/2; E is a file variable

```lean
lemma first_order_remainder_le_of_hessian_bound {f : E → ℝ} {S : Set E}
 (hS : Convex ℝ S) {B : ℝ} (hB : 0≤B)
 (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
 (hbound : ∀ z∈S, ‖fderiv ℝ (fderiv ℝ f) z‖≤B)
 {x y : E} (hx : x∈S) (hy : y∈S) :
 |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2
```

### Analysis/Fourier/WavePackets/PeriodicKernel [14] enorm_complexConvolution_le_of_enorm_bound  (general; file: clean)
Reader: On a measurable additive group with right-invariant s-finite measure: |(k*f)(x)| ≤ ‖k‖_1 · B at every x when |f| ≤ B everywhere.  Caveat: complexConvolution is a project def (integrand k y * f (x − y) per Young [10]); k measurable

```lean
-- /-- The endpoint Young estimate in pointwise form, useful for the amplitude pieces in the restricted-sector argument. -/
theorem enorm_complexConvolution_le_of_enorm_bound {G : Type*} [AddCommGroup G]
 [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
 {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
 {k f : G → ℂ} (hk : Measurable k) {B : ℝ≥0∞}
 (hf : ∀ y, ‖f y‖ₑ ≤ B) (x : G) :
 ‖complexConvolution k f μ x‖ₑ ≤ eLpNorm k 1 μ * B
```

### Analysis/Fourier/WavePackets/Young [8] eLpNorm_complexConvolution_le  (general; file: clean)
Reader: Young's inequality ‖k*f‖_p ≤ ‖k‖_1 · ‖f‖_p for a.e.-strongly-measurable complex k and f, 1 ≤ p < ∞.  Caveat: group G and measure μ are file variables, their assumptions not shown; complexConvolution project def

```lean
-- /-- Young's inequality for a.e.-strongly-measurable inputs. -/
theorem eLpNorm_complexConvolution_le {k f : G → ℂ}
 (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
 (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
 eLpNorm (complexConvolution k f μ) p μ ≤ eLpNorm k 1 μ * eLpNorm f p μ
```

### Analysis/PDE/Concentration/GaussianJets [1] pow_mul_exp_neg_sq_bound  (general; file: clean)
Reader: For every real r and natural n: r^n * exp(-(r^2)) <= 1 + n!.

```lean
theorem pow_mul_exp_neg_sq_bound (r : ℝ) (n : ℕ) :
 r ^ n * Real.exp (-(r ^ 2)) ≤ 1 + (n.factorial : ℝ)
```

### Analysis/Steinitz/GaussianTail [17] matrix_square_tail  (general; file: clean)
Reader: Standard Gaussian on Euclidean space: if |Bx|^2 <= b|x|^2 for all x (b>0), then P(2*squareMass B + 4*b*r <= |Bx|^2) <= exp(-r) for every real r.  Caveat: matrixMap and squareMass are project defs (bodies hidden); [15] gram_trace states trace(B^T B) = squareMass B; index types presumably finite

```lean
lemma matrix_square_tail (B : Matrix κ ι ℝ) {b : ℝ} (hb : 0 < b)
 (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ b*‖x‖^2) (r : ℝ) :
 stdGaussian (EuclideanSpace ℝ ι) {x | 2*squareMass B+4*b*r ≤ ‖matrixMap B x‖^2} ≤
 ENNReal.ofReal (Real.exp (-r))
```

### Analysis/Steinitz/GaussianTail [1] integral_exp_square  (general; file: clean)
Reader: Integral of exp(-t x^2/2) against the standard real Gaussian equals 1/sqrt(1+t), stated for every real t.  Caveat: one-dimensional; no hypothesis on t shown, so for t <= -1 it rests on Lean junk values

```lean
lemma integral_exp_square (t : ℝ) :
 (∫ x : ℝ, Real.exp (-t * x ^ 2 / 2) ∂gaussianReal 0 1) =
 (Real.sqrt (1 + t))⁻¹
```

### Analysis/Triangular/Auxiliary/ExponentialTail [3] exp_tail_bound  (general; file: clean)
Reader: Taylor remainder of exp: for 0 ≤ d ≤ r(N+1), 0 ≤ r < 1: exp d − Σ_{i<N} d^i/i! ≤ (d^N/N!)/(1−r).

```lean
lemma exp_tail_bound {d r : ℝ} (N : ℕ) (hd : 0 ≤ d) (hr : 0 ≤ r) (hr1 : r<1)
 (hdr : d ≤ r*(N+1)) :
 Real.exp d-(∑ i ∈ Finset.range N, d^i/i.factorial) ≤ (d^N/N.factorial)/(1-r)
```

### Analysis/Triangular/Schwartz/Gaussian [3] gaussianSchwartz  (general; file: clean)
Reader: For c > 0 the Gaussian x ↦ exp(−c‖x‖²) packaged as a real Schwartz map on E (formula stated by [4] gaussianSchwartz_apply).  Caveat: a def with hidden body; E is a file variable, its instances are not shown

```lean
def gaussianSchwartz (c : ℝ) (hc : 0 < c) : 𝓢(E,ℝ) where
```

### Combinatorics/EditApproximation/Probability/BernsteinEnvelope [5] exp_le_bernstein_envelope  (general; file: clean)
Reader: For every real x < 3: exp x <= 1 + x + x^2 / (2*(1 - x/3)).

```lean
-- /-- Exact Bernstein exponential majorant, valid for all `x < 3`. -/
theorem exp_le_bernstein_envelope (x : ℝ) (hx : x < 3) :
 Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - x / 3))
```

### Combinatorics/IndependentSets/Repetition/Pinsker [2] sqrt_distance_le_relativeEntropy_term  (general; file: clean)
Reader: For x, y >= 0 with (x != 0 -> y != 0): (sqrt x - sqrt y)^2 <= x*log(x/y) - x + y.

```lean
theorem sqrt_distance_le_relativeEntropy_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
 (hs : x ≠ 0 → y ≠ 0) :
 (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log (x / y) - x + y
```

### Combinatorics/Progressions/Lattices/LatticeGaussianTemperature [3] gaussian_perturbation_at_temperature  (general; file: clean)
Reader: If t ≥ 0, 0 ≤ ε ≤ 1 and sqrt t * ‖x - y‖ ≤ ε, then exp(-4π) * exp(-π t (1+ε)² ‖y‖²) ≤ exp(-π t ‖x‖²).  Caveat: ambient space E file-level, not shown

```lean
theorem gaussian_perturbation_at_temperature (x y : E) {t ε : ℝ}
 (ht : 0 ≤ t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
 (hxy : Real.sqrt t * ‖x - y‖ ≤ ε) :
 Real.exp (-4 * Real.pi) * Real.exp (-Real.pi * (t * (1 + ε) ^ 2) * ‖y‖ ^ 2) ≤
 Real.exp (-Real.pi * t * ‖x‖ ^ 2)
```

### Combinatorics/Progressions/Lattices/LatticeHyperplaneBasis [31] gaussian_translate_bound  (general; file: clean)
Reader: For t ≥ 0, R ≥ 0 and ‖x‖ ≤ R: exp(-π t ‖x - m‖²) ≤ exp(π t R²) * exp(-π (t/2) ‖m‖²).  Caveat: ambient space E file-level, not shown

```lean
theorem gaussian_translate_bound (t R : ℝ) (ht : 0 ≤ t) (hR : 0 ≤ R)
 (x m : E) (hx : ‖x‖ ≤ R) :
 Real.exp (-Real.pi * t * ‖x - m‖ ^ 2) ≤
 Real.exp (Real.pi * t * R ^ 2) * Real.exp (-Real.pi * (t / 2) * ‖m‖ ^ 2)
```

### Combinatorics/Ryser/Probability/Exponential [2] exp_le_one_add_add_sq  (general; file: clean)
Reader: exp x <= 1 + x + x^2 for |x| <= 1.

```lean
lemma exp_le_one_add_add_sq {x : ℝ} (hx : |x| ≤ 1) :
 Real.exp x ≤ 1 + x + x ^ 2
```

### Combinatorics/SparsestCut/GaussianTools [13] gaussian_real_exp_sq  (general; file: clean)
Reader: For t < 1/2 the integral of exp(t x^2) against the standard normal law equals exp(-(1/2) log(1 - 2t)).  Caveat: unit variance only (gaussianReal 0 1)

```lean
lemma gaussian_real_exp_sq (t : ℝ) (ht : t < 1/2) :
 (∫ x : ℝ, Real.exp (t * x^2) ∂gaussianReal 0 1) =
 Real.exp (-(1/2 : ℝ) * Real.log (1 - 2*t))
```

### Combinatorics/SparsestCut/GaussianTools [15] gaussian_exp_norm_sq  (general; file: clean)
Reader: For t < 1/2 the integral of exp(t |g|^2) against the standard Gaussian on R^n equals exp(-(n/2) log(1 - 2t)).  Caveat: stdGaussian on EuclideanSpace; whether it is Mathlib's or a project def is not visible

```lean
lemma gaussian_exp_norm_sq {n : ℕ} (t : ℝ) (ht : t < 1/2) :
 (∫ g : EuclideanSpace ℝ (Fin n), Real.exp (t * ‖g‖^2)
 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
 Real.exp (-(n : ℝ)/2 * Real.log (1-2*t))
```

### Combinatorics/SparsestCut/LatticeDensity [3] lattice_bound  (general; file: clean)
Reader: tau * sum over a finite set of integers k of h(k tau) <= integral of h + tau * integral of |h'|, for nonnegative differentiable integrable h.  Caveat: dimension one; upper bound only; also serves N1 for sums of exp(-c n^2)

```lean
lemma lattice_bound {h h' : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
 (hd : ∀ t, HasDerivAt h (h' t) t) (hh : ∀ t, 0 ≤ h t)
 (hi : Integrable h) (hi' : Integrable h') (s : Finset ℤ) :
 τ*(∑ k ∈ s, h ((k:ℝ)*τ)) ≤ (∫ t, h t)+τ*(∫ t, |h' t|)
```

### Geometry/ConjugatePoints/Geodesics [4] quadratic_taylor  (general; file: clean)
Reader: On a convex set where f is differentiable with C-Lipschitz derivative: norm of f y - f x - f'(x)(y-x) is at most C*|y-x|^2.  Caveat: E is a hidden section variable (instances not shown); constant is C, not C/2

```lean
lemma quadratic_taylor {f : E → E} {S : Set E} {C : ℝ≥0}
 (hS : Convex ℝ S) (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
 (hD : LipschitzOnWith C (fderiv ℝ f) S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
 ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ C*‖y-x‖^2
```

### Geometry/CylinderCovering/Convexity/QuadraticTaylorBound [1] remainder_le_on_closedBall  (general; file: clean)
Reader: If f and fderiv f are differentiable on closedBall x r and the second derivative has norm at most M there, then ‖f y − f x − f'(x)(y−x)‖ ≤ M·r² for y in the ball.  Caveat: E and F are file-level variables (types and instances not shown); bound is M·r², not (M/2)·‖y−x‖²

```lean
theorem remainder_le_on_closedBall {f : E → F} {x y : E} {r M : ℝ}
 (hr : 0 ≤ r) (hM : 0 ≤ M) (hy : y ∈ closedBall x r)
 (hf : ∀ z ∈ closedBall x r, DifferentiableAt ℝ f z)
 (hdf : ∀ z ∈ closedBall x r, DifferentiableAt ℝ (fderiv ℝ f) z)
 (hbound : ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M) :
 ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * r ^ 2
```

### Geometry/CylinderCovering/Convexity/QuadraticTaylorBound [2] exists_uniform_taylor_bound_of_bounded_hessian  (general; file: clean)
Reader: Compact D inside open U, second derivative bounded by B on U: some r>0 gives first-order Taylor remainder ≤ B·‖y−x‖² for all x in D and ‖y−x‖ ≤ r.  Caveat: r is only existential; E and F are file-level variables not shown

```lean
theorem exists_uniform_taylor_bound_of_bounded_hessian {f : E → F} {D U : Set E}
 {B : ℝ} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U) (hB : 0 ≤ B)
 (hf : ∀ z ∈ U, DifferentiableAt ℝ f z)
 (hdf : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ f) z)
 (hbound : ∀ z ∈ U, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B) :
 ∃ r : ℝ, 0 < r ∧ ∀ x ∈ D, ∀ y : E, ‖y - x‖ ≤ r →
 ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ B * ‖y - x‖ ^ 2
```

### Geometry/CylinderCovering/Convexity/UniformTaylor [1] remainder_sq_of_lipschitz_fderiv  (general; file: clean)
Reader: If f is differentiable on S, Df is C-Lipschitz on S and the segment from x to y lies in S, then norm(f y - f x - Df(x)(y-x)) <= C * norm(y-x)^2.  Caveat: spaces E, F declared out of view

```lean
theorem remainder_sq_of_lipschitz_fderiv {f : E → F} {S : Set E} {C : NNReal}
 (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
 (hLip : LipschitzOnWith C (fderiv ℝ f) S)
 {x y : E} (hseg : segment ℝ x y ⊆ S) :
 ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ (C : ℝ) * ‖y-x‖ ^ 2
```

### Geometry/CylinderCovering/Convexity/UniformTaylor [2] remainder_sq_of_hessian_bound  (general; file: clean)
Reader: On a convex S where f and Df are differentiable with norm(D^2 f) <= C, norm(f y - f x - Df(x)(y-x)) <= C * norm(y-x)^2 for x, y in S.  Caveat: constant is C, not C/2; spaces E, F declared out of view

```lean
theorem remainder_sq_of_hessian_bound {f : E → F} {S : Set E} {C : ℝ}
 (hC : 0 ≤ C) (hS : Convex ℝ S)
 (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
 (hdf : ∀ z ∈ S, DifferentiableAt ℝ (fderiv ℝ f) z)
 (hbound : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C)
 {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
 ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ C * ‖y-x‖ ^ 2
```

### Geometry/EinsteinFour/FourHeatGaussianMoments [2] fourHeatPolynomial_absorption  (general; file: clean)
Reader: For every natural m and real z ≥ 0: z^m · exp(−z) ≤ m!.

```lean
theorem fourHeatPolynomial_absorption (m : ℕ) (z : ℝ) (hz : 0 ≤ z) :
 z ^ m * Real.exp (-z) ≤ (m.factorial : ℝ)
```

### Geometry/HyperbolicGroups/Chernoff [3] bernoulli_centered_exp_le  (general; file: clean)
Reader: For p in [0,1] and |t| <= 1: (1-p)*exp(t*(0-p)) + p*exp(t*(1-p)) <= exp(p*t^2), the centred Bernoulli moment generating function bound.

```lean
lemma bernoulli_centered_exp_le {p t : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : |t| ≤ 1) :
 (1-p)*Real.exp (t*(0-p)) + p*Real.exp (t*(1-p)) ≤ Real.exp (p*t^2)
```

### Geometry/LatticeCovering/GaussianMoments [6] integral_norm_le_sqrt_second  (general; file: clean)
Reader: On a probability space, the integral of |f| is at most the square root of the integral of f^2, for f in L2.

```lean
lemma integral_norm_le_sqrt_second {α : Type*} [MeasurableSpace α]
 {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
 (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ)
```

### Geometry/LatticeCovering/GaussianMoments [10] exp_negative_lipschitz  (general; file: clean)
Reader: |exp u - exp v| <= |u - v| for u, v <= 0.

```lean
lemma exp_negative_lipschitz {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
 |Real.exp u-Real.exp v| ≤ |u-v|
```

### Geometry/NodalSets/Coefficients/GaussianCoefficientTail [1] standard_gaussian_abs_tail  (general; file: clean)
Reader: For the standard real Gaussian and r >= 0, the measure of {|x| >= r} is at most 2 exp(-r^2/2).

```lean
lemma standard_gaussian_abs_tail {r : ℝ} (hr : 0 ≤ r) :
 gaussianReal 0 1 {x | r ≤ |x|} ≤ ENNReal.ofReal (2*Real.exp (-r^2/2))
```

### Geometry/NodalSets/Waves/GaussianIntervalBound [1] gaussian_pdf_upper_bound  (general; file: clean)
Reader: The real Gaussian density with mean m and variance v is at most 1/sqrt(2 pi v) at every point.

```lean
lemma gaussian_pdf_upper_bound (mean x : ℝ) (v : ℝ≥0) :
 gaussianPDFReal mean v x ≤ (Real.sqrt (2*Real.pi*v))⁻¹
```

### Geometry/RCD/Heat/GaussianLinearGrowth [1] linear_sub_quadratic_le  (general; file: clean)
Reader: For real A, s and c > 0: A*s - c*s^2 <= A^2/(2c) - (c/2)*s^2 (completing the square, half the Gaussian exponent kept).  Caveat: elementary

```lean
-- /-- Completing the square leaves half of the Gaussian exponent available. -/
theorem linear_sub_quadratic_le (A s : ℝ) {c : ℝ} (hc : 0 < c) :
 A * s - c * s ^ 2 ≤ A ^ 2 / (2 * c) - (c / 2) * s ^ 2
```

### Geometry/RCD/Heat/GaussianUpperAlgebra [2] linear_quadratic_absorb  (general; file: clean)
Reader: For real b, z and eta > 0: b*z <= eta*z^2 + b^2/(4*eta) (Young / Peter-Paul with explicit constant).  Caveat: elementary, one-line proof; value is only saving the lemma

```lean
theorem linear_quadratic_absorb (b z : ℝ) {η : ℝ} (hη : 0 < η) :
 b*z ≤ η*z^2+b^2/(4*η)
```

### Geometry/WeakHessian/Calculus/LipschitzDerivQuadraticRemainder [1] lipschitzOn_deriv_quadratic_remainder  (general; file: clean)
Reader: If phi has derivative psi on a convex set s and psi is L-Lipschitz on s, then |phi b - phi a - psi a*(b-a)| <= L*|b-a|^2 for a,b in s.  Caveat: one real variable, real values; constant L rather than L/2

```lean
lemma lipschitzOn_deriv_quadratic_remainder {φ ψ : ℝ → ℝ} {L : ℝ≥0} {s : Set ℝ}
 (hs : Convex ℝ s) (hφ : ∀ x ∈ s, HasDerivAt φ (ψ x) x)
 (hψ : LipschitzOnWith L ψ s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
 |φ b - φ a - ψ a*(b-a)| ≤ (L:ℝ)*|b-a|^2
```

### Geometry/WeakHessian/LocalBounds/ExpNegQuadraticBound [1] exp_neg_quadratic_bound  (general; file: clean)
Reader: For r >= 0: exp(-r) <= 1 - r + r^2/2.

```lean
lemma exp_neg_quadratic_bound {r : ℝ} (hr : 0 ≤ r) :
 Real.exp (-r) ≤ 1-r+r^2/2
```

### GroupTheory/SimpleAmenable/Arithmetic/LatticeRiemann [1] fundamentalDomain_riemann_error  (general; file: clean)
Reader: Riemann sum over a lattice L in a normed space: bounds |vol(F) * sum of f over lattice points - integral of f| for integrable Lipschitz f, F a fundamental domain inside a ball of radius delta.  Caveat: statement cut: the right-hand side of the bound is not visible; needs a finite set T of lattice points outside which f vanishes on z + F

```lean
theorem fundamentalDomain_riemann_error
 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [MeasureSpace E] [BorelSpace E] [Measure.IsAddLeftInvariant (volume : Measure E)]
 (L : AddSubgroup E) [Countable L]
 {F : Set E} (hF : IsAddFundamentalDomain L F volume)
 (hFfin : volume F<⊤) {δ : ℝ} (hδ : ∀x∈F,‖x‖≤δ)
 {f : E → ℝ} (hf : Integrable f) {A : NNReal} (hlip : LipschitzWith A f)
 (T : Finset L) (hT : ∀z : L,z∉T → ∀x∈F,f ((z:E)+x)=0) :
 |volume.real F*(∑z∈T,f (z:E))-∫x,f x| ≤
```

### MathematicalPhysics/Boltzmann/Collision/GaussianEstimates [45] integral_gaussian_tail  (general; file: clean)
Reader: For b > 0 and any real r: the integral over a > r of a * exp(-b a^2) equals (2b)^(-1) * exp(-b r^2).  Caveat: declared private, has to be copied; [46] is the public variant

```lean
private theorem integral_gaussian_tail {b : ℝ} (hb : 0 < b) (r : ℝ) :
 (∫ a in Ioi r, a * Real.exp (-b * a ^ 2)) =
 (2 * b)⁻¹ * Real.exp (-b * r ^ 2)
```

### MathematicalPhysics/Boltzmann/Collision/GaussianEstimates [46] integral_radius_tail  (general; file: clean)
Reader: For d > 0 and any real r: the integral over a > r of a * exp(-a^2/d^2) equals d^2/2 * exp(-r^2/d^2).

```lean
theorem integral_radius_tail {d : ℝ} (hd : 0 < d) (r : ℝ) :
 (∫ a in Ioi r, a * Real.exp (-a ^ 2 / d ^ 2)) =
 d ^ 2 / 2 * Real.exp (-r ^ 2 / d ^ 2)
```

### MathematicalPhysics/Boltzmann/Collision/GaussianEstimates [83] integral_exp_quarter_gaussian  (general; file: clean)
Reader: For v != 0: the integral of exp(a^2/(4v)) against the centred real Gaussian of variance v equals sqrt 2.  Caveat: one fixed exponent only; [82] gives integrability

```lean
theorem integral_exp_quarter_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
 (∫ a : ℝ, Real.exp (a ^ 2 / (4 * (v : ℝ))) ∂gaussianReal 0 v) = Real.sqrt 2
```

### MathematicalPhysics/ContinuumCoulomb/ManyBody/FiniteDifferenceError [1] linear_remainder  (general; file: clean)
Reader: If f has derivative f' on [a, a+h] and |f' s - b| <= B on [a, a+h), then |f(a+h) - f a - h*b| <= B*h.

```lean
theorem linear_remainder (f f' : ℝ → ℝ) {a h b B : ℝ} (hh : 0 ≤ h)
 (hf : ∀ s ∈ Set.Icc a (a+h), HasDerivAt f (f' s) s)
 (hb : ∀ s ∈ Set.Ico a (a+h), |f' s-b| ≤ B) :
 |f (a+h)-f a-h*b| ≤ B*h
```

### MathematicalPhysics/ContinuumCoulomb/ManyBody/FiniteDifferenceError [3] centered_remainder  (general; file: clean)
Reader: If f'' satisfies |f'' s - f'' x| <= L|s-x| on [x-h, x+h], then |f(x+h) + f(x-h) - 2 f x - h^2 f'' x| <= L h^3.  Caveat: f and f' are assumed differentiable on all of R

```lean
theorem centered_remainder (f f' f'' : ℝ → ℝ) {x h L : ℝ}
 (hh : 0 ≤ h) (hL : 0 ≤ L)
 (hf : ∀ s, HasDerivAt f (f' s) s)
 (hf' : ∀ s, HasDerivAt f' (f'' s) s)
 (hLip : ∀ s ∈ Set.Icc (x-h) (x+h), |f'' s-f'' x| ≤ L*|s-x|) :
 |f (x+h)+f (x-h)-2*f x-h^2*f'' x| ≤ L*h^3
```

### MathematicalPhysics/ContinuumCoulomb/OneParticle/GaussianJetBounds [1] power_exponential_bound  (general; file: clean)
Reader: For natural k, a > 0 and t >= 0: t^k * exp(-a t) <= k!/a^k.

```lean
theorem power_exponential_bound (k : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
 t^k*Real.exp (-a*t) ≤ (k.factorial:ℝ)/a^k
```

### MathematicalPhysics/ContinuumCoulomb/OneParticle/HeatKernelModulus [4] exp_nonpositive_lipschitz  (general; file: clean)
Reader: For x <= 0 and y <= 0: |exp x - exp y| <= |x - y|.

```lean
theorem exp_nonpositive_lipschitz {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
 |Real.exp x - Real.exp y| ≤ |x - y|
```

### MathematicalPhysics/CriticalSK/CubeOverlap [9] log_cubic_error  (general; file: clean)
Reader: For |q| <= 1/2: |log(1-q) + q + q^2/2 + q^3/3| <= 2 q^4.

```lean
lemma log_cubic_error {q : ℝ} (hq : |q| ≤ 1/2) :
 |Real.log (1-q) + q + q^2/2 + q^3/3| ≤ 2*q^4
```

### MathematicalPhysics/CriticalSK/CubeOverlap [11] log_square_error  (general; file: clean)
Reader: For |q| <= 1/2: |log(1-q^2) + q^2| <= 2 q^4.

```lean
lemma log_square_error {q : ℝ} (hq : |q| ≤ 1/2) :
 |Real.log (1-q^2)+q^2| ≤ 2*q^4
```

### MathematicalPhysics/CriticalSK/GaussianConcentration [32] exp_quadratic_remainder  (general; file: clean)
Reader: exp x ≤ 1 + x + x^2·exp|x| for every real x.  Caveat: elementary

```lean
lemma exp_quadratic_remainder (x : ℝ) :
 Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x|
```

### MathematicalPhysics/CriticalSK/GaussianMoments [2] gaussian_square_integral  (general; file: clean)
Reader: For t < 1/2, the integral of exp(t·x^2) against the standard real Gaussian measure equals 1/sqrt(1 - 2t).  Caveat: integrability is [3] of the same file

```lean
lemma gaussian_square_integral (t : ℝ) (ht : t < 1 / 2) :
 (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
 (Real.sqrt (1 - 2 * t))⁻¹
```

### MathematicalPhysics/CriticalSK/SphereSaddle [60] gaussian_fourth_bound_var  (general; file: clean)
Reader: Fourth moment of the centred real Gaussian with variance v is at most 64 v^2.  Caveat: constant not sharp (true value 3 v^2); integrability is the separate lemma [59]

```lean
lemma gaussian_fourth_bound_var (v : ℝ≥0) :
 (∫ x : ℝ, x^4 ∂gaussianReal 0 v) ≤ 64 * (v:ℝ)^2
```

### MathematicalPhysics/CriticalSK/SphereSaddle [62] gaussian_square_mean  (general; file: clean)
Reader: Integral of x^2 against the centred real Gaussian with variance v equals v.

```lean
lemma gaussian_square_mean (v : ℝ≥0) :
 (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = v
```

### MathematicalPhysics/CriticalSK/SphereSaddle [88] gaussian_density_upper  (general; file: clean)
Reader: Density of the centred real Gaussian with variance v is at most 1/sqrt(2 pi v) at every point.

```lean
lemma gaussian_density_upper (v : ℝ≥0) (x : ℝ) :
 gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹
```

### MathematicalPhysics/CriticalSK/SphereSaddle [116] gaussian_square_pdf_le_double  (general; file: clean)
Reader: For v nonzero: x^2 times the N(0,v) density at x is at most 8 v times the N(0,2v) density at x.  Caveat: one-dimensional; uses Mathlib's gaussianPDFReal

```lean
lemma gaussian_square_pdf_le_double {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
 x^2 * gaussianPDFReal 0 v x ≤ 8 * (v:ℝ) * gaussianPDFReal 0 (2*v) x
```

### MathematicalPhysics/DefocusingNLS/Nonlinear/GaussianMoments [1] real_gaussian_second_moment  (general; file: clean)
Reader: Lower integral of x^2 against the centred real Gaussian with variance v equals v.  Caveat: extended-nonnegative (lintegral) form of CriticalSK/SphereSaddle [62]

```lean
-- /-- The nonnegative second moment of a centered real Gaussian. -/
theorem real_gaussian_second_moment (v : ℝ≥0) :
 (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂gaussianReal 0 v) = v
```

### MathematicalPhysics/DefocusingNLS/Nonlinear/NormedCurveTaylor [1] normedCurve_firstOrder_bound  (general; file: clean)
Reader: Curve u with derivative v and second derivative w bounded by B on [−r, r]: ‖u t − u 0 − t • v 0‖ ≤ B·|t|^2.  Caveat: constant is B, not B/2; class of E from a variable line not shown

```lean
theorem normedCurve_firstOrder_bound (u v w : ℝ → E) (r B : ℝ)
 (hB : 0 ≤ B)
 (hu : ∀ t ∈ Icc (-r) r, HasDerivAt u (v t) t)
 (hv : ∀ t ∈ Icc (-r) r, HasDerivAt v (w t) t)
 (hw : ∀ t ∈ Icc (-r) r, ‖w t‖ ≤ B)
 (t : ℝ) (ht : |t| ≤ r) :
 ‖u t - u 0 - t • v 0‖ ≤ B * |t| ^ 2
```

### MathematicalPhysics/NavierStokes/ForcedComputation/Scalar/HeatGaussianBounds [3] gaussian_time_factor  (general; file: clean)
Reader: For d > 0 and t > 0: (1/t) exp(-d^2/(8t)) <= 8/d^2.

```lean
theorem gaussian_time_factor {d t : ℝ} (hd : 0 < d) (ht : 0 < t) :
 t⁻¹ * Real.exp (-(d ^ 2 / (8 * t))) ≤ 8 / d ^ 2
```

### MathematicalPhysics/NavierStokes/ForcedComputation/Scalar/PlaneHeatKernel [9] absoluteFirstMoment  (general; file: clean)
Reader: For b > 0 the integral over the real line of |x| exp(-b x^2) equals 1/b.

```lean
theorem absoluteFirstMoment {b : ℝ} (hb : 0 < b) :
 (∫ x : ℝ, |x| * Real.exp (-b * x ^ 2)) = b⁻¹
```

### MathematicalPhysics/PEPSMove/LogMoments [3] exp_linear_remainder  (general; file: clean)
Reader: For every real x: exp x <= 1 + x + 3 x^2 exp|x|.

```lean
theorem exp_linear_remainder (x : ℝ) :
 Real.exp x≤1+x+3*x^2*Real.exp |x|
```

### NumberTheory/CubicMoment/Estimates/RieszHeatKernel [4] inverse_gaussian_moment  (general; file: clean)
Reader: For a, b > 0: integral over t > 0 of t^(-a-1) exp(-b/t) equals Gamma(a) * b^(-a) (time integral of a heat-kernel-type factor).

```lean
-- /-- The inverted Gaussian moment is the dual radial power. -/
lemma inverse_gaussian_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
 (∫ t in Ioi (0:ℝ), t^(-a-1)*Real.exp (-b/t)) = Real.Gamma a*b^(-a)
```

### NumberTheory/CubicMoment/Estimates/ThetaHeatKernelBound [1] power_exp_bound  (general; file: clean)
Reader: For b > 0, natural n and x >= 0: x^n exp(-b x) <= n!/b^n.

```lean
lemma power_exp_bound {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
 x^n*Real.exp (-b*x) ≤ (n.factorial:ℝ)/b^n
```

### NumberTheory/DirichletL/Poisson/GaussianMoments [2] gaussian_moment_term_bound  (general; file: clean)
Reader: For q >= 0 and t > 0: q*exp(-t*q) <= (2/t)*exp(-t*q/2); trades one power of the quadratic form for half the Gaussian rate.

```lean
theorem gaussian_moment_term_bound (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
 q * Real.exp (-t * q) ≤
 (2 / t) * Real.exp (-(t * q / 2))
```

### Probability/Ballisticity/Estimates/GaussianAbsTail [1] gaussian_abs_tail  (general; file: clean)
Reader: For Mathlib's centred real Gaussian gaussianReal 0 v with v > 0 and a >= 0: P(|z| >= a) <= 2*exp(-a^2/(2*v)).

```lean
lemma gaussian_abs_tail (v : ℝ≥0) (hv : 0 < (v : ℝ)) (a : ℝ) (ha : 0 ≤ a) :
 (gaussianReal 0 v).real {z | a ≤ |z|} ≤ 2*Real.exp (-a^2/(2*v))
```

### Probability/FreeIsing/Estimates/ExponentialTaylor [1] norm_exp_I_taylor_two_le  (general; file: clean)
Reader: For all real x: norm of exp(ix) - 1 - ix + x^2/2 is at most 4*|x|^3.  Caveat: constant 4 is not sharp

```lean
theorem norm_exp_I_taylor_two_le (x : ℝ) :
 ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I +
 (x : ℂ) ^ 2 / 2‖ ≤ 4 * |x| ^ 3
```

### Probability/FreeIsing/Estimates/ExponentialTaylor [3] norm_exp_neg_sub_one_add_le_sq  (general; file: clean)
Reader: For x >= 0: norm of exp(-x) - 1 + x is at most x^2 (stated with complex casts).

```lean
theorem norm_exp_neg_sub_one_add_le_sq {x : ℝ} (hx : 0 ≤ x) :
 ‖Complex.exp ((-x : ℝ) : ℂ) - 1 + (x : ℂ)‖ ≤ x ^ 2
```

### Probability/FreeIsing/Gaussian/Moments [3] integral_one_add_abs_pow_gaussian_le  (general; file: clean)
Reader: For natural p >= 1: the integral of (1+|x|)^p against the standard Gaussian on R is at most exp(2 p^2).  Caveat: one-dimensional standard Gaussian; crude constant; integrability is [2]

```lean
theorem integral_one_add_abs_pow_gaussian_le {p : ℕ} (hp : 1 ≤ p) :
 (∫ x : ℝ, (1 + |x|) ^ p ∂gaussianReal 0 1) ≤ Real.exp (2 * (p : ℝ) ^ 2)
```

### Probability/FreeIsing/Martingales/TaylorRemainder [1] cubic_le_quadratic_add_quartic  (general; file: clean)
Reader: For real x and eps > 0: |x|^3 <= eps*x^2 + x^4/(4 eps) (Young-type splitting).

```lean
theorem cubic_le_quadratic_add_quartic (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
 |x| ^ 3 ≤ ε * x ^ 2 + (1 / (4 * ε)) * x ^ 4
```

### Probability/InvariantIsing/Cavity/CavityGaussianIntegral [3] cavity_integral_exp_quadratic  (general; file: clean)
Reader: For b > 0: integral over R of exp(-b x^2 + c x + d) equals sqrt(pi/b) exp(c^2/(4b) + d).  Caveat: dimension 1; integrability is [2]

```lean
lemma cavity_integral_exp_quadratic (b c d : ℝ) (hb : 0 < b) :
 (∫ x : ℝ, Real.exp (-b * x ^ 2 + c * x + d)) =
 Real.sqrt (Real.pi / b) * Real.exp (c ^ 2 / (4 * b) + d)
```

### Probability/InvariantIsing/Cavity/CavityGaussianRadialMoments [6] cavity_gaussian_norm_sq_integral  (general; file: clean)
Reader: Integral of norm(z)^2 against the standard Gaussian on EuclideanSpace R (Fin n) equals n.  Caveat: same fact for Point d in LogConcave/Analysis/PoincareVectorVariance [3]

```lean
lemma cavity_gaussian_norm_sq_integral (n : ℕ) :
 (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 ∂stdGaussian _) = n
```

### Probability/ProjectionMoments/Polar [23] euclidean_gaussian_integral  (general; file: clean)
Reader: The integral over R^k of exp(-norm(x)^2) with the Euclidean norm equals sqrt(pi)^k.  Caveat: stated as a lower Lebesgue integral of ENNReal.ofReal; fixed scale 1 only

```lean
lemma euclidean_gaussian_integral (k : ℕ) :
 (∫⁻ x : Fin k → ℝ, ENNReal.ofReal (Real.exp (-‖WithLp.toLp 2 x‖^2)) ∂volume) =
 ENNReal.ofReal (Real.sqrt Real.pi ^ k)
```

### Probability/SKRatio/Dynamics/Concentration [13] real_exp_remainder_le  (general; file: clean)
Reader: For every real z: exp z - 1 - z <= z^2 exp|z| / 2.

```lean
lemma real_exp_remainder_le (z : ℝ) :
 Real.exp z - 1 - z ≤ z ^ 2 * Real.exp |z| / 2
```

### Probability/SKRatio/Matrices/GaussianTails [9] gaussian_real_abs_tail  (general; file: clean)
Reader: For the centred real Gaussian of variance r > 0 and d >= 0: P(|x| > d) <= 2 exp(-d^2/(4r)).  Caveat: constant 4r in the exponent, not the sharp 2r

```lean
lemma gaussian_real_abs_tail {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
 (gaussianReal 0 (Real.toNNReal r)).real {x : ℝ | d < |x|} ≤ 2*exp (-d^2/(4*r))
```

### Probability/SKRatio/Matrices/GaussianTails [5] product_gaussian_square_tail  (general; file: clean)
Reader: For n independent standard Gaussians: P(sum of squares > t) <= exp(-t/4 + n log 2), any real t.

```lean
lemma product_gaussian_square_tail {ι : Type*} [Fintype ι] (t : ℝ) :
 (Measure.pi (fun _ : ι=>gaussianReal 0 1)).real {g | t < ∑ i,g i^2} ≤
 exp (-t/4+(Fintype.card ι:ℝ)*log 2)
```

### Probability/SKSupport/Density/GaussianDecay [1] linear_abs_le_quadratic  (general; file: clean)
Reader: For d > 0 and real K, x: K |x| <= (d/2) x^2 + K^2/(2d).  Caveat: elementary

```lean
lemma linear_abs_le_quadratic {d : ℝ} (hd : 0 < d) (K x : ℝ) :
 K*|x| ≤ d/2*x^2+K^2/(2*d)
```

### Probability/SKSupport/Foundations/IntegralIoiMulExpSq [1] integral_Ioi_mul_exp_sq  (general; file: clean)
Reader: Integral over x > 0 of x exp(-a x^2) equals 1/(2a), for a > 0.

```lean
lemma integral_Ioi_mul_exp_sq {a : ℝ} (ha : 0 < a) :
 (∫ x : ℝ in Set.Ioi 0, x * Real.exp (-a*x^2)) = (2*a)⁻¹
```

### Probability/SKSupport/Foundations/IntegralIoiMulExpSq [2] integral_abs_mul_exp_sq  (general; file: clean)
Reader: Integral over the real line of |x| exp(-a x^2) equals 1/a, for a > 0.

```lean
lemma integral_abs_mul_exp_sq {a : ℝ} (ha : 0 < a) :
 (∫ x : ℝ, |x| * Real.exp (-a*x^2)) = a⁻¹
```

### Probability/SKSupport/Foundations/IntegralIoiMulExpSq [3] gaussian_abs_moment  (general; file: clean)
Reader: First absolute moment of the centred real Gaussian of variance v equals sqrt(2v/pi).

```lean
theorem gaussian_abs_moment (v : ℝ≥0) :
 (∫ x : ℝ, |x| ∂gaussianReal 0 v) = Real.sqrt (2*(v:ℝ)/Real.pi)
```

### Probability/SKSupport/Foundations/Taylor1Bound [1] taylor1_bound  (general; file: clean)
Reader: For C^2 f on R with |f''| <= C everywhere: |f(x+d) - f x - f'(x) d| <= (C/2) |d|^2.  Caveat: one variable, global bound on f''

```lean
lemma taylor1_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {C : ℝ}
 (hC : ∀ x, |deriv (deriv f) x| ≤ C) (x d : ℝ) :
 |f (x+d)-f x-deriv f x*d| ≤ C/2*|d|^2
```

### Probability/SKSupport/Moments/NormalThirdMoment [2] gaussian_abs_pow_integrable  (general; file: clean)
Reader: For natural p and variance v, x -> |x|^p is integrable under gaussianReal 0 v.  Caveat: dimension 1

```lean
lemma gaussian_abs_pow_integrable (p : ℕ) (v : ℝ≥0) :
 Integrable (fun x : ℝ => |x|^p) (gaussianReal 0 v)
```

### Probability/SKSupport/Moments/NormalThirdMoment [4] gaussian_abs_pow  (general; file: clean)
Reader: Integral of |x|^p under gaussianReal 0 v equals (sqrt v)^p times the integral of |x|^p under gaussianReal 0 1.  Caveat: dimension 1; same statement as Probability/SphericalField/Gaussian/Taylor [1]

```lean
lemma gaussian_abs_pow (p : ℕ) (v : ℝ≥0) :
 (∫ x : ℝ, |x|^p ∂gaussianReal 0 v) =
 (Real.sqrt (v : ℝ))^p * ∫ x : ℝ, |x|^p ∂gaussianReal 0 1
```

### Probability/SKValue/Equations/ThirdOrderRemainderBound [1] third_order_remainder_bound  (general; file: clean)
Reader: For C^3 f on R with |f'''| <= K everywhere: |f(x+d) - f x - f'(x) d - (1/2) f''(x) d^2| <= K |d|^3.  Caveat: one variable; constant K, not K/6

```lean
lemma third_order_remainder_bound {f : ℝ → ℝ} {K : ℝ}
 (hf : ContDiff ℝ 3 f) (hK : 0≤K)
 (hbound : ∀ x, |iteratedDeriv 3 f x|≤K) (x d : ℝ) :
 |f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2| ≤ K*|d|^3
```

### Probability/SKValue/Gaussian/IntegralPositiveMulGaussian [1] integral_positive_mul_gaussian  (general; file: clean)
Reader: For b > 0: integral over x > 0 of x exp(-b x^2) equals 1/(2b).

```lean
lemma integral_positive_mul_gaussian {b : ℝ} (hb : 0<b) :
 (∫ x : ℝ in Ioi 0, x*Real.exp (-b*x^2)) = (2*b)⁻¹
```

### Probability/SKValue/Gaussian/IntegralPositiveMulGaussian [2] integral_abs_centered_gaussian  (general; file: clean)
Reader: Integral of |x| under gaussianReal 0 v equals sqrt(2 v / pi).  Caveat: dimension 1

```lean
lemma integral_abs_centered_gaussian (v : ℝ≥0) :
 (∫ x : ℝ, |x| ∂gaussianReal 0 v) = Real.sqrt (2*(v : ℝ)/Real.pi)
```

### Probability/SLE/BrownianGenerators [7] gaussian_square_integral  (general; file: clean)
Reader: Integral of x^2 under gaussianReal 0 delta equals delta.  Caveat: dimension 1

```lean
lemma gaussian_square_integral (δ : ℝ≥0) :
 (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 δ) = δ
```

### Probability/SpanningForest/GaussianMomentScaling [2] gaussian_absolute_moment_scaling  (general; file: clean)
Reader: The k-th absolute moment of the centred Gaussian of variance v equals sqrt(v)^k times the k-th absolute moment of the standard Gaussian.

```lean
theorem gaussian_absolute_moment_scaling (v : ℝ≥0) (k : ℕ) :
 (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 v) =
 (Real.sqrt (v : ℝ)) ^ k * (∫ z : ℝ, |z| ^ k ∂gaussianReal 0 1)
```

### Probability/SphericalField/Gaussian/Quadratic [9] real_quadratic_integral  (general; file: clean)
Reader: For b>0 and real c,d: the integral over R of exp(-b y^2 + c y + d) equals exp(d + c^2/(4b)) * sqrt(pi/b).  Caveat: one-dimensional, real linear coefficient only (no complex frequency)

```lean
lemma real_quadratic_integral {b : ℝ} (hb : 0 < b) (c d : ℝ) :
 (∫ y : ℝ, Real.exp (-b*y^2+c*y+d)) =
 Real.exp (d+c^2/(4*b))*Real.sqrt (Real.pi/b)
```

### Probability/SphericalField/Heat/Translations [9] log_lipschitz_above  (general; file: clean)
Reader: For 0 < c <= a and c <= b: |log b - log a| <= |b - a| / c.

```lean
lemma log_lipschitz_above {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
 |Real.log b-Real.log a| ≤ c⁻¹*|b-a|
```

### Probability/SphericalField/Poisson/Mecke [4] one_sub_exp_neg_le_min  (general; file: clean)
Reader: For u >= 0: 0 <= 1 - exp(-u) and 1 - exp(-u) <= min u 1.

```lean
lemma one_sub_exp_neg_le_min {u : ℝ} (hu : 0 ≤ u) :
 0 ≤ 1-Real.exp (-u) ∧ 1-Real.exp (-u) ≤ min u 1
```

### Probability/SphericalField/Sphere/Heat [6] integral_exp_inner_stdGaussian  (general; file: clean)
Reader: On a finite-dimensional real inner product space: integral of exp(a <v, x>) under stdGaussian E equals exp(a^2 |v|^2 / 2).  Caveat: real exponent (Laplace transform), not the characteristic function; stdGaussian body not shown

```lean
lemma integral_exp_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
 [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 (v : E) (a : ℝ) : (∫ x, Real.exp (a*inner ℝ v x) ∂stdGaussian E)=
 Real.exp (a^2*‖v‖^2/2)
```

### Probability/StrongRayleigh/CharacteristicTaylor [2] norm_exp_I_mul_sub_one_sub_linear  (general; file: clean)
Reader: For real x: |exp(i x) - 1 - i x| <= |x|^2 / 2.

```lean
theorem norm_exp_I_mul_sub_one_sub_linear (x : ℝ) :
 ‖Complex.exp (Complex.I * x) - 1 - Complex.I * x‖ ≤ |x| ^ 2 / 2
```

### Probability/StrongRayleigh/CharacteristicTaylor [3] norm_exp_I_mul_sub_quadratic  (general; file: clean)
Reader: For real x: |exp(i x) - 1 - i x + x^2/2| <= |x|^3 / 6.

```lean
theorem norm_exp_I_mul_sub_quadratic (x : ℝ) :
 ‖Complex.exp (Complex.I * x) - 1 - Complex.I * x + (x : ℂ) ^ 2 / 2‖ ≤
 |x| ^ 3 / 6
```

### Probability/StrongRayleigh/GaussianMomentBounds [8] integrable_abs_pow_gaussianReal  (general; file: clean)
Reader: For every natural n, abs(x)^n is integrable under the centred real Gaussian gaussianReal 0 v.  Caveat: one-dimensional, centred

```lean
lemma integrable_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
 Integrable (fun x : ℝ => |x| ^ n) (gaussianReal 0 v)
```

### Probability/StrongRayleigh/GaussianMomentBounds [6] integral_abs_pow_gaussianReal  (general; file: clean)
Reader: Scaling of absolute moments: integral of abs(x)^n under N(0,v) equals sqrt(v)^n times the same integral under N(0,1).  Caveat: one-dimensional, centred; the N(0,1) moment itself is not evaluated

```lean
lemma integral_abs_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
 (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 v) =
 Real.sqrt v ^ n * (∫ x : ℝ, |x| ^ n ∂gaussianReal 0 1)
```

### RepresentationTheory/Theta/Adelic/GaussianSchwartz [2] polynomial_gaussian_bound  (general; file: clean)
Reader: (1+t)^M * exp(-t^2) <= 2^M * M! * e for every natural M and real t >= 0.

```lean
theorem polynomial_gaussian_bound (M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
 (1 + t) ^ M * Real.exp (-t ^ 2) ≤ 2 ^ M * (M.factorial : ℝ) * Real.exp 1
```
