/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LimitLaws
public import CausalInference.BiasAnalysis.VarianceCovariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Matrices as linear maps, covariance matrices and linear images of Gaussian vectors

## Main definitions

* `CausalInference.matrixCLM M`: the continuous linear map `x ↦ M x` from `ℝ^ι` to `ℝ^κ`
  (`EuclideanSpace`) of a rectangular matrix `M`; for a square matrix it is
  `Matrix.toEuclideanCLM M`.

The covariance matrix of a random vector `X` is the covariance matrix
`CausalInference.BiasAnalysis.MeasurementError.covMatrix μ (fun i ω ↦ X ω i)` of its coordinates.

## Main results

* `CausalInference.matrixCLM_adjoint`: the adjoint of `x ↦ M x` is `u ↦ Mᵀ u`.
* `CausalInference.multivariateGaussian_map_matrixCLM`: **the linear image of a Gaussian
  vector**: the image of `N(m, S)` under `x ↦ M x` is `N(M m, M S Mᵀ)`, and
  `CausalInference.HasLaw.matrixCLM_multivariateGaussian` in the language of random variables.
* `CausalInference.variance_inner_eq_covMatrix`: the variance of `⟪X, t⟫` is the quadratic form
  `tᵀ Σ t` of the covariance matrix `Σ` of `X`, and
  `CausalInference.posSemidef_covMatrix`: a covariance matrix is positive semidefinite.
* `CausalInference.hasLaw_inner_multivariateGaussian`: the projection `⟪Y, t⟫` of a vector with
  law `N(0, S)` has law `N(0, tᵀ S t)`.
* `MeasureTheory.TendstoInDistribution.inner_tendstoInMeasure` and
  `MeasureTheory.TendstoInDistribution.matrixCLM_tendstoInMeasure`: Slutsky's theorem for an
  inner product `⟪Y n, X n⟫` and for a random matrix `C n X n`, with `Y n` and `C n` converging
  in probability to constants. Both are instances of Mathlib's
  `MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`.

References: T. W. Anderson (2003), *An Introduction to Multivariate Statistical Analysis*, third
edition, chapter 2 (linear transformations of normal vectors); A. W. van der Vaart (1998),
*Asymptotic Statistics*, chapter 2 (Slutsky's lemma).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)
open BiasAnalysis.VarianceCovariance (quadraticVariance_eq_dotProduct
  variance_linearization_cov)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Matrices as continuous linear maps of Euclidean spaces -/

/-- The continuous linear map `x ↦ M x` from `ℝ^ι` to `ℝ^κ` of a matrix `M` with rows indexed by
`κ` and columns indexed by `ι`. -/
noncomputable def matrixCLM [DecidableEq ι] (M : Matrix κ ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

variable [DecidableEq ι]

/-- `matrixCLM M` multiplies the coordinate vector by `M`. -/
theorem matrixCLM_apply (M : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    matrixCLM M x = WithLp.toLp 2 (M *ᵥ WithLp.ofLp x) := rfl

/-- The coordinates of `M x`. -/
@[simp]
theorem matrixCLM_apply_apply (M : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) (k : κ) :
    matrixCLM M x k = (M *ᵥ WithLp.ofLp x) k := rfl

/-- For a square matrix, `matrixCLM M` is `Matrix.toEuclideanCLM M`. -/
theorem matrixCLM_eq_toEuclideanCLM (M : Matrix ι ι ℝ) :
    matrixCLM M = Matrix.toEuclideanCLM (𝕜 := ℝ) M := rfl

/-- **The adjoint of a matrix map** is the map of the transpose. -/
theorem matrixCLM_adjoint [DecidableEq κ] (M : Matrix κ ι ℝ) :
    (matrixCLM M).adjoint = matrixCLM Mᵀ := by
  rw [matrixCLM, matrixCLM, ← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_eq_transpose_of_trivial]

/-- The map of a product is the composite of the maps. -/
theorem matrixCLM_mul {ν' : Type*} [Fintype ν'] [DecidableEq κ] (M : Matrix ν' κ ℝ)
    (N : Matrix κ ι ℝ) : matrixCLM (M * N) = (matrixCLM M).comp (matrixCLM N) := by
  ext x k
  simp [matrixCLM_apply, Matrix.mulVec_mulVec]

/-- The map of the identity matrix is the identity. -/
@[simp]
theorem matrixCLM_one : matrixCLM (1 : Matrix ι ι ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext x k
  simp [matrixCLM_apply]

/-! ### Linear images of Gaussian vectors -/

/-- **The linear image of a Gaussian vector.** For a positive semidefinite `S`, the image of
`N(m, S)` under `x ↦ M x` is `N(M m, M S Mᵀ)`. Both laws are Gaussian; their means agree by
linearity of the integral and their covariance forms agree through the adjoint `u ↦ Mᵀ u`. -/
theorem multivariateGaussian_map_matrixCLM [DecidableEq κ] {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (m : EuclideanSpace ℝ ι) (M : Matrix κ ι ℝ) :
    (multivariateGaussian m S).map (matrixCLM M) =
      multivariateGaussian (matrixCLM M m) (M * S * Mᵀ) := by
  have hS' : (M * S * Mᵀ).PosSemidef := by
    simpa using hS.mul_mul_conjTranspose_same M
  apply IsGaussian.ext
  · change ∫ x, x ∂_ = ∫ x, x ∂_
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', matrixCLM_adjoint, matrixCLM_apply,
      matrixCLM_apply]
    simp only [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    conv_rhs => rw [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **The linear image of a Gaussian vector, for random variables.** If `Y` has law `N(m, S)`
with `S` positive semidefinite, then `M Y` has law `N(M m, M S Mᵀ)`. -/
theorem HasLaw.matrixCLM_multivariateGaussian [DecidableEq κ] {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {Y : Ω' → EuclideanSpace ℝ ι}
    {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hY : HasLaw Y (multivariateGaussian m S) P') (M : Matrix κ ι ℝ) :
    HasLaw (fun ω ↦ matrixCLM M (Y ω)) (multivariateGaussian (matrixCLM M m) (M * S * Mᵀ)) P' := by
  rw [← multivariateGaussian_map_matrixCLM hS m M]
  exact (hasLaw_map (matrixCLM M).continuous.measurable.aemeasurable).fun_comp hY

/-! ### Covariance matrices -/

section CovMatrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

omit [Fintype ι] [DecidableEq ι] in
/-- **A covariance matrix is positive semidefinite**: it is symmetric, and its quadratic form
`tᵀ Σ t` is the variance of `∑ i, tᵢ Xᵢ` (`variance_linearization_cov`). -/
theorem posSemidef_covMatrix [Finite ι] [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) : (covMatrix μ X).PosSemidef := by
  have := Fintype.ofFinite ι
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun t ↦ ?_⟩
  · ext i j
    simp [covMatrix, covariance_comm]
  · rw [star_trivial, ← quadraticVariance_eq_dotProduct, ← variance_linearization_cov X hX t]
    exact variance_nonneg _ _

omit [DecidableEq ι] in
/-- **The variance of a projection.** For a square integrable random vector `V` under a finite
measure, the variance of `⟪V, t⟫` is the quadratic form `tᵀ Σ t` of the covariance matrix `Σ` of
the coordinates of `V`. -/
theorem variance_inner_eq_covMatrix [IsFiniteMeasure μ] {V : Ω → EuclideanSpace ℝ ι}
    (hV : MemLp V 2 μ) (t : EuclideanSpace ℝ ι) :
    Var[fun ω ↦ ⟪V ω, t⟫; μ] =
      WithLp.ofLp t ⬝ᵥ covMatrix μ (fun i ω ↦ V ω i) *ᵥ WithLp.ofLp t := by
  have hc : ∀ i, MemLp (fun ω ↦ V ω i) 2 μ := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hV
  have heq : (fun ω ↦ ⟪V ω, t⟫) = fun ω ↦ ∑ i, t i * V ω i := by
    funext ω; simp [PiLp.inner_apply]
  rw [heq, variance_linearization_cov (fun i ω ↦ V ω i) hc, quadraticVariance_eq_dotProduct]

end CovMatrix

/-- **The projection of a Gaussian vector.** For `S` positive semidefinite, the image of
`N(0, S)` under `x ↦ ⟪x, t⟫` is `N(0, tᵀ S t)`. -/
theorem multivariateGaussian_map_inner {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (t : EuclideanSpace ℝ ι) :
    (multivariateGaussian 0 S).map (fun x ↦ ⟪x, t⟫) =
      gaussianReal 0 (WithLp.ofLp t ⬝ᵥ S *ᵥ WithLp.ofLp t).toNNReal := by
  have hfun : (fun x : EuclideanSpace ℝ ι ↦ ⟪x, t⟫) = ⇑(innerSL ℝ t) := by
    funext x; simp [real_inner_comm]
  rw [hfun, IsGaussian.map_eq_gaussianReal]
  congr 1
  · rw [(innerSL ℝ t).integral_comp_id_comm IsGaussian.integrable_id]
    simp
  · congr 1
    rw [← covarianceBilin_multivariateGaussian (μ := 0) hS t t,
      covarianceBilin_self IsGaussian.memLp_two_id]
    rfl

/-- **The projection of a Gaussian vector, for random variables.** If `Y` has law `N(0, S)` with
`S` positive semidefinite, then `⟪Y, t⟫` has law `N(0, tᵀ S t)`. -/
theorem hasLaw_inner_multivariateGaussian {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} {Y : Ω' → EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hY : HasLaw Y (multivariateGaussian 0 S) P') (t : EuclideanSpace ℝ ι) :
    HasLaw (fun ω ↦ ⟪Y ω, t⟫)
      (gaussianReal 0 (WithLp.ofLp t ⬝ᵥ S *ᵥ WithLp.ofLp t).toNNReal) P' := by
  rw [← multivariateGaussian_map_inner hS t]
  exact (hasLaw_map (continuous_id.inner continuous_const).measurable.aemeasurable).fun_comp hY

/-! ### Slutsky's theorem for inner products and random matrices -/

section Slutsky

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **Slutsky's theorem for an inner product.** In a separable real inner product space, if
`X n → Z` in distribution and `Y n → c` in probability with each `Y n` almost everywhere
measurable, then `⟪Y n, X n⟫ → ⟪c, Z⟫` in distribution. -/
theorem _root_.MeasureTheory.TendstoInDistribution.inner_tendstoInMeasure {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {X Y : ℕ → Ω → E} {Z : Ω' → E} {c : E}
    (hX : TendstoInDistribution X atTop Z (fun _ ↦ μ) P')
    (hY : TendstoInMeasure μ Y atTop (fun _ ↦ c)) (hYm : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution (fun n ω ↦ ⟪Y n ω, X n ω⟫) atTop (fun ω ↦ ⟪c, Z ω⟫)
      (fun _ ↦ μ) P' :=
  hX.continuous_comp_prodMk_of_tendstoInMeasure_const (g := fun p : E × E ↦ ⟪p.2, p.1⟫)
    (continuous_snd.inner continuous_fst) hY hYm

/-- **Slutsky's theorem for a random matrix.** If `X n → Z` in distribution in `ℝ^ι`, and the
random matrices `C n` converge entrywise in probability to `C₀`, with almost everywhere measurable
entries, then `C n X n → C₀ Z` in distribution. -/
theorem _root_.MeasureTheory.TendstoInDistribution.matrixCLM_tendstoInMeasure
    {X : ℕ → Ω → EuclideanSpace ℝ ι} {Z : Ω' → EuclideanSpace ℝ ι} {C : ℕ → Ω → Matrix κ ι ℝ}
    {C₀ : Matrix κ ι ℝ} (hX : TendstoInDistribution X atTop Z (fun _ ↦ μ) P')
    (hC : ∀ k i, TendstoInMeasure μ (fun n ω ↦ C n ω k i) atTop (fun _ ↦ C₀ k i))
    (hCm : ∀ n k i, AEMeasurable (fun ω ↦ C n ω k i) μ) :
    TendstoInDistribution (fun n ω ↦ matrixCLM (C n ω) (X n ω)) atTop
      (fun ω ↦ matrixCLM C₀ (Z ω)) (fun _ ↦ μ) P' := by
  have hC' : TendstoInMeasure μ (fun n ω ↦ (fun k i ↦ C n ω k i : κ → ι → ℝ)) atTop
      (fun _ ↦ (fun k i ↦ C₀ k i : κ → ι → ℝ)) :=
    tendstoInMeasure_pi (X := fun k n ω i ↦ C n ω k i) fun k ↦
      tendstoInMeasure_pi (X := fun i n ω ↦ C n ω k i) fun i ↦ hC k i
  have hCm' : ∀ n, AEMeasurable (fun ω ↦ (fun k i ↦ C n ω k i : κ → ι → ℝ)) μ := fun n ↦
    AEMeasurable.of_eval fun k ↦ AEMeasurable.of_eval fun i ↦ hCm n k i
  have hg : Continuous fun p : EuclideanSpace ℝ ι × (κ → ι → ℝ) ↦
      (WithLp.toLp 2 (Matrix.of p.2 *ᵥ WithLp.ofLp p.1) : EuclideanSpace ℝ κ) :=
    (PiLp.continuous_toLp 2 _).comp
      (Continuous.matrix_mulVec continuous_snd ((PiLp.continuous_ofLp 2 _).comp continuous_fst))
  exact hX.continuous_comp_prodMk_of_tendstoInMeasure_const hg hC' hCm'

end Slutsky

end CausalInference
