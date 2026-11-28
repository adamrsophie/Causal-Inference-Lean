/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.VectorCLT
public import CausalInference.Estimation.ZEstimatorNormality
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Asymptotic normality of Z-estimators of a vector parameter

Let `θh n` be a consistent approximate root of the estimating equation
`n⁻¹ ∑_{i < n} ψ (O i) θ = 0` for a parameter `θ ∈ ℝ^ι` (`EuclideanSpace ℝ ι`), with
`ψ z : ℝ^ι → ℝ^ι` differentiable near the true value `θ₀` with Jacobian matrix `J z θ`
(continuous in `θ` and dominated entrywise by an integrable envelope), `E ψ (O 0) θ₀ = 0`,
`E ‖ψ (O 0) θ₀‖² < ∞`, and a nonsingular bread `A = -E J (O 0) θ₀`. Then
`√n (θh n - θ₀) = A⁻¹ √n n⁻¹ ∑_{i < n} ψ (O i) θ₀ + o_p(1)`, every coordinate of `θh` is
asymptotically linear (`CausalInference.IsAsymptoticallyLinear`), and
`√n (θh n - θ₀) → N(0, A⁻¹ B A⁻ᵀ)` in distribution with meat `B = E ψ ψᵀ`.

## Main definitions

* `CausalInference.breadMatrix ν J θ`: the bread `-∫ J z θ dν`, entrywise.
* `CausalInference.meatMatrix ν ψ θ`: the meat `∫ ψ z θ ψ z θᵀ dν`, entrywise.

## Main results

* `CausalInference.vectorZEstimator_linearization`: the mean value step.
* `CausalInference.vectorZEstimator_tendstoInMeasure_sub`: the linear expansion
  `√n (θh n - θ₀) - A⁻¹ √n Ψₙ θ₀ → 0` in probability.
* `CausalInference.vectorZEstimator_isAsymptoticallyLinear`: every coordinate of `θh` is
  asymptotically linear with influence function `(A⁻¹ ψ (·) θ₀)ᵢ`; the scalar results of the
  library (Wald intervals, the delta method for asymptotically linear estimators) then apply.
* `CausalInference.vectorZEstimator_tendstoInDistribution`: **asymptotic normality** with the
  sandwich covariance `A⁻¹ B A⁻ᵀ`, and
  `CausalInference.vectorZEstimator_tendstoInDistribution_of_root` for an exact root on events
  of probability tending to one.
* `CausalInference.covMatrix_eq_meatMatrix`: the meat is the covariance matrix of the
  estimating function at a root of its mean.

The real parameter case is `CausalInference.Estimation.ZEstimatorNormality`; the bridge between
the bread and meat matrices and the scalar `sandwichBread`, `sandwichMeat` is
`CausalInference.breadMatrix_unique` and `CausalInference.meatMatrix_unique` in
`CausalInference.Estimation.SandwichMatrix`.

References: P. J. Huber (1967), *The behavior of maximum likelihood estimates under nonstandard
conditions*, Proceedings of the Fifth Berkeley Symposium; A. W. van der Vaart (1998),
*Asymptotic Statistics*, chapter 5; L. A. Stefanski and D. D. Boos (2002), *The calculus of
M-estimation*, The American Statistician.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  {O : ℕ → Ω → 𝒪} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bread matrix `-∫ J z θ dν` of a vector estimating function with Jacobian matrix
`J z θ` (`J z θ i j = ∂ψᵢ/∂θⱼ`). -/
noncomputable def breadMatrix (ν : Measure 𝒪) (J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (θ : EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ -∫ z, J z θ i j ∂ν

/-- The meat matrix `∫ ψ z θ ψ z θᵀ dν` of a vector estimating function. -/
noncomputable def meatMatrix (ν : Measure 𝒪)
    (ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ ∫ z, ψ z θ i * ψ z θ j ∂ν

omit [DecidableEq ι] in
/-- The integral of a function with values in `ι → ι → ℝ` is the array of the entrywise
integrals, for integrable entries. -/
theorem integral_apply_apply {ν : Measure 𝒪} {F : 𝒪 → ι → ι → ℝ}
    (hF : ∀ i j, Integrable (fun z ↦ F z i j) ν) (i j : ι) :
    (∫ z, F z ∂ν) i j = ∫ z, F z i j ∂ν := by
  rw [eval_integral (fun i ↦ Integrable.of_eval fun j ↦ hF i j) i]
  exact eval_integral (fun j ↦ hF i j) j

/-- The map `M ↦ (x ↦ M x)` from arrays `ι → ι → ℝ` (with the sup norm) to operators on `ℝ^ι`,
as a continuous linear map. -/
noncomputable def arrayToEuclideanCLM :
    (ι → ι → ℝ) →L[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of M)
      map_add' := fun M N ↦ by rw [← map_add, Matrix.of_add_of]
      map_smul' := fun c M ↦ by rw [← map_smul, Matrix.smul_of]; rfl }

/-- `arrayToEuclideanCLM M` is the operator of the matrix `M`. -/
theorem arrayToEuclideanCLM_apply (M : ι → ι → ℝ) :
    arrayToEuclideanCLM M = Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of M) := rfl

/-- **The mean value step for a vector parameter.** Let `ψ z` have derivative `x ↦ J z θ x` at
every `θ` of a closed ball around `θ₀` for almost every observation value, let
`n⁻¹ ∑_{i < n} J (O i) θ → M θ` uniformly on the ball in probability (as arrays with the sup
norm), with `M` continuous at `θ₀`, and let `θh n → θ₀` in probability. Then for every `η > 0`,
with probability tending to one,
`‖-M θ₀ √n (θh n - θ₀) - √n Ψₙ θ₀‖ ≤ η ‖√n (θh n - θ₀)‖ + ‖√n Ψₙ (θh n)‖`, where
`Ψₙ θ = n⁻¹ ∑_{i < n} ψ (O i) θ`. The mean value inequality is applied to `Ψₙ` relative to the
operator of `M θ₀`, on a ball where the derivative of `Ψₙ` is close to it in operator norm. -/
theorem vectorZEstimator_linearization (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 < r)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r,
      HasFDerivAt (ψ z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (J z θ)) θ)
    {M : EuclideanSpace ℝ ι → ι → ι → ℝ}
    (hunif : TendstoUniformlyOnInProbability μ
      (fun n ω θ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, (fun k l ↦ J (O i ω) θ k l : ι → ι → ℝ)) M
      (Metric.closedBall θ₀ r))
    (hM : ContinuousAt M θ₀) {θh : ℕ → Ω → EuclideanSpace ℝ ι}
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀)) {η : ℝ} (hη : 0 < η) :
    WithProbTendingToOne μ (fun n ↦ {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (-Matrix.of (M θ₀))
        (√(n : ℝ) • (θh n ω - θ₀)) - √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) θ₀)‖ ≤
      η * ‖√(n : ℝ) • (θh n ω - θ₀)‖ +
        ‖√(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (θh n ω))‖}) := by
  set L := (arrayToEuclideanCLM : (ι → ι → ℝ) →L[ℝ] _) with hL_def
  set c : ℝ := ‖L‖ + 1 with hc_def
  have hc : 0 < c := by positivity
  have hη' : 0 < η / c / 2 := by positivity
  obtain ⟨δ, hδ, hMδ⟩ := Metric.continuousAt_iff.1 hM (η / c / 2) hη'
  have hδr : 0 < min δ r := lt_min hδ hr
  refine (((hθ.withProbTendingToOne_dist_lt hδr).inter (hunif (η / c / 2) hη')).inter
    (WithProbTendingToOne.of_ae (hO.ae_forall hderiv))).mono fun n ω hω ↦ ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 ⊢
  have hsub : Metric.ball θ₀ (min δ r) ⊆ Metric.closedBall θ₀ r :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (min_le_right _ _))
  set Jbar : EuclideanSpace ℝ ι → ι → ι → ℝ :=
    fun θ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, (fun k l ↦ J (O i ω) θ k l : ι → ι → ℝ) with hJbar
  set Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun θ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) θ with hΨ_def
  have hΨ : ∀ θ ∈ Metric.ball θ₀ (min δ r),
      HasFDerivWithinAt Ψ (L (Jbar θ)) (Metric.ball θ₀ (min δ r)) θ := by
    intro θ hθs
    have hsum : HasFDerivAt (fun θ ↦ ∑ i ∈ range n, ψ (O i ω) θ)
        (∑ i ∈ range n, Matrix.toEuclideanCLM (𝕜 := ℝ) (J (O i ω) θ)) θ :=
      HasFDerivAt.fun_sum (fun i _ ↦ h3 i θ (hsub hθs))
    have heqL : L (Jbar θ) =
        (n : ℝ)⁻¹ • ∑ i ∈ range n, Matrix.toEuclideanCLM (𝕜 := ℝ) (J (O i ω) θ) := by
      simp only [hJbar, map_smul, map_sum]
      rfl
    rw [heqL]
    exact (hsum.const_smul (n : ℝ)⁻¹).hasFDerivWithinAt
  have hbound : ∀ θ ∈ Metric.ball θ₀ (min δ r),
      ‖L (Jbar θ) - Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (M θ₀))‖ ≤ η := by
    intro θ hθs
    have ha := h2 θ (hsub hθs)
    have hb := hMδ (lt_of_lt_of_le (Metric.mem_ball.1 hθs) (min_le_left _ _))
    have heq : L (Jbar θ) - Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (M θ₀)) =
        L (Jbar θ - M θ₀) := by
      rw [map_sub]; rfl
    rw [heq]
    calc ‖L (Jbar θ - M θ₀)‖ ≤ ‖L‖ * ‖Jbar θ - M θ₀‖ := L.le_opNorm _
      _ ≤ c * (η / c / 2 + η / c / 2) := by
        gcongr
        · linarith
        · rw [← dist_eq_norm]
          exact (dist_triangle _ (M θ) _).trans (add_le_add ha.le hb.le)
      _ = η := by field_simp; ring
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hΨ hbound (convex_ball _ _)
    (Metric.mem_ball_self hδr) (Metric.mem_ball.2 h1)
  have key : Matrix.toEuclideanCLM (𝕜 := ℝ) (-Matrix.of (M θ₀)) (√(n : ℝ) • (θh n ω - θ₀)) -
      √(n : ℝ) • Ψ θ₀ = √(n : ℝ) • (Ψ (θh n ω) - Ψ θ₀ -
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (M θ₀)) (θh n ω - θ₀)) -
          √(n : ℝ) • Ψ (θh n ω) := by
    rw [map_neg, neg_apply, map_smul]
    simp only [smul_sub]
    abel
  rw [key]
  have hs := Real.sqrt_nonneg (n : ℝ)
  calc ‖√(n : ℝ) • (Ψ (θh n ω) - Ψ θ₀ -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (M θ₀)) (θh n ω - θ₀)) -
        √(n : ℝ) • Ψ (θh n ω)‖
      ≤ ‖√(n : ℝ) • (Ψ (θh n ω) - Ψ θ₀ -
          Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (M θ₀)) (θh n ω - θ₀))‖ +
        ‖√(n : ℝ) • Ψ (θh n ω)‖ := norm_sub_le _ _
    _ ≤ η * ‖√(n : ℝ) • (θh n ω - θ₀)‖ + ‖√(n : ℝ) • Ψ (θh n ω)‖ := by
      gcongr
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hs]
      calc √(n : ℝ) * ‖Ψ (θh n ω) - Ψ θ₀ -
            Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of (M θ₀)) (θh n ω - θ₀)‖
          ≤ √(n : ℝ) * (η * ‖θh n ω - θ₀‖) := mul_le_mul_of_nonneg_left hmvt hs
        _ = η * (√(n : ℝ) * ‖θh n ω - θ₀‖) := by ring

/-- **The linear expansion of a Z-estimator of a vector parameter.** Let `O` be an i.i.d. sample
under a probability measure and `ψ : 𝒪 → ℝ^ι → ℝ^ι` an estimating function with the following
properties on a closed ball `K` of radius `r > 0` around `θ₀`: for almost every observation value
`z`, `ψ z` has derivative `x ↦ J z θ x` at every `θ ∈ K` and every entry of `J z` is continuous on
`K`; every entry `z ↦ J z θ i j` is measurable for `θ ∈ K` and `|J z θ i j| ≤ H z` on `K` for an
integrable envelope `H`. Assume `z ↦ ψ z θ₀` measurable, `ψ (O 0) θ₀` square integrable with mean
zero, and the bread `A = breadMatrix (μ.map (O 0)) J θ₀` nonsingular. If `θh n → θ₀` in
probability and `√n n⁻¹ ∑_{i < n} ψ (O i) (θh n) → 0` in probability, then
`√n (θh n - θ₀) - A⁻¹ √n n⁻¹ ∑_{i < n} ψ (O i) θ₀ → 0` in probability. -/
theorem vectorZEstimator_tendstoInMeasure_sub [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 < r)
    (hψm : Measurable fun z ↦ ψ z θ₀)
    (hJm : ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, Measurable fun z ↦ J z θ i j)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r,
      HasFDerivAt (ψ z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (J z θ)) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ∀ i j,
      ContinuousOn (fun θ ↦ J z θ i j) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, |J z θ i j| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : (breadMatrix (μ.map (O 0)) J θ₀).det ≠ 0) {θh : ℕ → Ω → EuclideanSpace ℝ ι}
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (θh n ω))) atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - θ₀) -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (breadMatrix (μ.map (O 0)) J θ₀)⁻¹
        (√(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) θ₀))) atTop (fun _ ↦ 0) := by
  set ν := μ.map (O 0) with hν
  set K := Metric.closedBall θ₀ r with hK_def
  have hθ₀K : θ₀ ∈ K := Metric.mem_closedBall_self hr.le
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers hO (isCompact_closedBall θ₀ r)
    (ψ := fun z θ ↦ (fun k l ↦ J z θ k l : ι → ι → ℝ))
    (fun θ hθ ↦ measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ hJm θ hθ i j)
    (hcont.mono fun z hz ↦ continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ hz i j)
    hH.norm
    (hdom.mono fun z hz θ hθ ↦ (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j ↦ by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact (hz θ hθ i j).trans (le_abs_self _))
  have hMat := hMc.continuousAt (Metric.closedBall_mem_nhds θ₀ hr)
  have hJint : ∀ i j, Integrable (fun z ↦ J z θ₀ i j) ν := fun i j ↦
    Integrable.mono' hH (hJm θ₀ hθ₀K i j).aestronglyMeasurable
      (hdom.mono fun z hz ↦ by rw [Real.norm_eq_abs]; exact hz θ₀ hθ₀K i j)
  have hMb : -Matrix.of (∫ z, (fun k l ↦ J z θ₀ k l : ι → ι → ℝ) ∂ν) =
      breadMatrix ν J θ₀ := by
    ext i j
    simp only [Matrix.neg_apply, Matrix.of_apply, breadMatrix]
    rw [integral_apply_apply (F := fun z k l ↦ J z θ₀ k l) hJint i j]
  have hclt := hO.tendstoInDistribution_multivariateGaussian hψm hB
    (HasLaw.id (μ := multivariateGaussian 0 (covMatrix μ fun i ω ↦ ψ (O 0 ω) θ₀ i)))
  simp only [hzero, sub_zero] at hclt
  set A := breadMatrix ν J θ₀ with hA_def
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hinv : ∀ v, Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (Matrix.toEuclideanCLM (𝕜 := ℝ) A v) =
      v := fun v ↦ by
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ * Matrix.toEuclideanCLM (𝕜 := ℝ) A = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul A hAu, map_one]
    exact congrArg (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι ↦ T v) h1
  have hlin : ∀ η : ℝ, 0 < η → WithProbTendingToOne μ (fun n ↦
      {ω | ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (√(n : ℝ) • (θh n ω - θ₀)) -
        √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) θ₀)‖ ≤
          η * ‖√(n : ℝ) • (θh n ω - θ₀)‖ +
            ‖√(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (θh n ω))‖}) := by
    intro η hη
    have := vectorZEstimator_linearization hO hr hderiv hunif hMat hθ hη
    rwa [hMb] at this
  exact tendstoInMeasure_sub_of_linearization hinv hclt.boundedInProbability hroot hlin

omit [DecidableEq ι] in
/-- **The meat is a covariance matrix.** At a parameter `θ` where the square integrable
estimating function `ψ (O 0) θ` has mean zero, its covariance matrix is the meat
`meatMatrix (μ.map (O 0)) ψ θ`. -/
theorem covMatrix_eq_meatMatrix [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {θ : EuclideanSpace ℝ ι}
    (hψm : Measurable fun z ↦ ψ z θ) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ) 2 μ)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ] = 0) :
    covMatrix μ (fun i ω ↦ ψ (O 0 ω) θ i) = meatMatrix (μ.map (O 0)) ψ θ := by
  have hc : ∀ i, MemLp (fun ω ↦ ψ (O 0 ω) θ i) 2 μ := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hB
  have hm : ∀ i, μ[fun ω ↦ ψ (O 0 ω) θ i] = 0 := fun i ↦ by
    rw [← eval_integral_piLp (fun j ↦ (hc j).integrable one_le_two), hzero]
    rfl
  have hψi : ∀ i, Measurable fun z ↦ ψ z θ i := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hψm
  ext i j
  simp only [covMatrix, meatMatrix, Matrix.of_apply]
  rw [covariance_eq_sub (hc i) (hc j), hm i, hm j, mul_zero, sub_zero]
  exact (integral_map (hO.aemeasurable 0) ((hψi i).mul (hψi j)).aestronglyMeasurable).symm

/-- **Asymptotic linearity of the coordinates of a Z-estimator.** Under the hypotheses of
`vectorZEstimator_tendstoInMeasure_sub`, every coordinate `θh n i` is asymptotically linear at
`θ₀ i` with influence function `z ↦ (A⁻¹ ψ z θ₀)ᵢ`, `A` the bread. -/
theorem vectorZEstimator_isAsymptoticallyLinear [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 < r)
    (hψm : Measurable fun z ↦ ψ z θ₀)
    (hJm : ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, Measurable fun z ↦ J z θ i j)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r,
      HasFDerivAt (ψ z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (J z θ)) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ∀ i j,
      ContinuousOn (fun θ ↦ J z θ i j) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, |J z θ i j| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : (breadMatrix (μ.map (O 0)) J θ₀).det ≠ 0) {θh : ℕ → Ω → EuclideanSpace ℝ ι}
    (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (θh n ω))) atTop (fun _ ↦ 0)) (i : ι) :
    IsAsymptoticallyLinear (fun n ω ↦ θh n ω i) (θ₀ i)
      (fun z ↦ ((breadMatrix (μ.map (O 0)) J θ₀)⁻¹ *ᵥ WithLp.ofLp (ψ z θ₀)) i) O μ := by
  have hdiff := vectorZEstimator_tendstoInMeasure_sub hO hr hψm hJm hderiv hcont hH hdom hzero hB
    hA hθ hroot
  set A := breadMatrix (μ.map (O 0)) J θ₀
  set p := EuclideanSpace.proj (𝕜 := ℝ) (ι := ι) i
  set ℓ := p.comp (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹) with hℓ
  have hℓapp : ∀ v, ℓ v = (A⁻¹ *ᵥ WithLp.ofLp v) i := fun v ↦ rfl
  have hint : Integrable (fun ω ↦ ψ (O 0 ω) θ₀) μ := hB.integrable one_le_two
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [← hℓapp]
    exact ℓ.continuous.measurable.comp hψm
  · simp_rw [← hℓapp]
    exact ℓ.comp_memLp' hB
  · simp_rw [← hℓapp]
    rw [ℓ.integral_comp_comm hint, hzero, map_zero]
  · have h1 := hdiff.comp_continuousAt (g := p) p.continuous.continuousAt
    rw [map_zero] at h1
    refine h1.congr' (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
    simp only [p, map_sub, map_smul, map_sum, smul_eq_mul]
    rw [← mul_assoc, sqrt_mul_inv_self]
    rfl

/-- **Asymptotic normality of a Z-estimator of a vector parameter.** Under the hypotheses of
`vectorZEstimator_tendstoInMeasure_sub` and almost everywhere measurability of each `θh n`,
`√n (θh n - θ₀)` converges in distribution to every random vector with law `N(0, A⁻¹ B A⁻ᵀ)`,
`A` the bread and `B` the meat at `θ₀`. -/
theorem vectorZEstimator_tendstoInDistribution [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 < r)
    (hψm : Measurable fun z ↦ ψ z θ₀)
    (hJm : ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, Measurable fun z ↦ J z θ i j)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r,
      HasFDerivAt (ψ z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (J z θ)) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ∀ i j,
      ContinuousOn (fun θ ↦ J z θ i j) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, |J z θ i j| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : (breadMatrix (μ.map (O 0)) J θ₀).det ≠ 0) {θh : ℕ → Ω → EuclideanSpace ℝ ι}
    (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : TendstoInMeasure μ (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (θh n ω))) atTop (fun _ ↦ 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 ((breadMatrix (μ.map (O 0)) J θ₀)⁻¹ *
      meatMatrix (μ.map (O 0)) ψ θ₀ * ((breadMatrix (μ.map (O 0)) J θ₀)⁻¹)ᵀ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - θ₀)) atTop Y
      (fun _ ↦ μ) P' := by
  have hdiff := vectorZEstimator_tendstoInMeasure_sub hO hr hψm hJm hderiv hcont hH hdom hzero hB
    hA hθ hroot
  set A := breadMatrix (μ.map (O 0)) J θ₀
  set Sg := covMatrix μ (fun i ω ↦ ψ (O 0 ω) θ₀ i)
  have hS : Sg.PosSemidef := posSemidef_covMatrix fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hB
  have hclt : TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) θ₀ - μ[fun ω ↦ ψ (O 0 ω) θ₀])) atTop
      id (fun _ ↦ μ) (multivariateGaussian 0 Sg) :=
    hO.tendstoInDistribution_multivariateGaussian hψm hB HasLaw.id
  simp only [hzero, sub_zero] at hclt
  have h1 := hclt.continuous_comp (Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹).continuous
  have hlaw : HasLaw (fun x ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) A⁻¹ (id x))
      (multivariateGaussian 0 (A⁻¹ * meatMatrix (μ.map (O 0)) ψ θ₀ * A⁻¹ᵀ))
      (multivariateGaussian 0 Sg) := by
    have h := HasLaw.matrixCLM_multivariateGaussian (m := 0) hS HasLaw.id A⁻¹
    have hmeat : Sg = meatMatrix (μ.map (O 0)) ψ θ₀ := covMatrix_eq_meatMatrix hO hψm hB hzero
    rw [map_zero] at h
    rw [← hmeat]
    exact h
  have h2 := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - θ₀)) _ h1 hdiff
    (fun n ↦ ((hθm n).sub_const θ₀).fun_const_smul _)
  exact h2.of_hasLaw hlaw hY

/-- **Asymptotic normality with an exact root.** The form of
`vectorZEstimator_tendstoInDistribution` in which `θh n` solves `∑_{i < n} ψ (O i) (θh n) = 0`
on events of probability tending to one. -/
theorem vectorZEstimator_tendstoInDistribution_of_root [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ)
    {ψ : 𝒪 → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {J : 𝒪 → EuclideanSpace ℝ ι → Matrix ι ι ℝ} {θ₀ : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 < r)
    (hψm : Measurable fun z ↦ ψ z θ₀)
    (hJm : ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, Measurable fun z ↦ J z θ i j)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r,
      HasFDerivAt (ψ z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (J z θ)) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ∀ i j,
      ContinuousOn (fun θ ↦ J z θ i j) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ∀ i j, |J z θ i j| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : (breadMatrix (μ.map (O 0)) J θ₀).det ≠ 0) {θh : ℕ → Ω → EuclideanSpace ℝ ι}
    (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀))
    (hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, ψ (O i ω) (θh n ω) = 0}))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 ((breadMatrix (μ.map (O 0)) J θ₀)⁻¹ *
      meatMatrix (μ.map (O 0)) ψ θ₀ * ((breadMatrix (μ.map (O 0)) J θ₀)⁻¹)ᵀ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - θ₀)) atTop Y
      (fun _ ↦ μ) P' := by
  refine vectorZEstimator_tendstoInDistribution hO hr hψm hJm hderiv hcont hH hdom hzero hB hA
    hθm hθ ((tendstoInMeasure_const (μ := μ) (0 : EuclideanSpace ℝ ι)).congr_withProbTendingToOne
      hroot fun n ω hω ↦ ?_) hY
  simp only [Set.mem_ofPred_eq] at hω
  simp [hω]

end CausalInference
