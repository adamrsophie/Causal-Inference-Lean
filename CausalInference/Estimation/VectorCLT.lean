/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.GaussianLinearImage
public import CausalInference.Estimation.LawOfLargeNumbers

/-!
# The multivariate central limit theorem

For an i.i.d. sample `O` and a measurable `f : 𝒪 → ℝ^ι` (`EuclideanSpace ℝ ι`) with
`f (O 0)` square integrable, the scaled vector sample mean
`√n (n⁻¹ ∑_{i < n} f (O i) - E f (O 0))` converges in distribution to `N(0, Σ)`, where `Σ` is
the covariance matrix of the coordinates of `f (O 0)`.

## Main results

* `CausalInference.IsIIDSample.tendstoInDistribution_multivariateGaussian`: **the multivariate
  central limit theorem**. By the Cramér-Wold device
  (`tendstoInDistribution_iff_tendstoInDistribution_inner`) it reduces to the scalar central
  limit theorem for every projection `⟪f, t⟫`, whose variance is `tᵀ Σ t`.
* `CausalInference.IsAsymptoticallyLinear.tendstoInDistribution_multivariateGaussian`:
  **joint asymptotic normality** of a finite vector of estimators, each asymptotically linear
  (`CausalInference.IsAsymptoticallyLinear`) for the same sample: `√n (θhat - θ)` converges to
  `N(0, Σ)`, with `Σ` the covariance matrix of the influence functions. This is the joint form of
  the marginal statements of `CausalInference.Estimation.AsymptoticLinear`; combined with the
  vector delta method (`CausalInference.Estimation.VectorDeltaMethod`) it gives the
  vector valued form of `IsAsymptoticallyLinear.tendstoInDistribution_comp_hasFDerivAt`, whose
  function `g` is real valued.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 2 (the multivariate
central limit theorem and the Cramér-Wold device).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  {O : ℕ → Ω → 𝒪} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- The scaled centered vector sample mean is the normalized centered sum:
`√n • (n⁻¹ • S - m) = (√n)⁻¹ • (S - n • m)`, also at `n = 0`. -/
lemma sqrt_smul_inv_smul_sub {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) (S m : E) :
    √(n : ℝ) • ((n : ℝ)⁻¹ • S - m) = (√(n : ℝ))⁻¹ • (S - (n : ℝ) • m) := by
  rw [smul_sub, smul_sub, smul_smul, smul_smul, sqrt_mul_inv_self,
    inv_sqrt_mul_self _ n.cast_nonneg]

/-- **The multivariate central limit theorem.** Let `O` be an i.i.d. sample under a probability
measure and `f : 𝒪 → ℝ^ι` measurable with `f (O 0)` square integrable. Then
`√n (n⁻¹ ∑_{i < n} f (O i) - E f (O 0))` converges in distribution to every random vector `Y`
with law `N(0, Σ)`, `Σ` the covariance matrix of the coordinates of `f (O 0)`. -/
theorem IsIIDSample.tendstoInDistribution_multivariateGaussian [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 (covMatrix μ fun i ω ↦ f (O 0 ω) i)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω) - μ[fun ω ↦ f (O 0 ω)])) atTop Y
      (fun _ ↦ μ) P' := by
  have hint : Integrable (fun ω ↦ f (O 0 ω)) μ := hf2.integrable one_le_two
  have hS := posSemidef_covMatrix (μ := μ) (X := fun i ω ↦ f (O 0 ω) i) fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf2
  have hmeas : ∀ n : ℕ, AEMeasurable (fun ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω) - μ[fun ω ↦ f (O 0 ω)])) μ := by
    have hfi : ∀ i, AEMeasurable (fun ω ↦ f (O i ω)) μ := fun i ↦
      hf.comp_aemeasurable (hO.aemeasurable i)
    intro n
    have hsum : AEMeasurable (fun ω ↦ ∑ i ∈ range n, f (O i ω)) μ :=
      Finset.aemeasurable_fun_sum _ fun i _ ↦ hfi i
    exact ((hsum.const_smul ((n : ℝ)⁻¹)).sub_const _).const_smul (√(n : ℝ))
  refine (tendstoInDistribution_iff_tendstoInDistribution_inner hY.aemeasurable hmeas).2
    fun t ↦ ?_
  have hg : Measurable fun z ↦ ⟪f z, t⟫ := by fun_prop
  have hX := hO.comp hg
  have hvar : Var[fun ω ↦ ⟪f (O 0 ω), t⟫; μ] =
      WithLp.ofLp t ⬝ᵥ covMatrix μ (fun i ω ↦ f (O 0 ω) i) *ᵥ WithLp.ofLp t :=
    variance_inner_eq_covMatrix hf2 t
  have hYt := hasLaw_inner_multivariateGaussian hS hY t
  rw [← hvar] at hYt
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ω ↦ ⟪f (O i ω), t⟫) hYt
    (hf2.inner_const t) hX.indep hX.ident
  have hI : ∫ ω, ⟪f (O 0 ω), t⟫ ∂μ = ⟪∫ ω, f (O 0 ω) ∂μ, t⟫ := by
    calc ∫ ω, ⟪f (O 0 ω), t⟫ ∂μ = ∫ ω, ⟪t, f (O 0 ω)⟫ ∂μ :=
          integral_congr_ae (ae_of_all _ fun ω ↦ real_inner_comm _ _)
      _ = ⟪t, ∫ ω, f (O 0 ω) ∂μ⟫ := integral_inner hint t
      _ = ⟪∫ ω, f (O 0 ω) ∂μ, t⟫ := real_inner_comm _ _
  convert hclt using 1
  funext n ω
  rw [sqrt_smul_inv_smul_sub, inner_smul_left, inner_sub_left, sum_inner, inner_smul_left, hI]
  simp

/-- **Joint asymptotic normality of asymptotically linear estimators.** Let `θhat i`, for `i` in a
finite index type, be asymptotically linear at `θ i` with influence functions `φ i` for the same
i.i.d. sample, each `θhat i n` almost everywhere measurable. Then the vector
`√n (θhat n - θ) ∈ ℝ^ι` converges in distribution to every random vector `Y` with law
`N(0, Σ)`, where `Σ` is the covariance matrix of the influence functions at the observation. By the
Cramér-Wold device it suffices that every linear combination `∑ i, tᵢ θhat i` is asymptotically
linear (`IsAsymptoticallyLinear.sum_const_mul`), with asymptotic variance `tᵀ Σ t`
(`IsAsymptoticallyLinear.integral_sq_eq_sum_cov`). -/
theorem IsAsymptoticallyLinear.tendstoInDistribution_multivariateGaussian
    [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ}
    {φ : ι → 𝒪 → ℝ} (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    (hmeas : ∀ i n, AEMeasurable (θhat i n) μ) {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 (covMatrix μ fun i ω ↦ φ i (O 0 ω))) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (fun i ↦ θhat i n ω) - WithLp.toLp 2 θ : EuclideanSpace ℝ ι)) atTop Y
      (fun _ ↦ μ) P' := by
  have hS := posSemidef_covMatrix (μ := μ) (X := fun i ω ↦ φ i (O 0 ω)) fun i ↦ (h i).memLp
  have hvec : ∀ n, AEMeasurable (fun ω ↦ (WithLp.toLp 2 (fun i ↦ θhat i n ω) :
      EuclideanSpace ℝ ι)) μ := fun n ↦
    (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable (AEMeasurable.of_eval fun i ↦ hmeas i n)
  have hmeas' : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (fun i ↦ θhat i n ω) - WithLp.toLp 2 θ : EuclideanSpace ℝ ι)) μ :=
    fun n ↦ ((hvec n).sub_const _).fun_const_smul _
  refine (tendstoInDistribution_iff_tendstoInDistribution_inner hY.aemeasurable hmeas').2
    fun t ↦ ?_
  have hAL := IsAsymptoticallyLinear.sum_const_mul univ (fun i ↦ t i) fun i _ ↦ h i
  have hYt := hasLaw_inner_multivariateGaussian hS hY t
  have hvar : WithLp.ofLp t ⬝ᵥ covMatrix μ (fun i ω ↦ φ i (O 0 ω)) *ᵥ WithLp.ofLp t =
      μ[fun ω ↦ (∑ i ∈ univ, t i * φ i (O 0 ω)) ^ 2] := by
    rw [IsAsymptoticallyLinear.integral_sq_eq_sum_cov h]
    simp only [covMatrix, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [hvar] at hYt
  have hlim := hAL.tendstoInDistribution hO
    (fun n ↦ Finset.aemeasurable_fun_sum _ fun i _ ↦ (hmeas i n).const_mul _) hYt
  convert hlim using 1
  funext n ω
  simp only [inner_smul_left, inner_sub_left, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]

end CausalInference
