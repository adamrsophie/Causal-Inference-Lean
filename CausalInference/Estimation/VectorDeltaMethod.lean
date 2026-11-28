/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.VectorCLT

/-!
# The vector delta method with a Gaussian limit

If `√n (T n - θ) → N(0, S)` in distribution in `ℝ^ι` and `g : ℝ^ι → ℝ^κ` is differentiable at
`θ` with Jacobian matrix `D`, then `√n (g (T n) - g θ) → N(0, D S Dᵀ)` in distribution. This is
`MeasureTheory.TendstoInDistribution.delta_method` (any limit law, in normed spaces) followed by
the linear image of a Gaussian vector (`CausalInference.multivariateGaussian_map_matrixCLM`).

## Main results

* `MeasureTheory.TendstoInDistribution.delta_method_multivariateGaussian`: **the vector delta
  method** with a centered Gaussian limit.
* `CausalInference.IsIIDSample.delta_method_multivariateGaussian`: the case of a vector sample
  mean, through the multivariate central limit theorem.
* `CausalInference.IsAsymptoticallyLinear.delta_method_multivariateGaussian`: the case of a
  vector of asymptotically linear estimators, through their joint asymptotic normality.

## Relation to the multivariate delta method for asymptotically linear estimators

`CausalInference.Estimation.DeltaMethodMultivariate` treats a real valued `g : (ι → ℝ) → ℝ` of
asymptotically linear estimators and proves that `g (θhat)` is again asymptotically linear
(`IsAsymptoticallyLinear.comp_hasFDerivAt`), with the asymptotic variance as the quadratic form of
the gradient in the covariance matrix of the influence functions. The results here have a vector
valued `g` and a joint Gaussian limit, and they need only convergence in distribution of
`√n (T n - θ)`, not an asymptotically linear expansion. For a real valued `g` and asymptotically
linear inputs both give the same limit law: with `κ` a singleton, `D S Dᵀ` is the quadratic form
of the gradient. `CausalInference.Estimation.DeltaMethodSeveralSamples` treats independent
samples of different sizes, which are outside the one sample model used here.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, Theorem 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']

/-- **The vector delta method.** Let `√n (T n - θ)` converge in distribution to `Y` with law
`N(0, S)`, `S` positive semidefinite, and let `g : ℝ^ι → ℝ^κ` be differentiable at `θ` with
Jacobian matrix `D` (derivative `x ↦ D x`). If each `√n (g (T n) - g θ)` is almost everywhere
measurable, then `√n (g (T n) - g θ)` converges in distribution to every random vector with law
`N(0, D S Dᵀ)`. -/
theorem _root_.MeasureTheory.TendstoInDistribution.delta_method_multivariateGaussian
    {T : ℕ → Ω → EuclideanSpace ℝ ι} {θ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) {Y : Ω' → EuclideanSpace ℝ ι}
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (T n ω - θ)) atTop Y
      (fun _ ↦ μ) P') (hY : HasLaw Y (multivariateGaussian 0 S) P')
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ} {D : Matrix κ ι ℝ}
    (hg : HasFDerivAt g (matrixCLM D) θ)
    (hgm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) • (g (T n ω) - g θ)) μ)
    {Y' : Ω'' → EuclideanSpace ℝ κ} (hY' : HasLaw Y' (multivariateGaussian 0 (D * S * Dᵀ)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (g (T n ω) - g θ)) atTop Y'
      (fun _ ↦ μ) P'' := by
  have h1 : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (g (T n ω) - g θ)) atTop
      (fun ω ↦ matrixCLM D (Y ω)) (fun _ ↦ μ) P' := hT.delta_method hg hgm
  have hlaw : HasLaw (fun ω ↦ matrixCLM D (Y ω)) (multivariateGaussian 0 (D * S * Dᵀ)) P' := by
    have h := HasLaw.matrixCLM_multivariateGaussian hS hY D
    rwa [map_zero] at h
  exact h1.of_hasLaw hlaw hY'

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {O : ℕ → Ω → 𝒪}

/-- **The vector delta method for a sample mean.** For an i.i.d. sample, a measurable
`f : 𝒪 → ℝ^ι` with `f (O 0)` square integrable and mean `m`, and `g : ℝ^ι → ℝ^κ` differentiable
at `m` with Jacobian matrix `D`, if each `√n (g (P_n f) - g m)` is almost everywhere measurable
(`P_n f = n⁻¹ ∑_{i < n} f (O i)`), then it converges in distribution to every random vector with
law `N(0, D Σ Dᵀ)`, `Σ` the covariance matrix of the coordinates of `f (O 0)`. -/
theorem IsIIDSample.delta_method_multivariateGaussian (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ} {D : Matrix κ ι ℝ}
    (hg : HasFDerivAt g (matrixCLM D) (μ[fun ω ↦ f (O 0 ω)]))
    (hgm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) •
      (g ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) - g (μ[fun ω ↦ f (O 0 ω)]))) μ)
    {Y' : Ω'' → EuclideanSpace ℝ κ}
    (hY' : HasLaw Y' (multivariateGaussian 0
      (D * covMatrix μ (fun i ω ↦ f (O 0 ω) i) * Dᵀ)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (g ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) - g (μ[fun ω ↦ f (O 0 ω)]))) atTop Y'
      (fun _ ↦ μ) P'' := by
  set S := covMatrix μ (fun i ω ↦ f (O 0 ω) i)
  have hS : S.PosSemidef :=
    posSemidef_covMatrix fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf2
  have hclt : TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω) - μ[fun ω ↦ f (O 0 ω)])) atTop id
      (fun _ ↦ μ) (multivariateGaussian 0 S) :=
    hO.tendstoInDistribution_multivariateGaussian hf hf2 HasLaw.id
  exact TendstoInDistribution.delta_method_multivariateGaussian
    (T := fun n ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) (θ := μ[fun ω ↦ f (O 0 ω)])
    hS hclt HasLaw.id hg hgm hY'

/-- **The vector delta method for asymptotically linear estimators.** Let `θhat i` be
asymptotically linear at `θ i` with influence functions `φ i` for the same i.i.d. sample, each
`θhat i n` almost everywhere measurable, and let `g : ℝ^ι → ℝ^κ` be differentiable at `θ` with
Jacobian matrix `D`. If each `√n (g (θhat n) - g θ)` is almost everywhere measurable, it converges
in distribution to every random vector with law `N(0, D Σ Dᵀ)`, `Σ` the covariance matrix of the
influence functions. -/
theorem IsAsymptoticallyLinear.delta_method_multivariateGaussian (hO : IsIIDSample O μ)
    {θhat : ι → ℕ → Ω → ℝ} {θ : ι → ℝ} {φ : ι → 𝒪 → ℝ}
    (h : ∀ i, IsAsymptoticallyLinear (θhat i) (θ i) (φ i) O μ)
    (hmeas : ∀ i n, AEMeasurable (θhat i n) μ) {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ}
    {D : Matrix κ ι ℝ} (hg : HasFDerivAt g (matrixCLM D) (WithLp.toLp 2 θ))
    (hgm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) •
      (g (WithLp.toLp 2 (fun i ↦ θhat i n ω)) - g (WithLp.toLp 2 θ))) μ)
    {Y' : Ω'' → EuclideanSpace ℝ κ}
    (hY' : HasLaw Y' (multivariateGaussian 0
      (D * covMatrix μ (fun i ω ↦ φ i (O 0 ω)) * Dᵀ)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (g (WithLp.toLp 2 (fun i ↦ θhat i n ω)) - g (WithLp.toLp 2 θ))) atTop Y'
      (fun _ ↦ μ) P'' := by
  set S := covMatrix μ (fun i ω ↦ φ i (O 0 ω))
  have hS : S.PosSemidef := posSemidef_covMatrix fun i ↦ (h i).memLp
  have hjoint : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (fun i ↦ θhat i n ω) - WithLp.toLp 2 θ : EuclideanSpace ℝ ι)) atTop id
      (fun _ ↦ μ) (multivariateGaussian 0 S) :=
    IsAsymptoticallyLinear.tendstoInDistribution_multivariateGaussian hO h hmeas HasLaw.id
  exact TendstoInDistribution.delta_method_multivariateGaussian
    (T := fun n ω ↦ WithLp.toLp 2 (fun i ↦ θhat i n ω)) (θ := WithLp.toLp 2 θ)
    hS hjoint HasLaw.id hg hgm hY'

end CausalInference
