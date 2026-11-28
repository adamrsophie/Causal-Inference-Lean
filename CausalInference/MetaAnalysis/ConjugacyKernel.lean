/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.Conjugacy
public import CausalInference.MetaAnalysis.Examples
public import Mathlib.Probability.Kernel.Posterior

/-!
# Meta-analysis: normal-normal conjugacy for the posterior kernel

`MetaAnalysis.Conjugacy` computes the normalized posterior `Z(y)⁻¹ · L(·; y) · prior` of the
mean effect for each data vector `y`. This file identifies it with Mathlib's posterior kernel
`κ†μ` (`ProbabilityTheory.posterior`, the disintegration of the joint law of parameter and data
with respect to the data), which is determined only almost everywhere under the marginal law of
the data.

**The model.** The likelihood kernel `θ ↦ ⊗ᵢ N(θ, sᵢ)` (`commonEffectKernel`, `sᵢ > 0`) and the
prior `μ = N(θ₀, σ₀²)`, `σ₀² > 0`. In the random effects model `sᵢ = vᵢ + τ²` with `τ²` known.

**Results.**

* The marginal law of the data has the density `Z(y) = ∫ L(θ; y) dμ(θ)` with respect to Lebesgue
  measure (`comp_commonEffectKernel`).
* **Conjugacy** (`posterior_commonEffectKernel`): for almost every `y` under the marginal law,
  `(κ†μ)(y) = N(posteriorMean θ₀ σ₀² s y, posteriorVariance σ₀² s)`. Proof: the kernel
  `y ↦ N(M(y), V)` (`gaussianPosteriorKernel`) reproduces the joint law,
  `(κ ∘ μ) ⊗ η = swap(μ ⊗ κ)`, on rectangles `B × A`, by the normalized density form of the
  posterior and Tonelli; uniqueness of the disintegration
  (`ProbabilityTheory.ae_eq_posterior_of_compProd_eq`) concludes.
* The random effects form (`posterior_randomEffectsKernel`) with `sᵢ = vᵢ + τ²`.

**Instance.** For the variances `(1, 1/2, 1/4)` of the three study example and the prior
`N(0, 1)`, almost surely the posterior is `N((y₁ + 2 y₂ + 4 y₃)/8, 1/8)`; at the observed
`y = (0, 1, 2)` the mean function takes the value `5/4` (`example_posteriorKernel`). The value of
the posterior kernel at one data vector has no meaning of its own: the kernel is defined up to a
null set of the marginal law.

## Main definitions

* `commonEffectKernel`, `gaussianPosteriorKernel`.

## Main results

* `commonEffectKernel_apply`, `comp_commonEffectKernel`, `posterior_commonEffectKernel`,
  `posterior_randomEffectsKernel`, `example_posteriorKernel`.
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι]

/-- The joint likelihood `(θ, y) ↦ ∏ᵢ φ(yᵢ; θ, sᵢ)` is measurable. -/
theorem measurable_commonEffectLikelihood (s : ι → ℝ) :
    Measurable (Function.uncurry fun θ (y : ι → ℝ) =>
      ENNReal.ofReal (commonEffectLikelihood s θ y)) := by
  unfold commonEffectLikelihood gaussianPDFReal
  fun_prop

/-- The **likelihood kernel** `θ ↦ ⊗ᵢ N(θ, sᵢ)`, as the kernel of densities
`∏ᵢ φ(yᵢ; θ, sᵢ)` with respect to Lebesgue measure. -/
noncomputable def commonEffectKernel (s : ι → ℝ) : Kernel ℝ (ι → ℝ) :=
  Kernel.withDensity (Kernel.const ℝ (Measure.pi fun _ : ι => (volume : Measure ℝ)))
    fun θ y => ENNReal.ofReal (commonEffectLikelihood s θ y)

/-- For `sᵢ > 0` the likelihood kernel at `θ` is `⊗ᵢ N(θ, sᵢ)`. -/
theorem commonEffectKernel_apply {s : ι → ℝ} (hs : ∀ i, 0 < s i) (θ : ℝ) :
    commonEffectKernel s θ = Measure.pi fun i => gaussianReal θ (s i).toNNReal := by
  rw [commonEffectKernel, Kernel.withDensity_apply _ (measurable_commonEffectLikelihood s),
    Kernel.const_apply, ← commonEffectFamily_law hs θ]
  rfl

theorem isMarkovKernel_commonEffectKernel {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    IsMarkovKernel (commonEffectKernel s) :=
  ⟨fun θ => by rw [commonEffectKernel_apply hs]; infer_instance⟩

/-- The likelihood kernel is finite for every `s`: of mass `1` when all `sᵢ > 0`, and `0` when
some `sᵢ ≤ 0`, where the density vanishes. -/
instance (s : ι → ℝ) : IsFiniteKernel (commonEffectKernel s) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun θ => ?_⟩⟩
  by_cases hs : ∀ i, 0 < s i
  · rw [commonEffectKernel_apply hs]
    simp
  · push Not at hs
    obtain ⟨j, hj⟩ := hs
    have h0 : (fun y : ι → ℝ => ENNReal.ofReal (commonEffectLikelihood s θ y)) = 0 := by
      funext y
      have hpdf : gaussianPDFReal θ (s j).toNNReal (y j) = 0 := by
        simp [gaussianPDFReal, Real.toNNReal_of_nonpos hj]
      rw [commonEffectLikelihood, Finset.prod_eq_zero (Finset.mem_univ j) hpdf]
      simp
    rw [commonEffectKernel, Kernel.withDensity_apply _ (measurable_commonEffectLikelihood s),
      Kernel.const_apply, h0, withDensity_zero]
    simp

/-- The candidate posterior kernel `y ↦ N(posteriorMean θ₀ σ₀² s y, posteriorVariance σ₀² s)`. -/
noncomputable def gaussianPosteriorKernel (θ0 σ02 : ℝ) (s : ι → ℝ) : Kernel (ι → ℝ) ℝ where
  toFun y := gaussianReal (posteriorMean θ0 σ02 s y) (posteriorVariance σ02 s).toNNReal
  measurable' := by
    have hM : Measurable fun y : ι → ℝ => posteriorMean θ0 σ02 s y := by
      unfold posteriorMean
      exact (measurable_const.add (measurable_const.mul (measurable_ivwEstimate s))).div_const _
    exact measurable_gaussianReal.comp (hM.prodMk measurable_const)

instance (θ0 σ02 : ℝ) (s : ι → ℝ) : IsMarkovKernel (gaussianPosteriorKernel θ0 σ02 s) :=
  ⟨fun y => by
    change IsProbabilityMeasure (gaussianReal _ _)
    infer_instance⟩

/-- **The marginal law of the data**: under the prior `μ`, the data have the density
`Z(y) = ∫ ∏ᵢ φ(yᵢ; θ, sᵢ) dμ(θ)` with respect to Lebesgue measure. -/
theorem comp_commonEffectKernel (s : ι → ℝ) (μ : Measure ℝ) [SFinite μ] :
    commonEffectKernel s ∘ₘ μ = (Measure.pi fun _ : ι => (volume : Measure ℝ)).withDensity
      fun y => ∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood s θ y) ∂μ := by
  have hLm := measurable_commonEffectLikelihood s
  ext B hB
  rw [Measure.bind_apply hB (Kernel.measurable _).aemeasurable, withDensity_apply _ hB]
  simp_rw [commonEffectKernel, Kernel.withDensity_apply' _ hLm, Kernel.const_apply]
  exact lintegral_lintegral_swap hLm.aemeasurable

/-- **Normal-normal conjugacy for the posterior kernel**: for `σ₀² > 0` and `sᵢ > 0`, the
posterior kernel of the likelihood kernel `θ ↦ ⊗ᵢ N(θ, sᵢ)` under the prior `N(θ₀, σ₀²)` is,
for almost every data vector under the marginal law,
`N(posteriorMean θ₀ σ₀² s y, posteriorVariance σ₀² s)`. -/
theorem posterior_commonEffectKernel [Nonempty ι] {θ0 σ02 : ℝ} (hσ0 : 0 < σ02) {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) :
    ∀ᵐ y ∂(commonEffectKernel s ∘ₘ gaussianReal θ0 σ02.toNNReal),
      ((commonEffectKernel s)†(gaussianReal θ0 σ02.toNNReal)) y =
        gaussianReal (posteriorMean θ0 σ02 s y) (posteriorVariance σ02 s).toNNReal := by
  have := isMarkovKernel_commonEffectKernel hs
  set μ := gaussianReal θ0 σ02.toNNReal
  set ν := Measure.pi fun _ : ι => (volume : Measure ℝ)
  set κ := commonEffectKernel s
  set η := gaussianPosteriorKernel θ0 σ02 s
  set L : ℝ → (ι → ℝ) → ℝ≥0∞ := fun θ y => ENNReal.ofReal (commonEffectLikelihood s θ y)
  set Z : (ι → ℝ) → ℝ≥0∞ := fun y => ∫⁻ θ, L θ y ∂μ
  have hLm : Measurable (Function.uncurry L) := measurable_commonEffectLikelihood s
  have hZm : Measurable Z := hLm.lintegral_prod_left'
  have hκB : ∀ θ B, κ θ B = ∫⁻ y in B, L θ y ∂ν := fun θ B => by
    simp only [κ, commonEffectKernel]
    rw [Kernel.withDensity_apply' _ hLm, Kernel.const_apply]
  have hη : ∀ y A, MeasurableSet A → Z y * η y A = ∫⁻ θ in A, L θ y ∂μ := by
    intro y A hA
    obtain ⟨h0, htop, heq⟩ := posterior_commonEffectLikelihood (θ0 := θ0) hσ0 hs y
    change Z y * gaussianReal _ _ A = _
    rw [← heq, smul_apply, withDensity_apply _ hA, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel h0.ne' htop, one_mul]
  have hjoint : (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap := by
    refine Measure.ext_prod fun {B A} hB hA => ?_
    rw [Measure.compProd_apply_prod hB hA, Measure.map_apply measurable_swap (hB.prod hA),
      Set.preimage_swap_prod, Measure.compProd_apply_prod hA hB, comp_commonEffectKernel,
      restrict_withDensity hB, lintegral_withDensity_eq_lintegral_mul _ hZm (η.measurable_coe hA)]
    simp only [Pi.mul_apply, hκB]
    simp only [L, Z] at hη ⊢
    simp_rw [hη _ A hA]
    exact lintegral_lintegral_swap ((hLm.comp measurable_swap).aemeasurable)
  filter_upwards [ae_eq_posterior_of_compProd_eq hjoint] with y hy
  rw [← hy]
  rfl

/-- **Conjugacy for the random effects posterior kernel**: with known `τ² ≥ 0`, within study
variances `vᵢ > 0` and the prior `N(θ₀, σ₀²)`, the posterior kernel of `θ ↦ ⊗ᵢ N(θ, vᵢ + τ²)`
is almost surely `N(posteriorMean θ₀ σ₀² (v + τ²) y, posteriorVariance σ₀² (v + τ²))`. -/
theorem posterior_randomEffectsKernel [Nonempty ι] {θ0 σ02 τ2 : ℝ} (hσ0 : 0 < σ02)
    (hτ : 0 ≤ τ2) {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ᵐ y ∂(commonEffectKernel (fun i => v i + τ2) ∘ₘ gaussianReal θ0 σ02.toNNReal),
      ((commonEffectKernel fun i => v i + τ2)†(gaussianReal θ0 σ02.toNNReal)) y =
        gaussianReal (posteriorMean θ0 σ02 (fun i => v i + τ2) y)
          (posteriorVariance σ02 fun i => v i + τ2).toNNReal :=
  posterior_commonEffectKernel hσ0 fun i => add_pos_of_pos_of_nonneg (hv i) hτ

/-- **The posterior kernel on the example**: with the variances `(1, 1/2, 1/4)` and the prior
`N(0, 1)`, the posterior precision is `8`; almost surely the posterior is
`N((y₁ + 2 y₂ + 4 y₃)/8, 1/8)`, and the mean function is `5/4` at the observed `(0, 1, 2)`. -/
theorem example_posteriorKernel :
    (∀ᵐ y ∂(commonEffectKernel exampleVar ∘ₘ gaussianReal 0 (1 : ℝ).toNNReal),
      ((commonEffectKernel exampleVar)†(gaussianReal 0 (1 : ℝ).toNNReal)) y =
        gaussianReal ((y 0 + 2 * y 1 + 4 * y 2) / 8) (1 / 8 : ℝ).toNNReal) ∧
      posteriorMean 0 1 exampleVar exampleY = 5 / 4 := by
  have hP : posteriorPrecision 1 exampleVar = 8 := by
    rw [posteriorPrecision, example_sum_ivWeight]; norm_num
  have hM : ∀ y : Fin 3 → ℝ, posteriorMean 0 1 exampleVar y = (y 0 + 2 * y 1 + 4 * y 2) / 8 := by
    intro y
    rw [posteriorMean, hP, example_sum_ivWeight, ivwEstimate, PopulationAdjustment.weightedMean,
      example_sum_ivWeight]
    norm_num [ivWeight, exampleVar, Fin.sum_univ_three]
    ring
  refine ⟨?_, by rw [hM]; norm_num [exampleY]⟩
  filter_upwards [posterior_commonEffectKernel (θ0 := 0) one_pos exampleVar_pos] with y hy
  rw [hy, hM, posteriorVariance, hP]

end MetaAnalysis

end CausalInference
