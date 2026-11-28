/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.GaussianLikelihood
public import CausalInference.MetaAnalysis.RandomEffects

/-!
# Meta-analysis: normal-normal conjugacy for the mean effect

Given the between study variance `τ²`, the random effects estimates are independent with
`Yᵢ ~ N(θ, sᵢ)`, `sᵢ = vᵢ + τ²` (`IsGaussianRandomEffectsModel.hasLaw_pi`), so the likelihood of
the mean effect is the Gaussian common effect likelihood `θ ↦ ∏ᵢ φ(yᵢ; θ, sᵢ)`
(`commonEffectLikelihood`). Put a normal prior `θ ~ N(θ₀, σ₀²)`, `σ₀² > 0`, on the mean effect.

**Conjugacy.** The posterior, the prior reweighted by the likelihood and normalized by the
marginal likelihood `Z = ∫ L dΠ`, is normal (`posterior_commonEffectLikelihood`):
`0 < Z < ∞` and `Z⁻¹ • Π.withDensity L = N(m*, v*)`, where

* the **posterior precision** is the sum of the prior precision and the data precision,
  `1 / v* = 1 / σ₀² + ∑ᵢ 1 / sᵢ` (`posteriorPrecision`);
* the **posterior mean** is the precision weighted average of the prior mean and the pooled
  estimate, `m* = (θ₀ / σ₀² + (∑ wᵢ) θ̂) / (1 / σ₀² + ∑ wᵢ)`, `wᵢ = 1 / sᵢ` (`posteriorMean`).

The posterior is written in the form used for the beta and binomial update of
`BiasAnalysis.Bayesian` (`betaBinomial_posterior`): the normalizing constant and the normalized
measure. In the random effects model the prior on `τ²` plays no role given `τ²`
(`posterior_randomEffects`).

**Flat prior limit.** As `σ₀² → ∞` the posterior mean tends to the pooled estimate `θ̂` and the
posterior variance to `1 / ∑ wᵢ` (`tendsto_posteriorMean_atTop`,
`tendsto_posteriorVariance_atTop`): the inverse variance pooled estimate and its variance are the
flat prior limit of the Bayesian analysis.

## Main definitions

* `posteriorPrecision`, `posteriorVariance`, `posteriorMean`.

## Main results

* `gaussianPDFReal_mul_commonEffectLikelihood`, `posterior_commonEffectLikelihood`,
  `posterior_randomEffects`.
* `tendsto_posteriorMean_atTop`, `tendsto_posteriorVariance_atTop`.

## References

* J. P. T. Higgins, S. G. Thompson and D. J. Spiegelhalter, *A re-evaluation of random-effects
  meta-analysis*, Journal of the Royal Statistical Society A 172 (2009).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι]

/-- The **posterior precision** `1 / σ₀² + ∑ᵢ 1 / sᵢ`: prior precision plus data precision. -/
noncomputable def posteriorPrecision (σ02 : ℝ) (s : ι → ℝ) : ℝ :=
  1 / σ02 + ∑ i, ivWeight s i

/-- The **posterior variance** `v* = 1 / (1 / σ₀² + ∑ᵢ 1 / sᵢ)`. -/
noncomputable def posteriorVariance (σ02 : ℝ) (s : ι → ℝ) : ℝ :=
  1 / posteriorPrecision σ02 s

/-- The **posterior mean**, the precision weighted average of the prior mean `θ₀` and the pooled
estimate `θ̂`: `m* = (θ₀ / σ₀² + (∑ wᵢ) θ̂) / (1 / σ₀² + ∑ wᵢ)`. -/
noncomputable def posteriorMean (θ0 σ02 : ℝ) (s y : ι → ℝ) : ℝ :=
  (θ0 / σ02 + (∑ i, ivWeight s i) * ivwEstimate s y) / posteriorPrecision σ02 s

theorem posteriorPrecision_pos {σ02 : ℝ} (hσ0 : 0 < σ02) {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    0 < posteriorPrecision σ02 s :=
  add_pos_of_pos_of_nonneg (one_div_pos.2 hσ0)
    (Finset.sum_nonneg fun i _ => (ivWeight_pos hs i).le)

theorem posteriorVariance_pos {σ02 : ℝ} (hσ0 : 0 < σ02) {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    0 < posteriorVariance σ02 s :=
  one_div_pos.2 (posteriorPrecision_pos hσ0 hs)

/-- **Prior times likelihood is a multiple of the posterior density**: for `σ₀² > 0` and
`sᵢ > 0` there is a constant `K > 0`, free of `θ`, with
`φ(θ; θ₀, σ₀²) ∏ᵢ φ(yᵢ; θ, sᵢ) = K φ(θ; m*, v*)` for every `θ`. Proof: by the weighted sum of
squares decomposition the exponent is `-(θ - θ₀)² / (2σ₀²) - Q / 2 - (∑ wᵢ)(θ - θ̂)² / 2`, and
completing the square gives `-(θ - m*)² / (2 v*)` plus a constant. -/
theorem gaussianPDFReal_mul_commonEffectLikelihood [Nonempty ι] {θ0 σ02 : ℝ} (hσ0 : 0 < σ02)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) (y : ι → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ θ, gaussianPDFReal θ0 σ02.toNNReal θ * commonEffectLikelihood s θ y =
      K * gaussianPDFReal (posteriorMean θ0 σ02 s y) (posteriorVariance σ02 s).toNNReal θ := by
  have hW := sum_ivWeight_pos hs
  have hA := posteriorPrecision_pos hσ0 hs
  have hV := posteriorVariance_pos hσ0 hs
  set W := ∑ i, ivWeight s i with hWdef
  set A := posteriorPrecision σ02 s with hAdef
  set t := ivwEstimate s y
  set M := posteriorMean θ0 σ02 s y with hM
  set V := posteriorVariance σ02 s with hVdef
  set CL := ∏ i, (√(2 * Real.pi * s i))⁻¹
  have hCL : 0 < CL := Finset.prod_pos fun i _ =>
    inv_pos.2 (Real.sqrt_pos.2 (by have := hs i; positivity))
  set K : ℝ := (√(2 * Real.pi * σ02))⁻¹ * CL * √(2 * Real.pi * V) *
    Real.exp (-(1 / 2) * cochranQ s y - (1 / 2) * (W / (σ02 * A)) * (θ0 - t) ^ 2)
  have hsV : 0 < √(2 * Real.pi * V) := Real.sqrt_pos.2 (by positivity)
  refine ⟨K, by positivity, fun θ => ?_⟩
  rw [commonEffectLikelihood_eq hs]
  simp only [gaussianPDFReal, Real.coe_toNNReal _ hσ0.le, Real.coe_toNNReal _ hV.le]
  have hAV : A * V = 1 := by rw [hVdef, posteriorVariance, ← hAdef, mul_one_div_cancel hA.ne']
  have hAeq : A = 1 / σ02 + W := rfl
  have hMeq : M * A = θ0 / σ02 + W * t := by
    rw [hM, posteriorMean, ← hAdef, div_mul_cancel₀ _ hA.ne']
  have hexp : -(θ - θ0) ^ 2 / (2 * σ02) +
      -(1 / 2) * (cochranQ s y + W * (t - θ) ^ 2) =
      (-(1 / 2) * cochranQ s y - (1 / 2) * (W / (σ02 * A)) * (θ0 - t) ^ 2) +
        -(θ - M) ^ 2 / (2 * V) := by
    have hV' : V = 1 / A := rfl
    rw [hV']
    have hM' : M = (θ0 / σ02 + W * t) / A := by
      rw [← hMeq, mul_div_cancel_right₀ _ hA.ne']
    rw [hM', hAeq]
    field_simp
    ring
  have hQ : ∑ i, ivWeight s i * (y i - θ) ^ 2 = cochranQ s y + W * (t - θ) ^ 2 := by
    rw [cochranQ_eq_sub hs y θ]; ring
  rw [hQ]
  calc (√(2 * Real.pi * σ02))⁻¹ * Real.exp (-(θ - θ0) ^ 2 / (2 * σ02)) *
        (CL * Real.exp (-(1 / 2) * (cochranQ s y + W * (t - θ) ^ 2)))
      = (√(2 * Real.pi * σ02))⁻¹ * CL * Real.exp (-(θ - θ0) ^ 2 / (2 * σ02) +
          -(1 / 2) * (cochranQ s y + W * (t - θ) ^ 2)) := by rw [Real.exp_add]; ring
    _ = K * ((√(2 * Real.pi * V))⁻¹ * Real.exp (-(θ - M) ^ 2 / (2 * V))) := by
      rw [hexp, Real.exp_add]
      have h1 : √(2 * Real.pi * V) * (√(2 * Real.pi * V))⁻¹ = 1 := mul_inv_cancel₀ hsV.ne'
      simp only [K]
      linear_combination (-((√(2 * Real.pi * σ02))⁻¹ * CL *
        Real.exp (-(1 / 2) * cochranQ s y - (1 / 2) * (W / (σ02 * A)) * (θ0 - t) ^ 2) *
        Real.exp (-(θ - M) ^ 2 / (2 * V)))) * h1

/-- **Normal-normal conjugacy for the mean effect.** Let the estimates have the likelihood
`L(θ) = ∏ᵢ φ(yᵢ; θ, sᵢ)`, `sᵢ > 0`, and let the prior be `θ ~ N(θ₀, σ₀²)`, `σ₀² > 0`. The
marginal likelihood `Z = ∫ L dΠ` is positive and finite, and the posterior `Z⁻¹ • Π.withDensity L`
is the normal law `N(m*, v*)`, with precision `1 / v* = 1 / σ₀² + ∑ᵢ 1 / sᵢ` and mean the
precision weighted average `m*` of `θ₀` and the pooled estimate. -/
theorem posterior_commonEffectLikelihood [Nonempty ι] {θ0 σ02 : ℝ} (hσ0 : 0 < σ02)
    {s : ι → ℝ} (hs : ∀ i, 0 < s i) (y : ι → ℝ) :
    0 < ∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood s θ y) ∂gaussianReal θ0 σ02.toNNReal ∧
      ∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood s θ y) ∂gaussianReal θ0 σ02.toNNReal ≠ ∞ ∧
      (∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood s θ y) ∂gaussianReal θ0 σ02.toNNReal)⁻¹ •
          (gaussianReal θ0 σ02.toNNReal).withDensity
            (fun θ => ENNReal.ofReal (commonEffectLikelihood s θ y)) =
        gaussianReal (posteriorMean θ0 σ02 s y) (posteriorVariance σ02 s).toNNReal := by
  obtain ⟨K, hK, hf⟩ := gaussianPDFReal_mul_commonEffectLikelihood (θ0 := θ0) hσ0 hs y
  set M := posteriorMean θ0 σ02 s y
  set V := posteriorVariance σ02 s
  have hσne : σ02.toNNReal ≠ 0 := by simpa using hσ0
  have hVne : V.toNNReal ≠ 0 := by simpa using posteriorVariance_pos hσ0 hs
  have hLm : Measurable fun θ => ENNReal.ofReal (commonEffectLikelihood s θ y) := by
    unfold commonEffectLikelihood gaussianPDFReal
    fun_prop
  have hpl : ∀ θ, gaussianPDF θ0 σ02.toNNReal θ * ENNReal.ofReal (commonEffectLikelihood s θ y) =
      ENNReal.ofReal K * gaussianPDF M V.toNNReal θ := by
    intro θ
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), hf θ,
      ENNReal.ofReal_mul hK.le]
  have hZ : ∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood s θ y) ∂gaussianReal θ0 σ02.toNNReal =
      ENNReal.ofReal K := by
    rw [gaussianReal_of_var_ne_zero θ0 hσne,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hLm]
    simp only [Pi.mul_apply, hpl]
    rw [lintegral_const_mul _ (measurable_gaussianPDF _ _), lintegral_gaussianPDF_eq_one _ hVne,
      mul_one]
  rw [hZ]
  refine ⟨ENNReal.ofReal_pos.2 hK, ENNReal.ofReal_ne_top, ?_⟩
  rw [gaussianReal_of_var_ne_zero θ0 hσne, ← withDensity_mul _ (measurable_gaussianPDF _ _) hLm,
    ← withDensity_smul _ ((measurable_gaussianPDF _ _).mul hLm),
    gaussianReal_of_var_ne_zero M hVne]
  congr 1
  funext θ
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hpl]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hK).ne' ENNReal.ofReal_ne_top,
    one_mul]

/-- **Conjugacy in the random effects model**: given `τ² ≥ 0`, with the random effects
likelihood `θ ↦ ∏ᵢ φ(yᵢ; θ, vᵢ + τ²)` (the density of the marginal law of
`IsGaussianRandomEffectsModel.hasLaw_pi`) and the prior `N(θ₀, σ₀²)`, the posterior of the mean
effect is `N(m*, v*)` with precision `1 / σ₀² + ∑ᵢ 1 / (vᵢ + τ²)` and mean the precision
weighted average of `θ₀` and the random effects pooled estimate. -/
theorem posterior_randomEffects [Nonempty ι] {θ0 σ02 τ2 : ℝ} (hσ0 : 0 < σ02) (hτ : 0 ≤ τ2)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) (y : ι → ℝ) :
    (∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood (fun i => v i + τ2) θ y)
        ∂gaussianReal θ0 σ02.toNNReal)⁻¹ •
        (gaussianReal θ0 σ02.toNNReal).withDensity
          (fun θ => ENNReal.ofReal (commonEffectLikelihood (fun i => v i + τ2) θ y)) =
      gaussianReal (posteriorMean θ0 σ02 (fun i => v i + τ2) y)
        (posteriorVariance σ02 fun i => v i + τ2).toNNReal :=
  (posterior_commonEffectLikelihood hσ0 (fun i => add_pos_of_pos_of_nonneg (hv i) hτ) y).2.2

/-- **The flat prior limit of the posterior mean**: as `σ₀² → ∞` the posterior mean tends to the
pooled estimate `θ̂`, whatever the prior mean. -/
theorem tendsto_posteriorMean_atTop [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) (θ0 : ℝ)
    (y : ι → ℝ) :
    Tendsto (fun σ02 => posteriorMean θ0 σ02 s y) atTop (𝓝 (ivwEstimate s y)) := by
  have hW := sum_ivWeight_pos hs
  have h0 : Tendsto (fun σ02 : ℝ => σ02⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hnum : Tendsto (fun σ02 : ℝ => θ0 / σ02 + (∑ i, ivWeight s i) * ivwEstimate s y) atTop
      (𝓝 ((∑ i, ivWeight s i) * ivwEstimate s y)) := by
    simpa [div_eq_mul_inv] using (h0.const_mul θ0).add_const ((∑ i, ivWeight s i) *
      ivwEstimate s y)
  have hden : Tendsto (fun σ02 : ℝ => posteriorPrecision σ02 s) atTop
      (𝓝 (∑ i, ivWeight s i)) := by
    simpa [posteriorPrecision, one_div] using h0.add_const (∑ i, ivWeight s i)
  have := hnum.div hden hW.ne'
  rwa [mul_div_cancel_left₀ _ hW.ne'] at this

/-- **The flat prior limit of the posterior variance**: as `σ₀² → ∞` the posterior variance tends
to `1 / ∑ᵢ 1 / sᵢ`, the variance of the pooled estimate. -/
theorem tendsto_posteriorVariance_atTop [Nonempty ι] {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    Tendsto (fun σ02 => posteriorVariance σ02 s) atTop (𝓝 (1 / ∑ i, ivWeight s i)) := by
  have hW := sum_ivWeight_pos hs
  have h0 : Tendsto (fun σ02 : ℝ => σ02⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hden : Tendsto (fun σ02 : ℝ => posteriorPrecision σ02 s) atTop
      (𝓝 (∑ i, ivWeight s i)) := by
    simpa [posteriorPrecision, one_div] using h0.add_const (∑ i, ivWeight s i)
  exact tendsto_const_nhds.div hden hW.ne'

end MetaAnalysis

end CausalInference
