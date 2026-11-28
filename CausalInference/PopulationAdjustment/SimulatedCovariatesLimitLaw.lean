/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.SimulatedCovariatesConstruction
public import CausalInference.PopulationAdjustment.WeightedNormalityContrast
public import CausalInference.Estimation.AsymptoticLinear

/-!
# Limit law of the simulated average

For a fixed outcome surface `g`, the average of `g` over `n` simulated covariate vectors
`X'_i = nortaMap μ (Z_i)`, with `Z_i` i.i.d. `N(0, R)`, satisfies the central limit theorem
`√n (n⁻¹ ∑_{i < n} g(X'_i) - ∫ g d(nortaLaw R μ)) ⇒ N(0, Var g)` with the variance under the
simulated law (`tendstoInDistribution_simulated_sampleMean`). This is the Monte Carlo error of the
simulation at the limit surface. When the simulated average is contrasted with an independent
comparator whose scaled error has a Gaussian limit `N(0, w)`, the contrast has the limit
`N(0, Var g + w)` (`tendstoInDistribution_simulated_contrast`).

The variability of the fitted surface `g = h θ̂_n t` is not part of these statements: they hold
at the limit coefficient.

## Main results

* `tendstoInDistribution_sampleMean_of_map`: the central limit theorem for an i.i.d. sample stated
  through the law of one observation.
* `tendstoInDistribution_simulated_sampleMean`, `tendstoInDistribution_simulated_contrast`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology BiasAnalysis.Distributions
open scoped NNReal

/-- **The central limit theorem for a sample mean, through the law of one observation.** For an
i.i.d. sample `O` whose observations have the law `ν` and a measurable `g` square integrable
under `ν`, `√n (P_n g - ∫ g dν)` converges in distribution to every variable with law
`N(0, ∫ (g - ∫ g dν)² dν)`. -/
theorem tendstoInDistribution_sampleMean_of_map {Ω 𝒪 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝒪] {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O P) {ν : Measure 𝒪} (hν : P.map (O 0) = ν) {g : 𝒪 → ℝ}
    (hg : Measurable g) (hg2 : MemLp g 2 ν) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (sampleMean g O n ω - ∫ x, g x ∂ν))
      atTop Y (fun _ => P) P' := by
  have h0 := hO.aemeasurable 0
  have hf2 : MemLp (fun ω => g (O 0 ω)) 2 P := by
    rw [← hν] at hg2
    exact hg2.comp_of_map h0
  have hm : P[fun ω => g (O 0 ω)] = ∫ x, g x ∂ν := by
    rw [← hν, integral_map h0 hg.aestronglyMeasurable]
  have hv : P[fun ω => (g (O 0 ω) - P[fun ω => g (O 0 ω)]) ^ 2] =
      ∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν := by
    rw [hm, ← hν, integral_map h0 ((hg.sub_const _).pow_const 2).aestronglyMeasurable, hν]
  have hmeas : ∀ n, AEMeasurable (sampleMean g O n) P :=
    (isSampleMeasurable_sampleMean hg O).aemeasurable hO
  have hclt := (sampleMean_isAsymptoticallyLinear hg hf2).tendstoInDistribution hO hmeas
    (Y := Y) (by simpa only [hv] using hY)
  simpa only [hm] using hclt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℝ} {μ : ι → Measure ℝ}
  {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
  {Z : ℕ → Ξ → EuclideanSpace ℝ ι}

/-- **The Monte Carlo limit law of the simulated average.** For i.i.d. `Z_i ∼ N(0, R)` and a
measurable surface `g` square integrable under the simulated law `ν = nortaLaw R μ`,
`√n (n⁻¹ ∑_{i < n} g(nortaMap μ (Z_i)) - ∫ g dν)` converges in distribution to every variable
with law `N(0, ∫ (g - ∫ g dν)² dν)`. -/
theorem tendstoInDistribution_simulated_sampleMean (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) {g : (ι → ℝ) → ℝ} (hg : Measurable g)
    (hg2 : MemLp g 2 (nortaLaw R μ)) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0
      (∫ x, (g x - ∫ y, g y ∂nortaLaw R μ) ^ 2 ∂nortaLaw R μ).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (sampleMean g (fun i ω => nortaMap μ (Z i ω)) n ω - ∫ x, g x ∂nortaLaw R μ))
      atTop Y (fun _ => P) P' :=
  have h := isIIDSample_nortaMap (μ := μ) hZ hZ0
  tendstoInDistribution_sampleMean_of_map h.1 h.2 hg hg2 hY

/-- **The limit law of a contrast with an independent comparator.** Under the hypotheses of
`tendstoInDistribution_simulated_sampleMean` with limit variance `v`, let `W n` be the scaled
error of a comparator with Gaussian limit `N(0, w)`, independent of the simulated average for
every `n`. Then `√n (n⁻¹ ∑ g(X'_i) - ∫ g dν) + W n` converges in distribution to every variable
with law `N(0, v + w)`. -/
theorem tendstoInDistribution_simulated_contrast (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) {g : (ι → ℝ) → ℝ} (hg : Measurable g)
    (hg2 : MemLp g 2 (nortaLaw R μ)) {v w : ℝ≥0}
    (hv : (∫ x, (g x - ∫ y, g y ∂nortaLaw R μ) ^ 2 ∂nortaLaw R μ).toNNReal = v)
    {W : ℕ → Ξ → ℝ} {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {Y₂ : Ω₂ → ℝ} (hW : TendstoInDistribution W atTop Y₂ (fun _ => P) P₂)
    (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    (hind : ∀ n : ℕ, IndepFun (fun ω => √(n : ℝ) *
      (sampleMean g (fun i ω => nortaMap μ (Z i ω)) n ω - ∫ x, g x ∂nortaLaw R μ)) (W n) P)
    {Ω₃ : Type*} [MeasurableSpace Ω₃] {P₃ : Measure Ω₃} [IsProbabilityMeasure P₃] {Y : Ω₃ → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (v + w)) P₃) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (sampleMean g (fun i ω => nortaMap μ (Z i ω)) n ω - ∫ x, g x ∂nortaLaw R μ) + W n ω)
      atTop Y (fun _ => P) P₃ := by
  subst hv
  exact tendstoInDistribution_add_of_indepFun
    (tendstoInDistribution_simulated_sampleMean hZ hZ0 hg hg2 HasLaw.id) hW hind HasLaw.id hY₂ hY

end PopulationAdjustment

end CausalInference
