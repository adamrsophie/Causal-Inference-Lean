/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HierarchicalPosterior

/-!
# The posterior predictive law

Given a posterior `π(· | y)` on the parameter space and a sampling kernel `ξ ↦ Q_ξ` for future
data, the **posterior predictive law** is the mixture `∫ Q_ξ dπ(ξ | y)` (`posteriorPredictive`,
Mathlib's composition `Q ∘ₘ π`).

* `posteriorPredictive_likelihoodKernel`: if the future data have the density `q(ξ, z)` with
  respect to `ν'`, the predictive law has the density `z ↦ ∫ q(ξ, z) dπ(ξ | y)`.
* `posteriorPredictive_posterior` (with Bayes' theorem): for almost every `y` under the marginal
  law of the observed data, the predictive law built from the posterior kernel `κ†μ` has the
  density `z ↦ Z(y)⁻¹ ∫ q(ξ, z) p(ξ, y) dμ(ξ)`, where `p` is the density of the observed data
  and `Z(y) = ∫ p(ξ, y) dμ(ξ)`, positive and finite at these `y`.

## Main definitions

* `posteriorPredictive`.

## Main results

* `posteriorPredictive_likelihoodKernel`, `posteriorPredictive_posterior`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ξ Y Z : Type*} [MeasurableSpace Ξ] [MeasurableSpace Y] [MeasurableSpace Z]

instance sFinite_normalizedPosterior (μ : Measure Ξ) [SFinite μ] (L : Ξ → ℝ≥0∞) :
    SFinite (normalizedPosterior μ L) := by
  unfold normalizedPosterior
  infer_instance

/-- The **posterior predictive law** `∫ Q_ξ dπ(ξ)` of future data with the sampling kernel `Q`
under the posterior `π`. -/
noncomputable def posteriorPredictive (post : Measure Ξ) (Q : Kernel Ξ Z) : Measure Z :=
  Q ∘ₘ post

/-- **The predictive density**: if the future data have the density `q(ξ, z)` with respect to
`ν'`, the predictive law has the density `z ↦ ∫ q(ξ, z) dπ(ξ)` with respect to `ν'`. -/
theorem posteriorPredictive_likelihoodKernel {ν' : Measure Z} [SFinite ν'] {q : Ξ → Z → ℝ≥0∞}
    (hq : Measurable (Function.uncurry q)) (post : Measure Ξ) [SFinite post] :
    posteriorPredictive post (likelihoodKernel ν' q) =
      ν'.withDensity fun z => ∫⁻ ξ, q ξ z ∂post :=
  comp_likelihoodKernel hq post

/-- **The predictive law given the data, through Bayes' theorem.** Let the observed data have
the density `p(ξ, y)` with respect to `ν` (finite likelihood kernel, finite prior `μ` on a
standard Borel space) and the future data the density `q(ξ, z)` with respect to `ν'`. For almost
every `y` under the marginal law `κ ∘ μ`, `0 < Z(y) < ∞` and the predictive law built from the
posterior `(κ†μ)(y)` has the density `z ↦ Z(y)⁻¹ ∫ q(ξ, z) p(ξ, y) dμ(ξ)` with respect to
`ν'`. -/
theorem posteriorPredictive_posterior [StandardBorelSpace Ξ] [Nonempty Ξ] {ν : Measure Y}
    [SFinite ν] {μ : Measure Ξ} [IsFiniteMeasure μ] {p : Ξ → Y → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) [IsFiniteKernel (likelihoodKernel ν p)]
    {ν' : Measure Z} [SFinite ν'] {q : Ξ → Z → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) :
    ∀ᵐ y ∂(likelihoodKernel ν p ∘ₘ μ), 0 < ∫⁻ ξ, p ξ y ∂μ ∧ ∫⁻ ξ, p ξ y ∂μ < ∞ ∧
      posteriorPredictive (((likelihoodKernel ν p)†μ) y) (likelihoodKernel ν' q) =
        ν'.withDensity fun z => (∫⁻ ξ, p ξ y ∂μ)⁻¹ * ∫⁻ ξ, q ξ z * p ξ y ∂μ := by
  filter_upwards [posterior_likelihoodKernel (μ := μ) hp] with y ⟨h0, htop, hpost⟩
  refine ⟨h0, htop, ?_⟩
  rw [hpost, posteriorPredictive_likelihoodKernel hq]
  congr 1
  funext z
  rw [normalizedPosterior, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ hp.of_uncurry_right hq.of_uncurry_right, smul_eq_mul]
  simp only [Pi.mul_apply, mul_comm (p _ y)]

end MetaAnalysis

end CausalInference
