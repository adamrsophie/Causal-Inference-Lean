/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HierarchicalPosterior

/-!
# Marginal likelihoods and Bayes factors

The **marginal likelihood** (evidence) of a model with prior `μ` and likelihood `L` is
`p(y) = ∫ L dμ` (`marginalLikelihood`), the normalizer of `normalizedPosterior μ L`. The
**Bayes factor** of model `M₁` against `M₀` is the ratio `p(y | M₁) / p(y | M₀)` of their
marginal likelihoods (`bayesFactor`) (Kass and Raftery 1995).

* `normalizedPosterior_modelIndex`: put a prior `π` on the model index `k ∈ {M₀, M₁}` and, given
  `k`, the prior `μ_k` on the parameter of model `k`. The posterior probability of the model
  index, computed from the joint posterior on `(k, ξ)` with likelihood `L_k(ξ)`, is the
  posterior of `π` with the marginal likelihoods `p(y | M_k)` as likelihood.
* `posterior_odds_eq_bayesFactor_mul`: **posterior odds = Bayes factor × prior odds**.
* `bayesFactor_normal_point`, `example_posterior_odds_normal`: two normal models for one
  observation, `M₀ : y ~ N(0, 1)` and `M₁ : y ~ N(1, 1)`. The Bayes factor is `exp(y - 1/2)`;
  at `y = 1/2` it is `1`, and at `y = 1` with prior odds `1` the posterior odds are `√e`.

## Main definitions

* `marginalLikelihood`, `bayesFactor`.

## Main results

* `normalizedPosterior_modelIndex`, `posterior_odds_eq_bayesFactor_mul`,
  `bayesFactor_normal_point`, `example_posterior_odds_normal`.

## References

* R. E. Kass and A. E. Raftery, *Bayes factors*, Journal of the American Statistical Association
  90 (1995).
* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- The **marginal likelihood** (evidence) `p(y) = ∫ L dμ` of a model with prior `μ` and
likelihood `L`. -/
noncomputable def marginalLikelihood (μ : Measure Ξ) (L : Ξ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ξ, L ξ ∂μ

/-- The **Bayes factor** `p(y | M₁) / p(y | M₀)` of two marginal likelihoods, as a real number;
it is meaningful when both are finite and the second is positive. -/
noncomputable def bayesFactor (ev₁ ev₀ : ℝ≥0∞) : ℝ := ev₁.toReal / ev₀.toReal

/-- **The posterior of the model index**: with a prior `π` on `Bool`, priors `μ k` (probability
laws) on the parameter of each model and measurable likelihoods `L k`, the joint posterior of
`(k, ξ)` under the prior `π ⊗ μ` and the likelihood `L k ξ` gives the model `k` the probability
`normalizedPosterior π (fun k => marginalLikelihood (μ k) (L k)) {k}`. -/
theorem normalizedPosterior_modelIndex (π : Measure Bool) [IsFiniteMeasure π]
    (μ : Bool → Measure Ξ) [∀ k, IsProbabilityMeasure (μ k)] {L : Bool → Ξ → ℝ≥0∞}
    (hL : ∀ k, Measurable (L k)) (k : Bool) :
    letI : IsMarkovKernel (Kernel.ofFunOfCountable μ) := ⟨fun k => inferInstanceAs
      (IsProbabilityMeasure (μ k))⟩
    normalizedPosterior (π ⊗ₘ Kernel.ofFunOfCountable μ) (fun q => L q.1 q.2)
        ({k} ×ˢ Set.univ) =
      normalizedPosterior π (fun k => marginalLikelihood (μ k) (L k)) {k} := by
  have : IsMarkovKernel (Kernel.ofFunOfCountable μ) := ⟨fun k => inferInstanceAs
    (IsProbabilityMeasure (μ k))⟩
  have hm : Measurable fun q : Bool × Ξ => L q.1 q.2 :=
    measurable_from_prod_countable_right hL
  have htot : ∫⁻ q, L q.1 q.2 ∂(π ⊗ₘ Kernel.ofFunOfCountable μ) =
      ∫⁻ k, marginalLikelihood (μ k) (L k) ∂π := by
    rw [Measure.lintegral_compProd hm]
    rfl
  rw [normalizedPosterior_apply _ _ ((measurableSet_singleton k).prod MeasurableSet.univ),
    normalizedPosterior_apply _ _ (measurableSet_singleton k), htot,
    Measure.setLIntegral_compProd hm (measurableSet_singleton k) MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rfl

/-- **Posterior odds equal the Bayes factor times the prior odds** (Kass and Raftery 1995): with
a finite prior `π` on the model index, `π(M₀) > 0`, and marginal likelihoods with
`0 < p(y | M₀) < ∞` and `p(y | M₁) < ∞`,
`P(M₁ | y) / P(M₀ | y) = BF₁₀ · π(M₁) / π(M₀)`. -/
theorem posterior_odds_eq_bayesFactor_mul (π : Measure Bool) [IsFiniteMeasure π]
    (μ : Bool → Measure Ξ) (L : Bool → Ξ → ℝ≥0∞) (hp0 : π {false} ≠ 0)
    (he0 : marginalLikelihood (μ false) (L false) ≠ 0)
    (he0' : marginalLikelihood (μ false) (L false) ≠ ∞)
    (he1' : marginalLikelihood (μ true) (L true) ≠ ∞) :
    (normalizedPosterior π (fun k => marginalLikelihood (μ k) (L k)) {true}).toReal /
        (normalizedPosterior π (fun k => marginalLikelihood (μ k) (L k)) {false}).toReal =
      bayesFactor (marginalLikelihood (μ true) (L true))
          (marginalLikelihood (μ false) (L false)) *
        ((π {true}).toReal / (π {false}).toReal) :=
  normalizedPosterior_bool_odds hp0 he0 he0' he1'

/-! ### Two normal models for one observation -/

/-- The likelihood `θ ↦ φ(y; θ, 1)` of one observation `y` with mean `θ` and variance `1`. -/
noncomputable def normalPointLik (y : ℝ) : Bool → ℝ → ℝ≥0∞ := fun _ θ => gaussianPDF θ 1 y

/-- The priors of the two models: the point masses at the means `0` (model `M₀`) and `1`
(model `M₁`). -/
noncomputable def normalPointPrior : Bool → Measure ℝ :=
  fun k => Measure.dirac (if k then 1 else 0)

/-- **The Bayes factor of `N(1, 1)` against `N(0, 1)` at `y` is `exp(y - 1/2)`**. -/
theorem bayesFactor_normal_point (y : ℝ) :
    bayesFactor (marginalLikelihood (normalPointPrior true) (normalPointLik y true))
        (marginalLikelihood (normalPointPrior false) (normalPointLik y false)) =
      Real.exp (y - 1 / 2) := by
  simp only [bayesFactor, marginalLikelihood, normalPointPrior, normalPointLik, ite_true,
    Bool.false_eq_true, ite_false, lintegral_dirac, gaussianPDF, gaussianPDFReal, NNReal.coe_one,
    mul_one]
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    mul_div_mul_left _ _ (inv_ne_zero (Real.sqrt_pos.2 (by positivity)).ne'), ← Real.exp_sub]
  congr 1
  ring

/-- **A computed instance**: at `y = 1/2` the Bayes factor is `1`, and at `y = 1` with equal
prior probabilities `1/2` the posterior odds of `M₁` against `M₀` are `exp(1/2) = √e`. -/
theorem example_posterior_odds_normal :
    bayesFactor (marginalLikelihood (normalPointPrior true) (normalPointLik (1 / 2) true))
        (marginalLikelihood (normalPointPrior false) (normalPointLik (1 / 2) false)) = 1 ∧
      (normalizedPosterior ((1 / 2 : ℝ≥0∞) • Measure.count) (fun k =>
          marginalLikelihood (normalPointPrior k) (normalPointLik 1 k)) {true}).toReal /
        (normalizedPosterior ((1 / 2 : ℝ≥0∞) • Measure.count) (fun k =>
          marginalLikelihood (normalPointPrior k) (normalPointLik 1 k)) {false}).toReal =
        Real.exp (1 / 2) := by
  refine ⟨by rw [bayesFactor_normal_point]; norm_num, ?_⟩
  have hfin : ∀ k, marginalLikelihood (normalPointPrior k) (normalPointLik 1 k) ≠ ∞ := by
    intro k
    cases k <;> simp [marginalLikelihood, normalPointPrior, normalPointLik, gaussianPDF,
      lintegral_dirac]
  have hpos : marginalLikelihood (normalPointPrior false) (normalPointLik 1 false) ≠ 0 := by
    simp only [marginalLikelihood, normalPointPrior, normalPointLik, Bool.false_eq_true,
      ite_false, lintegral_dirac, gaussianPDF, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact gaussianPDFReal_pos _ _ _ one_ne_zero
  have hp0 : ((1 / 2 : ℝ≥0∞) • Measure.count) {false} ≠ 0 := by
    simp
  have : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • (Measure.count : Measure Bool)) := by
    constructor
    simp [Measure.count_apply_finite, ENNReal.mul_lt_top]
  rw [posterior_odds_eq_bayesFactor_mul _ normalPointPrior (normalPointLik 1) hp0 hpos (hfin _)
    (hfin _), bayesFactor_normal_point]
  have : ((1 / 2 : ℝ≥0∞) • (Measure.count : Measure Bool)) {true} =
      ((1 / 2 : ℝ≥0∞) • (Measure.count : Measure Bool)) {false} := by
    simp
  rw [this, div_self (ENNReal.toReal_pos hp0 (measure_ne_top _ _)).ne']
  norm_num

end MetaAnalysis

end CausalInference
