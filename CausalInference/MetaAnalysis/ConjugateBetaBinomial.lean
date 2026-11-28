/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HierarchicalPosterior
public import CausalInference.BiasAnalysis.Bayesian
public import CausalInference.BiasAnalysis.Distributions

/-!
# Beta and binomial conjugacy: posterior mean and predictive probability

The conjugate update itself is `BiasAnalysis.Bayesian.betaBinomial_posterior`: for `k ≤ n`
successes and the prior `Beta(α, β)`, `α, β > 0`, the normalized posterior is
`Beta(α + k, β + n - k)`. This file restates it with `normalizedPosterior` and adds:

* **Posterior mean as shrinkage** (`betaBinomial_posteriorMean`): the posterior mean
  `(α + k)/(α + β + n)` is `B · α/(α + β) + (1 - B) · k/n` with `B = (α + β)/(α + β + n) ∈ (0, 1)`:
  the observed proportion is shrunk toward the prior mean, with the prior acting as `α + β`
  pseudo observations.
* **Predictive probability** (`betaBinomial_predictive`): the posterior predictive probability
  that a further trial is a success, `∫ p d(posterior)`, is `(α + k)/(α + β + n)`.
* **Laplace's rule of succession** (`laplace_rule_of_succession`): with the uniform prior
  `Beta(1, 1)` the predictive probability is `(k + 1)/(n + 2)`.

## Main results

* `betaBinomial_normalizedPosterior`, `betaBinomial_posteriorMean`, `betaBinomial_predictive`,
  `laplace_rule_of_succession`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory BiasAnalysis.Bayesian
open scoped ENNReal

/-- **Beta and binomial conjugacy** in the `normalizedPosterior` form: for `k ≤ n` the marginal
likelihood is `C(n, k) B(α + k, β + n - k) / B(α, β)` and the normalized posterior is
`Beta(α + k, β + n - k)`. A restatement of `betaBinomial_posterior`. -/
theorem betaBinomial_normalizedPosterior {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ}
    (hk : k ≤ n) :
    ∫⁻ x, ENNReal.ofReal (binomPMF n x k) ∂betaMeasure α β =
        ENNReal.ofReal (n.choose k * (beta (α + k) (β + (n - k : ℕ)) / beta α β)) ∧
      normalizedPosterior (betaMeasure α β) (fun x => ENNReal.ofReal (binomPMF n x k)) =
        betaMeasure (α + k) (β + (n - k : ℕ)) := by
  obtain ⟨h1, h2⟩ := betaBinomial_posterior α β hα hβ hk
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  exact ⟨h1, by rw [normalizedPosterior, h1, h2]⟩

/-- **The posterior mean shrinks the observed proportion toward the prior mean**: for
`1 ≤ n` trials and `k ≤ n` successes, the mean of `Beta(α + k, β + n - k)` is
`(α + k)/(α + β + n) = B · α/(α + β) + (1 - B) · k/n` with `B = (α + β)/(α + β + n) ∈ (0, 1)`. -/
theorem betaBinomial_posteriorMean {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ n) :
    ∫ x, x ∂betaMeasure (α + k) (β + (n - k : ℕ)) = (α + k) / (α + β + n) ∧
      (α + k) / (α + β + n) = (α + β) / (α + β + n) * (α / (α + β)) +
        (1 - (α + β) / (α + β + n)) * (k / n) ∧
      (α + β) / (α + β + n) ∈ Set.Ioo 0 1 := by
  have hcast : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hk
  have hny : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨?_, ?_, ?_⟩
  · rw [BiasAnalysis.Distributions.integral_id_betaMeasure (by positivity)
      (by rw [hcast]; linarith), hcast]
    congr 1
    ring
  · have : 0 < α + β := by linarith
    field_simp
    ring
  · exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

/-- **The predictive probability of a success**: the posterior predictive probability that one
further trial succeeds, `∫ p dπ(p | k)` under the posterior `Beta(α + k, β + n - k)`, is
`(α + k)/(α + β + n)`. -/
theorem betaBinomial_predictive {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {n k : ℕ} (hk : k ≤ n) :
    ∫ p, p ∂normalizedPosterior (betaMeasure α β) (fun x => ENNReal.ofReal (binomPMF n x k)) =
      (α + k) / (α + β + n) := by
  have hcast : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hk
  have hny : (k : ℝ) ≤ n := by exact_mod_cast hk
  rw [(betaBinomial_normalizedPosterior hα hβ hk).2,
    BiasAnalysis.Distributions.integral_id_betaMeasure (by positivity)
      (by rw [hcast]; linarith), hcast]
  congr 1
  ring

/-- **Laplace's rule of succession**: with the uniform prior `Beta(1, 1)`, after `k` successes in
`n` trials the predictive probability that the next trial succeeds is `(k + 1)/(n + 2)`. -/
theorem laplace_rule_of_succession {n k : ℕ} (hk : k ≤ n) :
    ∫ p, p ∂normalizedPosterior (betaMeasure 1 1) (fun x => ENNReal.ofReal (binomPMF n x k)) =
      (k + 1) / (n + 2) := by
  rw [betaBinomial_predictive one_pos one_pos hk]
  congr 1 <;> ring

end MetaAnalysis

end CausalInference
