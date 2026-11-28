/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.CommonComparator
public import CausalInference.BiasAnalysis.VarianceFormulas
public import CausalInference.Measures.OddsRatioLink
public import Mathlib.Probability.Distributions.Binomial
public import CausalInference.BiasAnalysis.VarianceSeveralSamplesWitnesses

/-!
# The large sample law of an empirical log odds

The arm level input of an indirect comparison of binary outcomes is an empirical log odds
`logit(r / n)` from `r` events among `n` patients.

* **Asymptotic normality** (`tendstoInDistribution_logit_sampleMean`): for an i.i.d. sample of
  event indicators with event probability `0 < p < 1`, `√n (logit p̂_n - logit p)` converges in
  distribution to `N(0, 1/(p(1 - p)))`. The statement uses the log odds of
  `Measures/OddsRatioLink.lean`, which agrees everywhere with the one of the variance formulas
  (`logit_eq_varianceFormulas_logit`); at the boundary counts `r ∈ {0, n}` it takes the value `0`,
  and those counts have probability `(1 - p)^n + p^n → 0` (`binomial_boundary`), so the limit
  does not depend on that value.
* **Plug in variances** (`plugin_variance_logit`, `plugin_variance_logOddsRatio`): for interior
  counts `0 < r < n`, `1/(n p̂ (1 - p̂)) = 1/r + 1/(n - r)`, and the plug in variance of a
  difference of two independent empirical log odds is the sum of the four inverse cell counts.
  The variance of the difference itself is `variance_indirectEstimate_of_indepFun`.

## Main results

* `logit_eq_varianceFormulas_logit`, `tendstoInDistribution_logit_sampleMean`,
  `plugin_variance_logit`, `plugin_variance_logOddsRatio`, `binomial_boundary`,
  `plugin_variance_example`, `binomial_boundary_example`, `tendstoInDistribution_logit_example`.

## References

* B. Woolf, *On estimating the relation between blood group and disease*, Annals of Human
  Genetics 19 (1955).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory Filter Topology

/-- The log odds `log (p / (1 - p))` equals `log p - log (1 - p)` at every real `p`, including
`p = 0` and `p = 1`, where both are `0`. -/
theorem logit_eq_varianceFormulas_logit :
    EffectMeasure.logit = BiasAnalysis.VarianceFormulas.logit := by
  funext p
  simp only [EffectMeasure.logit, EffectMeasure.odds, BiasAnalysis.VarianceFormulas.logit]
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h1 : 1 - p = 0
  · have hp : p = 1 := by linarith
    simp [hp]
  exact Real.log_div h0 h1

/-- **The large sample law of an empirical log odds.** For an i.i.d. sample `O` and a measurable
event indicator `f` with event probability `0 < p < 1`, the empirical log odds
`logit(p̂_n)` of the sample mean satisfies `√n (logit p̂_n - logit p) → N(0, 1/(p(1 - p)))` in
distribution: it converges to any random variable `Y` with that law. -/
theorem tendstoInDistribution_logit_sampleMean {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace 𝒪] {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1)
    {p : ℝ} (hp : ∫ ω, f (O 0 ω) ∂μ = p) (h0 : 0 < p) (h1 : p < 1) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (1 / (p * (1 - p))).toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √n * (EffectMeasure.logit (sampleMean f O n ω) - EffectMeasure.logit p))
      atTop Y (fun _ => μ) P' := by
  rw [logit_eq_varianceFormulas_logit]
  have h := BiasAnalysis.VarianceFormulas.logit_sampleMean_isAsymptoticallyLinear hO hf h01 hp
    h0 h1
  have hv := BiasAnalysis.VarianceFormulas.integral_sq_logit_influence hO hf h01 hp h0 h1
  have hmeas : ∀ n, AEMeasurable
      (fun ω => BiasAnalysis.VarianceFormulas.logit (sampleMean f O n ω)) μ := fun n => by
    have hm : Measurable BiasAnalysis.VarianceFormulas.logit := by
      unfold BiasAnalysis.VarianceFormulas.logit; fun_prop
    exact hm.comp_aemeasurable ((isSampleMeasurable_sampleMean hf O).aemeasurable hO n)
  exact h.tendstoInDistribution hO hmeas (by rw [hv]; exact hY)

/-- **The plug in variance of an empirical log odds**: for interior counts `0 < r < n`, with
`p̂ = r / n`, `1 / (n p̂ (1 - p̂)) = 1 / r + 1 / (n - r)`. -/
theorem plugin_variance_logit {n r : ℝ} (hr : 0 < r) (hrn : r < n) :
    1 / (n * (r / n) * (1 - r / n)) = 1 / r + 1 / (n - r) := by
  have hn : 0 < n := hr.trans hrn
  have hnr : 0 < n - r := by linarith
  field_simp
  ring

/-- **The plug in variance of an empirical log odds ratio**: for two independent arms with
interior counts, the sum of the two plug in variances is the sum of the four inverse cell
counts. -/
theorem plugin_variance_logOddsRatio {n₁ r₁ n₂ r₂ : ℝ} (hr₁ : 0 < r₁) (hrn₁ : r₁ < n₁)
    (hr₂ : 0 < r₂) (hrn₂ : r₂ < n₂) :
    1 / (n₁ * (r₁ / n₁) * (1 - r₁ / n₁)) + 1 / (n₂ * (r₂ / n₂) * (1 - r₂ / n₂)) =
      (1 / r₁ + 1 / (n₁ - r₁)) + (1 / r₂ + 1 / (n₂ - r₂)) := by
  rw [plugin_variance_logit hr₁ hrn₁, plugin_variance_logit hr₂ hrn₂]

/-- **The boundary counts are asymptotically negligible**: for `r ∼ Bin(n, p)` with `n ≥ 1`,
`P(r ∈ {0, n}) = (1 - p)^n + p^n`, and for `0 < p < 1` this tends to `0`. -/
theorem binomial_boundary (p : unitInterval) :
    (∀ n : ℕ, 1 ≤ n → (binomial n p).real {0, n} = (1 - (p : ℝ)) ^ n + (p : ℝ) ^ n) ∧
      (0 < (p : ℝ) → (p : ℝ) < 1 →
        Tendsto (fun n : ℕ => (1 - (p : ℝ)) ^ n + (p : ℝ) ^ n) atTop (𝓝 0)) := by
  refine ⟨fun n hn => ?_, fun h0 h1 => ?_⟩
  · rw [Set.insert_eq, measureReal_union (by simp; omega) (measurableSet_singleton _),
      binomial_real_zero, binomial_real_self]
  · have ha := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - (p : ℝ))
      (by linarith : 1 - (p : ℝ) < 1)
    have hb := tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
    simpa using ha.add hb

/-- **An instance of the plug in variances**: with `3` events among `10` patients and `5` among
`20`, the plug in variance of the log odds ratio is `1/3 + 1/7 + 1/5 + 1/15 = 26/35`. -/
theorem plugin_variance_example :
    1 / (10 * (3 / 10) * (1 - 3 / 10)) + 1 / (20 * (5 / 20) * (1 - 5 / 20)) = (26 / 35 : ℝ) := by
  rw [plugin_variance_logOddsRatio (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **An instance of the boundary probability**: for `Bin(2, 1/2)`,
`P(r ∈ {0, 2}) = 1/4 + 1/4 = 1/2`, and `(1/2)^n + (1/2)^n → 0`. -/
theorem binomial_boundary_example :
    (binomial 2 ⟨1 / 2, by norm_num, by norm_num⟩).real {0, 2} = 1 / 2 ∧
      Tendsto (fun n : ℕ => (1 - (1 / 2 : ℝ)) ^ n + (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
  have h := binomial_boundary ⟨1 / 2, by norm_num, by norm_num⟩
  refine ⟨?_, h.2 (by norm_num) (by norm_num)⟩
  rw [h.1 2 (by norm_num)]
  norm_num

/-- **An instance of the large sample law**: for an i.i.d. sample of fair coins (event
probability `1/2`), `√n (logit p̂_n - logit (1/2))` converges in distribution to `N(0, 4)`. -/
theorem tendstoInDistribution_logit_example :
    TendstoInDistribution
      (fun (n : ℕ) ω => √n * (EffectMeasure.logit
        (sampleMean BiasAnalysis.SamplingWitnesses.coin (fun (j : ℕ) (ω : Unit → ℕ → Bool) =>
          ω () j) n ω) - EffectMeasure.logit (1 / 2)))
      atTop id (fun _ => BiasAnalysis.SamplingWitnesses.gridMeasure
        fun (_ : Unit) (_ : ℕ) => (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval))
      (gaussianReal 0 (1 / ((1 / 2 : ℝ) * (1 - 1 / 2))).toNNReal) :=
  tendstoInDistribution_logit_sampleMean
    (BiasAnalysis.SamplingWitnesses.gridMeasure_rows_isIIDSample _ ())
    BiasAnalysis.SamplingWitnesses.measurable_coin BiasAnalysis.SamplingWitnesses.coin_mem
    (by rw [BiasAnalysis.SamplingWitnesses.gridMeasure_integral_coin]) (by norm_num)
    (by norm_num) HasLaw.id

end IndirectComparison

end CausalInference
