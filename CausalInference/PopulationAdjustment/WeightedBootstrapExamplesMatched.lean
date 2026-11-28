/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedBootstrapCoverage
public import CausalInference.PopulationAdjustment.WeightedNormalityExamples

/-!
# Bootstrap coverage with one matched feature

The two coin model of `WeightedNormalityExamples`: a fair coin `X`, an independent fair coin `A`
and the outcome `Y = μ_A(X)` with `μ_true(x) = 1 + 2·1{x}` and `μ_false(x) = 1{x}`. The matched
feature is `φ(x) = 1{x}` (`p = 1`), with `‖φ(x) - t‖ ≤ 1`, the margin condition at `δ = 1/2` and
the target mean `t = 1/2`. Every hypothesis of the coverage theorems is verified, and the
variances are computed:

* the treated arm: `m₀ = 2`, `σ² = 1`;
* the anchored index part `m_false - m_true - d`: centering `1/2 - 2 - d` and
  `E[(IF_false - IF_true)²] = 9/4`.

## Main results

* `example_isBootstrapLinear`: bootstrap linearity of both weighted arm means.
* `example_bootstrap_coverage_true`: percentile and basic coverage `1 - α` for `m₀ = 2`.
* `example_bootstrapAnchoredVariance`: `E[(IF_false - IF_true)²] = 9/4`.
* `example_bootstrapIndexContrast_coverage`: percentile and basic coverage `1 - α` of the
  anchored comparison.
* `exists_example_bootstrap_coverage`: the instance is not vacuous.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix Set
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap IndirectComparison

/-- **The variance of the anchored index part in the two coin model**:
`E[(IF_false - IF_true)²] = 9/4`. -/
theorem example_bootstrapAnchoredVariance :
    ∫ z, (weightedArmInfluence exampleRecordLaw exampleFeature exampleTarget false z -
      weightedArmInfluence exampleRecordLaw exampleFeature exampleTarget true z) ^ 2
        ∂exampleRecordLaw = 9 / 4 := by
  rw [example_weightedArmInfluence_false, example_weightedArmInfluence_true,
    integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

/-- **Bootstrap linearity with one matched feature**: for an i.i.d. sample of the two coin
record law, both weighted arm means are bootstrap linear. -/
theorem example_isBootstrapLinear (hO : IsIIDSample O P) (hlaw : P.map (O 0) = exampleRecordLaw)
    (a : Bool) :
    IsBootstrapLinear P O (bootstrapArmMean exampleFeature exampleTarget a)
      (weightedArmInfluence (P.map (O 0)) exampleFeature exampleTarget a) :=
  isBootstrapLinear_bootstrapArmMean hO measurable_exampleFeature example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) a
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)

/-- **Bootstrap coverage in the treated arm with one matched feature.** For an i.i.d. sample of
the two coin record law, `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the bootstrap percentile and basic
intervals of the weighted arm mean cover `m₀ = 2` with probability tending to `1 - α`; the
variance is `σ² = weightedArmVariance = 1`. -/
theorem example_bootstrap_coverage_true (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | (2 : ℝ) ∈ percentileInterval
        (bootstrapLaw (bootstrapArmMean exampleFeature exampleTarget true) O n ω) α})
        atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | (2 : ℝ) ∈ basicInterval
        (bootstrapLaw (bootstrapArmMean exampleFeature exampleTarget true) O n ω)
          (sampleBalancedArmMean exampleFeature exampleTarget O true n ω) α}) atTop
        (𝓝 (1 - α)) := by
  have h := tendsto_bootstrapArmMean_coverage hO measurable_exampleFeature example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) true
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (by rw [hlaw, example_weightedArmVariance_true]; norm_num) hα hz
  rwa [hlaw, example_tiltArmMean_true] at h

/-- **Bootstrap coverage of the anchored comparison with one matched feature.** For an i.i.d.
sample of the two coin record law and a reported aggregate comparison `d`, the bootstrap
percentile and basic intervals of `(m*_false - m*_true) - d` cover `1/2 - 2 - d` with
probability tending to `1 - α`; here `E[(IF_false - IF_true)²] = 9/4`. -/
theorem example_bootstrapIndexContrast_coverage (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) (d : ℝ) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | 1 / 2 - 2 - d ∈ percentileInterval
        (bootstrapLaw (fun n y => bootstrapArmMean exampleFeature exampleTarget false n y -
          bootstrapArmMean exampleFeature exampleTarget true n y - d) O n ω) α})
        atTop (𝓝 (1 - α)) ∧
      Tendsto (fun n => P.real {ω | 1 / 2 - 2 - d ∈ basicInterval
        (bootstrapLaw (fun n y => bootstrapArmMean exampleFeature exampleTarget false n y -
          bootstrapArmMean exampleFeature exampleTarget true n y - d) O n ω)
          (sampleBalancedArmMean exampleFeature exampleTarget O false n ω -
            sampleBalancedArmMean exampleFeature exampleTarget O true n ω - d) α}) atTop
        (𝓝 (1 - α)) := by
  have h := tendsto_bootstrapIndexContrast_coverage hO measurable_exampleFeature example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (fun a => by rw [hlaw, example_prob_arm]; norm_num)
    (by rw [hlaw]; exact example_memLp_outcome) d
    (by rw [hlaw, example_bootstrapAnchoredVariance]; norm_num) hα hz
  rwa [hlaw, example_tiltArmMean_false, example_tiltArmMean_true] at h

/-- **The instance is not vacuous**: an i.i.d. sample of the two coin record law exists, and on
it the bootstrap percentile interval of the weighted arm mean of the treated arm covers `2` with
probability tending to `1 - α`. -/
theorem exists_example_bootstrap_coverage {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → Bool × Bool × ℝ,
      IsProbabilityMeasure P ∧ IsIIDSample O P ∧ P.map (O 0) = exampleRecordLaw ∧
        Tendsto (fun n => P.real {ω | (2 : ℝ) ∈ percentileInterval
          (bootstrapLaw (bootstrapArmMean exampleFeature exampleTarget true) O n ω) α})
          atTop (𝓝 (1 - α)) := by
  obtain ⟨Ω, _, P, O, hP, -, hO, hlaw⟩ := exists_exampleSample
  exact ⟨Ω, _, P, O, hP, hO, hlaw, (example_bootstrap_coverage_true hO hlaw hα hz).1⟩

end PopulationAdjustment

end CausalInference
