/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityWaldAnchored
public import CausalInference.PopulationAdjustment.WeightedNormalityVarianceCompare
public import CausalInference.PopulationAdjustment.WeightedNormalityExamples
public import CausalInference.BiasAnalysis.DistributionsExamples

/-!
# Sandwich variances and Wald intervals in the two coin model

The two coin model of `WeightedConsistencyExamples`: a fair coin `X`, an independent fair coin
`A`, `Y = μ_A(X)` with `μ_true(x) = 1 + 2·1{x}` and `μ_false(x) = 1{x}`, the feature
`φ(x) = 1{x}` and the target mean `t = 1/2`. Every hypothesis of the sandwich consistency and of
the Wald coverage theorems is verified:

* the sandwich estimator `n Σ̂ₙ` of the arm variance tends in probability to `1` in the treated
  arm and to `1/4` in the control arm;
* the 95% Wald interval `[m̂ₙ ± z σ̂ₙ / √n]` with `Φ(z) = 1 - 0.05/2` covers the arm mean `2`
  (respectively `1/2`) with probability tending to `0.95`;
* the cross covariance of the two arms is `E[IF_false IF_true] = -1/2`;
* with an aggregate comparison that is known exactly (a constant, of variance `0`), the
  unanchored comparison of the treated arm has limiting variance `1` and the anchored comparison
  on the identity scale has limiting variance `1/4 + 2·(1/2) + 1 = 9/4`, and both Wald intervals
  attain the nominal coverage;
* the naive variances `2` and `1/2` exceed the sandwich variances by the quadratic form
  `(π / q)² E[w₀² (γ (φ(X) - t))²]` of the affine comparison, here `γ = 2` and `γ = 1`.

## Main definitions

* none: the file instantiates the general results.

## Main results

* `nonneg_of_cdf_gaussianReal_eq`: a normal quantile of a level above `1/2` is nonnegative.
* `example_sandwich_tendstoInMeasure_true`, `example_sandwich_tendstoInMeasure_false`.
* `example_waldInterval_coverage_true`, `example_waldInterval_coverage_false`.
* `example_weightedInfluenceCov`: `E[IF_false IF_true] = -1/2`.
* `example_unanchored_waldInterval_coverage`, `example_anchored_waldInterval_coverage`.
* `example_weightedNaiveVariance_true`, `example_weightedNaiveVariance_false`,
  `example_weightedNaiveVariance_sub_true`.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
* Stefanski, Boos, *The calculus of M-estimation* (2002).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology NNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-- **A normal quantile of a level above `1/2` is nonnegative**: `Φ(z) = 1 - α/2` with `α < 1`
forces `0 ≤ z`, since `Φ(0) = 1/2` and `Φ` is monotone. -/
theorem nonneg_of_cdf_gaussianReal_eq {z α : ℝ} (hα : α < 1)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) : 0 ≤ z := by
  by_contra hz
  have h := (cdf (gaussianReal 0 1)).mono (not_le.1 hz).le
  rw [hzα, BiasAnalysis.Distributions.cdf_stdNormal_zero] at h
  linarith

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

/-- **The sandwich estimator of the treated arm is consistent for `σ² = 1`.** -/
theorem example_sandwich_tendstoInMeasure_true (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    TendstoInMeasure P (fun (n : ℕ) ω => ((n : ℝ) • sandwichMatrixHat O
      (weightedEstFun exampleFeature exampleTarget true)
      (weightedEstJac exampleFeature exampleTarget true)
      (weightedStackedEstimate exampleFeature exampleTarget O true) n ω) (Sum.inr ())
        (Sum.inr ())) atTop (fun _ => 1) := by
  have h := sandwichMatrixHat_weighted_tendstoInMeasure hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) true
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
  rwa [hlaw, example_weightedArmVariance_true] at h

/-- **The sandwich estimator of the control arm is consistent for `σ² = 1/4`.** -/
theorem example_sandwich_tendstoInMeasure_false (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    TendstoInMeasure P (fun (n : ℕ) ω => ((n : ℝ) • sandwichMatrixHat O
      (weightedEstFun exampleFeature exampleTarget false)
      (weightedEstJac exampleFeature exampleTarget false)
      (weightedStackedEstimate exampleFeature exampleTarget O false) n ω) (Sum.inr ())
        (Sum.inr ())) atTop (fun _ => 1 / 4) := by
  have h := sandwichMatrixHat_weighted_tendstoInMeasure hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) false
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
  rwa [hlaw, example_weightedArmVariance_false] at h

/-- **The 95% Wald interval of the treated arm** covers the arm mean `2` with probability
tending to `0.95`, for the normal quantile `z` with `Φ(z) = 1 - 0.05/2`. -/
theorem example_waldInterval_coverage_true (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) {z : ℝ}
    (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => P.real {ω | (2 : ℝ) ∈
      waldInterval (sampleBalancedArmMean exampleFeature exampleTarget O true n ω)
        (weightedArmSdHat exampleFeature exampleTarget O true n ω) z n}) atTop
      (𝓝 (1 - 0.05)) := by
  have h := tendsto_weightedArm_waldInterval_coverage hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) true
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (by rw [hlaw, example_weightedArmVariance_true]; norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw, example_tiltArmMean_true] at h

/-- **The 95% Wald interval of the control arm** covers the arm mean `1/2` with probability
tending to `0.95`. -/
theorem example_waldInterval_coverage_false (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) {z : ℝ}
    (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => P.real {ω | (1 / 2 : ℝ) ∈
      waldInterval (sampleBalancedArmMean exampleFeature exampleTarget O false n ω)
        (weightedArmSdHat exampleFeature exampleTarget O false n ω) z n}) atTop
      (𝓝 (1 - 0.05)) := by
  have h := tendsto_weightedArm_waldInterval_coverage hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) false
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (by rw [hlaw, example_weightedArmVariance_false]; norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw, example_tiltArmMean_false] at h

end Sample

/-- **The cross covariance of the two arms is `E[IF_false IF_true] = -1/2`.** -/
theorem example_weightedInfluenceCov :
    weightedInfluenceCov exampleRecordLaw exampleFeature exampleTarget false true = -1 / 2 := by
  rw [weightedInfluenceCov, example_weightedArmInfluence_false, example_weightedArmInfluence_true,
    integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

/-- The anchored limiting variance on the identity scale with a known aggregate:
`σ_F² - 2 C_FT + σ_T² = 1/4 + 1 + 1 = 9/4`. -/
theorem example_anchoredVariance :
    (1 : ℝ) ^ 2 * weightedArmVariance exampleRecordLaw exampleFeature exampleTarget false -
      2 * 1 * 1 * weightedInfluenceCov exampleRecordLaw exampleFeature exampleTarget false true +
      1 ^ 2 * weightedArmVariance exampleRecordLaw exampleFeature exampleTarget true + 0 =
      9 / 4 := by
  rw [example_weightedArmVariance_false, example_weightedInfluenceCov,
    example_weightedArmVariance_true]
  norm_num

/-- The unanchored limiting variance on the identity scale with a known aggregate is
`σ_T² = 1`. -/
theorem example_unanchoredVariance :
    (1 : ℝ) ^ 2 * weightedArmVariance exampleRecordLaw exampleFeature exampleTarget true + 0 =
      1 := by
  rw [example_weightedArmVariance_true]
  norm_num

section Aggregate

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

/-- An exactly known aggregate: `√n (c - c) = 0` tends in law to the constant `0`. -/
theorem tendstoInDistribution_sqrt_mul_sub_self (c : ℝ) :
    TendstoInDistribution (fun (n : ℕ) (_ : Ω) => √n * (c - c)) atTop (fun _ : Ω => (0 : ℝ))
      (fun _ => P) P :=
  (tendstoInDistribution_const (l := atTop) (μ' := P) (Z := fun _ : Ω => (0 : ℝ))
    aemeasurable_const).congr (fun _ => ae_of_all _ fun _ => by simp) (ae_eq_refl _)

/-- The constant `0` has the degenerate normal law `N(0, 0)`. -/
theorem hasLaw_zero_gaussianReal : HasLaw (fun _ : Ω => (0 : ℝ)) (gaussianReal 0 0) P where
  aemeasurable := aemeasurable_const
  map_eq := by rw [Measure.map_const, measure_univ, one_smul, gaussianReal_zero_var]

omit [IsProbabilityMeasure P] in
theorem isConsistent_zero_coe : IsConsistent (fun _ _ => (0 : ℝ)) ((0 : ℝ≥0) : ℝ) P := by
  rw [NNReal.coe_zero]
  exact tendstoInMeasure_const 0

/-- **Unanchored comparison with a known aggregate.** If the aggregate mean of the comparator
arm is a constant `c`, the 95% Wald interval for `c - 2` built from `c - m̂ₙ` and
`σ̂ₙ = √(σ̂_T²)` attains the nominal coverage; the limiting variance is `1`. -/
theorem example_unanchored_waldInterval_coverage (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) (c : ℝ) {z : ℝ}
    (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => P.real {ω | c - 2 ∈
      waldInterval (unanchoredBalancedEstimate id exampleFeature exampleTarget O
        (fun _ _ => c) n ω)
        (unanchoredSdHat (fun _ => 1) exampleFeature exampleTarget O (fun _ _ => 0) n ω) z n})
      atTop (𝓝 (1 - 0.05)) := by
  have hm := example_tiltArmMean_true
  have h := tendsto_unanchored_waldInterval_coverage hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (g := id) (dg := fun _ => 1) measurable_id measurable_const (hasDerivAt_id _)
    continuousAt_const (mB := fun _ _ => c) (mB₀ := c)
    (fun n => indepFun_const_right _ c) (tendstoInDistribution_sqrt_mul_sub_self (P := P) c)
    hasLaw_zero_gaussianReal isConsistent_zero_coe (fun _ => aemeasurable_const)
    (by rw [hlaw, example_weightedArmVariance_true]; norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw, hm] at h

/-- **Anchored comparison with a known aggregate.** If the comparator contrast is a constant
`d`, the 95% Wald interval for `(1/2 - 2) - d` built from the anchored estimate on the identity
scale attains the nominal coverage; the limiting variance is `9/4`. -/
theorem example_anchored_waldInterval_coverage (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) (d : ℝ) {z : ℝ}
    (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => P.real {ω | 1 / 2 - 2 - d ∈
      waldInterval (anchoredBalancedEstimate id exampleFeature exampleTarget O (fun _ _ => d) n ω)
        (anchoredSdHat (fun _ => 1) (fun _ => 1) exampleFeature exampleTarget O
          (fun _ _ => 0) n ω) z n}) atTop (𝓝 (1 - 0.05)) := by
  have h := tendsto_anchored_waldInterval_coverage hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (fun a => by rw [hlaw, example_prob_arm]; norm_num)
    (by rw [hlaw]; exact example_memLp_outcome)
    (g := id) (dgF := fun _ => 1) (dgT := fun _ => 1) measurable_id measurable_const
    measurable_const (hasDerivAt_id _) (hasDerivAt_id _) continuousAt_const continuousAt_const
    (dBC := fun _ _ => d) (d := d) (fun n => indepFun_const_right _ d)
    (tendstoInDistribution_sqrt_mul_sub_self (P := P) d) hasLaw_zero_gaussianReal
    isConsistent_zero_coe (fun _ => aemeasurable_const)
    (by rw [hlaw, NNReal.coe_zero, example_anchoredVariance]; norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw, example_tiltArmMean_false, example_tiltArmMean_true] at h

end Aggregate

/-! ### The naive variance against the sandwich variance -/

/-- **The naive variance of the treated arm is `2`**, against the sandwich variance `1`. -/
theorem example_weightedNaiveVariance_true :
    weightedNaiveVariance exampleRecordLaw exampleFeature exampleTarget true = 2 := by
  rw [← example_naiveVariance_true, weightedNaiveVariance]
  congr 1
  funext z
  simp only [weightedArmResidual, example_tiltMinimizer, tiltWeight_zero_param, mul_one,
    example_weightedArmMass]
  rw [← example_tiltMinimizer, example_tiltArmMean_true]

/-- **The naive variance of the control arm is `1/2`**, against the sandwich variance `1/4`. -/
theorem example_weightedNaiveVariance_false :
    weightedNaiveVariance exampleRecordLaw exampleFeature exampleTarget false = 1 / 2 := by
  rw [← example_naiveVariance_false, weightedNaiveVariance]
  congr 1
  funext z
  simp only [weightedArmResidual, example_tiltMinimizer, tiltWeight_zero_param, mul_one,
    example_weightedArmMass]
  rw [← example_tiltMinimizer, example_tiltArmMean_false]

/-- **The difference is the quadratic form of the affine comparison**: in the treated arm,
`σ_naive² - σ² = 2 - 1 = (π / q)² E[w₀² (γ (φ(X) - t))²]` with `π = q = 1/2`, `w₀ = 1` and
`γ = 2`. -/
theorem example_weightedNaiveVariance_sub_true :
    weightedNaiveVariance exampleRecordLaw exampleFeature exampleTarget true -
      weightedArmVariance exampleRecordLaw exampleFeature exampleTarget true =
      (exampleRecordLaw.real {z | z.2.1 = true} /
        weightedArmMass exampleRecordLaw exampleFeature exampleTarget true) ^ 2 *
        ∫ z, tiltWeight exampleFeature exampleTarget 0
          (tiltMinimizer exampleRecordLaw exampleFeature exampleTarget) z.1 ^ 2 *
          ((fun _ => (2 : ℝ)) ⬝ᵥ (exampleFeature z.1 - exampleTarget)) ^ 2 ∂exampleRecordLaw := by
  rw [example_weightedNaiveVariance_true, example_weightedArmVariance_true, example_prob_arm,
    example_weightedArmMass, example_tiltMinimizer, integral_exampleRecordLaw]
  norm_num [tiltWeight_zero_param, exampleRecord, exampleFeature, exampleTarget, exampleInd,
    dotProduct]

end PopulationAdjustment

end CausalInference
