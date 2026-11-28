/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityContrast
public import CausalInference.PopulationAdjustment.WeightedConsistencyExamples

/-!
# Asymptotic normality of the weighted arm means in the two coin model

The two coin model of `WeightedConsistencyExamples`: a fair coin `X`, an independent fair coin
`A` and the outcome `Y = μ_A(X)` with `μ_true(x) = 1 + 2·1{x}` and `μ_false(x) = 1{x}`; the
matched feature is `φ(x) = 1{x}` and the target mean is `t = 1/2`. Every hypothesis of
`sampleBalancedArmMean_tendstoInDistribution` is verified, and all population quantities are
computed: the population tilt is `β₀ = 0` (identified through the uniqueness of the root of the
balance equations), the tilted second moment is `M = 1/4`, and

* for `a = true`: `m₀ = 2`, `c = 1/4`, `q = 1/2`, `IF = 2 (1{A = a} (Y - 2) - (1{X} - 1/2))`, so
  `IF² = 1` and `σ² = 1`, against the naive variance `E[(1{A = a} (Y - m₀) / q)²] = 2` that
  ignores the estimation of the tilt;
* for `a = false`: `m₀ = 1/2`, `c = 1/8`, `σ² = 1/4`, against the naive variance `1/2`.

The estimation of the tilt halves the variance here: the outcome depends on the matched feature,
and the balance equations remove that part of the noise.

## Main results

* `integral_exampleRecordLaw`: integrals under the record law.
* `example_tiltMinimizer`, `example_tiltArmMean_true`, `example_tiltArmMean_false`.
* `example_weightedArmVariance_true`, `example_weightedArmVariance_false`.
* `example_naiveVariance_true`, `example_naiveVariance_false`.
* `example_tendstoInDistribution_true`, `example_tendstoInDistribution_false`.
* `example_indexContrast_isAsymptoticallyLinear`: the anchored index part on the identity scale.
* `exists_example_tendstoInDistribution`: an instance with an explicit sample and normal limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

/-- **Integrals under the record law** are averages over the four coin outcomes; no
measurability is needed, because the outcome is almost surely a function of the coins. -/
theorem integral_exampleRecordLaw (f : Bool × Bool × ℝ → ℝ) :
    ∫ z, f z ∂exampleRecordLaw = (f (exampleRecord (true, true)) +
      f (exampleRecord (true, false)) + f (exampleRecord (false, true)) +
      f (exampleRecord (false, false))) / 4 := by
  set g : Bool × Bool → ℝ := fun q => f (exampleRecord q)
  have hg : Measurable fun z : Bool × Bool × ℝ => g (z.1, z.2.1) :=
    (measurable_of_countable g).comp (measurable_fst.prodMk measurable_snd.fst)
  have h1 : ∫ z, f z ∂exampleRecordLaw = ∫ z, g (z.1, z.2.1) ∂exampleRecordLaw := by
    refine integral_congr_ae (ae_exampleRecordLaw_outcome.mono fun z hz => ?_)
    obtain ⟨x, s, y⟩ := z
    simp only at hz
    subst hz
    rfl
  rw [h1, exampleRecordLaw, integral_map measurable_exampleRecord.aemeasurable
    hg.aestronglyMeasurable]
  exact integral_uniformPairLaw g

/-- The matched feature is measurable. -/
theorem measurable_exampleFeature : Measurable exampleFeature := measurable_of_countable _

/-- The outcome is square integrable under the record law. -/
theorem example_memLp_outcome : MemLp (fun z : Bool × Bool × ℝ => z.2.2) 2 exampleRecordLaw :=
  MemLp.of_bound measurable_snd.snd.aestronglyMeasurable 3
    (ae_exampleRecordLaw_outcome.mono fun z hz => by
      rw [hz, Real.norm_eq_abs]
      cases z.2.1 <;> cases z.1 <;> norm_num [exampleRegression, exampleInd])

/-- **The population tilt is zero**: the untilted law already balances the feature. -/
theorem example_tiltMinimizer :
    tiltMinimizer exampleRecordLaw exampleFeature exampleTarget = 0 := by
  refine tiltMinimizer_eq_of_balance measurable_exampleFeature example_bound
    (by norm_num : (0 : ℝ) < 1 / 2) example_margin fun j => ?_
  simp only [tiltWeight_zero_param, one_mul]
  rw [integral_exampleRecordLaw]
  norm_num [exampleRecord, exampleFeature, exampleTarget, exampleInd]

/-- The tilted mass of arm `a` is `1/2`. -/
theorem example_weightedArmMass (a : Bool) :
    weightedArmMass exampleRecordLaw exampleFeature exampleTarget a = 1 / 2 := by
  rw [weightedArmMass, example_tiltMinimizer]
  simp only [tiltWeight_zero_param, mul_one]
  rw [integral_exampleRecordLaw]
  cases a <;> norm_num [exampleRecord, armIndObs]

/-- The tilted second moment matrix is `1/4`. -/
theorem example_tiltedSecondMoment :
    tiltedSecondMoment exampleRecordLaw exampleFeature exampleTarget 0 =
      Matrix.of fun _ _ => 1 / 4 := by
  ext j k
  simp only [tiltedSecondMoment, Matrix.of_apply, tiltWeight_zero_param, one_mul]
  rw [integral_exampleRecordLaw]
  norm_num [exampleRecord, exampleFeature, exampleTarget, exampleInd]

/-- The inverse of the tilted second moment matrix is `4`. -/
theorem example_tiltedSecondMoment_inv :
    (tiltedSecondMoment exampleRecordLaw exampleFeature exampleTarget 0)⁻¹ =
      Matrix.of fun _ _ => 4 := by
  rw [example_tiltedSecondMoment]
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul_apply]

/-- The weighted mean of the treated arm is `m₀ = 2`. -/
theorem example_tiltArmMean_true :
    tiltArmMean exampleRecordLaw exampleFeature exampleTarget true
      (tiltMinimizer exampleRecordLaw exampleFeature exampleTarget) = 2 := by
  rw [example_tiltMinimizer, tiltArmMean]
  simp only [tiltWeight_zero_param, mul_one]
  rw [integral_exampleRecordLaw, integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

/-- The weighted mean of the control arm is `m₀ = 1/2`. -/
theorem example_tiltArmMean_false :
    tiltArmMean exampleRecordLaw exampleFeature exampleTarget false
      (tiltMinimizer exampleRecordLaw exampleFeature exampleTarget) = 1 / 2 := by
  rw [example_tiltMinimizer, tiltArmMean]
  simp only [tiltWeight_zero_param, mul_one]
  rw [integral_exampleRecordLaw, integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

/-- The influence function of the treated arm: `IF = 2 (1{A = a} (Y - 2) - (1{X} - 1/2))`. -/
theorem example_weightedArmInfluence_true :
    weightedArmInfluence exampleRecordLaw exampleFeature exampleTarget true = fun z =>
      2 * (armIndObs true z * (z.2.2 - 2) - (exampleInd z.1 - 1 / 2)) := by
  have hm := example_tiltArmMean_true
  have hc : weightedCoupling exampleRecordLaw exampleFeature exampleTarget true =
      fun _ => 1 / 4 := by
    funext k
    rw [weightedCoupling, hm, example_tiltMinimizer]
    simp only [tiltWeight_zero_param, mul_one]
    rw [integral_exampleRecordLaw]
    norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd, exampleFeature,
      exampleTarget]
  funext z
  rw [weightedArmInfluence, hm, hc, example_weightedArmMass, example_tiltMinimizer,
    example_tiltedSecondMoment_inv]
  simp only [tiltWeight_zero_param, one_mul, mul_one, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one, Matrix.of_apply, exampleFeature, exampleTarget]
  ring

/-- The influence function of the control arm: `IF = 2 · 1{A = a} (Y - 1/2) - (1{X} - 1/2)`. -/
theorem example_weightedArmInfluence_false :
    weightedArmInfluence exampleRecordLaw exampleFeature exampleTarget false = fun z =>
      2 * (armIndObs false z * (z.2.2 - 1 / 2)) - (exampleInd z.1 - 1 / 2) := by
  have hm := example_tiltArmMean_false
  have hc : weightedCoupling exampleRecordLaw exampleFeature exampleTarget false =
      fun _ => 1 / 8 := by
    funext k
    rw [weightedCoupling, hm, example_tiltMinimizer]
    simp only [tiltWeight_zero_param, mul_one]
    rw [integral_exampleRecordLaw]
    norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd, exampleFeature,
      exampleTarget]
  funext z
  rw [weightedArmInfluence, hm, hc, example_weightedArmMass, example_tiltMinimizer,
    example_tiltedSecondMoment_inv]
  simp only [tiltWeight_zero_param, one_mul, mul_one, Matrix.mulVec, dotProduct,
    Fin.sum_univ_one, Matrix.of_apply, exampleFeature, exampleTarget]
  ring

/-- **The asymptotic variance of the treated arm is `σ² = 1`.** -/
theorem example_weightedArmVariance_true :
    weightedArmVariance exampleRecordLaw exampleFeature exampleTarget true = 1 := by
  rw [weightedArmVariance, example_weightedArmInfluence_true, integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

/-- **The asymptotic variance of the control arm is `σ² = 1/4`.** -/
theorem example_weightedArmVariance_false :
    weightedArmVariance exampleRecordLaw exampleFeature exampleTarget false = 1 / 4 := by
  rw [weightedArmVariance, example_weightedArmInfluence_false, integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

/-- **The naive variance of the treated arm is `2`**: the variance
`E[(1{A = a} w₀ (Y - m₀) / q)²]` that treats the tilt as known is twice the sandwich variance. -/
theorem example_naiveVariance_true :
    ∫ z, (armIndObs true z * (z.2.2 - 2) / (1 / 2)) ^ 2 ∂exampleRecordLaw = 2 := by
  rw [integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

/-- **The naive variance of the control arm is `1/2`**, twice the sandwich variance `1/4`. -/
theorem example_naiveVariance_false :
    ∫ z, (armIndObs false z * (z.2.2 - 1 / 2) / (1 / 2)) ^ 2 ∂exampleRecordLaw = 1 / 2 := by
  rw [integral_exampleRecordLaw]
  norm_num [exampleRecord, armIndObs, exampleRegression, exampleInd]

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Bool × Bool × ℝ}

/-- **Asymptotic normality in the treated arm**: for an i.i.d. sample of the record law,
`√n (m̂ₙ - 2) → N(0, 1)` in law. Every hypothesis of
`sampleBalancedArmMean_tendstoInDistribution` is verified. -/
theorem example_tendstoInDistribution_true (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
      √n * (sampleBalancedArmMean exampleFeature exampleTarget O true n ω - 2)) atTop Y
      (fun _ => P) P' := by
  have h := sampleBalancedArmMean_tendstoInDistribution hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) true
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (Y := Y) (by rw [hlaw, example_weightedArmVariance_true]; simpa using hY)
  rwa [hlaw, example_tiltArmMean_true] at h

/-- **Asymptotic normality in the control arm**: `√n (m̂ₙ - 1/2) → N(0, 1/4)` in law. -/
theorem example_tendstoInDistribution_false (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (1 / 4 : ℝ).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω =>
      √n * (sampleBalancedArmMean exampleFeature exampleTarget O false n ω - 1 / 2)) atTop Y
      (fun _ => P) P' := by
  have h := sampleBalancedArmMean_tendstoInDistribution hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin) false
    (by rw [hlaw, example_prob_arm]; norm_num) (by rw [hlaw]; exact example_memLp_outcome)
    (Y := Y) (by rw [hlaw, example_weightedArmVariance_false]; exact hY)
  rwa [hlaw, example_tiltArmMean_false] at h

/-- **The anchored index part in the two coin model**: on the identity scale,
`m̂_false - m̂_true` is asymptotically linear for `1/2 - 2` with the influence function
`IF_false - IF_true`. Every hypothesis of `weightedIndexContrast_isAsymptoticallyLinear` is
verified. -/
theorem example_indexContrast_isAsymptoticallyLinear (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = exampleRecordLaw) :
    IsAsymptoticallyLinear (fun n ω =>
        sampleBalancedArmMean exampleFeature exampleTarget O false n ω -
          sampleBalancedArmMean exampleFeature exampleTarget O true n ω) (1 / 2 - 2)
      (weightedAnchoredInfluence exampleRecordLaw exampleFeature exampleTarget 1 1) O P := by
  have h := weightedIndexContrast_isAsymptoticallyLinear hO measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw]; exact example_margin)
    (fun a => by rw [hlaw, example_prob_arm]; norm_num)
    (by rw [hlaw]; exact example_memLp_outcome) (hasDerivAt_id _) (hasDerivAt_id _)
  rwa [hlaw, example_tiltArmMean_false, example_tiltArmMean_true] at h

end Sample

/-- **An instance with every hypothesis discharged**: an i.i.d. sample of the record law exists,
and along it the weighted mean of the treated arm satisfies `√n (m̂ₙ - 2) → N(0, 1)`, the limit
being the identity on the standard normal law. -/
theorem exists_example_tendstoInDistribution : ∃ (Ω : Type) (_ : MeasurableSpace Ω)
    (P : Measure Ω) (_ : IsProbabilityMeasure P) (O : ℕ → Ω → Bool × Bool × ℝ),
      IsIIDSample O P ∧ TendstoInDistribution (fun (n : ℕ) ω =>
        √n * (sampleBalancedArmMean exampleFeature exampleTarget O true n ω - 2)) atTop
        (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, O, hP, -, hO, hlaw⟩ := exists_exampleSample
  exact ⟨Ω, _, P, hP, O, hO, example_tendstoInDistribution_true hO hlaw
    ⟨aemeasurable_id, Measure.map_id⟩⟩

end PopulationAdjustment

end CausalInference
