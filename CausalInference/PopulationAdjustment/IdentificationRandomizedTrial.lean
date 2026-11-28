/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationExamples
public import CausalInference.PointTreatment.Randomized
public import CausalInference.PointTreatment.SampleEstimators

/-!
# Conditional mean functions from a randomized trial, and a Hájek finite sample bias

* **A randomized trial gives conditional mean functions** (`Trial.isCondMean_of_indepFun`). In a
  trial with treatments `Bool` where the assignment is independent of the covariate and the
  potential outcomes, `A ⫫ (X, (Y(0), Y(1)))`, and both arms have positive probability, every
  version `m` of the observed regression `E[Y | X, A]` gives conditional mean functions
  `m(t, ·)` of both arms, which is what the identification theorems take as input; and the trial
  marginal effect is the marginal estimand of `m`. The proof assembles
  `PointTreatment.indicatorIgnorable_of_indepFun`,
  `PointTreatment.IndicatorIgnorable.meanIgnorable`,
  `PointTreatment.isPropensityScore_const_of_indepFun` and
  `Trial.isCondMean_of_isOutcomeRegression`. `randomized_trial_example` is an instance on
  `standardizationTrial`.
* **The Hájek weighted mean is not unbiased** (`hajek_two_unit_bias`). Two independent units with
  a covariate `x` in two equally likely strata, all in the arm `true`, outcome `Y = 1{x}`, and
  the weight `1/e(x)` with `e(true) = 1`, `e(false) = 1/3`: the weights are proportional to the
  density ratio `(1/2, 3/2)` of the target law `P(x) = 1/4` against the source. The population
  ratio `E[Y/e(X)] / E[1/e(X)]` is the target mean `1/4`, the Hájek denominator is positive on
  every sample, and the expectation of the two unit Hájek estimate
  `(1/4)·1 + (1/4)·0 + (1/2)·(1/4)` is `3/8`.

## Main definitions

* `twoUnitScore`, `twoUnitSample`: the score and the two unit sample of the Hájek
  computation.

## Main results

* `Trial.isCondMean_of_indepFun`, `randomized_trial_example`.
* `hajek_two_unit_bias`.

## References

* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70 (1983).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison PointTreatment

/-! ### A randomized trial -/

section Randomized

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {T : Trial Ω 𝒳 Bool}

/-- **A randomized trial gives conditional mean functions.** In a trial with treatments `Bool`,
measurable covariate, assignment and potential outcomes, integrable potential outcomes, the
assignment independent of the covariate and the potential outcomes, and
`0 < P(A = true) < 1`, every version `m` of the observed regression `E[Y | X, A]` gives
conditional mean functions `m(t, ·)` of both arms in the trial population, and the trial
marginal effect of `true` relative to `false` on any scale is
`linkMarginal g P_X m_false m_true`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.isCondMean_of_indepFun
    [IsFiniteMeasure T.μ] (hX : Measurable T.X) (hA : Measurable T.A)
    (hY : ∀ t, Measurable (T.Y t)) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hind : IndepFun T.A (fun ω => (T.X ω, potentialPair T.Y ω)) T.μ)
    (hp₀ : 0 < T.μ.real (T.A ⁻¹' {true})) (hp₁ : T.μ.real (T.A ⁻¹' {true}) < 1)
    {m : Bool → 𝒳 → ℝ} (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m) (g : ℝ → ℝ) :
    (∀ t, T.toPopulation.IsCondMean t (m t)) ∧
      T.toPopulation.marginalEffect g false true =
        linkMarginal g T.toPopulation.covLaw (m false) (m true) := by
  have hii := indicatorIgnorable_of_indepFun hX hA hY hind
  have hps := isPropensityScore_const_of_indepFun hX hA (hind.comp measurable_id measurable_fst)
  have hcm : ∀ t, T.toPopulation.IsCondMean t (m t) := fun t =>
    T.isCondMean_of_isOutcomeRegression hX hA hYi hreg hps t
      (hii.meanIgnorable hX hA hY t (hYi t))
      (Filter.Eventually.of_forall fun _ => by cases t <;> simp [armProb] <;> linarith)
  exact ⟨hcm, T.toPopulation.marginalEffect_eq_linkMarginal g hX (hYi false) (hYi true)
    (hcm false) (hcm true)⟩

end Randomized

/-- **An instance of `Trial.isCondMean_of_indepFun`.** In `standardizationTrial` (two equally
likely arms, trivial covariate, `Y(true) = 1`, `Y(false) = 0`) the potential outcomes are
constant, so the assignment is independent of the covariate and the potential outcomes, the
treated arm has probability `1/2`, and `m(t) = 1{t}` is a version of the observed regression:
these are the hypotheses of `Trial.isCondMean_of_indepFun`, which then gives the conditional mean
functions of both arms; the trial effect on the identity scale is `1`. -/
theorem randomized_trial_example :
    IndepFun standardizationTrial.A
        (fun ω => (standardizationTrial.X ω, potentialPair standardizationTrial.Y ω))
        standardizationTrial.μ ∧
      standardizationTrial.μ.real (standardizationTrial.A ⁻¹' {true}) = 1 / 2 ∧
      IsOutcomeRegression standardizationTrial.μ standardizationTrial.A standardizationTrial.X
        standardizationTrial.obsOutcome standardizationTrialRegression ∧
      (∀ t, standardizationTrial.toPopulation.IsCondMean t (standardizationTrialRegression t)) ∧
      standardizationTrial.toPopulation.marginalEffect id false true = 1 := by
  set T := standardizationTrial
  have hX : Measurable T.X := measurable_const
  have hA : Measurable T.A := measurable_id
  have hμ : IsProbabilityMeasure T.μ := by simp only [T, standardizationTrial]; infer_instance
  have hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome standardizationTrialRegression := by
    refine ⟨fun _ => measurable_of_finite _, ?_⟩
    have hm : Measurable[MeasurableSpace.comap (fun ω => (T.X ω, T.A ω)) inferInstance]
        T.obsOutcome :=
      (measurable_of_finite fun q : Unit × Bool => standardizationTrialRegression q.2 q.1).comp
        (comap_measurable _)
    rw [condExp_of_stronglyMeasurable (hX.prodMk hA).comap_le hm.stronglyMeasurable
      Integrable.of_finite]
    exact Filter.Eventually.of_forall fun ω => rfl
  have hind : IndepFun T.A (fun ω => (T.X ω, potentialPair T.Y ω)) T.μ :=
    indepFun_const_right T.A (((), ((0 : ℝ), (1 : ℝ))) : Unit × ℝ × ℝ)
  have hp : T.μ.real (T.A ⁻¹' {true}) = 1 / 2 := by
    change halfLaw.real (id ⁻¹' {true}) = 1 / 2
    rw [Set.preimage_id, measureReal_def, halfLaw, stratumLaw]
    simp
  obtain ⟨hcm, hm⟩ := T.isCondMean_of_indepFun hX hA (fun _ => measurable_const)
    (fun _ => Integrable.of_finite) hind (by rw [hp]; norm_num) (by rw [hp]; norm_num) hreg id
  refine ⟨hind, hp, hreg, hcm, ?_⟩
  rw [hm]
  have : IsProbabilityMeasure T.toPopulation.covLaw := T.toPopulation.isProbabilityMeasure_covLaw hX
  simp [linkMarginal, standardizationTrialRegression]

/-! ### The Hájek weighted mean -/

/-- The weight score of `hajek_two_unit_bias`: `e(true) = 1`, `e(false) = 1/3`. -/
noncomputable def twoUnitScore (x : Bool) : ℝ := if x then 1 else 1 / 3

/-- The two units of `hajek_two_unit_bias` on the sample space `Bool × Bool`: unit `0` has
covariate `ξ.1`, unit `1` covariate `ξ.2` (and further units repeat unit `1`); every unit is in
the arm `true` with outcome `1{x}`. -/
def twoUnitSample (i : ℕ) (ξ : Bool × Bool) : Bool × Bool × ℝ :=
  let x := if i = 0 then ξ.1 else ξ.2
  (x, true, if x then 1 else 0)

/-- **The Hájek weighted mean is not unbiased.** Two independent units with covariates in two
equally likely strata (the law `halfLaw ⊗ halfLaw` on `Bool × Bool`), all in the arm `true`,
outcome `1{x}`, and the score `e = twoUnitScore`, whose inverse `1/e` is twice the density ratio
`(1/2, 3/2)` of the target law `P(x) = 1/4` against `halfLaw`. Then:
* the population weighted mean `E[Y/e(X)] / E[1/e(X)]` is the target mean `1/4`;
* the Hájek denominator is positive on every sample of size two;
* the expectation of the two unit Hájek estimate is `3/8`, not `1/4`. -/
theorem hajek_two_unit_bias :
    (∀ x, 1 / twoUnitScore x = 2 * ((if x then 1 / 4 else 3 / 4) / (1 / 2))) ∧
      (∫ x, (if x then (1 : ℝ) else 0) / twoUnitScore x ∂halfLaw) /
          (∫ x, 1 / twoUnitScore x ∂halfLaw) =
        ∫ x, (if x then (1 : ℝ) else 0) ∂standardizationTargetLaw ∧
      (∫ x, (if x then (1 : ℝ) else 0) ∂standardizationTargetLaw) = 1 / 4 ∧
      (∀ ξ, 0 < sampleIpwWeightMean (fun _ _ => twoUnitScore) true twoUnitSample 2 ξ) ∧
      ∫ ξ, sampleHajekArmMean (fun _ _ => twoUnitScore) true twoUnitSample 2 ξ
          ∂(halfLaw.prod halfLaw) = 3 / 8 := by
  have hint : ∀ f : Bool → ℝ, ∫ x, f x ∂standardizationTargetLaw = f true / 4 + 3 * f false / 4 :=
    fun f => by
      rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
      simp [standardizedRisk]; ring
  have hval : ∀ ξ : Bool × Bool,
      sampleHajekArmMean (fun _ _ => twoUnitScore) true twoUnitSample 2 ξ =
      ((if ξ.1 then 1 else 0) / twoUnitScore ξ.1 + (if ξ.2 then 1 else 0) / twoUnitScore ξ.2) /
        (1 / twoUnitScore ξ.1 + 1 / twoUnitScore ξ.2) := fun ξ => by
    simp only [sampleHajekArmMean, sampleIpwArmMean, sampleIpwWeightMean, sampleMean, ipwObs,
      ipwWeightObs, armIndObs, armProb, twoUnitSample, Finset.sum_range_succ, Finset.sum_range_zero]
    simp
    field_simp
  refine ⟨fun x => by cases x <;> norm_num [twoUnitScore], ?_, hint _ ▸ by norm_num,
    fun ξ => ?_, ?_⟩
  · rw [integral_halfLaw, integral_halfLaw, hint]
    norm_num [twoUnitScore]
  · simp only [sampleIpwWeightMean, sampleMean, ipwWeightObs, armIndObs, armProb, twoUnitSample,
      Finset.sum_range_succ, Finset.sum_range_zero]
    cases ξ.1 <;> cases ξ.2 <;> norm_num [twoUnitScore]
  · simp_rw [hval]
    rw [integral_prod _ Integrable.of_finite, integral_halfLaw]
    simp only [integral_halfLaw]
    norm_num [twoUnitScore]

end PopulationAdjustment

end CausalInference
