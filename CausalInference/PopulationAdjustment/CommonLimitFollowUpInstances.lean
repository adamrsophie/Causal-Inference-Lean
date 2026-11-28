/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitExamples

/-!
# Instances of the comparisons composed with identification

Every hypothesis of `unanchored_identified`, `anchored_identity_identified` and
`anchored_link_identified` is verified in the model of `CommonLimitExamples`: the randomized
trial `lsExampleTrial` with a binary covariate, the outcome `Y(a) = 1[x] + 1[a](1 + 1[x])`
(regression linear in the interaction design of `φ(x) = 1[x]`, no residual), the target
`lsExampleTarget` with the covariate `true` with probability `1/4`, and the matched feature mean
`t = 1/4`. The target means are `E_Q[Y(true)] = 3/2` and `E_Q[Y(false)] = 1/4`, both positive, so
the log link is continuous at both.

* **Unanchored, log scale** (`commonLimitFollowUpInst_unanchored`): treatment `a = true` from the
  trial, treatment `b = false` from a second source (the control arm of the trial, which carries
  over to the target), the reported mean of `b` exact. Both estimators converge to
  `log(1/4) - log(3/2) = -log 6`.
* **Anchored, identity scale, relative constancy** (`commonLimitFollowUpInst_anchored_identity`):
  `RelativeConstancy id (lsExampleTrial.relabelArms true false).toPopulation lsExampleTarget
  true false` is verified (`commonLimitFollowUpInst_relativeConstancy`); the identified estimand
  and both limits are `1/4 - 3/2 = -5/4`.
* **Anchored, log scale, absolute constancy** (`commonLimitFollowUpInst_anchored_log`): both
  estimators converge to `-log 6`.

## Main results

* `commonLimitFollowUpInst_armMean_false`, `commonLimitFollowUpInst_relativeConstancy`.
* `commonLimitFollowUpInst_unanchored`, `commonLimitFollowUpInst_anchored_identity`,
  `commonLimitFollowUpInst_anchored_log`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The target mean of `Y(false)` in the example is `1/4`. -/
theorem commonLimitFollowUpInst_armMean_false : lsExampleTarget.armMean false = 1 / 4 := by
  have h := lsExample_marginalEffect
  have h1 := commonLimitExample_armMean_value
  simp only [Population.marginalEffect, id] at h
  linarith

/-- The log scale effect of `false` relative to `true` in the target is `-log 6`. -/
theorem commonLimitFollowUpInst_marginalEffect_log :
    lsExampleTarget.marginalEffect Real.log true false = -Real.log 6 := by
  rw [Population.marginalEffect, commonLimitFollowUpInst_armMean_false,
    commonLimitExample_armMean_value, ← Real.log_div (by norm_num) (by norm_num),
    show (1 / 4 : ℝ) / (3 / 2) = 6⁻¹ by norm_num, Real.log_inv]

/-- The identity scale effect of `false` relative to `true` in the target is `-5/4`. -/
theorem commonLimitFollowUpInst_marginalEffect_id :
    lsExampleTarget.marginalEffect id true false = -5 / 4 := by
  rw [Population.marginalEffect, commonLimitFollowUpInst_armMean_false,
    commonLimitExample_armMean_value]
  norm_num

/-- The control arm regression `lsExampleOutcome false` is a conditional mean function of
`Y(false)` in the trial. -/
theorem commonLimitFollowUpInst_isCondMean_false :
    lsExampleTrial.toPopulation.IsCondMean false (lsExampleOutcome false) := by
  have hm : Measurable[MeasurableSpace.comap lsExampleTrial.X inferInstance]
      (lsExampleTrial.Y false) :=
    (measurable_of_finite (lsExampleOutcome false)).comp (comap_measurable _)
  exact ⟨measurable_of_finite _, EventuallyEq.of_eq (condExp_of_stronglyMeasurable
    lsExampleTrial_isRandomizedTwoArm.measurable_X.comap_le hm.stronglyMeasurable
    Integrable.of_finite).symm⟩

theorem commonLimitFollowUpInst_continuousAt_log (a : Bool) :
    ContinuousAt Real.log (lsExampleTarget.armMean a) := by
  refine Real.continuousAt_log ?_
  cases a
  · rw [commonLimitFollowUpInst_armMean_false]; norm_num
  · rw [commonLimitExample_armMean_value]; norm_num

/-- **The unanchored comparison on the log scale.** Every hypothesis of `unanchored_identified`
holds with the index arm `true ↦ a = true`, the source of `b = false` the control arm of the
trial (absolutely constant to the target, with overlap), the log link, and the reported mean of
`b` equal to the target mean `1/4`. The weighted and the standardized comparisons both converge
in probability to `log(1/4) - log(3/2) = -log 6`, the unanchored estimand is the target log
scale effect, and their difference converges in probability to `0`. -/
theorem commonLimitFollowUpInst_unanchored :
    IsConsistent (unanchoredBalancedEstimate Real.log commonLimitExampleFeature
      commonLimitExampleMean lsExampleSample fun _ _ => lsExampleTarget.armMean false)
      (-Real.log 6) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => Real.log (lsExampleTarget.armMean false) -
        Real.log (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω)) atTop (fun _ => -Real.log 6) ∧
      linkMarginal Real.log lsExampleTarget.covLaw
        (fun x => featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          commonLimitExampleCoef) (lsExampleOutcome false) =
        lsExampleTarget.marginalEffect Real.log true false ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => (Real.log (lsExampleTarget.armMean false) -
        Real.log (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω)) -
          unanchoredBalancedEstimate Real.log commonLimitExampleFeature commonLimitExampleMean
            lsExampleSample (fun _ _ => lsExampleTarget.armMean false) n ω) atTop
        (fun _ => 0) := by
  obtain ⟨hW, hS, heq, hd⟩ := unanchored_identified (a := true) (b := false)
    (Pb := lsExampleTrial.toPopulation) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_regression
    commonLimitExample_variance isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) measurable_id commonLimitExample_featureMean Integrable.of_finite
    Integrable.of_finite (lsExample_structurallyInvariant true) lsExample_absolutelyContinuous
    lsExampleTrial_isRandomizedTwoArm.measurable_X commonLimitFollowUpInst_isCondMean_false
    (lsExample_structurallyInvariant false) lsExample_absolutelyContinuous
    (commonLimitFollowUpInst_continuousAt_log true) (commonLimitFollowUpInst_continuousAt_log false)
    (tendstoInMeasure_const _)
  rw [heq, commonLimitFollowUpInst_marginalEffect_log] at hW hS
  exact ⟨hW, hS, heq, hd⟩

/-- **Relative constancy on the identity scale** from the relabeled trial (arm `true` is
treatment `true`, arm `false` is treatment `false`) to the target: both arms carry over. -/
theorem commonLimitFollowUpInst_relativeConstancy :
    RelativeConstancy id (lsExampleTrial.relabelArms true false).toPopulation lsExampleTarget
      true false :=
  relativeConstancy_of_structurallyInvariant (lsExample_structurallyInvariant true)
    (lsExample_structurallyInvariant false)

/-- **The anchored comparison on the identity scale under relative constancy.** Every hypothesis
of `anchored_identity_identified` holds with `a = true`, `c = false`, `b = false` and the
reported contrast `d̂_bc = 0`: the identified conditional estimand is the target effect
`1/4 - 3/2 = -5/4`, the weighted and the standardized anchored comparisons both converge in
probability to `-5/4`, and their difference converges in probability to `0`. -/
theorem commonLimitFollowUpInst_anchored_identity :
    linkConditional id lsExampleTarget.covLaw
        (fun x => featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          commonLimitExampleCoef)
        (fun x => featureInteractionDesign commonLimitExampleFeature false x ⬝ᵥ
          commonLimitExampleCoef) = -5 / 4 ∧
      IsConsistent (anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
        lsExampleSample fun _ _ => 0) (-5 / 4) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample false n ω -
        commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω - 0) atTop (fun _ => -5 / 4) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample false n ω -
        commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω - 0) -
          anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
            lsExampleSample (fun _ _ => 0) n ω) atTop (fun _ => 0) := by
  have h0 : lsExampleTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have hdbc : TendstoInMeasure lsExampleSampleLaw
      (fun (_ : ℕ) (_ : ℕ → Bool × Bool) => (0 : ℝ)) atTop
        fun _ => lsExampleTarget.marginalEffect id false false := by
    rw [h0]; exact tendstoInMeasure_const 0
  rw [← commonLimitFollowUpInst_marginalEffect_id]
  exact anchored_identity_identified (a := true) (b := false) (c := false)
    lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_regression
    commonLimitExample_variance isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) measurable_id commonLimitExample_featureMean (by decide)
    Integrable.of_finite Integrable.of_finite commonLimitFollowUpInst_relativeConstancy
    lsExample_absolutelyContinuous hdbc

/-- **The anchored comparison on the log scale under absolute constancy.** Every hypothesis of
`anchored_link_identified` holds with the log link, `a = true`, `c = false`, `b = false` and the
reported contrast `d̂_bc = 0`; the target means `3/2` and `1/4` are positive. The weighted and the
standardized anchored comparisons both converge in probability to `log(1/4) - log(3/2) = -log 6`,
and their difference converges in probability to `0`. -/
theorem commonLimitFollowUpInst_anchored_log :
    IsConsistent (anchoredBalancedEstimate Real.log commonLimitExampleFeature
      commonLimitExampleMean lsExampleSample fun _ _ => 0) (-Real.log 6) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        Real.log (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample false n ω) -
        Real.log (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω) - 0) atTop (fun _ => -Real.log 6) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        (Real.log (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample false n ω) -
        Real.log (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω) - 0) -
          anchoredBalancedEstimate Real.log commonLimitExampleFeature commonLimitExampleMean
            lsExampleSample (fun _ _ => 0) n ω) atTop (fun _ => 0) := by
  have h0 : lsExampleTarget.marginalEffect Real.log false false = 0 := by
    simp [Population.marginalEffect]
  have hdbc : TendstoInMeasure lsExampleSampleLaw
      (fun (_ : ℕ) (_ : ℕ → Bool × Bool) => (0 : ℝ)) atTop
        fun _ => lsExampleTarget.marginalEffect Real.log false false := by
    rw [h0]; exact tendstoInMeasure_const 0
  rw [← commonLimitFollowUpInst_marginalEffect_log]
  exact anchored_link_identified (a := true) (b := false) (c := false) (g := Real.log)
    lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_regression
    commonLimitExample_variance isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) measurable_id commonLimitExample_featureMean Integrable.of_finite
    Integrable.of_finite (lsExample_structurallyInvariant true)
    (lsExample_structurallyInvariant false) lsExample_absolutelyContinuous
    hdbc (commonLimitFollowUpInst_continuousAt_log true)
    (commonLimitFollowUpInst_continuousAt_log false)

end PopulationAdjustment

end CausalInference
