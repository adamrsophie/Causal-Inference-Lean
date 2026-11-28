/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitFollowUpInstances
public import CausalInference.PopulationAdjustment.StandardizationInstancesAnchored
public import CausalInference.PointTreatment.WeightingConsistency

/-!
# Anchored comparisons of three distinct treatments: weighting and standardization

Every hypothesis of `anchored_identity_identified`, `anchored_link_identified`,
`commonLimit_leastSquares_anchored` and `commonLimit_leastSquares_anchored_identity` is verified
with three distinct treatments `a = 0`, `b = 1`, `c = 2` and a reported contrast of `b` against
`c` that is not constant.

* **The index trial** is `lsExampleTrial` (a binary covariate with `P(X = 1) = 1/2`, a fair coin,
  potential outcomes `Y(t) = 1[x] + 1[t](1 + 1[x])`, no noise), fitted with the interaction design
  of the feature `φ(x) = 1[x]` matched at `t = 1/4`. Its arm `true` stands for `a` and its arm
  `false` for `c`.
* **The target** is `anchoredInstTarget`: `P(X = 1) = 1/4`, the outcomes of `a` and `c` are those
  of the two arms of the trial, and `b` has the outcome `1 + 1[x]`. The target means are `3/2`,
  `5/4` and `1/4`, all positive.
* **The reported contrasts** of `c` against `b` are deterministic sequences that converge to the
  true target contrast, as an aggregate estimate from a growing trial of `b` against `c` in the
  target does: `-1 + 1/(n + 1)` on the identity scale (target contrast `1/4 - 5/4 = -1`) and
  `-log 5 + 1/(n + 1)` on the log scale (target contrast `log(1/4) - log(5/4) = -log 5`).

**Limits.** On the identity scale both anchored estimators converge in probability to the target
effect `E_Q[Y(b)] - E_Q[Y(a)] = 5/4 - 3/2 = -1/4`, under relative constancy
(`commonLimitFollowUpAnch_relativeConstancy`) and under absolute constancy. On the log scale both
converge to `log(5/4) - log(3/2) = log(5/6)`. In each case their difference converges to `0`.

**The unadjusted indirect comparison** subtracts the reported contrast from the difference of the
observed arm means of the trial, `1/2 - 2 = -3/2` in the limit. It converges to
`-3/2 - (-1) = -1/2 ≠ -1/4` on the identity scale and to `log(1/2) - log 2 + log 5 = log(5/4) ≠
log(5/6)` on the log scale (`commonLimitFollowUpAnch_unadjusted`): the covariate modifies the
effect and its law differs between the trial and the target.

## Main definitions

* `commonLimitFollowUpAnchReported`, `commonLimitFollowUpAnchReportedLog`.

## Main results

* `commonLimitFollowUpAnch_relativeConstancy`.
* `commonLimitFollowUpAnch_identity`, `commonLimitFollowUpAnch_log`.
* `commonLimitFollowUpAnch_leastSquares_identity`, `commonLimitFollowUpAnch_leastSquares_log`.
* `commonLimitFollowUpAnch_unadjusted`.

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

/-- The reported contrast of `c` against `b` on the identity scale: `-1 + 1/(n + 1)`. -/
noncomputable def commonLimitFollowUpAnchReported (n : ℕ) (_ : ℕ → Bool × Bool) : ℝ :=
  -1 + 1 / ((n : ℝ) + 1)

/-- The reported contrast of `c` against `b` on the log scale: `-log 5 + 1/(n + 1)`. -/
noncomputable def commonLimitFollowUpAnchReportedLog (n : ℕ) (_ : ℕ → Bool × Bool) : ℝ :=
  -Real.log 5 + 1 / ((n : ℝ) + 1)

theorem commonLimitFollowUpAnch_effect_id :
    anchoredInstTarget.marginalEffect id 0 1 = -1 / 4 ∧
      anchoredInstTarget.marginalEffect id 1 2 = -1 ∧
      anchoredInstTarget.marginalEffect id 0 2 = -5 / 4 := by
  obtain ⟨h0, h1, h2⟩ := anchoredInstTarget_armMean
  simp only [Population.marginalEffect, id, h0, h1, h2]
  norm_num

theorem commonLimitFollowUpAnch_effect_log :
    anchoredInstTarget.marginalEffect Real.log 0 1 = Real.log (5 / 6) ∧
      anchoredInstTarget.marginalEffect Real.log 1 2 = -Real.log 5 := by
  obtain ⟨h0, h1, h2⟩ := anchoredInstTarget_armMean
  simp only [Population.marginalEffect, h0, h1, h2]
  refine ⟨?_, ?_⟩
  · rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  · rw [← Real.log_div (by norm_num) (by norm_num), show (1 / 4 : ℝ) / (5 / 4) = 5⁻¹ by norm_num,
      Real.log_inv]

theorem commonLimitFollowUpAnch_reported :
    TendstoInMeasure lsExampleSampleLaw commonLimitFollowUpAnchReported atTop
      fun _ => anchoredInstTarget.marginalEffect id 1 2 := by
  rw [commonLimitFollowUpAnch_effect_id.2.1]
  exact tendstoInMeasure_add_one_div_succ _ _

theorem commonLimitFollowUpAnch_reportedLog :
    TendstoInMeasure lsExampleSampleLaw commonLimitFollowUpAnchReportedLog atTop
      fun _ => anchoredInstTarget.marginalEffect Real.log 1 2 := by
  rw [commonLimitFollowUpAnch_effect_log.2]
  exact tendstoInMeasure_add_one_div_succ _ _

theorem commonLimitFollowUpAnch_continuousAt_log (s : Fin 3) (hs : s = 0 ∨ s = 2) :
    ContinuousAt Real.log (anchoredInstTarget.armMean s) := by
  obtain ⟨h0, -, h2⟩ := anchoredInstTarget_armMean
  refine Real.continuousAt_log ?_
  rcases hs with rfl | rfl
  · rw [h0]; norm_num
  · rw [h2]; norm_num

/-- **Relative constancy on the identity scale** from the index trial, its arms named `a = 0`
and `c = 2`, to the target. -/
theorem commonLimitFollowUpAnch_relativeConstancy :
    RelativeConstancy id (lsExampleTrial.relabelArms (0 : Fin 3) 2).toPopulation
      anchoredInstTarget 0 2 := by
  have h0 : (lsExampleTrial.relabelArms (0 : Fin 3) 2).Y 0 = lsExampleTrial.Y true := by
    simp [Trial.relabelArms]
  have h2 : (lsExampleTrial.relabelArms (0 : Fin 3) 2).Y 2 = lsExampleTrial.Y false := by
    simp [Trial.relabelArms]
  refine relativeConstancy_of_structurallyInvariant ?_ ?_
  · change StructurallyInvariant lsExampleTrial.μ lsExampleTrial.X
      ((lsExampleTrial.relabelArms (0 : Fin 3) 2).Y 0) _ _ _
    rw [h0]
    exact anchoredInst_structurallyInvariant true 0 rfl
  · change StructurallyInvariant lsExampleTrial.μ lsExampleTrial.X
      ((lsExampleTrial.relabelArms (0 : Fin 3) 2).Y 2) _ _ _
    rw [h2]
    exact anchoredInst_structurallyInvariant false 2 rfl

/-! ### The comparisons composed with identification -/

/-- The target mean of the matched feature `1[x]` is `1/4`. -/
theorem commonLimitFollowUpAnch_featureMean (k : Fin 1) :
    ∫ x, commonLimitExampleFeature x k ∂anchoredInstTarget.covLaw = commonLimitExampleMean k := by
  rw [anchoredInstTarget_covLaw, standardizationTargetLaw,
    integral_stratumLaw (fun v => by cases v <;> norm_num)]
  simp [standardizedRisk, commonLimitExampleFeature, commonLimitExampleMean]

/-- **The anchored comparison of three treatments on the identity scale under relative
constancy.** Every hypothesis of `anchored_identity_identified` holds with `a = 0`, `b = 1`,
`c = 2` and the reported contrast `-1 + 1/(n + 1)`: the identified conditional estimand of the
index comparison is `E_Q[Y(c)] - E_Q[Y(a)] = -5/4`, the weighted and the standardized anchored
comparisons both converge in probability to `-1/4`, and their difference converges in
probability to `0`. -/
theorem commonLimitFollowUpAnch_identity :
    linkConditional id anchoredInstTarget.covLaw
        (fun x => featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          commonLimitExampleCoef)
        (fun x => featureInteractionDesign commonLimitExampleFeature false x ⬝ᵥ
          commonLimitExampleCoef) = -5 / 4 ∧
      IsConsistent (anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
        lsExampleSample commonLimitFollowUpAnchReported) (-1 / 4) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample false n ω -
        commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample true n ω - commonLimitFollowUpAnchReported n ω)
        atTop (fun _ => -1 / 4) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        (commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample false n ω -
        commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample true n ω - commonLimitFollowUpAnchReported n ω) -
          anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
            lsExampleSample commonLimitFollowUpAnchReported n ω) atTop (fun _ => 0) := by
  obtain ⟨e01, -, e02⟩ := commonLimitFollowUpAnch_effect_id
  rw [← e01, ← e02]
  exact anchored_identity_identified (Q := anchoredInstTarget) (a := (0 : Fin 3)) (b := 1) (c := 2)
    lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_regression
    commonLimitExample_variance isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) measurable_id commonLimitFollowUpAnch_featureMean (by decide)
    Integrable.of_finite Integrable.of_finite commonLimitFollowUpAnch_relativeConstancy
    anchoredInst_absolutelyContinuous commonLimitFollowUpAnch_reported

/-- **The anchored comparison of three treatments on the log scale under absolute constancy.**
Every hypothesis of `anchored_link_identified` holds with the log link, `a = 0`, `b = 1`,
`c = 2`, both arms of the trial carried over to the target, and the reported contrast
`-log 5 + 1/(n + 1)`; the target means `3/2` and `1/4` are positive. The weighted and the
standardized anchored comparisons both converge in probability to `log(5/6)`, and their
difference converges in probability to `0`. -/
theorem commonLimitFollowUpAnch_log :
    IsConsistent (anchoredBalancedEstimate Real.log commonLimitExampleFeature
      commonLimitExampleMean lsExampleSample commonLimitFollowUpAnchReportedLog)
      (Real.log (5 / 6)) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        Real.log (commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample false n ω) -
        Real.log (commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample true n ω) - commonLimitFollowUpAnchReportedLog n ω)
        atTop (fun _ => Real.log (5 / 6)) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        (Real.log (commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample false n ω) -
        Real.log (commonLimitStandardized commonLimitExampleFeature anchoredInstTarget.covLaw
          lsExampleSample true n ω) - commonLimitFollowUpAnchReportedLog n ω) -
          anchoredBalancedEstimate Real.log commonLimitExampleFeature commonLimitExampleMean
            lsExampleSample commonLimitFollowUpAnchReportedLog n ω) atTop (fun _ => 0) := by
  rw [← commonLimitFollowUpAnch_effect_log.1]
  exact anchored_link_identified (Q := anchoredInstTarget) (a := (0 : Fin 3)) (b := 1) (c := 2)
    (g := Real.log)
    lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_regression
    commonLimitExample_variance isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) measurable_id commonLimitFollowUpAnch_featureMean Integrable.of_finite
    Integrable.of_finite (anchoredInst_structurallyInvariant true 0 rfl)
    (anchoredInst_structurallyInvariant false 2 rfl) anchoredInst_absolutelyContinuous
    commonLimitFollowUpAnch_reportedLog (commonLimitFollowUpAnch_continuousAt_log 0 (.inl rfl))
    (commonLimitFollowUpAnch_continuousAt_log 2 (.inr rfl))

/-! ### The least squares anchored comparisons -/

theorem commonLimitFollowUpAnch_linearOutcomeModel :
    lsExampleTrial.LinearOutcomeModel (featureInteractionDesign commonLimitExampleFeature)
      commonLimitExampleCoef :=
  lsExampleTrial.linearOutcomeModel_featureInteraction lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num : (0 : ℝ) < 1 / 4) commonLimitExample_margin commonLimitExample_regression

/-- **Relative constancy in the form of `commonLimit_leastSquares_anchored_identity`**: the
conditional contrast `z(false, ·)ᵀξ₀ - z(true, ·)ᵀξ₀` of the trial is the conditional mean of
`Y(c) - Y(a)` in the target. -/
theorem commonLimitFollowUpAnch_condExp_contrast :
    (fun ω => featureInteractionDesign commonLimitExampleFeature false (anchoredInstTarget.X ω) ⬝ᵥ
        commonLimitExampleCoef -
      featureInteractionDesign commonLimitExampleFeature true (anchoredInstTarget.X ω) ⬝ᵥ
        commonLimitExampleCoef) =ᵐ[anchoredInstTarget.μ]
      anchoredInstTarget.μ[fun ω => anchoredInstTarget.Y 2 ω - anchoredInstTarget.Y 0 ω |
        MeasurableSpace.comap anchoredInstTarget.X inferInstance] := by
  have hX : Measurable anchoredInstTarget.X := measurable_id
  have hm : Measurable[MeasurableSpace.comap anchoredInstTarget.X inferInstance]
      (fun ω => anchoredInstTarget.Y 2 ω - anchoredInstTarget.Y 0 ω) := by
    change Measurable[MeasurableSpace.comap anchoredInstTarget.X inferInstance]
      ((fun x => anchoredInstOutcome 2 x - anchoredInstOutcome 0 x) ∘ anchoredInstTarget.X)
    exact (measurable_of_finite _).comp (comap_measurable _)
  rw [condExp_of_stronglyMeasurable hX.comap_le hm.stronglyMeasurable Integrable.of_finite]
  refine EventuallyEq.of_eq (funext fun ω => ?_)
  rw [commonLimitExample_dotProduct, commonLimitExample_dotProduct]
  rfl

/-- **The three treatment instance of `commonLimit_leastSquares_anchored_identity`.** With the
reported contrast `-1 + 1/(n + 1)`, the weighted anchored comparison and the standardized one,
`linkMarginal id Q_X (z(true, ·)ᵀξ̂) (z(false, ·)ᵀξ̂) - d̂_bc`, both converge in probability to
`-1/4`, and their difference converges in probability to `0`. -/
theorem commonLimitFollowUpAnch_leastSquares_identity :
    IsConsistent (anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
        lsExampleSample commonLimitFollowUpAnchReported) (-1 / 4) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => linkMarginal id anchoredInstTarget.covLaw
        (fun x => featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω)
        (fun x => featureInteractionDesign commonLimitExampleFeature false x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω) -
          commonLimitFollowUpAnchReported n ω) atTop (fun _ => -1 / 4) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => (linkMarginal id anchoredInstTarget.covLaw
        (fun x => featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω)
        (fun x => featureInteractionDesign commonLimitExampleFeature false x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω) -
          commonLimitFollowUpAnchReported n ω) -
        anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
          lsExampleSample commonLimitFollowUpAnchReported n ω) atTop (fun _ => 0) := by
  rw [← commonLimitFollowUpAnch_effect_id.1]
  exact commonLimit_leastSquares_anchored_identity (Q := anchoredInstTarget) (a := (0 : Fin 3))
    (b := 1) (c := 2)
    lsExampleTrial_isRandomizedTwoArm commonLimitFollowUpAnch_linearOutcomeModel
    isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_variance
    (α := fun e => interactionIntercept commonLimitExampleCoef +
      if e then interactionEffect commonLimitExampleCoef else 0)
    (β := fun e => interactionMain commonLimitExampleCoef +
      if e then interactionModifier commonLimitExampleCoef else 0)
    (fun e x => featureInteractionDesign_dotProduct commonLimitExampleFeature e x
      commonLimitExampleCoef) measurable_id commonLimitFollowUpAnch_featureMean
    (fun _ _ => Integrable.of_finite) Integrable.of_finite Integrable.of_finite
    commonLimitFollowUpAnch_condExp_contrast commonLimitFollowUpAnch_reported

/-- **The three treatment instance of `commonLimit_leastSquares_anchored` on the log scale.**
With both arms carried over and the reported contrast `-log 5 + 1/(n + 1)`, the weighted anchored
comparison and the standardized one,
`linkMarginal log Q_X (z(true, ·)ᵀξ̂) (z(false, ·)ᵀξ̂) - d̂_bc`, both converge in probability to
`log(5/6)`, and their difference converges in probability to `0`. -/
theorem commonLimitFollowUpAnch_leastSquares_log :
    IsConsistent (anchoredBalancedEstimate Real.log commonLimitExampleFeature
        commonLimitExampleMean lsExampleSample commonLimitFollowUpAnchReportedLog)
        (Real.log (5 / 6)) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => linkMarginal Real.log
        anchoredInstTarget.covLaw
        (fun x => featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω)
        (fun x => featureInteractionDesign commonLimitExampleFeature false x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω) -
          commonLimitFollowUpAnchReportedLog n ω) atTop (fun _ => Real.log (5 / 6)) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => (linkMarginal Real.log
        anchoredInstTarget.covLaw
        (fun x => featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω)
        (fun x => featureInteractionDesign commonLimitExampleFeature false x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω) -
          commonLimitFollowUpAnchReportedLog n ω) -
        anchoredBalancedEstimate Real.log commonLimitExampleFeature commonLimitExampleMean
          lsExampleSample commonLimitFollowUpAnchReportedLog n ω) atTop (fun _ => 0) := by
  rw [← commonLimitFollowUpAnch_effect_log.1]
  exact commonLimit_leastSquares_anchored (Q := anchoredInstTarget) (a := (0 : Fin 3)) (b := 1)
    (c := 2)
    lsExampleTrial_isRandomizedTwoArm commonLimitFollowUpAnch_linearOutcomeModel
    isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_variance
    (α := fun e => interactionIntercept commonLimitExampleCoef +
      if e then interactionEffect commonLimitExampleCoef else 0)
    (β := fun e => interactionMain commonLimitExampleCoef +
      if e then interactionModifier commonLimitExampleCoef else 0)
    (fun e x => featureInteractionDesign_dotProduct commonLimitExampleFeature e x
      commonLimitExampleCoef) measurable_id commonLimitFollowUpAnch_featureMean
    (fun _ _ => Integrable.of_finite) Integrable.of_finite Integrable.of_finite
    (anchoredInst_structurallyInvariant true 0 rfl)
    (anchoredInst_structurallyInvariant false 2 rfl) anchoredInst_absolutelyContinuous
    commonLimitFollowUpAnch_reportedLog (commonLimitFollowUpAnch_continuousAt_log 0 (.inl rfl))
    (commonLimitFollowUpAnch_continuousAt_log 2 (.inr rfl))

/-! ### The unadjusted indirect comparison -/

/-- The arm means of the index trial in its own population: `2` for arm `true` and `1/2` for
arm `false`. -/
theorem commonLimitFollowUpAnch_trial_armMean :
    PointTreatment.armMean lsExampleTrial.μ lsExampleTrial.Y true = 2 ∧
      PointTreatment.armMean lsExampleTrial.μ lsExampleTrial.Y false = 1 / 2 := by
  have h : ∀ t, PointTreatment.armMean lsExampleTrial.μ lsExampleTrial.Y t =
      (lsExampleOutcome t true + lsExampleOutcome t false) / 2 := fun t => by
    change ∫ ω, lsExampleOutcome t ω.2 ∂(halfLaw.prod halfLaw) = _
    rw [integral_prod _ Integrable.of_finite]
    simp only [integral_const, smul_eq_mul, probReal_univ, one_mul, integral_halfLaw]
  rw [h, h]
  simp [lsExampleOutcome]
  norm_num

theorem commonLimitFollowUpAnch_isConsistent_sampleArmMean (t : Bool) :
    IsConsistent (sampleArmMean t lsExampleSample)
      (PointTreatment.armMean lsExampleTrial.μ lsExampleTrial.Y t) lsExampleSampleLaw :=
  isConsistent_sampleArmMean_of_indepFun lsExampleTrial_isRandomizedTwoArm.measurable_X
    lsExampleTrial_isRandomizedTwoArm.measurable_A lsExampleTrial_isRandomizedTwoArm.measurable_Y
    lsExampleTrial_isRandomizedTwoArm.indepFun lsExampleTrial_isRandomizedTwoArm.prob_pos
    lsExampleTrial_isRandomizedTwoArm.prob_lt_one t Integrable.of_finite
    isIIDSample_lsExampleSample (map_lsExampleSample 0)

/-- **The unadjusted indirect comparison has a different limit.** The unadjusted comparison takes
the difference of the observed arm means of the index trial, `μ̂_false - μ̂_true`, in place of the
standardized one and subtracts the same reported contrast. On the identity scale it converges in
probability to `(1/2 - 2) - (-1) = -1/2`, not to the anchored limit `-1/4`; on the log scale it
converges to `log(1/2) - log 2 + log 5 = log(5/4)`, not to `log(5/6)`. -/
theorem commonLimitFollowUpAnch_unadjusted :
    TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        sampleArmMean false lsExampleSample n ω - sampleArmMean true lsExampleSample n ω -
          commonLimitFollowUpAnchReported n ω) atTop (fun _ => -1 / 2) ∧
      (-1 / 2 : ℝ) ≠ -1 / 4 ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        Real.log (sampleArmMean false lsExampleSample n ω) -
          Real.log (sampleArmMean true lsExampleSample n ω) -
          commonLimitFollowUpAnchReportedLog n ω) atTop (fun _ => Real.log (5 / 4)) ∧
      Real.log (5 / 4) ≠ Real.log (5 / 6) := by
  obtain ⟨h1, h0⟩ := commonLimitFollowUpAnch_trial_armMean
  have hT := commonLimitFollowUpAnch_isConsistent_sampleArmMean true
  have hF := commonLimitFollowUpAnch_isConsistent_sampleArmMean false
  rw [h1] at hT
  rw [h0] at hF
  have hR : TendstoInMeasure lsExampleSampleLaw commonLimitFollowUpAnchReported atTop
      fun _ => -1 := tendstoInMeasure_add_one_div_succ _ _
  have hRL : TendstoInMeasure lsExampleSampleLaw commonLimitFollowUpAnchReportedLog atTop
      fun _ => -Real.log 5 := tendstoInMeasure_add_one_div_succ _ _
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · have h := (hF.sub hT).sub hR
    have e : (1 / 2 : ℝ) - 2 - -1 = -1 / 2 := by norm_num
    simp only [Pi.sub_def, e] at h
    exact h
  · have hL1 : IsConsistent (fun n ω => Real.log (sampleArmMean true lsExampleSample n ω))
        (Real.log 2) lsExampleSampleLaw :=
      hT.comp_continuousAt (Real.continuousAt_log (by norm_num))
    have hL0 : IsConsistent (fun n ω => Real.log (sampleArmMean false lsExampleSample n ω))
        (Real.log (1 / 2)) lsExampleSampleLaw :=
      hF.comp_continuousAt (Real.continuousAt_log (by norm_num))
    have h := (hL0.sub hL1).sub hRL
    have e : Real.log (1 / 2) - Real.log 2 - -Real.log 5 = Real.log (5 / 4) := by
      rw [Real.log_div (x := 5) (y := 4) (by norm_num) (by norm_num), one_div, Real.log_inv,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    simp only [Pi.sub_def, e] at h
    exact h
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (by norm_num : (0 : ℝ) < 5 / 4))
      (Set.mem_Ioi.2 (by norm_num : (0 : ℝ) < 5 / 6)) h
    norm_num at this

end PopulationAdjustment

end CausalInference
