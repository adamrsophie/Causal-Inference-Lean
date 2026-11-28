/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitLikelihood
public import CausalInference.PopulationAdjustment.StandardizationInstancesLogistic

/-!
# Weighting and standardization with a logistic fit: a verified instance

Every hypothesis of `commonLimit_logistic_armMean` and `commonLimit_logistic_linkMarginal` is
verified in the logistic model of `StandardizationInstancesLogistic`: a fair coin `A`, a binary
covariate `x ∈ {0, 1} ⊂ ℝ¹` with `P(X = 1) = 1/2` in the trial and `3/4` in the target, and the
risks `σ(z(x, t) ⬝ ξ₀) = 1/3` when `t = x` and `2/3` otherwise, over the interaction design.

**The matched feature.** Both theorems ask the logistic regression of the arm to be affine in the
feature at every point of the covariate space `ℝ¹`, not only on the support `{0, 1}`. The linear
predictors of the two arms are opposite, `z(x, false) ⬝ ξ₀ = -(z(x, true) ⬝ ξ₀)`
(`commonLimitFollowUpLogit_predictor_false`), so both regressions are affine in the bounded
feature `φ(x) = σ(z(x, true) ⬝ ξ₀)`, the risk score of the active arm:
`m_true = φ` and `m_false = 1 - φ`. On the support it is the affine function `2/3 - x/3` of the
covariate. Its target mean is `t = 1/4 · 2/3 + 3/4 · 1/3 = 5/12`, and the margin condition holds
with `δ = 1/12`.

* `commonLimitFollowUpLogit_armMean`: the weighted arm mean of the active arm and the
  standardized logistic fit both converge in probability to the target arm mean `5/12`.
* `commonLimitFollowUpLogit_linkMarginal`: on the logit scale, the weighted and the standardized
  marginal log odds ratios of the arms `true ↦ a` against `false ↦ c` both converge in
  probability to `log (25/49)`, and their difference to `0`.

## Main definitions

* `commonLimitFollowUpLogitFeature`, `commonLimitFollowUpLogitMean`.

## Main results

* `commonLimitFollowUpLogit_margin`, `commonLimitFollowUpLogit_featureMean`.
* `commonLimitFollowUpLogit_armMean`, `commonLimitFollowUpLogit_linkMarginal`.

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

/-- The matched feature: the risk score `σ(z(x, true) ⬝ ξ₀)` of the active arm. -/
noncomputable def commonLimitFollowUpLogitFeature (x : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun _ => logisticInstSurface true x

/-- The target mean of the matched feature, `5/12`. -/
noncomputable def commonLimitFollowUpLogitMean : Fin 1 → ℝ := fun _ => 5 / 12

theorem commonLimitFollowUpLogit_measurable : Measurable commonLimitFollowUpLogitFeature :=
  measurable_pi_iff.2 fun _ => measurable_logisticInstSurface true

theorem commonLimitFollowUpLogit_feature_cov (b : Bool) (k : Fin 1) :
    commonLimitFollowUpLogitFeature (logisticInstCov b) k = if b then 1 / 3 else 2 / 3 := by
  rw [commonLimitFollowUpLogitFeature, logisticInstSurface, logisticInst_risk]
  cases b <;> simp

/-- The linear predictor of the control arm is the opposite of the one of the active arm, at
every point of `ℝ¹`. -/
theorem commonLimitFollowUpLogit_predictor_false (x : Fin 1 → ℝ) :
    interactionDesign false x ⬝ᵥ logisticInstCoef =
      -(interactionDesign true x ⬝ᵥ logisticInstCoef) := by
  simp [dotProduct, Fintype.sum_sum_type, Fintype.sum_option, interactionDesign,
    logisticInstCoef]
  ring

/-- **Both logistic regressions are affine in the feature**: `m_true = φ` and `m_false = 1 - φ`
at every point of `ℝ¹`. -/
theorem commonLimitFollowUpLogit_affine (e : Bool) (x : Fin 1 → ℝ) :
    Real.sigmoid ((fun c : (Fin 1 → ℝ) × Bool => interactionDesign c.2 c.1) (x, e) ⬝ᵥ
        logisticInstCoef) =
      (if e then 0 else 1) + (fun _ : Fin 1 => if e then (1 : ℝ) else -1) ⬝ᵥ
        commonLimitFollowUpLogitFeature x := by
  cases e
  · change Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstCoef) = _
    rw [commonLimitFollowUpLogit_predictor_false, Real.sigmoid_neg]
    simp [dotProduct, commonLimitFollowUpLogitFeature, logisticInstSurface]
    ring
  · simp [dotProduct, commonLimitFollowUpLogitFeature, logisticInstSurface]

theorem commonLimitFollowUpLogit_bound (x : Fin 1 → ℝ) :
    ‖commonLimitFollowUpLogitFeature x - commonLimitFollowUpLogitMean‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => ?_
  have h0 := Real.sigmoid_pos (interactionDesign true x ⬝ᵥ logisticInstCoef)
  have h1 := Real.sigmoid_lt_one (interactionDesign true x ⬝ᵥ logisticInstCoef)
  simp only [Pi.sub_apply, commonLimitFollowUpLogitFeature, commonLimitFollowUpLogitMean,
    logisticInstSurface, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- The target mean of the feature is `5/12`. -/
theorem commonLimitFollowUpLogit_featureMean (k : Fin 1) :
    ∫ x, commonLimitFollowUpLogitFeature x k ∂logisticInstTarget.covLaw =
      commonLimitFollowUpLogitMean k := by
  rw [integral_logisticInstTarget_covLaw, commonLimitFollowUpLogit_feature_cov,
    commonLimitFollowUpLogit_feature_cov]
  simp [commonLimitFollowUpLogitMean]
  norm_num

theorem commonLimitFollowUpLogit_halfLaw_singleton (b : Bool) : halfLaw.real {b} = 1 / 2 := by
  rw [← integral_indicator_one (measurableSet_singleton b), integral_halfLaw]
  cases b <;> simp [Set.indicator]

/-- **The margin condition** at `t = 5/12` with `δ = 1/12` for the trial covariate law: the
feature is `2/3` at `x = 0` and `1/3` at `x = 1`, each with probability `1/2`. -/
theorem commonLimitFollowUpLogit_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 12 : ℝ) ≤
    logisticInstTrial.covLaw.real
      {x | 1 / 12 ≤ v ⬝ᵥ (commonLimitFollowUpLogitFeature x - commonLimitFollowUpLogitMean)} := by
  intro v hv
  have hv0 : |v 0| = 1 := by
    have h : ‖v‖ = ‖v 0‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
        (norm_le_pi_norm v 0)
      rw [Subsingleton.elim j 0]
    rw [← Real.norm_eq_abs, ← h, hv]
  have hSm : MeasurableSet {x | (1 / 12 : ℝ) ≤
      v ⬝ᵥ (commonLimitFollowUpLogitFeature x - commonLimitFollowUpLogitMean)} :=
    measurableSet_le measurable_const (by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul
        (((measurable_pi_apply i).comp commonLimitFollowUpLogit_measurable).sub measurable_const))
  rw [logisticInstTrial_covLaw, map_measureReal_apply (measurable_of_finite _) hSm]
  have key : ∀ b : Bool, (1 / 12 : ℝ) ≤ v ⬝ᵥ (commonLimitFollowUpLogitFeature (logisticInstCov b)
      - commonLimitFollowUpLogitMean) → (1 / 12 : ℝ) ≤ halfLaw.real
        (logisticInstCov ⁻¹' {x | (1 / 12 : ℝ) ≤
          v ⬝ᵥ (commonLimitFollowUpLogitFeature x - commonLimitFollowUpLogitMean)}) := by
    intro b hb
    calc (1 / 12 : ℝ) ≤ halfLaw.real {b} := by
          rw [commonLimitFollowUpLogit_halfLaw_singleton]; norm_num
      _ ≤ _ := measureReal_mono (Set.singleton_subset_iff.2 hb) (measure_ne_top _ _)
  rcases abs_eq zero_le_one |>.1 hv0 with h | h
  · refine key false ?_
    simp [dotProduct, h, commonLimitFollowUpLogit_feature_cov, commonLimitFollowUpLogitMean]
    norm_num
  · refine key true ?_
    simp [dotProduct, h, commonLimitFollowUpLogit_feature_cov, commonLimitFollowUpLogitMean]
    norm_num

/-- **Weighting and standardization with the logistic fit share their limit in the example.**
Every hypothesis of `commonLimit_logistic_armMean` holds for the active arm `true`, standing for
the target treatment `a = 0`, with the risk score feature at its target mean `5/12`: the weighted
arm mean and the standardized logistic fit both converge in probability to the target arm mean
`5/12`, and their difference converges in probability to `0`. -/
theorem commonLimitFollowUpLogit_armMean :
    IsConsistent (sampleBalancedArmMean commonLimitFollowUpLogitFeature
      commonLimitFollowUpLogitMean (fun i ω => commonLimitReassoc (logisticInstSample i ω)) true)
      (5 / 12) logisticInstSampleLaw ∧
      TendstoInMeasure logisticInstSampleLaw (fun n ω => ∫ x,
        Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω) ∂logisticInstTarget.covLaw)
        atTop (fun _ => 5 / 12) ∧
      TendstoInMeasure logisticInstSampleLaw (fun n ω => ∫ x,
        Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω) ∂logisticInstTarget.covLaw -
          sampleBalancedArmMean commonLimitFollowUpLogitFeature commonLimitFollowUpLogitMean
            (fun i ω => commonLimitReassoc (logisticInstSample i ω)) true n ω)
        atTop (fun _ => 0) := by
  rw [← logisticInstTarget_armMean.1]
  exact commonLimit_logistic_armMean logisticInstTrial_isRandomizedTwoArm
    logisticInst_logisticOutcomeModel (isCompact_closedBall _ _) logisticInstCoef_mem_ball
    isIIDSample_logisticInstSample
    (fun i => (measurable_of_finite logisticInstRecord).comp (measurable_pi_apply i))
    (map_logisticInstSample 0) commonLimitFollowUpLogit_measurable
    commonLimitFollowUpLogit_bound (by norm_num) commonLimitFollowUpLogit_margin true
    (commonLimitFollowUpLogit_affine true) (measurable_of_finite _)
    commonLimitFollowUpLogit_featureMean Integrable.of_finite
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous

/-- **The marginal log odds ratio with the logistic fit in the example.** Every hypothesis of
`commonLimit_logistic_linkMarginal` holds with the arms `true ↦ a = 0` and `false ↦ c = 2`, the
logit link and the risk score feature: the weighted contrast `logit μ̂_true - logit μ̂_false` and
the standardized marginal log odds ratio of the logistic fit both converge in probability to
`log (25/49)`, and their difference converges in probability to `0`. -/
theorem commonLimitFollowUpLogit_linkMarginal :
    TendstoInMeasure logisticInstSampleLaw (fun n ω =>
        logit (sampleBalancedArmMean commonLimitFollowUpLogitFeature commonLimitFollowUpLogitMean
          (fun i ω => commonLimitReassoc (logisticInstSample i ω)) true n ω) -
        logit (sampleBalancedArmMean commonLimitFollowUpLogitFeature commonLimitFollowUpLogitMean
          (fun i ω => commonLimitReassoc (logisticInstSample i ω)) false n ω))
      atTop (fun _ => Real.log (25 / 49)) ∧
      TendstoInMeasure logisticInstSampleLaw (fun n ω => linkMarginal logit
        logisticInstTarget.covLaw
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstFit n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω)))
      atTop (fun _ => Real.log (25 / 49)) ∧
      TendstoInMeasure logisticInstSampleLaw (fun n ω => linkMarginal logit
        logisticInstTarget.covLaw
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstFit n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω)) -
        (logit (sampleBalancedArmMean commonLimitFollowUpLogitFeature commonLimitFollowUpLogitMean
          (fun i ω => commonLimitReassoc (logisticInstSample i ω)) true n ω) -
        logit (sampleBalancedArmMean commonLimitFollowUpLogitFeature commonLimitFollowUpLogitMean
          (fun i ω => commonLimitReassoc (logisticInstSample i ω)) false n ω)))
      atTop (fun _ => 0) := by
  rw [← logisticInstTarget_marginalEffect.1]
  exact commonLimit_logistic_linkMarginal (s₀ := 2) (s₁ := 0)
    logisticInstTrial_isRandomizedTwoArm
    logisticInst_logisticOutcomeModel (isCompact_closedBall _ _) logisticInstCoef_mem_ball
    isIIDSample_logisticInstSample
    (fun i => (measurable_of_finite logisticInstRecord).comp (measurable_pi_apply i))
    (map_logisticInstSample 0) commonLimitFollowUpLogit_measurable
    commonLimitFollowUpLogit_bound (by norm_num) commonLimitFollowUpLogit_margin
    commonLimitFollowUpLogit_affine (measurable_of_finite _)
    commonLimitFollowUpLogit_featureMean Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous (logisticInst_continuousAt_logit 2)
    (logisticInst_continuousAt_logit 0)

end PopulationAdjustment

end CausalInference
