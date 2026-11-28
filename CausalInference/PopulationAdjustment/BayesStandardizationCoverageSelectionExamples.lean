/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.BayesStandardizationCoverageSelection
public import CausalInference.PopulationAdjustment.BayesStandardizationCoverageExamples

/-!
# The logistic example with the measurable fit

In the randomized trial `logisticInstTrial` with the interaction design, the logistic outcome
model at `ξ₀ = logisticInstCoef`, the i.i.d. sample `logisticInstSample` and the parameter ball
`logisticInstBall`, every hypothesis of the theorems with no hypothesis on the fit holds:

* the measurable fit is asymptotically normal
  (`logisticInst_tendstoInDistribution_measurableLogisticFit`);
* it agrees with the fit `logisticInstFit` (the choice `glmMLE`) with probability tending to one
  (`logisticInst_withProbTendingToOne_fit_eq_measurableLogisticFit`);
* the credible intervals of the target, of the target marginal effect and of the anchored target
  cover with probability tending to `1 - α`
  (`logisticInst_tendsto_coverage_logisticPosterior`,
  `logisticInst_tendsto_coverage_marginalEffect_logisticPosterior`,
  `logisticInst_tendsto_coverage_anchored_logisticPosterior`).

None of these uses the measurability of `logisticInstFit`.

## Main results

* `logisticInst_tendstoInDistribution_measurableLogisticFit`,
  `logisticInst_withProbTendingToOne_fit_eq_measurableLogisticFit`.
* `logisticInst_tendsto_coverage_logisticPosterior`,
  `logisticInst_tendsto_coverage_marginalEffect_logisticPosterior`,
  `logisticInst_tendsto_coverage_anchored_logisticPosterior`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open PosteriorLimit IndirectComparison EffectMeasure BayesStandardization

/-- **Asymptotic normality of the measurable fit in the example**:
`√n (θ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)` for the measurable fit over `logisticInstBall`. -/
theorem logisticInst_tendstoInDistribution_measurableLogisticFit :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (measurableLogisticFit logisticInstDesign
        logisticInstBall logisticInstSample n ω - logisticInstCoef))
      atTop id (fun _ ↦ logisticInstSampleLaw)
      (logisticLimit (logisticInstTrial.μ.map fun ω ↦ (logisticInstTrial.X ω,
        logisticInstTrial.A ω)) logisticInstDesign logisticInstCoef) :=
  logisticInst_logisticOutcomeModel.tendstoInDistribution_measurableLogisticFit
    logisticInstTrial_isRandomizedTwoArm (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0) HasLaw.id

/-- **The two fits of the example agree with probability tending to one**: the fit
`logisticInstFit` and the measurable fit over `logisticInstBall` are equal on events of
probability tending to one. -/
theorem logisticInst_withProbTendingToOne_fit_eq_measurableLogisticFit :
    WithProbTendingToOne logisticInstSampleLaw fun n ↦ {ω | logisticInstFit n ω =
      measurableLogisticFit logisticInstDesign logisticInstBall logisticInstSample n ω} := by
  have h := logisticInst_logisticOutcomeModel.bound_fullRank logisticInstTrial_isRandomizedTwoArm
    (B := 1) (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j)
  exact withProbTendingToOne_glmMLE_eq_of_isMaxOn isIIDSample_logisticInstSample
    ((map_logisticInstSample 0).trans logisticInst_logisticOutcomeModel.law_eq) h.1 h.2
    (isCompact_closedBall _ _) logisticInstBall_mem_nhds
    (fun n ↦ ae_of_all _ fun ω ↦ measurableLogisticFit_mem_isMaxOn
      logisticInst_logisticOutcomeModel.measurable_z (isCompact_closedBall _ _)
      ⟨_, logisticInstCoef_mem_ball⟩ logisticInstSample n ω)

/-- **Coverage in the example, with no hypothesis on the fit.** For the standard normal prior
density, the equal tailed credible interval of level `1 - α` for the target under the logistic
posterior of the sample contains the target marginal effect `log (25/49)` with probability
tending to `1 - α`. -/
theorem logisticInst_tendsto_coverage_logisticPosterior {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ logisticInstSampleLaw.real {ω | Real.log (25 / 49) ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity logisticInstDesign
        fun i : Fin n ↦ logisticInstSample i ω).map
        (logisticTarget logit logisticInstTarget.covLaw logisticInstDesign false true)) α}) atTop
      (𝓝 (1 - α)) := by
  rw [← logisticInst_logisticTarget]
  exact tendsto_credibleInterval_coverage_logisticPosterior logisticInstTrial_isRandomizedTwoArm
    logisticInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) logisticInst_absolutelyContinuous
    measurable_logit (hasStrictDerivAt_logisticInst_logit false)
    (hasStrictDerivAt_logisticInst_logit true) logisticInst_logisticTargetDeriv_ne_zero hα

/-- **Coverage of the target marginal effect in the example, with no hypothesis on the fit.**
The equal tailed credible interval of level `1 - α` for the target under the logistic posterior
contains the target marginal effect `g(E_Q[Y(0)]) - g(E_Q[Y(2)])` on the logit scale with
probability tending to `1 - α`. -/
theorem logisticInst_tendsto_coverage_marginalEffect_logisticPosterior {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ logisticInstSampleLaw.real {ω | logisticInstTarget.marginalEffect logit 2 0 ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity logisticInstDesign
        fun i : Fin n ↦ logisticInstSample i ω).map
        (logisticTarget logit logisticInstTarget.covLaw logisticInstDesign false true)) α}) atTop
      (𝓝 (1 - α)) :=
  tendsto_credibleInterval_coverage_marginalEffect_logisticPosterior (t₀ := false) (t₁ := true)
    logisticInstTrial_isRandomizedTwoArm logisticInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) (measurable_of_finite _) Integrable.of_finite
    Integrable.of_finite (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous measurable_logit (hasStrictDerivAt_logisticInst_logit false)
    (hasStrictDerivAt_logisticInst_logit true) logisticInst_logisticTargetDeriv_ne_zero hα

/-- **Anchored coverage in the example, with no hypothesis on the fit.** With the comparator an
independent i.i.d. sample with law `N(d₀, 1)` analyzed with the normal location model of
variance `1` and the prior `N(0, 1)`, the equal tailed credible interval of level `1 - α` of the
product posterior for `Ψ(ξ) - d` contains `log (25/49) - d₀` with probability tending to
`1 - α`. -/
theorem logisticInst_tendsto_coverage_anchored_logisticPosterior (d₀ : ℝ) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ (logisticInstSampleLaw.prod (logisticInstComparatorLaw d₀)).real
      {ω | Real.log (25 / 49) - d₀ ∈ credibleInterval
        (((logisticPosterior stdNormalPriorDensity logisticInstDesign
          fun i : Fin n ↦ logisticInstSample i ω.1).prod
          (normalLocationPosterior 0 1 1 logisticInstComparator n ω.2)).map
          (anchoredTarget logit logisticInstTarget.covLaw logisticInstDesign false true)) α})
      atTop (𝓝 (1 - α)) := by
  have hlaw0 := hasLaw_logisticInstComparator d₀ 0
  have hmean : (logisticInstComparatorLaw d₀)[logisticInstComparator 0] = d₀ := by
    rw [hlaw0.integral_eq, integral_id_gaussianReal]
  have hvar : Var[logisticInstComparator 0; logisticInstComparatorLaw d₀] = 1 := by
    rw [hlaw0.variance_eq, variance_id_gaussianReal]
    rfl
  have e : Real.log (25 / 49) - d₀ = anchoredTarget logit logisticInstTarget.covLaw
      logisticInstDesign false true
      (logisticInstCoef, (logisticInstComparatorLaw d₀)[logisticInstComparator 0]) := by
    rw [hmean, anchoredTarget, logisticInst_logisticTarget]
  rw [e]
  exact tendsto_credibleInterval_coverage_anchored_logisticPosterior
    logisticInstTrial_isRandomizedTwoArm logisticInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) (isIIDSample_logisticInstComparator d₀)
    one_pos hvar one_pos
    logisticInst_absolutelyContinuous measurable_logit
    (hasStrictDerivAt_logisticInst_logit false) (hasStrictDerivAt_logisticInst_logit true) hα

end PopulationAdjustment

end CausalInference
