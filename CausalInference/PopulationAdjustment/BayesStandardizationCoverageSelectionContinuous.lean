/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.BayesStandardizationCoverageSelectionContinuousTrial

/-!
# Coverage of Bayesian standardization with a uniform covariate

The randomized trial `unifInstTrial` has a fair coin assignment, a covariate uniform on
`[0, 1]`, the interaction design `z(x, t) = (1, x, 1[t], 1[t] x)` and the logistic outcome model
at `ξ₀ = (0, 0, log 2, 0)`; its records `((X, A), Y)` take uncountably many values. The fit is
the measurable maximizer `measurableLogisticFit` of the likelihood over the closed ball of radius
`1`. With the standard normal prior density every hypothesis holds of

* `Trial.LogisticOutcomeModel.tendstoInDistribution_measurableLogisticFit`: the fit is
  asymptotically normal (`unifInst_tendstoInDistribution_measurableLogisticFit`);
* `tendsto_credibleInterval_coverage_logisticPosterior`: the credible interval for the target
  `Ψ(ξ) = logit(∫ σ(z(x, true) ⬝ ξ) dν) - logit(∫ σ(z(x, false) ⬝ ξ) dν)`, with `ν` the uniform
  covariate law, contains `Ψ(ξ₀) = log 2` with probability tending to `1 - α`
  (`unifInst_tendsto_coverage_logisticPosterior`);
* `tendsto_credibleInterval_coverage_marginalEffect_logisticPosterior`: it contains the target
  marginal log odds ratio `log 2` of arm `true` against arm `false`
  (`unifInst_tendsto_coverage_marginalEffect_logisticPosterior`);
* `tendsto_credibleInterval_coverage_anchored_logisticPosterior`: with an independent comparator
  sample with law `N(d₀, 1)`, the credible interval of the product posterior for `Ψ(ξ) - d`
  contains `log 2 - d₀` with probability tending to `1 - α`
  (`unifInst_tendsto_coverage_anchored_logisticPosterior`).

## Main definitions

* `unifInstDesign`, `unifInstLinkDeriv`.

## Main results

* `unifInstTrial_covLaw_singleton`, `unifInst_logisticTarget`, `unifInstTarget_marginalEffect`,
  `unifInst_logisticTargetDeriv_ne_zero`.
* `unifInst_tendstoInDistribution_measurableLogisticFit`,
  `unifInst_tendsto_coverage_logisticPosterior`,
  `unifInst_tendsto_coverage_marginalEffect_logisticPosterior`,
  `unifInst_tendsto_coverage_anchored_logisticPosterior`.
-/

@[expose] public section

open scoped unitInterval

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix PosteriorLimit IndirectComparison
  EffectMeasure BayesStandardization

/-- The interaction design of the example as a function of the record `(x, t)`. -/
abbrev unifInstDesign : (Fin 1 → ℝ) × Bool → Option (Fin 1) ⊕ Option (Fin 1) → ℝ :=
  fun c ↦ interactionDesign c.2 c.1

lemma measurable_unifInst_design (j : Option (Fin 1) ⊕ Option (Fin 1)) :
    Measurable fun c : (Fin 1 → ℝ) × Bool ↦ interactionDesign c.2 c.1 j :=
  unifInst_logisticOutcomeModel.measurable_z j

lemma integrable_unifInst_design (t : Bool) (j : Option (Fin 1) ⊕ Option (Fin 1)) :
    Integrable (fun x ↦ interactionDesign t x j) unifInstTarget.covLaw :=
  integrable_design_of_absolutelyContinuous (z := unifInstDesign)
    unifInstTrial_isRandomizedTwoArm measurable_unifInst_design (B := 1)
    (ae_of_all _ fun ω j ↦ abs_unifInst_design_le ω j) unifInst_absolutelyContinuous t j

/-- **The covariate law of the trial has no atoms**, so the records of the sample do not take
finitely many values. -/
theorem unifInstTrial_covLaw_singleton (x : Fin 1 → ℝ) : unifInstTrial.covLaw {x} = 0 := by
  rw [unifInstTrial_covLaw, unifInstCovLaw,
    Measure.map_apply measurable_unifInstCov (measurableSet_singleton x)]
  refine Set.Subsingleton.measure_zero (fun a ha b hb ↦ ?_) _
  have h : unifInstCov a = unifInstCov b := (ha : unifInstCov a = x).trans (hb : _ = x).symm
  exact Subtype.ext (congrFun h 0)

theorem logit_one_half : logit (1 / 2) = 0 := by
  rw [logit_eq_log_div]; norm_num

/-- **The target at the true coefficient**: under every covariate law the standardized means
are `1/2` and `2/3`, so `Ψ(ξ₀) = logit(2/3) - logit(1/2) = log 2`. -/
theorem unifInst_logisticTarget (ν : Measure (Fin 1 → ℝ)) [IsProbabilityMeasure ν] :
    logisticTarget logit ν unifInstDesign false true unifInstCoef = Real.log 2 := by
  simp only [logisticTarget, linkMarginal, unifInstDesign, unifInst_risk, integral_const,
    probReal_univ, one_smul, unifInstRisk]
  norm_num
  rw [show (2 / 3 : ℝ) = 2 / 3 from rfl, logit_two_thirds, logit_one_half, sub_zero]

/-- **The target marginal log odds ratio** of arm `true` against arm `false` is `log 2`. -/
theorem unifInstTarget_marginalEffect :
    unifInstTarget.marginalEffect logit false true = Real.log 2 := by
  rw [← unifInst_logisticTarget unifInstTarget.covLaw]
  exact (logisticTarget_eq_marginalEffect (t₀ := false) (t₁ := true) (s₀ := false) (s₁ := true)
    unifInstTrial_isRandomizedTwoArm
    (fun s ↦ integrable_of_ae_zero_or_one ((measurable_unifInstOutcome s).comp measurable_snd)
      (ae_of_all _ fun _ ↦ unifInstOutcome_mem _ _))
    unifInst_logisticOutcomeModel measurable_unifInstTarget_X (integrable_unifInstTarget_Y false)
    (integrable_unifInstTarget_Y true) (unifInst_structurallyInvariant false)
    (unifInst_structurallyInvariant true) unifInst_absolutelyContinuous logit).symm

/-- The derivative of the logit link at the standardized mean of arm `t`. -/
noncomputable def unifInstLinkDeriv (t : Bool) : ℝ :=
  1 / (logisticMean unifInstTarget.covLaw unifInstDesign t unifInstCoef *
    (1 - logisticMean unifInstTarget.covLaw unifInstDesign t unifInstCoef))

lemma hasStrictDerivAt_unifInst_logit (t : Bool) :
    HasStrictDerivAt logit (unifInstLinkDeriv t)
      (logisticMean unifInstTarget.covLaw unifInstDesign t unifInstCoef) :=
  hasStrictDerivAt_logit_of_mem_Ioo (logisticMean_mem_Ioo measurable_unifInst_design t _)

lemma unifInstLinkDeriv_ne_zero (t : Bool) : unifInstLinkDeriv t ≠ 0 := by
  have h := logisticMean_mem_Ioo (ν := unifInstTarget.covLaw) measurable_unifInst_design
    t unifInstCoef
  unfold unifInstLinkDeriv
  exact one_div_ne_zero (mul_ne_zero h.1.ne' (by linarith [h.2]))

/-- **The derivative of the target is nonzero**: the coordinate `1[t]` of the design is the
indicator of arm `true`. -/
theorem unifInst_logisticTargetDeriv_ne_zero :
    logisticTargetDeriv unifInstTarget.covLaw unifInstDesign false true
      (unifInstLinkDeriv false) (unifInstLinkDeriv true) unifInstCoef ≠ 0 :=
  logisticTargetDeriv_ne_zero_of_indicator measurable_unifInst_design
    (integrable_unifInst_design false) (integrable_unifInst_design true)
    (j := .inr none) (fun _ ↦ rfl) (fun _ ↦ rfl) (unifInstLinkDeriv_ne_zero true) _

/-- **Asymptotic normality of the measurable fit with a uniform covariate**:
`√n (θ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)` for the measurable fit over the closed ball of radius `1`, with
`I(ξ₀)` the information of the covariate and assignment law of the trial. -/
theorem unifInst_tendstoInDistribution_measurableLogisticFit :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (measurableLogisticFit unifInstDesign
        unifInstBall unifInstSample n ω - unifInstCoef))
      atTop id (fun _ ↦ unifInstSampleLaw)
      (logisticLimit (unifInstTrial.μ.map fun ω ↦ (unifInstTrial.X ω, unifInstTrial.A ω))
        unifInstDesign unifInstCoef) :=
  unifInst_logisticOutcomeModel.tendstoInDistribution_measurableLogisticFit
    unifInstTrial_isRandomizedTwoArm (B := 1)
    (ae_of_all _ fun ω j ↦ abs_unifInst_design_le ω j) (isCompact_closedBall _ _)
    unifInstBall_mem_nhds isIIDSample_unifInstSample (map_unifInstSample 0) HasLaw.id

/-- **Coverage with a uniform covariate.** For the standard normal prior density, the equal
tailed credible interval of level `1 - α` for the target under the logistic posterior of the
sample contains `log 2` with probability tending to `1 - α`. -/
theorem unifInst_tendsto_coverage_logisticPosterior {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ unifInstSampleLaw.real {ω | Real.log 2 ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity unifInstDesign
        fun i : Fin n ↦ unifInstSample i ω).map
        (logisticTarget logit unifInstTarget.covLaw unifInstDesign false true)) α}) atTop
      (𝓝 (1 - α)) := by
  rw [← unifInst_logisticTarget unifInstTarget.covLaw]
  exact tendsto_credibleInterval_coverage_logisticPosterior unifInstTrial_isRandomizedTwoArm
    unifInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_unifInst_design_le ω j) (isCompact_closedBall _ _)
    unifInstBall_mem_nhds isIIDSample_unifInstSample (map_unifInstSample 0)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) unifInst_absolutelyContinuous
    measurable_logit (hasStrictDerivAt_unifInst_logit false)
    (hasStrictDerivAt_unifInst_logit true) unifInst_logisticTargetDeriv_ne_zero hα

/-- **Coverage of the target marginal effect with a uniform covariate.** The equal tailed
credible interval of level `1 - α` for the target under the logistic posterior contains the
target marginal log odds ratio of arm `true` against arm `false`, which is `log 2`
(`unifInstTarget_marginalEffect`), with probability tending to `1 - α`. -/
theorem unifInst_tendsto_coverage_marginalEffect_logisticPosterior {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ unifInstSampleLaw.real {ω | unifInstTarget.marginalEffect logit false true ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity unifInstDesign
        fun i : Fin n ↦ unifInstSample i ω).map
        (logisticTarget logit unifInstTarget.covLaw unifInstDesign false true)) α}) atTop
      (𝓝 (1 - α)) :=
  tendsto_credibleInterval_coverage_marginalEffect_logisticPosterior (t₀ := false) (t₁ := true)
    unifInstTrial_isRandomizedTwoArm unifInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_unifInst_design_le ω j) (isCompact_closedBall _ _)
    unifInstBall_mem_nhds isIIDSample_unifInstSample (map_unifInstSample 0)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) measurable_unifInstTarget_X (integrable_unifInstTarget_Y false)
    (integrable_unifInstTarget_Y true) (unifInst_structurallyInvariant false)
    (unifInst_structurallyInvariant true) unifInst_absolutelyContinuous measurable_logit
    (hasStrictDerivAt_unifInst_logit false) (hasStrictDerivAt_unifInst_logit true)
    unifInst_logisticTargetDeriv_ne_zero hα

/-- **Anchored coverage with a uniform covariate.** With the comparator an independent i.i.d.
sample with law `N(d₀, 1)` analyzed with the normal location model of variance `1` and the prior
`N(0, 1)`, the equal tailed credible interval of level `1 - α` of the product posterior for
`Ψ(ξ) - d` contains `log 2 - d₀` with probability tending to `1 - α`. -/
theorem unifInst_tendsto_coverage_anchored_logisticPosterior (d₀ : ℝ) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ (unifInstSampleLaw.prod (logisticInstComparatorLaw d₀)).real
      {ω | Real.log 2 - d₀ ∈ credibleInterval
        (((logisticPosterior stdNormalPriorDensity unifInstDesign
          fun i : Fin n ↦ unifInstSample i ω.1).prod
          (normalLocationPosterior 0 1 1 logisticInstComparator n ω.2)).map
          (anchoredTarget logit unifInstTarget.covLaw unifInstDesign false true)) α})
      atTop (𝓝 (1 - α)) := by
  have hlaw0 := hasLaw_logisticInstComparator d₀ 0
  have hmean : (logisticInstComparatorLaw d₀)[logisticInstComparator 0] = d₀ := by
    rw [hlaw0.integral_eq, integral_id_gaussianReal]
  have hvar : Var[logisticInstComparator 0; logisticInstComparatorLaw d₀] = 1 := by
    rw [hlaw0.variance_eq, variance_id_gaussianReal]
    rfl
  have e : Real.log 2 - d₀ = anchoredTarget logit unifInstTarget.covLaw unifInstDesign false true
      (unifInstCoef, (logisticInstComparatorLaw d₀)[logisticInstComparator 0]) := by
    rw [hmean, anchoredTarget, unifInst_logisticTarget]
  rw [e]
  exact tendsto_credibleInterval_coverage_anchored_logisticPosterior
    unifInstTrial_isRandomizedTwoArm unifInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_unifInst_design_le ω j) (isCompact_closedBall _ _)
    unifInstBall_mem_nhds isIIDSample_unifInstSample (map_unifInstSample 0)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) (isIIDSample_logisticInstComparator d₀)
    one_pos hvar one_pos
    unifInst_absolutelyContinuous measurable_logit
    (hasStrictDerivAt_unifInst_logit false) (hasStrictDerivAt_unifInst_logit true) hα

end PopulationAdjustment

end CausalInference
