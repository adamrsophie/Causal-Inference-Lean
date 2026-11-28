/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.BayesStandardizationCoverageAnchored
public import CausalInference.Estimation.PosteriorLimitLogisticExamples

/-!
# Coverage of Bayesian standardization in a logistic example

The randomized trial `logisticInstTrial` has a binary covariate, the interaction design
`z(x, t) = (1, x, 1[t], 1[t] x)`, the logistic outcome model at
`ξ₀ = (-log 2, 2 log 2, 2 log 2, -4 log 2)`, and the i.i.d. sample `logisticInstSample`; the
target population `logisticInstTarget` has the target marginal effect `log (25/49)` of
treatment `0` relative to treatment `2` on the logit scale. With the standard normal prior
density every hypothesis of `tendsto_credibleInterval_coverage_logisticFit` holds:

* the fit `logisticInstFit n` depends on the first `n` units only, which take finitely many
  values, so it is measurable (`measurable_logisticInstFit`);
* the target covariate law is absolutely continuous with respect to the trial one;
* the logit link is strictly differentiable at the two standardized means, which lie in
  `(0, 1)`;
* the coordinate `1[t]` of the design is the indicator of arm `true`, so the derivative of the
  target is nonzero (`logisticInst_logisticTargetDeriv_ne_zero`).

Hence the equal tailed credible interval of level `1 - α` for the target under the logistic
posterior contains `log (25/49)` with probability tending to `1 - α`
(`logisticInst_tendsto_coverage`).

With both arms equal to `true` the derivative vanishes, and the coverage probability is `1`
for every `n`, so it does not tend to `1 - α` (`logisticInst_not_tendsto_coverage_self`).

For the anchored comparison, an independent comparator sample with law `N(d₀, 1)` is analyzed
with the normal location model; the credible interval of the product posterior for `Ψ(ξ) - d`
contains `log (25/49) - d₀` with probability tending to `1 - α`
(`logisticInst_tendsto_coverage_anchored`).

## Main definitions

* `logisticInstDesign`, `logisticInstLinkDeriv`, `logisticInstComparatorLaw`,
  `logisticInstComparator`.

## Main results

* `measurable_logisticInstFit`, `logisticInst_tendstoInDistribution`,
  `logisticInst_logisticTargetDeriv_ne_zero`, `logisticInst_tendsto_coverage_marginalEffect`.
* `logisticInst_tendsto_coverage`, `logisticInst_not_tendsto_coverage_self`.
* `isIIDSample_logisticInstComparator`, `logisticInst_tendsto_coverage_anchored`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open PosteriorLimit IndirectComparison EffectMeasure BayesStandardization

/-- The interaction design of the example as a function of the record `(x, t)`. -/
abbrev logisticInstDesign : (Fin 1 → ℝ) × Bool → Option (Fin 1) ⊕ Option (Fin 1) → ℝ :=
  fun c ↦ interactionDesign c.2 c.1

/-- **The fit of the example is measurable**: it is a function of the first `n` units, which
range over a finite set. -/
theorem measurable_logisticInstFit (n : ℕ) : Measurable (logisticInstFit n) := by
  have e : logisticInstFit n = (fun u : Fin n → (Bool × Bool) × Fin 3 ↦
      glmMLECoef logisticDens logisticInstDesign logisticInstBall
        fun i ↦ logisticInstRecord (u i)) ∘
      fun ω i ↦ ω (i : ℕ) := rfl
  rw [e]
  exact (measurable_of_finite _).comp (Measurable.of_eval fun i ↦ measurable_pi_apply _)

lemma measurable_logisticInst_design (j : Option (Fin 1) ⊕ Option (Fin 1)) :
    Measurable fun c : (Fin 1 → ℝ) × Bool ↦ interactionDesign c.2 c.1 j :=
  logisticInst_logisticOutcomeModel.measurable_z j

lemma integrable_logisticInst_design (t : Bool) (j : Option (Fin 1) ⊕ Option (Fin 1)) :
    Integrable (fun x ↦ interactionDesign t x j) logisticInstTarget.covLaw :=
  integrable_design_of_absolutelyContinuous (z := logisticInstDesign)
    logisticInstTrial_isRandomizedTwoArm
    measurable_logisticInst_design (B := 1) (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j)
    logisticInst_absolutelyContinuous t j

/-- The derivative of the logit link at the standardized mean of arm `t`. -/
noncomputable def logisticInstLinkDeriv (t : Bool) : ℝ :=
  1 / (logisticMean logisticInstTarget.covLaw logisticInstDesign t logisticInstCoef *
    (1 - logisticMean logisticInstTarget.covLaw logisticInstDesign t logisticInstCoef))

lemma hasStrictDerivAt_logisticInst_logit (t : Bool) :
    HasStrictDerivAt logit (logisticInstLinkDeriv t)
      (logisticMean logisticInstTarget.covLaw logisticInstDesign t logisticInstCoef) :=
  hasStrictDerivAt_logit_of_mem_Ioo (logisticMean_mem_Ioo measurable_logisticInst_design t _)

lemma logisticInstLinkDeriv_ne_zero (t : Bool) : logisticInstLinkDeriv t ≠ 0 := by
  have h := logisticMean_mem_Ioo (ν := logisticInstTarget.covLaw) measurable_logisticInst_design
    t logisticInstCoef
  unfold logisticInstLinkDeriv
  exact one_div_ne_zero (mul_ne_zero h.1.ne' (by linarith [h.2]))

/-- **The derivative of the target of the example is nonzero**: the coordinate `1[t]` of the
design is the indicator of arm `true`. -/
theorem logisticInst_logisticTargetDeriv_ne_zero :
    logisticTargetDeriv logisticInstTarget.covLaw logisticInstDesign false true
      (logisticInstLinkDeriv false) (logisticInstLinkDeriv true) logisticInstCoef ≠ 0 :=
  logisticTargetDeriv_ne_zero_of_indicator measurable_logisticInst_design
    (integrable_logisticInst_design false) (integrable_logisticInst_design true)
    (j := .inr none) (fun _ ↦ rfl) (fun _ ↦ rfl) (logisticInstLinkDeriv_ne_zero true) _

/-- **Coverage in the example.** For the standard normal prior density, the equal tailed
credible interval of level `1 - α` for the target under the logistic posterior of the sample
contains the target marginal effect `log (25/49)` with probability tending to `1 - α`. -/
theorem logisticInst_tendsto_coverage {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ logisticInstSampleLaw.real {ω | Real.log (25 / 49) ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity logisticInstDesign
        fun i : Fin n ↦ logisticInstSample i ω).map
        (logisticTarget logit logisticInstTarget.covLaw logisticInstDesign false true)) α}) atTop
      (𝓝 (1 - α)) := by
  rw [← logisticInst_logisticTarget]
  exact tendsto_credibleInterval_coverage_logisticFit logisticInstTrial_isRandomizedTwoArm
    logisticInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    (fun n ↦ (measurable_logisticInstFit n).aemeasurable)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) logisticInst_absolutelyContinuous
    (measurable_logit) (hasStrictDerivAt_logisticInst_logit false)
    (hasStrictDerivAt_logisticInst_logit true) logisticInst_logisticTargetDeriv_ne_zero hα

/-- **Asymptotic normality of the fit in the example**:
`√n (ξ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)`, with `I(ξ₀)` the information of the covariate and assignment
law of the trial. -/
theorem logisticInst_tendstoInDistribution :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (logisticInstFit n ω - logisticInstCoef))
      atTop id (fun _ ↦ logisticInstSampleLaw)
      (logisticLimit (logisticInstTrial.μ.map fun ω ↦ (logisticInstTrial.X ω,
        logisticInstTrial.A ω)) logisticInstDesign logisticInstCoef) :=
  logisticInst_logisticOutcomeModel.tendstoInDistribution_glmMLE
    logisticInstTrial_isRandomizedTwoArm (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    (fun n ↦ (measurable_logisticInstFit n).aemeasurable) HasLaw.id

/-- **Coverage of the target marginal effect in the example.** The equal tailed credible
interval of level `1 - α` for the target under the logistic posterior contains the target
marginal effect `g(E_Q[Y(0)]) - g(E_Q[Y(2)])` on the logit scale with probability tending to
`1 - α`; the trial arms `false, true` are used for the target arms `2, 0`. -/
theorem logisticInst_tendsto_coverage_marginalEffect {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ logisticInstSampleLaw.real {ω | logisticInstTarget.marginalEffect logit 2 0 ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity logisticInstDesign
        fun i : Fin n ↦ logisticInstSample i ω).map
        (logisticTarget logit logisticInstTarget.covLaw logisticInstDesign false true)) α}) atTop
      (𝓝 (1 - α)) :=
  tendsto_credibleInterval_coverage_marginalEffect_logisticFit (t₀ := false) (t₁ := true)
    logisticInstTrial_isRandomizedTwoArm logisticInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    (fun n ↦ (measurable_logisticInstFit n).aemeasurable)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) (measurable_of_finite _) Integrable.of_finite
    Integrable.of_finite (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous measurable_logit (hasStrictDerivAt_logisticInst_logit false)
    (hasStrictDerivAt_logisticInst_logit true) logisticInst_logisticTargetDeriv_ne_zero hα

/-- **With equal arms the derivative vanishes and coverage fails.** For `t₀ = t₁ = true` the
derivative of the target is `0`, and the coverage probability of the credible interval is `1`
for every `n`, so it does not tend to `1 - α`. -/
theorem logisticInst_not_tendsto_coverage_self {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    logisticTargetDeriv logisticInstTarget.covLaw logisticInstDesign true true
      (logisticInstLinkDeriv true) (logisticInstLinkDeriv true) logisticInstCoef = 0 ∧
    ¬ Tendsto (fun n ↦ logisticInstSampleLaw.real {ω |
      logisticTarget logit logisticInstTarget.covLaw logisticInstDesign true true logisticInstCoef ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity logisticInstDesign
        fun i : Fin n ↦ logisticInstSample i ω).map
        (logisticTarget logit logisticInstTarget.covLaw logisticInstDesign true true)) α}) atTop
      (𝓝 (1 - α)) := by
  refine ⟨sub_self _, fun h ↦ ?_⟩
  have h1 : (fun n ↦ logisticInstSampleLaw.real {ω |
      logisticTarget logit logisticInstTarget.covLaw logisticInstDesign true true logisticInstCoef ∈
      credibleInterval ((logisticPosterior stdNormalPriorDensity logisticInstDesign
        fun i : Fin n ↦ logisticInstSample i ω).map
        (logisticTarget logit logisticInstTarget.covLaw logisticInstDesign true true)) α}) =
      fun _ ↦ 1 :=
    funext fun n ↦ measureReal_coverage_logisticTarget_self logit _ true
      logisticInst_isBernsteinVonMises.isProbabilityMeasure hα logisticInstCoef n
  rw [h1] at h
  have := tendsto_nhds_unique tendsto_const_nhds h
  linarith [hα.1]

/-! ### The anchored comparison -/

/-- The sampling law of the comparator: i.i.d. outcomes with law `N(d₀, 1)`. -/
noncomputable def logisticInstComparatorLaw (d₀ : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ ↦ gaussianReal d₀ 1

instance (d₀ : ℝ) : IsProbabilityMeasure (logisticInstComparatorLaw d₀) := by
  unfold logisticInstComparatorLaw; infer_instance

/-- The comparator outcomes. -/
def logisticInstComparator (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

lemma hasLaw_logisticInstComparator (d₀ : ℝ) (i : ℕ) :
    HasLaw (logisticInstComparator i) (gaussianReal d₀ 1) (logisticInstComparatorLaw d₀) :=
  ⟨(measurable_pi_apply i).aemeasurable, by
    rw [logisticInstComparatorLaw]
    exact Measure.infinitePi_map_eval _ i⟩

/-- **The comparator sample is i.i.d.** -/
theorem isIIDSample_logisticInstComparator (d₀ : ℝ) :
    IsIIDSample logisticInstComparator (logisticInstComparatorLaw d₀) where
  indep := iIndepFun_infinitePi (P := fun _ ↦ gaussianReal d₀ 1) fun _ ↦ measurable_id
  ident i := ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    (hasLaw_logisticInstComparator d₀ i).map_eq.trans
      (hasLaw_logisticInstComparator d₀ 0).map_eq.symm⟩

/-- **Anchored coverage in the example.** The index trial is the logistic example with the
standard normal prior density; the comparator is an independent i.i.d. sample with law
`N(d₀, 1)`, analyzed with the normal location model of variance `1` and the prior `N(0, 1)`.
Under the product sampling law the equal tailed credible interval of level `1 - α` of the
product posterior for `Ψ(ξ) - d` contains `log (25/49) - d₀` with probability tending to
`1 - α`. -/
theorem logisticInst_tendsto_coverage_anchored (d₀ : ℝ) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
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
  exact tendsto_credibleInterval_coverage_anchored_logisticFit
    logisticInstTrial_isRandomizedTwoArm logisticInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    (fun n ↦ (measurable_logisticInstFit n).aemeasurable)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _) (isIIDSample_logisticInstComparator d₀)
    one_pos hvar one_pos
    logisticInst_absolutelyContinuous measurable_logit
    (hasStrictDerivAt_logisticInst_logit false) (hasStrictDerivAt_logisticInst_logit true) hα

end PopulationAdjustment

end CausalInference
