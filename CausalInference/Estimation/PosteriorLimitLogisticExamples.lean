/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.BayesStandardizationLogistic
public import CausalInference.PopulationAdjustment.StandardizationInstancesLogistic

/-!
# The Bernstein and von Mises theorem in a logistic example

The randomized trial `logisticInstTrial` has a binary covariate, the interaction design
`z(x, t) = (1, x, 1[t], 1[t] x)` and the logistic outcome model at
`ξ₀ = (-log 2, 2 log 2, 2 log 2, -4 log 2)`; `logisticInstSample` is an i.i.d. sample of its
records and `logisticInstFit` the maximum likelihood fit over the closed ball of radius `4`.

With the standard normal prior density `∏ⱼ φ(ξⱼ)` (`stdNormalPriorDensity`), every hypothesis of
`isBernsteinVonMises_logisticOutcomeModel` holds: the design takes values in `{0, 1}`, the ball
is a neighborhood of `ξ₀` because `4 log 2 < 4`, and the prior density is integrable, continuous
and positive. So the logistic posteriors of the example satisfy
`‖Π_n - N(ξ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability (`logisticInst_isBernsteinVonMises`), and the
standardized target at `ξ₀` is the target marginal effect on the logit scale,
`log (25/49)` (`logisticInst_logisticTarget`).

## Main definitions

* `PosteriorLimit.stdNormalPriorDensity`.

## Main results

* `integrable_stdNormalPriorDensity`, `continuous_stdNormalPriorDensity`,
  `stdNormalPriorDensity_pos`.
* `logisticInst_isBernsteinVonMises`, `logisticInst_logisticTarget`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open PopulationAdjustment IndirectComparison EffectMeasure BayesStandardization

/-! ### The standard normal prior density -/

section Prior

variable {κ : Type*} [Fintype κ]

/-- The **standard normal prior density** `∏ⱼ φ(ξⱼ)` on `κ → ℝ`, with `φ` the standard normal
density. -/
noncomputable def stdNormalPriorDensity (ξ : κ → ℝ) : ℝ := ∏ j, gaussianPDFReal 0 1 (ξ j)

lemma stdNormalPriorDensity_pos (ξ : κ → ℝ) : 0 < stdNormalPriorDensity ξ :=
  Finset.prod_pos fun j _ ↦ gaussianPDFReal_pos 0 1 (ξ j) one_ne_zero

omit [Fintype κ] in
lemma continuous_gaussianPDFReal_zero_one : Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]
  fun_prop

lemma continuous_stdNormalPriorDensity : Continuous (stdNormalPriorDensity (κ := κ)) :=
  continuous_finsetProd _ fun j _ ↦
    continuous_gaussianPDFReal_zero_one.comp (continuous_apply j)

lemma integrable_stdNormalPriorDensity : Integrable (stdNormalPriorDensity (κ := κ)) := by
  have h := Integrable.fintype_prod (μ := fun _ : κ ↦ (volume : Measure ℝ))
    (f := fun _ : κ ↦ gaussianPDFReal 0 1) fun _ ↦ integrable_gaussianPDFReal 0 1
  rw [← volume_pi] at h
  exact h

end Prior

/-! ### The example -/

/-- The interaction design of the example takes values in `{0, 1}`. -/
lemma abs_logisticInst_design_le (ω : (Bool × Bool) × Fin 3)
    (j : Option (Fin 1) ⊕ Option (Fin 1)) :
    |interactionDesign (logisticInstTrial.A ω) (logisticInstTrial.X ω) j| ≤ 1 := by
  rcases ω with ⟨⟨a, b⟩, u⟩
  rcases j with (_ | _) | (_ | _) <;> cases a <;> cases b <;>
    simp [interactionDesign, logisticInstTrial, logisticInstCov]

/-- The ball of radius `4` is a neighborhood of the coefficient of the example. -/
lemma logisticInstBall_mem_nhds : logisticInstBall ∈ 𝓝 logisticInstCoef := by
  refine Metric.closedBall_mem_nhds_of_mem ?_
  have h1 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num); linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)]
  rintro ((_ | _) | (_ | _)) <;> simp only [logisticInstCoef, Real.norm_eq_abs] <;>
    rw [abs_lt] <;> constructor <;> linarith

/-- **The Bernstein and von Mises theorem in the example.** For the standard normal prior
density, the logistic posteriors of the sample of the example satisfy
`‖Π_n - N(ξ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability, with `ξ̂_n = logisticInstFit n`. -/
theorem logisticInst_isBernsteinVonMises :
    IsBernsteinVonMises logisticInstSampleLaw
      (fun n ω ↦ logisticPosterior stdNormalPriorDensity (fun c ↦ interactionDesign c.2 c.1)
        fun i : Fin n ↦ logisticInstSample i ω)
      logisticInstFit
      (logisticLimit (logisticInstTrial.μ.map fun ω ↦ (logisticInstTrial.X ω,
        logisticInstTrial.A ω)) (fun c ↦ interactionDesign c.2 c.1) logisticInstCoef) :=
  isBernsteinVonMises_logisticOutcomeModel logisticInstTrial_isRandomizedTwoArm
    logisticInst_logisticOutcomeModel (B := 1)
    (ae_of_all _ fun ω j ↦ abs_logisticInst_design_le ω j) (isCompact_closedBall _ _)
    logisticInstBall_mem_nhds isIIDSample_logisticInstSample (map_logisticInstSample 0)
    continuous_stdNormalPriorDensity.measurable (fun ξ ↦ (stdNormalPriorDensity_pos ξ).le)
    integrable_stdNormalPriorDensity continuous_stdNormalPriorDensity.continuousAt
    (stdNormalPriorDensity_pos _)

/-- **The target of the example at the true coefficient** is the target marginal effect of
treatment `0` relative to treatment `2` on the logit scale, `log (25/49)`. -/
theorem logisticInst_logisticTarget :
    logisticTarget logit logisticInstTarget.covLaw (fun c ↦ interactionDesign c.2 c.1) false true
      logisticInstCoef = Real.log (25 / 49) := by
  rw [← logisticInstTarget_marginalEffect.1]
  exact logisticTarget_eq_marginalEffect (t₀ := false) (t₁ := true) (s₀ := 2) (s₁ := 0)
    logisticInstTrial_isRandomizedTwoArm (fun _ ↦ Integrable.of_finite)
    logisticInst_logisticOutcomeModel (measurable_of_finite _) Integrable.of_finite
    Integrable.of_finite (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous logit

end PosteriorLimit

end CausalInference
