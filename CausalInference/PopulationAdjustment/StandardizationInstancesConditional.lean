/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationInstancesTargetSample
public import CausalInference.PopulationAdjustment.StandardizationConsistencyConditional

/-!
# The conditional plug-in at the target mean: every hypothesis verified

The conditional plug-in evaluates the fitted treatment effect of the interaction model
`g(m_t(x)) = α + β₁ᵀx + γ 1[t] + β₂ᵀx 1[t]` at an estimate of the target covariate mean, giving
`γ̂ + x̂ᵀβ̂₂`. This file verifies every hypothesis of the three large sample theorems for it, in the
trial `logisticInstTrial` with covariates in `ℝ¹` and the target `logisticInstTarget`.

* **Logit link** (`condInst_conditionalPlugIn`, `condInst_conditionalPlugIn_sampleMean`): with
  the logistic maximum likelihood fit and a reported target covariate mean (a deterministic
  sequence converging to `x̄ = 3/4`), or the mean of `n` target draws independent of the trial
  sample, the plug-in converges in probability to `γ + x̄ β₂ = -log 2`. The target marginal log
  odds ratio is `log (25/49)`, so the plug-in is not consistent for it
  (`condInst_conditionalPlugIn_ne`).
* **Identity link** (`condInst_conditionalPlugIn_leastSquares`): the interaction model is
  saturated for a binary covariate, so the same trial also satisfies the linear outcome model
  `Trial.LinearOutcomeModel interactionDesign ζ₀` with `ζ₀ = (1/3, 1/3, 1/3, -2/3)`
  (`condInst_linearOutcomeModel`). The least squares plug-in converges to
  `E_Q[Y(a)] - E_Q[Y(c)] = 5/12 - 7/12 = -1/6`, which here is the marginal effect: on the
  identity link the averaging gaps vanish.

## Main definitions

* `condInstLinearCoef`, `condInstRecord`, `condInstSample`.

## Main results

* `condInst_linearOutcomeModel`, `isIIDSample_condInstSample`, `condInst_conditionalPlugIn`,
  `condInst_conditionalPlugIn_sampleMean`, `condInst_conditionalPlugIn_ne`,
  `condInst_conditionalPlugIn_leastSquares`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The coordinates of the target covariate are integrable under the target covariate law. -/
theorem condInst_integrable_coord (k : Fin 1) :
    Integrable (fun x : Fin 1 → ℝ => x k) logisticInstTarget.covLaw :=
  (integrable_map_measure (measurable_pi_apply _).aestronglyMeasurable
    (measurable_of_finite _).aemeasurable).2 Integrable.of_finite

/-- The reported target covariate mean `3/4 + 1/(n + 1)` converges to `x̄`. -/
theorem condInst_covMean_tendsto {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ)
    [IsProbabilityMeasure P] :
    TendstoInMeasure P (fun (n : ℕ) (_ : Ξ) (_ : Fin 1) => 3 / 4 + 1 / ((n : ℝ) + 1)) atTop
      (fun _ => covMean logisticInstTarget.covLaw) := by
  rw [logisticInstTarget_covMean]
  exact tendstoInMeasure_pi fun _ => tendstoInMeasure_add_one_div_succ _ _

/-- The limit of the logistic plug-in: `Δ_Q + J(m₀) - J(m₁) = log (25/49) - log (50/49) =
-log 2`. -/
theorem condInst_plugIn_limit :
    logisticInstTarget.marginalEffect logit 2 0 +
        (averagingGap logit logisticInstTarget.covLaw
            (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstCoef)) -
          averagingGap logit logisticInstTarget.covLaw
            (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstCoef))) =
      -Real.log 2 := by
  have h : averagingGap logit logisticInstTarget.covLaw
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstCoef)) -
      averagingGap logit logisticInstTarget.covLaw
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstCoef)) =
      -Real.log (50 / 49) := logisticInst_averagingGap
  rw [logisticInstTarget_marginalEffect.1, h,
    show (50 / 49 : ℝ) = 2 * (25 / 49) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- **The logistic conditional plug-in at a reported target mean converges to `-log 2`.** Every
hypothesis of `tendstoInMeasure_conditionalPlugIn` is verified with the logit link, its inverse
the sigmoid, the logistic maximum likelihood fit and the reported mean `3/4 + 1/(n + 1)`. -/
theorem condInst_conditionalPlugIn :
    TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) ω => linkContrast logit
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstFit n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω))
        (fun _ => 3 / 4 + 1 / ((n : ℝ) + 1)))
      atTop (fun _ => -Real.log 2) := by
  rw [← condInst_plugIn_limit]
  exact tendstoInMeasure_conditionalPlugIn (s₀ := 2) (s₁ := 0)
    logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    (CausalInference.PopulationAdjustment.logit_sigmoid) logisticInst_isOutcomeRegression
    (measurable_of_finite _) Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous condInst_integrable_coord
    logisticInstFit_tendstoInMeasure (condInst_covMean_tendsto _)

/-- **The logistic conditional plug-in at the mean of a target sample converges to `-log 2`.**
The target covariate mean is the average of `n` target draws, independent of the trial sample.
Every hypothesis of `tendstoInMeasure_conditionalPlugIn_sampleMean` is verified. -/
theorem condInst_conditionalPlugIn_sampleMean :
    TendstoInMeasure targetSampleInstLogLaw
      (fun n ω => linkContrast logit
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ targetSampleInstLogFit n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ targetSampleInstLogFit n ω))
        (fun k => sampleMean (fun x => x k) targetSampleInstLogDraw n ω))
      atTop (fun _ => -Real.log 2) := by
  rw [← condInst_plugIn_limit]
  exact tendstoInMeasure_conditionalPlugIn_sampleMean (s₀ := 2) (s₁ := 0) (m := fun n => n)
    logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    (CausalInference.PopulationAdjustment.logit_sigmoid) logisticInst_isOutcomeRegression
    (measurable_of_finite _) Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous condInst_integrable_coord
    targetSampleInstLogFit_tendstoInMeasure isIIDSample_targetSampleInstLogDraw
    map_targetSampleInstLogDraw tendsto_id_nat

/-- **The logistic conditional plug-in is not consistent for the marginal log odds ratio.** Its
limit `-log 2` differs from the target marginal log odds ratio `log (25/49)` of `a` against `c`
by `log (50/49) ∈ [1/50, 1/49]`. -/
theorem condInst_conditionalPlugIn_ne :
    logisticInstTarget.marginalEffect logit 2 0 - -Real.log 2 = Real.log (50 / 49) ∧
      1 / 50 ≤ Real.log (50 / 49) ∧ Real.log (50 / 49) ≤ 1 / 49 := by
  obtain ⟨e, hlo, hhi, -⟩ := logisticInst_conditionalPlugIn_ne_linkMarginal
  exact ⟨logisticInstTarget_marginalEffect.1 ▸ e, hlo, hhi⟩

/-! ### The identity link -/

/-- The coefficient `ζ₀ = (α, β₁, γ, β₂) = (1/3, 1/3, 1/3, -2/3)` of the linear model of the
risk of the trial. -/
noncomputable def condInstLinearCoef : Option (Fin 1) ⊕ Option (Fin 1) → ℝ
  | .inl none => 1 / 3
  | .inl (some _) => 1 / 3
  | .inr none => 1 / 3
  | .inr (some _) => -(2 / 3)

/-- The linear surface agrees with the logistic risk at both covariate values. -/
theorem condInst_linear_eq (t b : Bool) :
    interactionDesign t (logisticInstCov b) ⬝ᵥ condInstLinearCoef =
      logisticInstSurface t (logisticInstCov b) := by
  rw [interactionDesign_logisticInstCov_dotProduct, logisticInstSurface, logisticInst_risk]
  cases t <;> cases b <;> simp [condInstLinearCoef] <;> norm_num

/-- **The trial satisfies the linear outcome model** over the interaction design at `ζ₀`: the
interaction model is saturated for a binary covariate. -/
theorem condInst_linearOutcomeModel :
    logisticInstTrial.LinearOutcomeModel interactionDesign condInstLinearCoef where
  measurable_z a j := measurable_interactionDesign a j
  memLp_z t j := MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rcases ω with ⟨⟨a, b⟩, _⟩
      rcases j with (_ | _) | (_ | _) <;>
        cases t <;> cases b <;> simp [interactionDesign, logisticInstTrial, logisticInstCov])
  memLp_Y t := MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rcases logisticInstOutcome_mem t ω.1.2 ω.2 with h | h <;>
        simp [logisticInstTrial, h])
  posDef := by
    refine posDef_gram_of_ae (fun j => MemLp.of_bound
      (measurable_of_finite _).aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)) fun v hv => ?_
    · rcases ω with ⟨⟨a, b⟩, _⟩
      rcases j with (_ | _) | (_ | _) <;>
        cases a <;> cases b <;> simp [interactionDesign, logisticInstTrial, logisticInstCov]
    · rw [ae_logisticInstTrial_iff] at hv
      have h : ∀ a b : Bool, interactionDesign a (logisticInstCov b) ⬝ᵥ v = 0 := fun a b =>
        hv ((a, b), 0)
      have h00 := h false false
      have h01 := h false true
      have h10 := h true false
      have h11 := h true true
      simp only [interactionDesign_logisticInstCov_dotProduct, ite_true, ite_false,
        Bool.false_eq_true] at h00 h01 h10 h11
      funext k
      rcases k with (_ | j) | (_ | j)
      · simp only [Pi.zero_apply]; linarith
      · rw [Subsingleton.elim j 0]; simp only [Pi.zero_apply]; linarith
      · simp only [Pi.zero_apply]; linarith
      · rw [Subsingleton.elim j 0]; simp only [Pi.zero_apply]; linarith
  isOutcomeRegression := by
    refine ⟨fun a => Finset.measurable_sum _ fun k _ =>
      (measurable_interactionDesign a k).mul_const _, ?_⟩
    filter_upwards [logisticInst_isOutcomeRegression.2] with ω hω
    rw [hω]
    exact (condInst_linear_eq _ _).symm

/-- The record `(X, A, Y)` of a unit of the trial. -/
noncomputable def condInstRecord (ω : (Bool × Bool) × Fin 3) : (Fin 1 → ℝ) × Bool × ℝ :=
  (logisticInstTrial.X ω, logisticInstTrial.A ω, logisticInstTrial.obsOutcome ω)

/-- The records `(X, A, Y)` of the sample of the trial. -/
noncomputable def condInstSample (i : ℕ) (ω : ℕ → (Bool × Bool) × Fin 3) :
    (Fin 1 → ℝ) × Bool × ℝ :=
  condInstRecord (ω i)

theorem isIIDSample_condInstSample : IsIIDSample condInstSample logisticInstSampleLaw :=
  isIIDSample_infinitePi_comp _ (measurable_of_finite condInstRecord)

theorem map_condInstSample : logisticInstSampleLaw.map (condInstSample 0) =
    logisticInstTrial.ipdLaw :=
  map_infinitePi_comp_eval _ (measurable_of_finite condInstRecord) 0

/-- **The least squares conditional plug-in converges to the target mean difference `-1/6`.**
The estimated treatment effect `z(true, x̂)ᵀζ̂ - z(false, x̂)ᵀζ̂` at the reported target mean
`x̂ = 3/4 + 1/(n + 1)` converges in probability to `E_Q[Y(a)] - E_Q[Y(c)] = -1/6`. Every
hypothesis of `tendstoInMeasure_conditionalPlugIn_leastSquares` is verified. -/
theorem condInst_conditionalPlugIn_leastSquares :
    TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) ω =>
        interactionDesign true (fun _ => 3 / 4 + 1 / ((n : ℝ) + 1)) ⬝ᵥ
            leastSquaresFit (recordDesign interactionDesign) recordResponse condInstSample n ω -
          interactionDesign false (fun _ => 3 / 4 + 1 / ((n : ℝ) + 1)) ⬝ᵥ
            leastSquaresFit (recordDesign interactionDesign) recordResponse condInstSample n ω)
      atTop (fun _ => -1 / 6) := by
  obtain ⟨h0, -, h2⟩ := logisticInstTarget_armMean
  have e : logisticInstTarget.armMean 0 - logisticInstTarget.armMean 2 = -1 / 6 := by
    rw [h0, h2]; norm_num
  rw [← e]
  exact tendstoInMeasure_conditionalPlugIn_leastSquares (s₀ := 2) (s₁ := 0)
    logisticInstTrial_isRandomizedTwoArm condInst_linearOutcomeModel isIIDSample_condInstSample
    map_condInstSample (measurable_of_finite _) Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous condInst_integrable_coord (condInst_covMean_tendsto _)

end PopulationAdjustment

end CausalInference
