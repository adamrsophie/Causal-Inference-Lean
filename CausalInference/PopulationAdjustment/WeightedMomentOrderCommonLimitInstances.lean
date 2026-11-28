/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderCommonLimit
public import CausalInference.PopulationAdjustment.CommonLimitFollowUpInstances

/-!
# Instances of the common limit theorems under one exponential moment

The finite order common limit theorems (`commonLimit_reportedMoments_arm_of_isMinOn` and the four
theorems built on it) hold in the two arm example `lsExampleTrial`: a fair coin assignment, a fair
binary covariate `x`, the feature `φ(x) = 1[x]`, the outcomes `Y(t) = 1[x] + 1[t](1 + 1[x])` with
the linear regression `z(a, x)ᵀξ₀` in the interaction design, and the target `lsExampleTarget` in
which `x` is `true` with probability `1/4`. The reported moments are the deterministic sequence
`tₙ = 1/4 + 1/(n + 1) → 1/4`. The feature is bounded, so every exponential moment is finite and a
minimizer `β*` of the population dual objective exists
(`lsInst_exists_isMinOn`); every hypothesis is discharged.

## Main results

* `lsInst_arm`: both estimators of arm `true` converge to `3/2`.
* `lsInst_armMean`: the common limit is the target mean `E_Q[Y(true)] = 3/2`.
* `lsInst_unanchored`: the unanchored comparisons converge to `-5/4`.
* `lsInst_anchored`, `lsInst_anchored_identity`: the anchored comparisons converge to `-5/4`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The reported feature means `tₙ = 1/4 + 1/(n + 1)` of the instances. -/
noncomputable def lsInstReported (n : ℕ) : Fin 1 → ℝ := fun _ => 1 / 4 + 1 / ((n : ℝ) + 1)

theorem lsInst_tendsto :
    TendstoInMeasure lsExampleSampleLaw (fun n (_ : ℕ → Bool × Bool) => lsInstReported n) atTop
      (fun _ => commonLimitExampleMean) := by
  have htn : Tendsto lsInstReported atTop (𝓝 commonLimitExampleMean) :=
    tendsto_pi_nhds.2 fun _ => by
      simpa [lsInstReported, commonLimitExampleMean] using
        (tendsto_const_nhds (x := (1 / 4 : ℝ))).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (ae_of_all _ fun _ => htn)

instance : IsProbabilityMeasure lsExampleTrial.covLaw := by
  rw [lsExampleTrial_covLaw]; infer_instance

/-- **The weighting hypotheses of the example.** The feature mean `1/4` is interior to the
support of the feature law, the population dual objective has a minimizer `β*` and the moment of
some order `κ > 2 ‖β*‖` is finite. -/
theorem lsInst_exists_isMinOn :
    commonLimitExampleMean ∈ interior (closedConvexHull ℝ
      (lsExampleTrial.covLaw.map commonLimitExampleFeature).support) ∧
    ∃ βs, IsMinOn (sharpDualObjective lsExampleTrial.covLaw commonLimitExampleFeature
      commonLimitExampleMean) Set.univ βs ∧ ∃ κ, Integrable (fun x => Real.exp (κ *
        ‖commonLimitExampleFeature x - commonLimitExampleMean‖)) lsExampleTrial.covLaw ∧
          2 * (1 : ℕ) * ‖βs‖ < κ := by
  have hint := mem_interior_map_of_margin (measurable_of_finite commonLimitExampleFeature)
    (by norm_num : (0 : ℝ) < 1 / 4) commonLimitExample_margin
  exact ⟨hint, exists_isMinOn_sharpDualObjective_of_allOrders (measurable_of_finite _) hint
    fun _ => Integrable.of_finite⟩

/-- The outcome of the example has no residual about the regression, so its conditional
variance is `0`. -/
theorem lsInst_variance (e : Bool) :
    lsExampleTrial.μ[fun ω => (lsExampleTrial.Y e ω -
      featureInteractionDesign commonLimitExampleFeature e (lsExampleTrial.X ω) ⬝ᵥ
        commonLimitExampleCoef) ^ 2 | MeasurableSpace.comap lsExampleTrial.X inferInstance]
      ≤ᵐ[lsExampleTrial.μ] fun _ => 0 := by
  have h0 : (fun ω => (lsExampleTrial.Y e ω -
      featureInteractionDesign commonLimitExampleFeature e (lsExampleTrial.X ω) ⬝ᵥ
        commonLimitExampleCoef) ^ 2) = 0 := funext fun ω => by
    rw [commonLimitExample_dotProduct]; simp [lsExampleTrial]
  rw [h0, condExp_zero]
  rfl

theorem lsInst_designValue (a : Bool) :
    interactionDesign a commonLimitExampleMean ⬝ᵥ commonLimitExampleCoef =
      if a then 3 / 2 else 1 / 4 := by
  change featureInteractionDesign (fun s => s) a commonLimitExampleMean ⬝ᵥ _ = _
  rw [featureInteractionDesign_dotProduct]
  cases a
  · simp [interactionIntercept, interactionMain, commonLimitExampleCoef,
      commonLimitExampleMean, dotProduct]
  · simp [interactionIntercept, interactionMain, interactionEffect, interactionModifier,
      commonLimitExampleCoef, commonLimitExampleMean, dotProduct]
    norm_num

theorem measurable_lsExampleSample (i : ℕ) : Measurable (lsExampleSample i) :=
  (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i)

/-- **An instance of `commonLimit_reportedMoments_arm_of_isMinOn`.** In the example, the weighted
arm mean and the standardized estimate of arm `true` at the reported moments `tₙ` both converge in
probability to `3/2`. -/
theorem lsInst_arm :
    IsConsistent (fun n ω => sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n)
        lsExampleSample true n ω) (3 / 2) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => reportedMomentsArmFit
        commonLimitExampleFeature lsExampleSample (lsInstReported n) true n ω) atTop
        (fun _ => 3 / 2) := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := commonLimit_reportedMoments_arm_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) hint hmin hexp hκ
    commonLimitExample_regression isIIDSample_lsExampleSample measurable_lsExampleSample
    (map_lsExampleSample 0) measurable_const (indepFun_const_left _ _)
    (fun _ => measurable_const) lsInst_tendsto true (lsInst_variance true)
  rw [lsInst_designValue] at h
  exact h

/-- **An instance of `commonLimit_reportedMoments_armMean_of_isMinOn`.** In the example, both
estimators of arm `true` at the reported moments converge in probability to the target mean
`E_Q[Y(true)] = 3/2`, and their difference converges in probability to `0`. -/
theorem lsInst_armMean :
    IsConsistent (fun n ω => sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n)
        lsExampleSample true n ω) (3 / 2) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => reportedMomentsArmFit
        commonLimitExampleFeature lsExampleSample (lsInstReported n) true n ω) atTop
        (fun _ => 3 / 2) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => reportedMomentsArmFit
        commonLimitExampleFeature lsExampleSample (lsInstReported n) true n ω -
          sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n)
            lsExampleSample true n ω) atTop (fun _ => 0) := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := commonLimit_reportedMoments_armMean_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) hint hmin hexp hκ
    commonLimitExample_regression isIIDSample_lsExampleSample measurable_lsExampleSample
    (map_lsExampleSample 0) measurable_const (indepFun_const_left _ _)
    (fun _ => measurable_const) lsInst_tendsto true (lsInst_variance true) measurable_id
    (fun _ => Integrable.of_finite) commonLimitExample_featureMean Integrable.of_finite
    (lsExample_structurallyInvariant true) lsExample_absolutelyContinuous
  rw [commonLimitExample_armMean_value] at h
  exact h

/-- **An instance of `commonLimit_reportedMoments_unanchored_of_isMinOn`.** With the target
mean of `Y(false)` reported exactly (`m̂_b = E_Q[Y(false)] = 1/4`) and the identity link, the
weighted and the standardized unanchored comparisons of `false` against `true` both converge in
probability to `-5/4`, and their difference converges in probability to `0`. -/
theorem lsInst_unanchored :
    IsConsistent (fun n ω => id (lsExampleTarget.armMean false) - id (sampleBalancedArmMean
        commonLimitExampleFeature (lsInstReported n) lsExampleSample true n ω)) (-5 / 4)
        lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => id (lsExampleTarget.armMean false) -
        id (reportedMomentsArmFit commonLimitExampleFeature lsExampleSample (lsInstReported n)
          true n ω)) atTop (fun _ => -5 / 4) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => (id (lsExampleTarget.armMean false) -
        id (reportedMomentsArmFit commonLimitExampleFeature lsExampleSample (lsInstReported n)
          true n ω)) - (id (lsExampleTarget.armMean false) - id (sampleBalancedArmMean
            commonLimitExampleFeature (lsInstReported n) lsExampleSample true n ω))) atTop
        (fun _ => 0) := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := commonLimit_reportedMoments_unanchored_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (a := true) (b := false)
    (mb := fun _ _ => lsExampleTarget.armMean false) (g := id) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) hint hmin hexp hκ
    commonLimitExample_regression isIIDSample_lsExampleSample measurable_lsExampleSample
    (map_lsExampleSample 0) measurable_const (indepFun_const_left _ _)
    (fun _ => measurable_const) lsInst_tendsto (lsInst_variance true) measurable_id
    (fun _ => Integrable.of_finite) commonLimitExample_featureMean Integrable.of_finite
    (lsExample_structurallyInvariant true) lsExample_absolutelyContinuous
    (tendstoInMeasure_const _) continuousAt_id continuousAt_id
  rw [commonLimitExample_marginalEffect] at h
  exact h

/-- **An instance of `commonLimit_reportedMoments_anchored_of_isMinOn`.** With `a = true`,
`b = c = false`, the identity link and the reported contrast `d̂_bc = 0`, the weighted and the
standardized anchored comparisons both converge in probability to `-5/4`, and their difference
converges in probability to `0`. -/
theorem lsInst_anchored :
    IsConsistent (fun n ω => (id (sampleBalancedArmMean commonLimitExampleFeature
        (lsInstReported n) lsExampleSample false n ω) - id (sampleBalancedArmMean
          commonLimitExampleFeature (lsInstReported n) lsExampleSample true n ω)) - 0)
        (-5 / 4) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => (id (reportedMomentsArmFit
        commonLimitExampleFeature lsExampleSample (lsInstReported n) false n ω) -
          id (reportedMomentsArmFit commonLimitExampleFeature lsExampleSample
            (lsInstReported n) true n ω)) - 0) atTop (fun _ => -5 / 4) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => ((id (reportedMomentsArmFit
        commonLimitExampleFeature lsExampleSample (lsInstReported n) false n ω) -
          id (reportedMomentsArmFit commonLimitExampleFeature lsExampleSample
            (lsInstReported n) true n ω)) - 0) - ((id (sampleBalancedArmMean
              commonLimitExampleFeature (lsInstReported n) lsExampleSample false n ω) -
                id (sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n)
                  lsExampleSample true n ω)) - 0)) atTop (fun _ => 0) := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h0 : lsExampleTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have h := commonLimit_reportedMoments_anchored_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (a := true) (b := false) (c := false)
    (dbc := fun _ _ => 0) (g := id) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) hint hmin hexp hκ
    commonLimitExample_regression isIIDSample_lsExampleSample measurable_lsExampleSample
    (map_lsExampleSample 0) measurable_const (indepFun_const_left _ _)
    (fun _ => measurable_const) lsInst_tendsto lsInst_variance measurable_id
    (fun _ => Integrable.of_finite) commonLimitExample_featureMean Integrable.of_finite
    Integrable.of_finite (lsExample_structurallyInvariant true)
    (lsExample_structurallyInvariant false) lsExample_absolutelyContinuous
    (by rw [h0]; exact tendstoInMeasure_const 0) continuousAt_id continuousAt_id
  rw [commonLimitExample_marginalEffect] at h
  exact h

/-- Relative constancy on the identity scale in the target of the example: the contrast of the
regressions is the conditional mean of `Y(false) - Y(true)` given the covariate. -/
theorem lsInst_relativeConstancy :
    (fun ω => featureInteractionDesign commonLimitExampleFeature false (lsExampleTarget.X ω) ⬝ᵥ
        commonLimitExampleCoef - featureInteractionDesign commonLimitExampleFeature true
          (lsExampleTarget.X ω) ⬝ᵥ commonLimitExampleCoef) =ᵐ[lsExampleTarget.μ]
      lsExampleTarget.μ[fun ω => lsExampleTarget.Y false ω - lsExampleTarget.Y true ω |
        MeasurableSpace.comap lsExampleTarget.X inferInstance] := by
  have hX : Measurable lsExampleTarget.X := measurable_id
  have hm : Measurable[MeasurableSpace.comap lsExampleTarget.X inferInstance]
      (fun ω => lsExampleTarget.Y false ω - lsExampleTarget.Y true ω) :=
    (measurable_of_finite fun x : Bool => lsExampleOutcome false x - lsExampleOutcome true x).comp
      (comap_measurable _)
  rw [condExp_of_stronglyMeasurable hX.comap_le hm.stronglyMeasurable Integrable.of_finite]
  refine EventuallyEq.of_eq (funext fun ω => ?_)
  rw [commonLimitExample_dotProduct, commonLimitExample_dotProduct]
  rfl

/-- **An instance of `commonLimit_reportedMoments_anchored_identity_of_isMinOn`.** With
`a = true`, `b = c = false` and the reported contrast `d̂_bc = 0`, under relative constancy on
the identity scale, the weighted and the standardized anchored comparisons both converge in
probability to `E_Q[Y(false)] - E_Q[Y(true)] = -5/4`, and their difference converges in
probability to `0`. -/
theorem lsInst_anchored_identity :
    IsConsistent (fun n ω => (sampleBalancedArmMean commonLimitExampleFeature
        (lsInstReported n) lsExampleSample false n ω - sampleBalancedArmMean
          commonLimitExampleFeature (lsInstReported n) lsExampleSample true n ω) - 0)
        (-5 / 4) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => (reportedMomentsArmFit
        commonLimitExampleFeature lsExampleSample (lsInstReported n) false n ω -
          reportedMomentsArmFit commonLimitExampleFeature lsExampleSample
            (lsInstReported n) true n ω) - 0) atTop (fun _ => -5 / 4) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => ((reportedMomentsArmFit
        commonLimitExampleFeature lsExampleSample (lsInstReported n) false n ω -
          reportedMomentsArmFit commonLimitExampleFeature lsExampleSample
            (lsInstReported n) true n ω) - 0) - ((sampleBalancedArmMean
              commonLimitExampleFeature (lsInstReported n) lsExampleSample false n ω -
                sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n)
                  lsExampleSample true n ω) - 0)) atTop (fun _ => 0) := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h0 : lsExampleTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have h := (commonLimit_reportedMoments_anchored_identity_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (a := true) (b := false) (c := false)
    (dbc := fun _ _ => 0) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) hint hmin hexp hκ
    commonLimitExample_regression isIIDSample_lsExampleSample measurable_lsExampleSample
    (map_lsExampleSample 0) measurable_const (indepFun_const_left _ _)
    (fun _ => measurable_const) lsInst_tendsto lsInst_variance measurable_id
    (fun _ => Integrable.of_finite) commonLimitExample_featureMean Integrable.of_finite
    Integrable.of_finite lsInst_relativeConstancy
    (by rw [h0]; exact tendstoInMeasure_const 0))
  have he : lsExampleTarget.marginalEffect id true false = -5 / 4 :=
    commonLimitExample_marginalEffect
  rw [he] at h
  exact h

end PopulationAdjustment

end CausalInference
