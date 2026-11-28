/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitIdentified
public import CausalInference.PopulationAdjustment.StandardizationConsistencyExamples

/-!
# Examples of the common limit

An instance in which every hypothesis of `commonLimit_interaction_armMean` and of
`anchored_link_identified` is verified. The trial is the randomized trial of
`StandardizationConsistencyExamples` (a binary covariate, equally likely, and an independent
equally likely binary assignment) with the potential outcome `Y(a) = 1[x] + 1[a](1 + 1[x])`; the
feature is `φ(x) = 1[x]`, the target covariate is `true` with probability `1/4`, and the matched
feature mean is `t = 1/4`. The regression is linear in the interaction design of the feature with
coefficient `ξ₀ = (0, 1, 1, 1)`, and the outcome has no residual.

## Main definitions

* `commonLimitExampleFeature`, `commonLimitExampleCoef`.

## Main results

* `commonLimitExample_armMean`: the weighted arm mean and the standardized arm mean of arm `true`
  both converge in probability to `3/2`, the target mean of `Y(true)`, and their difference
  converges in probability to `0`.
* `commonLimitExample_anchored`: the anchored comparisons on the identity scale both converge in
  probability to `-5/4`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The feature `φ(x) = 1[x]` of the example. -/
noncomputable def commonLimitExampleFeature (x : Bool) : Fin 1 → ℝ :=
  fun _ => if x then 1 else 0

/-- The matched feature mean `t = 1/4` of the example. -/
noncomputable def commonLimitExampleMean : Fin 1 → ℝ := fun _ => 1 / 4

/-- The coefficient `ξ₀ = (0, 1, 1, 1)` of the example in the interaction design: no intercept,
and the main effect, the treatment effect and the interaction all `1`. -/
noncomputable def commonLimitExampleCoef : Option (Fin 1) ⊕ Option (Fin 1) → ℝ :=
  fun k => if k = .inl none then 0 else 1

theorem commonLimitExample_dotProduct (a x : Bool) :
    featureInteractionDesign commonLimitExampleFeature a x ⬝ᵥ commonLimitExampleCoef =
      lsExampleOutcome a x := by
  rw [featureInteractionDesign_dotProduct]
  cases a <;> cases x <;>
    simp [interactionIntercept, interactionMain, interactionEffect, interactionModifier,
      commonLimitExampleCoef, commonLimitExampleFeature, lsExampleOutcome, dotProduct]

theorem commonLimitExample_bound (x : Bool) :
    ‖commonLimitExampleFeature x - commonLimitExampleMean‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => ?_
  cases x <;> norm_num [commonLimitExampleFeature, commonLimitExampleMean, abs_of_nonneg]

theorem lsExampleTrial_covLaw : lsExampleTrial.covLaw = halfLaw := by
  change (halfLaw.prod halfLaw).map Prod.snd = halfLaw
  rw [Measure.map_snd_prod, measure_univ, one_smul]

theorem commonLimitExample_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 4 : ℝ) ≤
    lsExampleTrial.covLaw.real {x | 1 / 4 ≤ v ⬝ᵥ (commonLimitExampleFeature x -
      commonLimitExampleMean)} := by
  intro v hv
  have hv0 : |v 0| = 1 := by
    have h : ‖v‖ = ‖v 0‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
        (norm_le_pi_norm v 0)
      rw [Subsingleton.elim j 0]
    rw [← Real.norm_eq_abs, ← h, hv]
  rw [lsExampleTrial_covLaw]
  have hhalf : ∀ b : Bool, (1 / 4 : ℝ) ≤ halfLaw.real {b} := fun b => by
    rw [measureReal_def]
    cases b <;> simp [halfLaw, stratumLaw] <;> norm_num
  rcases abs_eq (zero_le_one) |>.1 hv0 with h | h
  · refine (hhalf true).trans (measureReal_mono (fun x hx => ?_) (measure_ne_top _ _))
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, commonLimitExampleFeature, commonLimitExampleMean]
    norm_num
  · refine (hhalf false).trans (measureReal_mono (fun x hx => ?_) (measure_ne_top _ _))
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, commonLimitExampleFeature, commonLimitExampleMean]

theorem commonLimitExample_regression :
    IsOutcomeRegression lsExampleTrial.μ lsExampleTrial.A lsExampleTrial.X
      lsExampleTrial.obsOutcome fun a x =>
        featureInteractionDesign commonLimitExampleFeature a x ⬝ᵥ commonLimitExampleCoef := by
  have h := lsExample_linearOutcomeModel.isOutcomeRegression
  have he : (fun a x => lsExampleDesign a x ⬝ᵥ lsExampleCoef) = fun a x =>
      featureInteractionDesign commonLimitExampleFeature a x ⬝ᵥ commonLimitExampleCoef := by
    funext a x
    rw [lsExampleDesign_dotProduct, commonLimitExample_dotProduct]
  rwa [he] at h

theorem commonLimitExample_variance :
    lsExampleTrial.ipdLaw[fun o => (o.2.2 -
      featureInteractionDesign commonLimitExampleFeature o.2.1 o.1 ⬝ᵥ commonLimitExampleCoef) ^ 2 |
        MeasurableSpace.comap (fun o : Bool × Bool × ℝ => (o.1, o.2.1)) inferInstance]
      ≤ᵐ[lsExampleTrial.ipdLaw] fun _ => 0 := by
  have hm : Measurable fun o : Bool × Bool × ℝ => (o.2.2 -
      featureInteractionDesign commonLimitExampleFeature o.2.1 o.1 ⬝ᵥ commonLimitExampleCoef) ^ 2 :=
    (measurable_snd.snd.sub ((measurable_of_finite fun q : Bool × Bool =>
      featureInteractionDesign commonLimitExampleFeature q.2 q.1 ⬝ᵥ commonLimitExampleCoef).comp
        (measurable_fst.prodMk measurable_snd.fst))).pow_const 2
  have h0 : (fun o : Bool × Bool × ℝ => (o.2.2 -
      featureInteractionDesign commonLimitExampleFeature o.2.1 o.1 ⬝ᵥ commonLimitExampleCoef) ^ 2)
      =ᵐ[lsExampleTrial.ipdLaw] 0 := by
    rw [EventuallyEq, Trial.ipdLaw]
    simp only [Pi.zero_apply]
    rw [ae_map_iff (measurable_of_finite _).aemeasurable
      (measurableSet_eq_fun hm (measurable_const (a := (0 : ℝ))))]
    refine ae_of_all _ fun ω => ?_
    rw [commonLimitExample_dotProduct]
    simp [Trial.obsOutcome, lsExampleTrial]
  filter_upwards [condExp_congr_ae h0] with o ho
  rw [ho, condExp_zero]
  rfl

theorem commonLimitExample_featureMean (k : Fin 1) :
    ∫ x, commonLimitExampleFeature x k ∂lsExampleTarget.covLaw = commonLimitExampleMean k := by
  have hc : lsExampleTarget.covLaw = standardizationTargetLaw := by
    change standardizationTargetLaw.map id = _
    rw [Measure.map_id]
  rw [hc, standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
  simp [standardizedRisk, commonLimitExampleFeature, commonLimitExampleMean]

theorem commonLimitExample_armMean_value : lsExampleTarget.armMean true = 3 / 2 := by
  simp only [Population.armMean, lsExampleTarget]
  rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
  simp [standardizedRisk, lsExampleOutcome]
  norm_num

/-- **Weighting and standardization share their limit in the example.** Every hypothesis of
`commonLimit_interaction_armMean` holds; the weighted and the standardized estimators of the
target mean of `Y(true)` both converge in probability to `3/2`, and their difference converges in
probability to `0`. -/
theorem commonLimitExample_armMean :
    IsConsistent (sampleBalancedArmMean commonLimitExampleFeature commonLimitExampleMean
      lsExampleSample true) (3 / 2) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => ∫ x,
        featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω ∂lsExampleTarget.covLaw) atTop (fun _ => 3 / 2) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω => ∫ x,
        featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
            recordResponse lsExampleSample n ω ∂lsExampleTarget.covLaw -
          sampleBalancedArmMean commonLimitExampleFeature commonLimitExampleMean
            lsExampleSample true n ω) atTop (fun _ => 0) := by
  rw [← commonLimitExample_armMean_value]
  exact commonLimit_interaction_armMean lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_regression
    commonLimitExample_variance isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) measurable_id commonLimitExample_featureMean true Integrable.of_finite
    (lsExample_structurallyInvariant true) lsExample_absolutelyContinuous

theorem commonLimitExample_marginalEffect :
    lsExampleTarget.marginalEffect id true false = -5 / 4 := by
  have h := lsExample_marginalEffect
  simp only [Population.marginalEffect, id] at h ⊢
  linarith

/-- **The anchored comparisons in the example.** Every hypothesis of `anchored_link_identified`
holds on the identity scale with `a = true`, `c = false`, `b = false` and the reported contrast
`d̂_bc = 0`; the weighted and the standardized anchored comparisons both converge in probability
to the target effect `-5/4`, and their difference converges in probability to `0`. -/
theorem commonLimitExample_anchored :
    IsConsistent (anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
      lsExampleSample fun _ _ => 0) (-5 / 4) lsExampleSampleLaw ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        id (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample false n ω) -
        id (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω) - 0) atTop (fun _ => -5 / 4) ∧
      TendstoInMeasure lsExampleSampleLaw (fun n ω =>
        (id (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample false n ω) -
        id (commonLimitStandardized commonLimitExampleFeature lsExampleTarget.covLaw
          lsExampleSample true n ω) - 0) -
          anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
            lsExampleSample (fun _ _ => 0) n ω) atTop (fun _ => 0) := by
  have h0 : lsExampleTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have hdbc : TendstoInMeasure lsExampleSampleLaw
      (fun (_ : ℕ) (_ : ℕ → Bool × Bool) => (0 : ℝ)) atTop
        fun _ => lsExampleTarget.marginalEffect id false false := by
    rw [h0]; exact tendstoInMeasure_const 0
  rw [← commonLimitExample_marginalEffect]
  exact anchored_link_identified (a := true) (b := false) (c := false) (g := id)
    lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.memLp_Y (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin commonLimitExample_regression
    commonLimitExample_variance isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) measurable_id commonLimitExample_featureMean Integrable.of_finite
    Integrable.of_finite (lsExample_structurallyInvariant true)
    (lsExample_structurallyInvariant false) lsExample_absolutelyContinuous
    hdbc continuousAt_id continuousAt_id

end PopulationAdjustment

end CausalInference
