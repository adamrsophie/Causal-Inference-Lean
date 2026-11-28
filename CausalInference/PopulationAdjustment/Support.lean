/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.DensityRatio
public import CausalInference.PartialIdentification.IdentifiedSet

/-!
# Population adjustment: no reweighting beyond the support of the trial

Reweighting the trial can only reproduce target quantities on the part of the covariate space
that the trial covers. If the target covariate law puts mass where the trial has none, the
observed data (the law of the trial data and the target covariate law) do not determine the
target mean, so no weighting of the trial recovers it.

The models `beyondSupportModel r`, `r ∈ ℝ`: a trial of one unit with covariate `false`, treated,
with outcome `0`, and a target population of one unit with covariate `true` and potential outcomes
`r`. All of them have the same observed data, the target covariate law `δ_true` is not
absolutely continuous with respect to the trial covariate law `δ_false`
(`not_absolutelyContinuous_beyondSupportModel`), and the target mean is `r`
(`targetMean_beyondSupportModel`). Hence the target mean is not point identified from the
observed data (`not_pointIdentified_targetMean_beyondSupport`, for the treated arm, the arm the
trial observes), and for every weight function `w` the population weighted mean of the treated
arm is `0`, so it equals the target mean `r` only for `r = 0`
(`lawWeightedArmMean_beyondSupportModel`).

## Main results

* `not_absolutelyContinuous_beyondSupportModel`, `targetMean_beyondSupportModel`,
  `observed_beyondSupportModel`.
* `not_pointIdentified_targetMean_beyondSupport`, `lawWeightedArmMean_beyondSupportModel`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory Transport

/-- A trial of one treated unit with covariate `false` and outcome `0`, and a target of one unit
with covariate `true` and potential outcomes `r`. -/
noncomputable def beyondSupportModel (r : ℝ) : TransportModel Unit Unit Bool where
  μ₁ := Measure.dirac ()
  X₁ := fun _ => false
  A := fun _ => true
  Y₁ := fun _ _ => 0
  μ₂ := Measure.dirac ()
  X₂ := fun _ => true
  Y₂ := fun _ _ => r

/-- The target covariate law of `beyondSupportModel r` is not absolutely continuous with respect
to the trial covariate law: the target lies outside the support of the trial. -/
theorem not_absolutelyContinuous_beyondSupportModel (r : ℝ) :
    ¬ (beyondSupportModel r).targetCovLaw ≪
      (beyondSupportModel r).μ₁.map (beyondSupportModel r).X₁ := by
  intro h
  have h1 : (Measure.dirac false : Measure Bool) {true} = 0 := by simp
  have h2 : (Measure.dirac true : Measure Bool) {true} ≠ 0 := by simp
  refine h2 (?_ : _ = _)
  have := h (s := {true})
  simp only [TransportModel.targetCovLaw, beyondSupportModel, Measure.map_const,
    measure_univ, one_smul] at this
  exact this h1

/-- The target mean of `beyondSupportModel r` is `r`, for both arms. -/
theorem targetMean_beyondSupportModel (r : ℝ) (a : Bool) :
    (beyondSupportModel r).targetMean a = r := by
  simp [TransportModel.targetMean, beyondSupportModel]

/-- All the models `beyondSupportModel r` have the same observed data. -/
theorem observed_beyondSupportModel (r r' : ℝ) :
    (beyondSupportModel r).observed = (beyondSupportModel r').observed := rfl

/-- **The target mean is not identified beyond the support of the trial**: on the models
`beyondSupportModel r`, which share their observed data, the target mean is not a function of
the observed data. -/
theorem not_pointIdentified_targetMean_beyondSupport :
    ¬ PointIdentified (Set.range beyondSupportModel)
      TransportModel.observed fun M => M.targetMean true := by
  intro h
  have := h _ ⟨0, rfl⟩ _ ⟨1, rfl⟩ (observed_beyondSupportModel 0 1)
  simp only [targetMean_beyondSupportModel] at this
  exact zero_ne_one this

/-- **No weighting of the trial recovers the target mean beyond the support**: for every weight
function `w`, the population weighted mean of the treated arm of `beyondSupportModel r` is `0`
(the outcome of the only trial unit), whatever the target mean `r`. -/
theorem lawWeightedArmMean_beyondSupportModel (w : Bool → ℝ) (r : ℝ) :
    lawWeightedArmMean (beyondSupportModel r).sourceLaw w true = 0 ∧
      (beyondSupportModel r).targetMean true = r := by
  refine ⟨?_, targetMean_beyondSupportModel r true⟩
  simp [lawWeightedArmMean, TransportModel.sourceLaw, beyondSupportModel,
    PointTreatment.obsOutcome]

end PopulationAdjustment

end CausalInference
