/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.Support

/-!
# Population adjustment: overlap is the condition that fails beyond the support

Conditional transportability of an arm (`Transport.TransportModel.IsConditionallyTransportable`)
is the conjunction of overlap of the covariate laws with the other conditions, collected here
in `TransportModel.TransportableExceptOverlap` (probability laws, measurability,
integrability, exchangeability in the trial, positivity of the arm, structural invariance and
integrability of the reweighted outcome): `isConditionallyTransportable_iff`.

Without overlap the target mean is not identified, and overlap is the only condition missing.

* **One treated trial unit.** The models `beyondSupportModel r` (a trial of one treated unit with
  covariate `false` and outcome `0`, a target of one unit with covariate `true` and potential
  outcomes `r`) satisfy every condition except overlap for the treated arm
  (`transportableExceptOverlap_beyondSupportModel`). For the untreated arm positivity fails as
  well, since every trial unit is treated.
* **A randomized trial.** The models `randomizedBeyondSupportModel r` (a trial whose treatment is
  a fair coin, with covariate `false` and outcome `0`, and the same target) satisfy every
  condition except overlap for both arms (`transportableExceptOverlap_randomizedBeyondSupport`),
  have the same observed data (`observed_randomizedBeyondSupportModel`), a target covariate law
  `δ_true` not absolutely continuous with respect to the trial covariate law `δ_false`
  (`not_absolutelyContinuous_randomizedBeyondSupportModel`) and target mean `r`.
* **Non identification.** On the class of models that satisfy every condition of conditional
  transportability except overlap, the target mean is not point identified from the observed
  data, for the treated arm (`not_pointIdentified_targetMean_exceptOverlap`) and for every arm
  of a trial with two covariate values (`not_pointIdentified_targetMean_exceptOverlap_bool`).
* **The contrast.** With overlap added, the class is that of conditionally transportable models
  and the target mean is point identified (`pointIdentified_targetMean_exceptOverlap_overlap`,
  from `Transport.pointIdentified_targetMean`).

## Main definitions

* `Transport.TransportModel.TransportableExceptOverlap`.
* `randomizedBeyondSupportModel`.

## Main results

* `Transport.TransportModel.isConditionallyTransportable_iff`.
* `transportableExceptOverlap_beyondSupportModel`,
  `transportableExceptOverlap_randomizedBeyondSupport`,
  `not_absolutelyContinuous_randomizedBeyondSupportModel`,
  `targetMean_randomizedBeyondSupportModel`, `observed_randomizedBeyondSupportModel`.
* `not_pointIdentified_targetMean_exceptOverlap`,
  `not_pointIdentified_targetMean_exceptOverlap_bool`,
  `pointIdentified_targetMean_exceptOverlap_overlap`.

## References

* J. Pearl and E. Bareinboim, *Transportability of causal and statistical relations: a formal
  approach*, Proceedings of the AAAI Conference on Artificial Intelligence (2011).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory MissingData PointTreatment EffectMeasure

namespace Transport

namespace TransportModel

variable {Ω₁ Ω₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]

/-- **Every condition of conditional transportability of the arm `a` except overlap**: the
fields of `IsConditionallyTransportable` other than `overlap`. -/
structure TransportableExceptOverlap (M : TransportModel Ω₁ Ω₂ 𝒳) (a : Bool) : Prop where
  /-- The source measure is a probability measure. -/
  isProbabilityMeasure_μ₁ : IsProbabilityMeasure M.μ₁
  /-- The target measure is a probability measure. -/
  isProbabilityMeasure_μ₂ : IsProbabilityMeasure M.μ₂
  /-- The source covariates are measurable. -/
  measurable_X₁ : Measurable M.X₁
  /-- The treatment is measurable. -/
  measurable_A : Measurable M.A
  /-- The source potential outcomes are measurable. -/
  measurable_Y₁ : ∀ b, Measurable (M.Y₁ b)
  /-- The target covariates are measurable. -/
  measurable_X₂ : Measurable M.X₂
  /-- The source potential outcome of arm `a` is integrable. -/
  integrable_Y₁ : Integrable (M.Y₁ a) M.μ₁
  /-- The target potential outcome of arm `a` is integrable. -/
  integrable_Y₂ : Integrable (M.Y₂ a) M.μ₂
  /-- Exchangeability in the source, in indicator form. -/
  marMean : MARMean M.μ₁ M.X₁ (M.Y₁ a) (arm M.A a)
  /-- Positivity of the arm in the source. -/
  pos : ∀ᵐ ω ∂M.μ₁,
    0 < (M.μ₁[respInd (arm M.A a) | MeasurableSpace.comap M.X₁ inferInstance]) ω
  /-- Structural invariance of the conditional mean of `Y(a)`. -/
  structurallyInvariant : StructurallyInvariant M.μ₁ M.X₁ (M.Y₁ a) M.μ₂ M.X₂ (M.Y₂ a)
  /-- The reweighted source potential outcome is integrable. -/
  integrable_weight : Integrable (fun ω => densityRatio M.μ₁ M.X₁ M.μ₂ M.X₂ (M.X₁ ω) *
    M.Y₁ a ω) M.μ₁

/-- **Conditional transportability is the other conditions plus overlap.** -/
theorem isConditionallyTransportable_iff (M : TransportModel Ω₁ Ω₂ 𝒳) (a : Bool) :
    M.IsConditionallyTransportable a ↔
      M.TransportableExceptOverlap a ∧ M.μ₂.map M.X₂ ≪ M.μ₁.map M.X₁ := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.13⟩, h.12⟩
  · rintro ⟨h, hov⟩
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, hov, h.12⟩

end TransportModel

end Transport

namespace PopulationAdjustment

open Transport

/-! ### One treated trial unit -/

/-- **`beyondSupportModel r` satisfies every condition except overlap for the treated arm**:
the trial unit is treated, so the propensity of the treated arm is `1`; the conditional means
are `0` in the trial and `r` in the target, both values of `x ↦ if x then r else 0` at the
covariates `false` and `true`. -/
theorem transportableExceptOverlap_beyondSupportModel (r : ℝ) :
    (beyondSupportModel r).TransportableExceptOverlap true := by
  have hR : respInd (arm (fun _ : Unit => true) true) = fun _ => 1 :=
    funext fun _ => by simp [respInd_arm_apply]
  refine ⟨by simp only [beyondSupportModel]; infer_instance,
    by simp only [beyondSupportModel]; infer_instance, measurable_const, measurable_const,
    fun _ => measurable_const, measurable_const,
    by simp only [beyondSupportModel]; exact Integrable.of_finite,
    by simp only [beyondSupportModel]; exact Integrable.of_finite,
    ?_, ?_, ?_, by simp only [beyondSupportModel]; exact Integrable.of_finite⟩
  · simp only [MARMean, beyondSupportModel, MeasurableSpace.comap_const]
    rfl
  · simp only [beyondSupportModel, MeasurableSpace.comap_const]
    rw [hR, condExp_const bot_le]
    exact Filter.Eventually.of_forall fun _ => one_pos
  · refine ⟨fun x => if x then r else 0, Measurable.of_discrete, ?_, ?_⟩ <;>
      simp only [beyondSupportModel, MeasurableSpace.comap_const] <;>
      rw [condExp_const bot_le] <;> rfl

/-- **The target mean of the treated arm is not identified without overlap**: on the class of
transport models (one point trial and target spaces, covariates in `Bool`) that satisfy every
condition of conditional transportability of the treated arm except overlap, the target mean
of the treated arm is not a function of the observed data. The witnesses are
`beyondSupportModel 0` and `beyondSupportModel 1`. -/
theorem not_pointIdentified_targetMean_exceptOverlap :
    ¬ PointIdentified {M : TransportModel Unit Unit Bool | M.TransportableExceptOverlap true}
      TransportModel.observed fun M => M.targetMean true := by
  intro h
  have := h _ (transportableExceptOverlap_beyondSupportModel 0) _
    (transportableExceptOverlap_beyondSupportModel 1) (observed_beyondSupportModel 0 1)
  simp only [targetMean_beyondSupportModel] at this
  exact zero_ne_one this

/-! ### A randomized trial -/

/-- A trial whose treatment is a fair coin, with covariate `false` and outcome `0` in both arms,
and a target of one unit with covariate `true` and potential outcomes `r`. -/
noncomputable def randomizedBeyondSupportModel (r : ℝ) : TransportModel Bool Unit Bool where
  μ₁ := halfLaw
  X₁ := fun _ => false
  A := id
  Y₁ := fun _ _ => 0
  μ₂ := Measure.dirac ()
  X₂ := fun _ => true
  Y₂ := fun _ _ => r

/-- **`randomizedBeyondSupportModel r` satisfies every condition except overlap for both
arms**: the covariate is constant in the trial, so the conditional expectations given it are
means; the propensity of each arm is `1/2`. -/
theorem transportableExceptOverlap_randomizedBeyondSupport (r : ℝ) (a : Bool) :
    (randomizedBeyondSupportModel r).TransportableExceptOverlap a := by
  refine ⟨by simp only [randomizedBeyondSupportModel]; infer_instance,
    by simp only [randomizedBeyondSupportModel]; infer_instance, measurable_const,
    Measurable.of_discrete, fun _ => measurable_const, measurable_const,
    by simp only [randomizedBeyondSupportModel]; exact Integrable.of_finite,
    by simp only [randomizedBeyondSupportModel]; exact Integrable.of_finite, ?_, ?_, ?_,
    by simp only [randomizedBeyondSupportModel]; exact Integrable.of_finite⟩
  · simp only [MARMean, randomizedBeyondSupportModel, MeasurableSpace.comap_const]
    rfl
  · simp only [randomizedBeyondSupportModel, MeasurableSpace.comap_const]
    rw [condExp_bot]
    refine Filter.Eventually.of_forall fun _ => ?_
    rw [integral_halfLaw]
    cases a <;> simp [respInd_arm_apply]
  · refine ⟨fun x => if x then r else 0, Measurable.of_discrete, ?_, ?_⟩ <;>
      simp only [randomizedBeyondSupportModel, MeasurableSpace.comap_const] <;>
      rw [condExp_const bot_le] <;> rfl

/-- The target covariate law `δ_true` of `randomizedBeyondSupportModel r` is not absolutely
continuous with respect to its trial covariate law `δ_false`. -/
theorem not_absolutelyContinuous_randomizedBeyondSupportModel (r : ℝ) :
    ¬ (randomizedBeyondSupportModel r).μ₂.map (randomizedBeyondSupportModel r).X₂ ≪
      (randomizedBeyondSupportModel r).μ₁.map (randomizedBeyondSupportModel r).X₁ := by
  intro h
  have h1 : (randomizedBeyondSupportModel r).μ₁.map (randomizedBeyondSupportModel r).X₁ {true}
      = 0 := by
    simp [randomizedBeyondSupportModel, Measure.map_const]
  have h2 := h h1
  simp [randomizedBeyondSupportModel] at h2

/-- The target mean of `randomizedBeyondSupportModel r` is `r`, for both arms. -/
theorem targetMean_randomizedBeyondSupportModel (r : ℝ) (a : Bool) :
    (randomizedBeyondSupportModel r).targetMean a = r := by
  simp [TransportModel.targetMean, randomizedBeyondSupportModel]

/-- All the models `randomizedBeyondSupportModel r` have the same observed data. -/
theorem observed_randomizedBeyondSupportModel (r r' : ℝ) :
    (randomizedBeyondSupportModel r).observed = (randomizedBeyondSupportModel r').observed :=
  rfl

/-- **The target mean is not identified without overlap, for every arm**: on the class of
transport models (trial space `Bool`, one point target space, covariates in `Bool`) that satisfy
every condition of conditional transportability of the arm `a` except overlap, the target mean
of `a` is not a function of the observed data. The witnesses are
`randomizedBeyondSupportModel 0` and `randomizedBeyondSupportModel 1`, which share their
observed data, satisfy all the other conditions, fail overlap and have target means `0` and
`1`. -/
theorem not_pointIdentified_targetMean_exceptOverlap_bool (a : Bool) :
    ¬ PointIdentified {M : TransportModel Bool Unit Bool | M.TransportableExceptOverlap a}
      TransportModel.observed fun M => M.targetMean a := by
  intro h
  have := h _ (transportableExceptOverlap_randomizedBeyondSupport 0 a) _
    (transportableExceptOverlap_randomizedBeyondSupport 1 a)
    (observed_randomizedBeyondSupportModel 0 1)
  simp only [targetMean_randomizedBeyondSupportModel] at this
  exact zero_ne_one this

/-- **With overlap the target mean is identified**: on the class of models that satisfy every
condition except overlap and also overlap, which is the class of conditionally transportable
models (`TransportModel.isConditionallyTransportable_iff`), the target mean is point identified
(`Transport.pointIdentified_targetMean`). -/
theorem pointIdentified_targetMean_exceptOverlap_overlap {Ω₁ Ω₂ 𝒳 : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳] (a : Bool) :
    PointIdentified {M : TransportModel Ω₁ Ω₂ 𝒳 |
        M.TransportableExceptOverlap a ∧ M.μ₂.map M.X₂ ≪ M.μ₁.map M.X₁}
      TransportModel.observed fun M => M.targetMean a := by
  have hK : {M : TransportModel Ω₁ Ω₂ 𝒳 |
      M.TransportableExceptOverlap a ∧ M.μ₂.map M.X₂ ≪ M.μ₁.map M.X₁} =
      {M | M.IsConditionallyTransportable a} :=
    Set.ext fun M => (TransportModel.isConditionallyTransportable_iff M a).symm
  rw [hK]
  exact pointIdentified_targetMean a

end PopulationAdjustment

end CausalInference
