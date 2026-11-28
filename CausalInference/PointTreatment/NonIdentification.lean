/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Bridges

/-!
# Point treatment: the average effect is not identified without assumptions

The fundamental problem of causal inference (Holland 1986): only the potential outcome of the
treatment received is observed. Identification is a property of the law of the observed data
`(W, A, Y)` (`PointTreatmentModel.observedLaw`, `PointIdentified`). Without an assumption on the
assignment, the law of the observed data carries no information on the average effect: changing
the counterfactual outcome of every unit, `Y(0)` of the treated by `-c` and `Y(1)` of the
controls by `+c`, keeps the observed data and adds `c` to the individual effect of every unit.

On the class of regular models (probability measure, measurable variables, integrable potential
outcomes, no assumption on the assignment) the identified set of the average effect at every
attainable observed law is the whole real line (`identifiedSet_ate_eq_univ`). Hence the average
effect is not point identified (`not_pointIdentified_ate`, with the concrete pair
`ate_ne_of_observedLaw_eq_example`), and no map from observed laws to random variables recovers
the individual effect even almost everywhere (`not_exists_ae_eq_indivEffect`). Under
ignorability and positivity the average effect is point identified (`pointIdentified_ate`).

## Main definitions

* `PointTreatmentModel.IsRegular`: the regularity conditions, with no causal assumption.
* `shiftCounterfactualBy A Y c`: the potential outcomes with the counterfactual outcomes moved
  so that every individual effect grows by `c`.

## Main results

* `obsOutcome_shiftCounterfactualBy`, `indivEffect_shiftCounterfactualBy`.
* `exists_observedLaw_eq_ate_add`: every regular model has, for every `c`, a regular model with
  the same observed law and average effect `ATE + c`.
* `identifiedSet_ate_eq_univ`, `not_pointIdentified_ate`, `ate_ne_of_observedLaw_eq_example`,
  `not_exists_ae_eq_indivEffect`.

## References

* P. W. Holland, *Statistics and causal inference*, Journal of the American Statistical
  Association 81 (1986).
* C. F. Manski, *Partial Identification of Probability Distributions*, Springer, 2003.
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Set

variable {Ω 𝒲 : Type*}

/-- The potential outcomes that keep the factual outcome and move the counterfactual one:
`Y(0)` of a treated unit becomes `Y(0) - c`, `Y(1)` of a control becomes `Y(1) + c`. -/
def shiftCounterfactualBy (A : Ω → Bool) (Y : Bool → Ω → ℝ) (c : ℝ) : Bool → Ω → ℝ :=
  fun a ω => if A ω = a then Y a ω else if a then Y a ω + c else Y a ω - c

/-- The shift keeps the observed outcome. -/
theorem obsOutcome_shiftCounterfactualBy (A : Ω → Bool) (Y : Bool → Ω → ℝ) (c : ℝ) :
    obsOutcome A (shiftCounterfactualBy A Y c) = obsOutcome A Y := by
  funext ω; simp [obsOutcome, shiftCounterfactualBy]

/-- The shift adds `c` to the individual effect of every unit. -/
theorem indivEffect_shiftCounterfactualBy (A : Ω → Bool) (Y : Bool → Ω → ℝ) (c : ℝ) (ω : Ω) :
    indivEffect (shiftCounterfactualBy A Y c) ω = indivEffect Y ω + c := by
  cases h : A ω <;> simp [indivEffect, shiftCounterfactualBy, h] <;> ring

variable [MeasurableSpace Ω] [MeasurableSpace 𝒲]

/-- The regularity conditions of a point treatment model, with no assumption on the
assignment: a probability measure, measurable variables and integrable potential outcomes. -/
structure PointTreatmentModel.IsRegular (M : PointTreatmentModel Ω 𝒲) : Prop where
  /-- The underlying measure is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure M.μ
  /-- The conditioning variable is measurable. -/
  measurable_W : Measurable M.W
  /-- The treatment is measurable. -/
  measurable_A : Measurable M.A
  /-- The potential outcomes are measurable. -/
  measurable_Y : ∀ a, Measurable (M.Y a)
  /-- The potential outcomes are integrable. -/
  integrable_Y : ∀ a, Integrable (M.Y a) M.μ

theorem measurable_shiftCounterfactualBy {A : Ω → Bool} {Y : Bool → Ω → ℝ}
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (c : ℝ) (a : Bool) :
    Measurable (shiftCounterfactualBy A Y c a) := by
  have hs : MeasurableSet {ω | A ω = a} := hA (measurableSet_singleton a)
  refine Measurable.ite hs (hY a) ?_
  cases a
  · exact (hY false).sub_const c
  · exact (hY true).add_const c

theorem integrable_shiftCounterfactualBy {μ : Measure Ω} [IsFiniteMeasure μ] {A : Ω → Bool}
    {Y : Bool → Ω → ℝ} (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (c : ℝ) (a : Bool) :
    Integrable (shiftCounterfactualBy A Y c a) μ := by
  refine Integrable.mono' (((hYi a).norm.add (integrable_const |c|)))
    (measurable_shiftCounterfactualBy hA hY c a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [shiftCounterfactualBy, Pi.add_apply, Real.norm_eq_abs]
  have h1 := abs_add_le (Y a ω) c
  have h2 := abs_sub (Y a ω) c
  have h3 := abs_nonneg c
  split_ifs <;> linarith

/-- The model with the same measure, covariates and treatment, and the potential outcomes
`shiftCounterfactualBy M.A M.Y c`. -/
def PointTreatmentModel.shiftBy (M : PointTreatmentModel Ω 𝒲) (c : ℝ) :
    PointTreatmentModel Ω 𝒲 :=
  ⟨M.μ, M.W, M.A, shiftCounterfactualBy M.A M.Y c⟩

theorem PointTreatmentModel.IsRegular.shiftBy {M : PointTreatmentModel Ω 𝒲} (hM : M.IsRegular)
    (c : ℝ) : (M.shiftBy c).IsRegular :=
  have := hM.isProbabilityMeasure
  ⟨hM.isProbabilityMeasure, hM.measurable_W, hM.measurable_A,
    measurable_shiftCounterfactualBy hM.measurable_A hM.measurable_Y c,
    integrable_shiftCounterfactualBy hM.measurable_A hM.measurable_Y hM.integrable_Y c⟩

theorem PointTreatmentModel.observedLaw_shiftBy (M : PointTreatmentModel Ω 𝒲) (c : ℝ) :
    (M.shiftBy c).observedLaw = M.observedLaw := by
  have h : (M.shiftBy c).observedData = M.observedData := by
    funext ω
    simp only [PointTreatmentModel.observedData, PointTreatmentModel.shiftBy,
      obsOutcome_shiftCounterfactualBy]
  simp only [PointTreatmentModel.observedLaw, h]
  rfl

theorem PointTreatmentModel.IsRegular.ate_shiftBy {M : PointTreatmentModel Ω 𝒲}
    (hM : M.IsRegular) (c : ℝ) : ate (M.shiftBy c).μ (M.shiftBy c).Y = ate M.μ M.Y + c := by
  have := hM.isProbabilityMeasure
  simp only [ate, PointTreatmentModel.shiftBy]
  simp_rw [indivEffect_shiftCounterfactualBy]
  rw [integral_add (integrable_indivEffect (hM.integrable_Y true) (hM.integrable_Y false))
    (integrable_const c)]
  simp

/-- **The observed law carries no information on the average effect.** For every regular model
and every `c : ℝ` there is a regular model with the same measure, covariates and treatment, the
same law of the observed data `(W, A, Y)`, individual effects larger by `c` at every unit and
average effect `ATE + c`. -/
theorem exists_observedLaw_eq_ate_add {M : PointTreatmentModel Ω 𝒲} (hM : M.IsRegular) (c : ℝ) :
    ∃ M' : PointTreatmentModel Ω 𝒲, M'.IsRegular ∧ M'.observedLaw = M.observedLaw ∧
      (∀ ω, indivEffect M'.Y ω = indivEffect M.Y ω + c) ∧ ate M'.μ M'.Y = ate M.μ M.Y + c :=
  ⟨M.shiftBy c, hM.shiftBy c, M.observedLaw_shiftBy c,
    indivEffect_shiftCounterfactualBy M.A M.Y c, hM.ate_shiftBy c⟩

/-- **The identified set of the average effect is the whole line.** On the regular models, at
every observed law attained by one of them, every real number is the average effect of a regular
model with that observed law. -/
theorem identifiedSet_ate_eq_univ {M : PointTreatmentModel Ω 𝒲} (hM : M.IsRegular) :
    identifiedSet {M : PointTreatmentModel Ω 𝒲 | M.IsRegular} PointTreatmentModel.observedLaw
      (fun M => ate M.μ M.Y) M.observedLaw = univ := by
  refine eq_univ_of_forall fun t => ?_
  obtain ⟨M', hM', hobs, -, hate⟩ := exists_observedLaw_eq_ate_add hM (t - ate M.μ M.Y)
  exact mem_identifiedSet.2 ⟨M', hM', hobs, by simp only [hate]; ring⟩

/-- The regular model on `(Ω, μ)` with constant covariate `w`, every unit treated and potential
outcomes `0`. -/
noncomputable abbrev constModel (μ : Measure Ω) (w : 𝒲) : PointTreatmentModel Ω 𝒲 :=
  ⟨μ, fun _ => w, fun _ => true, fun _ _ => 0⟩

theorem constModel_isRegular (μ : Measure Ω) [IsProbabilityMeasure μ] (w : 𝒲) :
    (constModel μ w).IsRegular :=
  ⟨inferInstance, measurable_const, measurable_const, fun _ => measurable_const,
    fun _ => integrable_const 0⟩

/-- **The average effect is not point identified** from the law of `(W, A, Y)` on the regular
models over any probability space `(Ω, μ)` and covariate space with a point `w`. -/
theorem not_pointIdentified_ate (μ : Measure Ω) [IsProbabilityMeasure μ] (w : 𝒲) :
    ¬ PointIdentified {M : PointTreatmentModel Ω 𝒲 | M.IsRegular}
      PointTreatmentModel.observedLaw (fun M => ate M.μ M.Y) := by
  have hM := constModel_isRegular μ w
  obtain ⟨M', hM', hobs, -, hate⟩ := exists_observedLaw_eq_ate_add hM 1
  intro h
  have := h _ hM' _ hM hobs
  simp only at this
  linarith

/-- **A concrete pair of models with the same observed law and different average effects.** On
one unit, treated, with `Y(1) = 1`: the first model has `Y(0) = 0`, the second `Y(0) = 1`. Both
observe `(W, A, Y) = ((), 1, 1)`, so the observed laws are the same Dirac mass, and the average
effects are `1` and `0`. -/
theorem ate_ne_of_observedLaw_eq_example :
    ∃ M M' : PointTreatmentModel Unit Unit, M.IsRegular ∧ M'.IsRegular ∧
      M.observedLaw = M'.observedLaw ∧ ate M.μ M.Y = 1 ∧ ate M'.μ M'.Y = 0 := by
  refine ⟨⟨Measure.dirac (), fun _ => (), fun _ => true, fun a _ => if a then 1 else 0⟩,
    ⟨Measure.dirac (), fun _ => (), fun _ => true, fun _ _ => 1⟩, ⟨inferInstance,
      measurable_const, measurable_const, fun _ => measurable_const,
      fun _ => Integrable.of_finite⟩, ⟨inferInstance, measurable_const, measurable_const,
      fun _ => measurable_const, fun _ => Integrable.of_finite⟩, ?_, ?_, ?_⟩
  · simp only [PointTreatmentModel.observedLaw]
    congr 1
  · simp [ate, indivEffect]
  · simp [ate, indivEffect]

/-- **The individual effect is not identified, even almost everywhere.** On the regular models
over a probability space `(Ω, μ)`, there is no map `F` from laws of `(W, A, Y)` to random
variables with `F (law of (W, A, Y)) = Y(1) - Y(0)` almost everywhere in every regular model. -/
theorem not_exists_ae_eq_indivEffect (μ : Measure Ω) [IsProbabilityMeasure μ] (w : 𝒲) :
    ¬ ∃ F : Measure (𝒲 × Bool × ℝ) → Ω → ℝ, ∀ M : PointTreatmentModel Ω 𝒲, M.IsRegular →
      F M.observedLaw =ᵐ[M.μ] indivEffect M.Y := by
  rintro ⟨F, hF⟩
  have hM := constModel_isRegular μ w
  have h1 := hF _ hM
  have h2 := hF _ (hM.shiftBy 1)
  rw [PointTreatmentModel.observedLaw_shiftBy] at h2
  have hfalse : ∀ᵐ ω ∂μ, False := by
    filter_upwards [h1, h2] with ω a b
    have := indivEffect_shiftCounterfactualBy (constModel μ w).A (constModel μ w).Y 1 ω
    change F (constModel μ w).observedLaw ω =
      indivEffect (shiftCounterfactualBy (constModel μ w).A (constModel μ w).Y 1) ω at b
    linarith
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

end PointTreatment

end CausalInference
