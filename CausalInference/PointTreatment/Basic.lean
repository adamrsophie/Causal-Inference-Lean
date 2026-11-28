/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MissingData.Basic
public import CausalInference.PartialIdentification.Manski

/-!
# Point treatment: potential outcomes, observed outcome and causal estimands

The potential outcome model for a binary point treatment (Neyman 1923, Rubin 1974) on a measure
space. A unit `ω ∈ Ω` has two potential outcomes `Y true ω` (under treatment) and `Y false ω`
(under control), a treatment `A ω : Bool` and covariates `X ω`. Only the potential outcome of
the treatment received is observed (Holland 1986).

## Setting

A measurable space `Ω` with a measure `μ` (a probability measure in applications), a treatment
`A : Ω → Bool` and potential outcomes `Y : Bool → Ω → ℝ`. Means given an arm are integrals
against Mathlib's conditional measure `μ[|A ⁻¹' {a}]`, as for `MissingData.completeCaseMean`
and `Manski.boundY1_eq_cond`. Such a mean is a genuine conditional mean only when
`μ (A ⁻¹' {a}) ≠ 0`; otherwise the conditional measure is `0` and the integral is `0` by
convention. The theorems below that read an arm mean as a conditional mean assume a positive
arm probability; the algebraic identities (the decompositions) hold without it, because a null
arm enters them multiplied by its probability or through both sides alike.

## Main definitions

* `obsOutcome A Y`: the observed outcome `ω ↦ Y (A ω) ω`; consistency is built into this
  definition, and `IsObservedOutcome A Y Yo` states it for a separately given outcome `Yo`.
* `indivEffect Y`: the individual effect `Y true - Y false`.
* `armMean μ Y a`, `ate μ Y`: the mean `E[Y(a)]` and the average effect `E[Y(1) - Y(0)]`.
* `condMeanArm μ A a f`: the mean of `f` in the arm `{A = a}`.
* `att μ A Y`, `atc μ A Y`: the average effects in the treated and in the controls.
* `naiveContrast μ A Y`: `E[Y | A = 1] - E[Y | A = 0]` for the observed outcome.

## Main results

* `isObservedOutcome_iff`, `obsOutcome_eq_respInd`: the two forms of consistency.
* `ate_eq_armMean_sub`: `E[Y(1) - Y(0)] = E[Y(1)] - E[Y(0)]` for integrable potential outcomes.
* `ate_eq_att_add_atc`: `ATE = P(A = 1) ATT + P(A = 0) ATC` under a probability measure.
* `att_eq_setIntegral_div`: with `P(A = 1) > 0`, the ATT is the mean of the individual effect
  over the treated, `∫_{A = 1} (Y(1) - Y(0)) dμ / P(A = 1)`.
* `condMeanArm_obsOutcome`: in the arm `a` the observed outcome has the mean of `Y(a)`.
* `naiveContrast_eq_att_add`: the naive contrast is the ATT plus the selection bias
  `E[Y(0) | A = 1] - E[Y(0) | A = 0]`.
* `exists_indivEffect_ne_of_obsOutcome_eq`: the individual effect is not a function of the
  observed data. Every model has a second model with the same treatment and observed outcome
  (hence the same law of the observed data) whose individual effect differs at every unit;
  `indivEffect_not_function_of_obsOutcome` is the concrete two model instance on one point.

## References

* J. Neyman, *On the application of probability theory to agricultural experiments* (1923;
  English translation, Statistical Science 5, 1990).
* D. B. Rubin, *Estimating causal effects of treatments in randomized and nonrandomized
  studies*, Journal of Educational Psychology 66 (1974).
* P. W. Holland, *Statistics and causal inference*, Journal of the American Statistical
  Association 81 (1986).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω : Type*}

/-! ### The observed outcome and consistency -/

/-- The observed outcome: the potential outcome of the treatment received,
`ω ↦ Y (A ω) ω`. Consistency (the observed outcome is the potential outcome under the treatment
received) is built into this definition. -/
def obsOutcome (A : Ω → Bool) (Y : Bool → Ω → ℝ) : Ω → ℝ := fun ω => Y (A ω) ω

/-- Consistency for a separately given outcome `Yo`: at every unit, `Yo` is the potential
outcome of the treatment received. -/
def IsObservedOutcome (A : Ω → Bool) (Y : Bool → Ω → ℝ) (Yo : Ω → ℝ) : Prop :=
  ∀ ω, Yo ω = Y (A ω) ω

/-- Consistency determines the observed outcome: `Yo` satisfies it exactly when it is
`obsOutcome A Y`. -/
theorem isObservedOutcome_iff {A : Ω → Bool} {Y : Bool → Ω → ℝ} {Yo : Ω → ℝ} :
    IsObservedOutcome A Y Yo ↔ Yo = obsOutcome A Y :=
  ⟨fun h => funext h, fun h ω => by rw [h]; rfl⟩

theorem obsOutcome_of_eq {A : Ω → Bool} (Y : Bool → Ω → ℝ) {ω : Ω} {a : Bool} (h : A ω = a) :
    obsOutcome A Y ω = Y a ω := by
  simp [obsOutcome, h]

/-- Consistency in arithmetic form: `Y = 1{A} Y(1) + (1 - 1{A}) Y(0)`, with the response
indicator `MissingData.respInd A` of the treated event. -/
theorem obsOutcome_eq_respInd (A : Ω → Bool) (Y : Bool → Ω → ℝ) (ω : Ω) :
    obsOutcome A Y ω = respInd A ω * Y true ω + (1 - respInd A ω) * Y false ω := by
  cases h : A ω <;> simp [obsOutcome, respInd_apply, h]

theorem measurable_obsOutcome [MeasurableSpace Ω] {A : Ω → Bool} {Y : Bool → Ω → ℝ}
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) : Measurable (obsOutcome A Y) := by
  have h : obsOutcome A Y = fun ω => if A ω = true then Y true ω else Y false ω := by
    funext ω; cases h : A ω <;> simp [obsOutcome, h]
  rw [h]
  exact Measurable.ite (hA (measurableSet_singleton true)) (hY true) (hY false)

/-- Under a finite measure the observed outcome is integrable when both potential outcomes are:
it is bounded in absolute value by `|Y(1)| + |Y(0)|`. -/
theorem integrable_obsOutcome [MeasurableSpace Ω] {μ : Measure Ω} {A : Ω → Bool}
    {Y : Bool → Ω → ℝ} (hA : Measurable A) (hY : ∀ a, Integrable (Y a) μ) :
    Integrable (obsOutcome A Y) μ := by
  classical
  have h : obsOutcome A Y = (A ⁻¹' {true}).piecewise (Y true) (Y false) := by
    funext ω; cases h : A ω <;> simp [obsOutcome, Set.piecewise, h]
  rw [h]
  exact Integrable.piecewise (hA (measurableSet_singleton true)).nullMeasurableSet
    (hY true).integrableOn
    (hY false).integrableOn

/-! ### Estimands -/

/-- The individual effect `Y(1) - Y(0)` of the unit `ω`. -/
def indivEffect (Y : Bool → Ω → ℝ) : Ω → ℝ := fun ω => Y true ω - Y false ω

variable [MeasurableSpace Ω]

/-- The mean of the potential outcome `Y(a)`, `E[Y(a)] = ∫ Y a dμ`. -/
noncomputable def armMean (μ : Measure Ω) (Y : Bool → Ω → ℝ) (a : Bool) : ℝ := ∫ ω, Y a ω ∂μ

/-- The average treatment effect `E[Y(1) - Y(0)]`, the integral of the individual effect. -/
noncomputable def ate (μ : Measure Ω) (Y : Bool → Ω → ℝ) : ℝ := ∫ ω, indivEffect Y ω ∂μ

/-- The mean of `f` in the arm `{A = a}`: the integral against the conditional measure
`μ[|A ⁻¹' {a}]`. It is a conditional mean when `μ (A ⁻¹' {a}) ≠ 0`. -/
noncomputable def condMeanArm (μ : Measure Ω) (A : Ω → Bool) (a : Bool) (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω ∂μ[|A ⁻¹' {a}]

/-- The average effect in the treated, `E[Y(1) - Y(0) | A = 1]`. -/
noncomputable def att (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) : ℝ :=
  condMeanArm μ A true (indivEffect Y)

/-- The average effect in the controls, `E[Y(1) - Y(0) | A = 0]`. -/
noncomputable def atc (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) : ℝ :=
  condMeanArm μ A false (indivEffect Y)

/-- The naive contrast of observed means, `E[Y | A = 1] - E[Y | A = 0]`. -/
noncomputable def naiveContrast (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) : ℝ :=
  condMeanArm μ A true (obsOutcome A Y) - condMeanArm μ A false (obsOutcome A Y)

variable {μ : Measure Ω} {A : Ω → Bool} {Y : Bool → Ω → ℝ}

/-- The average effect is the difference of the two potential outcome means, for integrable
potential outcomes. -/
theorem ate_eq_armMean_sub (h1 : Integrable (Y true) μ) (h0 : Integrable (Y false) μ) :
    ate μ Y = armMean μ Y true - armMean μ Y false :=
  integral_sub h1 h0

theorem integrable_indivEffect (h1 : Integrable (Y true) μ) (h0 : Integrable (Y false) μ) :
    Integrable (indivEffect Y) μ :=
  h1.sub h0

/-- An integrable function stays integrable under a conditional measure. -/
theorem integrable_cond {f : Ω → ℝ} (hf : Integrable f μ) (s : Set Ω) :
    Integrable f μ[|s] := by
  by_cases hs : μ s = 0
  · rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 hs, smul_zero]
    exact integrable_zero_measure
  · exact (hf.restrict).smul_measure (ENNReal.inv_ne_top.2 hs)

/-- Locality of an arm mean: it only depends on the values of `f` in the arm. -/
theorem condMeanArm_congr (hA : Measurable A) (a : Bool) {f g : Ω → ℝ}
    (h : ∀ ω, A ω = a → f ω = g ω) : condMeanArm μ A a f = condMeanArm μ A a g := by
  rw [condMeanArm, condMeanArm, ProbabilityTheory.cond, integral_smul_measure,
    integral_smul_measure, setIntegral_congr_fun (hA (measurableSet_singleton a))
      (fun ω hω => h ω hω)]

/-- Arm means are linear for integrable functions. -/
theorem condMeanArm_sub {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (a : Bool) :
    condMeanArm μ A a (fun ω => f ω - g ω) = condMeanArm μ A a f - condMeanArm μ A a g :=
  integral_sub (integrable_cond hf _) (integrable_cond hg _)

/-- In the arm `a`, the observed outcome has the mean of the potential outcome `Y(a)`. -/
theorem condMeanArm_obsOutcome (hA : Measurable A) (a : Bool) :
    condMeanArm μ A a (obsOutcome A Y) = condMeanArm μ A a (Y a) :=
  condMeanArm_congr hA a fun _ h => obsOutcome_of_eq Y h

/-- The integral over the arm `{A = a}` is the arm probability times the arm mean. -/
theorem setIntegral_eq_measureReal_mul_condMeanArm [IsFiniteMeasure μ] (a : Bool)
    (f : Ω → ℝ) :
    ∫ ω in A ⁻¹' {a}, f ω ∂μ = μ.real (A ⁻¹' {a}) * condMeanArm μ A a f :=
  Manski.setIntegral_eq_measureReal_mul_cond _ f

/-- With a treated arm of positive probability, the ATT is the mean of the individual effect
over the treated units: `ATT = ∫_{A = 1} (Y(1) - Y(0)) dμ / P(A = 1)`. -/
theorem att_eq_setIntegral_div [IsFiniteMeasure μ] (hpos : μ (A ⁻¹' {true}) ≠ 0) :
    att μ A Y = (∫ ω in A ⁻¹' {true}, indivEffect Y ω ∂μ) / μ.real (A ⁻¹' {true}) := by
  have hne : μ.real (A ⁻¹' {true}) ≠ 0 :=
    (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hpos
  rw [setIntegral_eq_measureReal_mul_condMeanArm, mul_div_cancel_left₀ _ hne, att]

/-- With a control arm of positive probability, the ATC is the mean of the individual effect
over the control units. -/
theorem atc_eq_setIntegral_div [IsFiniteMeasure μ] (hpos : μ (A ⁻¹' {false}) ≠ 0) :
    atc μ A Y = (∫ ω in A ⁻¹' {false}, indivEffect Y ω ∂μ) / μ.real (A ⁻¹' {false}) := by
  have hne : μ.real (A ⁻¹' {false}) ≠ 0 :=
    (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hpos
  rw [setIntegral_eq_measureReal_mul_condMeanArm, mul_div_cancel_left₀ _ hne, atc]

omit [MeasurableSpace Ω] in
theorem preimage_false_eq_compl (A : Ω → Bool) : A ⁻¹' {false} = (A ⁻¹' {true})ᶜ := by
  ext ω; simp

/-- **Decomposition of the average effect over the arms.** Under a probability measure,
`ATE = P(A = 1) ATT + P(A = 0) ATC` for a measurable treatment and an integrable individual
effect. -/
theorem ate_eq_att_add_atc [IsProbabilityMeasure μ] (hA : Measurable A)
    (hint : Integrable (indivEffect Y) μ) :
    ate μ Y = μ.real (A ⁻¹' {true}) * att μ A Y + μ.real (A ⁻¹' {false}) * atc μ A Y := by
  rw [att, atc, ← setIntegral_eq_measureReal_mul_condMeanArm,
    ← setIntegral_eq_measureReal_mul_condMeanArm, preimage_false_eq_compl,
    integral_add_compl (hA (measurableSet_singleton true)) hint, ate]

/-- The arm probabilities of a probability measure add to one. -/
theorem measureReal_false_eq_one_sub [IsProbabilityMeasure μ] (hA : Measurable A) :
    μ.real (A ⁻¹' {false}) = 1 - μ.real (A ⁻¹' {true}) := by
  rw [preimage_false_eq_compl, probReal_compl_eq_one_sub (hA (measurableSet_singleton true))]

/-- The ATT is the difference of the arm means of the two potential outcomes among the
treated. -/
theorem att_eq_sub [IsFiniteMeasure μ] (h1 : Integrable (Y true) μ)
    (h0 : Integrable (Y false) μ) :
    att μ A Y = condMeanArm μ A true (Y true) - condMeanArm μ A true (Y false) :=
  condMeanArm_sub h1 h0 true

/-- **Selection bias decomposition** (Holland 1986). For a measurable treatment and integrable
potential outcomes, the naive contrast of observed means is the ATT plus the selection bias,
the difference `E[Y(0) | A = 1] - E[Y(0) | A = 0]` in untreated outcomes between the treated and
the controls. -/
theorem naiveContrast_eq_att_add [IsFiniteMeasure μ] (hA : Measurable A)
    (h1 : Integrable (Y true) μ) (h0 : Integrable (Y false) μ) :
    naiveContrast μ A Y = att μ A Y +
      (condMeanArm μ A true (Y false) - condMeanArm μ A false (Y false)) := by
  rw [naiveContrast, condMeanArm_obsOutcome hA, condMeanArm_obsOutcome hA, att_eq_sub h1 h0]
  ring

/-! ### The individual effect is not identified -/

/-- The potential outcomes that keep the factual outcome and add one to the counterfactual
one. -/
def shiftCounterfactual (A : Ω → Bool) (Y : Bool → Ω → ℝ) : Bool → Ω → ℝ :=
  fun a ω => if A ω = a then Y a ω else Y a ω + 1

omit [MeasurableSpace Ω] in
theorem obsOutcome_shiftCounterfactual (A : Ω → Bool) (Y : Bool → Ω → ℝ) :
    obsOutcome A (shiftCounterfactual A Y) = obsOutcome A Y := by
  funext ω; simp [obsOutcome, shiftCounterfactual]

omit [MeasurableSpace Ω] in
theorem indivEffect_shiftCounterfactual (A : Ω → Bool) (Y : Bool → Ω → ℝ) (ω : Ω) :
    indivEffect (shiftCounterfactual A Y) ω =
      indivEffect Y ω + (if A ω = true then -1 else 1) := by
  cases h : A ω <;> simp [indivEffect, shiftCounterfactual, h] <;> ring

/-- **The individual effect is not a function of the observed data.** For every treatment `A`
and potential outcomes `Y` there are potential outcomes `Y'`, measurable when `A` and `Y` are,
with the same observed outcome as `Y` (so that, with the same measure, covariates and
treatment, the observed data and their law coincide) and an individual effect that differs from
that of `Y` at every unit. The construction keeps the factual outcome and shifts the
counterfactual one by one. -/
theorem exists_indivEffect_ne_of_obsOutcome_eq (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) :
    ∃ Y' : Bool → Ω → ℝ, (∀ a, Measurable (Y' a)) ∧ obsOutcome A Y' = obsOutcome A Y ∧
      ∀ ω, indivEffect Y' ω ≠ indivEffect Y ω := by
  refine ⟨shiftCounterfactual A Y, fun a => ?_, obsOutcome_shiftCounterfactual A Y,
    fun ω => ?_⟩
  · have hs : MeasurableSet {ω | A ω = a} := hA (measurableSet_singleton a)
    exact Measurable.ite hs (hY a) ((hY a).add_const 1)
  · rw [indivEffect_shiftCounterfactual]
    split_ifs <;> norm_num

/-- **A concrete pair of models with the same observed data and different individual
effects.** On one unit, treated, with `Y(1) = 1`: the first model has `Y(0) = 0`, the second
`Y(0) = 1`. The observed outcomes agree (both are `1`) and the individual effects are `1` and
`0`. -/
theorem indivEffect_not_function_of_obsOutcome :
    ∃ (A : Unit → Bool) (Y Y' : Bool → Unit → ℝ),
      obsOutcome A Y = obsOutcome A Y' ∧ indivEffect Y () ≠ indivEffect Y' () :=
  ⟨fun _ => true, fun a _ => if a then 1 else 0, fun _ _ => 1, rfl, by norm_num [indivEffect]⟩

end PointTreatment

end CausalInference
