/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Assumptions
public import Mathlib.Probability.Independence.Integration

/-!
# Point treatment: the naive contrast under marginal independence

If the treatment is independent of the pair of potential outcomes, `A ⫫ (Y(0), Y(1))` (as in a
completely randomized experiment), then within each arm of positive probability the potential
outcomes keep their population law. The mean of any function of `(Y(0), Y(1))` in an arm is its
population mean, so the naive contrast of observed means, the average effect in the treated, the
average effect in the controls and the average effect coincide. The selection bias term of
`naiveContrast_eq_att_add` vanishes.

This is a population identity about one law; it uses Mathlib's `IndepFun` and needs no standard
Borel structure. `ate_eq_naiveContrast_of_ignorable` reaches the equality of the naive contrast
and the average effect from ignorability given a constant covariate.

## Main results

* `condMeanArm_comp_potentialPair_of_indepFun`: `E[f(Y(0), Y(1)) | A = b] = E[f(Y(0), Y(1))]`.
* `naiveContrast_eq_att_of_indepFun`, `att_eq_ate_of_indepFun`, `atc_eq_ate_of_indepFun`: the
  naive contrast is the effect in the treated, and the effects in the treated, in the controls
  and in the population agree.

## References

* P. W. Holland, *Statistics and causal inference*, Journal of the American Statistical
  Association 81 (1986).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ}

/-- **Arm means under marginal independence.** If `A ⫫ (Y(0), Y(1))`, `P(A = b) > 0` and
`f(Y(0), Y(1))` is integrable for a measurable `f`, then `f(Y(0), Y(1))` is integrable in the
arm `{A = b}` and its mean there is its population mean. The integral over the arm is
`E[1{A = b} f(Y(0), Y(1))]`, which factors as `P(A = b) E[f(Y(0), Y(1))]`. -/
theorem condMeanArm_comp_potentialPair_of_indepFun (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hind : IndepFun A (potentialPair Y) μ) {f : ℝ × ℝ → ℝ}
    (hf : Measurable f) (hfi : Integrable (fun ω => f (potentialPair Y ω)) μ) (b : Bool)
    (hb : μ (A ⁻¹' {b}) ≠ 0) :
    Integrable (fun ω => f (potentialPair Y ω)) (μ[|A ⁻¹' {b}]) ∧
      condMeanArm μ A b (fun ω => f (potentialPair Y ω)) = ∫ ω, f (potentialPair Y ω) ∂μ := by
  refine ⟨integrable_cond hfi _, ?_⟩
  have hs : MeasurableSet (A ⁻¹' {b}) := hA (measurableSet_singleton b)
  have hg : Measurable fun c : Bool => if c = b then (1 : ℝ) else 0 := Measurable.of_discrete
  have hind' := hind.comp hg hf
  have hmul := hind'.integral_mul_eq_mul_integral (hg.comp hA).aestronglyMeasurable
    (hf.comp (measurable_potentialPair hY)).aestronglyMeasurable
  have hind1 : (fun c : Bool => if c = b then (1 : ℝ) else 0) ∘ A = (A ⁻¹' {b}).indicator 1 := by
    funext ω
    by_cases h : A ω = b <;> simp [Set.indicator, h]
  have hset : ∫ ω in A ⁻¹' {b}, f (potentialPair Y ω) ∂μ =
      ∫ ω, (((fun c : Bool => if c = b then (1 : ℝ) else 0) ∘ A) *
        (f ∘ potentialPair Y)) ω ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    funext ω
    by_cases h : A ω = b <;> simp [Set.indicator, h]
  have hne : μ.real (A ⁻¹' {b}) ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hb
  have h := setIntegral_eq_measureReal_mul_condMeanArm (μ := μ) (A := A) b
    (fun ω => f (potentialPair Y ω))
  rw [hset, hmul, hind1, integral_indicator_one hs] at h
  exact (mul_left_cancel₀ hne h).symm

/-- **The effect in the treated is the average effect** under marginal independence
`A ⫫ (Y(0), Y(1))`, with integrable potential outcomes and a treated arm of positive
probability. -/
theorem att_eq_ate_of_indepFun (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hind : IndepFun A (potentialPair Y) μ)
    (h1 : μ (A ⁻¹' {true}) ≠ 0) : att μ A Y = ate μ Y :=
  (condMeanArm_comp_potentialPair_of_indepFun hA hY hind (f := fun p => p.2 - p.1)
    (measurable_snd.sub measurable_fst) ((hYi true).sub (hYi false)) true h1).2

/-- **The effect in the controls is the average effect** under marginal independence, with
integrable potential outcomes and a control arm of positive probability. -/
theorem atc_eq_ate_of_indepFun (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hind : IndepFun A (potentialPair Y) μ)
    (h0 : μ (A ⁻¹' {false}) ≠ 0) : atc μ A Y = ate μ Y :=
  (condMeanArm_comp_potentialPair_of_indepFun hA hY hind (f := fun p => p.2 - p.1)
    (measurable_snd.sub measurable_fst) ((hYi true).sub (hYi false)) false h0).2

/-- **The naive contrast is the effect in the treated and the average effect** under marginal
independence `A ⫫ (Y(0), Y(1))`, with both arms of positive probability and integrable potential
outcomes: `E[Y | A = 1] - E[Y | A = 0] = ATT = ATE`. The arm means of the observed outcome are
the arm means of the potential outcomes (consistency), which are the population means. -/
theorem naiveContrast_eq_att_of_indepFun (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hind : IndepFun A (potentialPair Y) μ)
    (h1 : μ (A ⁻¹' {true}) ≠ 0) (h0 : μ (A ⁻¹' {false}) ≠ 0) :
    naiveContrast μ A Y = att μ A Y ∧ att μ A Y = ate μ Y := by
  have e1 : condMeanArm μ A true (Y true) = armMean μ Y true :=
    (condMeanArm_comp_potentialPair_of_indepFun hA hY hind (f := Prod.snd) measurable_snd
      (hYi true) true h1).2
  have e0 : condMeanArm μ A false (Y false) = armMean μ Y false :=
    (condMeanArm_comp_potentialPair_of_indepFun hA hY hind (f := Prod.fst) measurable_fst
      (hYi false) false h0).2
  have hatt := att_eq_ate_of_indepFun hA hY hYi hind h1
  refine ⟨?_, hatt⟩
  rw [hatt, naiveContrast, condMeanArm_obsOutcome hA, condMeanArm_obsOutcome hA, e1, e0,
    ate_eq_armMean_sub (hYi true) (hYi false)]

end PointTreatment

end CausalInference
