/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Weighting

/-!
# Point treatment: stabilized weights

The stabilized weight multiplies the inverse probability weight of each arm by the marginal
probability of that arm (Robins, Hernán and Brumback 2000):
`sw = P(A = 1) 1{A = 1} / e(W) + P(A = 0) 1{A = 0} / (1 - e(W))`. At the true propensity score
the stabilized weights have mean one, their mean over the arm `a` is `P(A = a)`, and the weighted
arm mean with stabilized weights (the ratio of `E[1{A = a} sw Y]` to `E[1{A = a} sw]`) is
`E[Y(a)]` under ignorability. The unstabilized weights `ipwWeight` have mean one in each arm
(`ipwWeight_integral`); their Hájek form is `Ignorable.hajekArmMean_eq`.

## Main definitions

* `stabilizedWeight μ A W e`: the stabilized weight.

## Main results

* `respInd_arm_mul_stabilizedWeight`: on the arm `a` the stabilized weight is
  `P(A = a) / π_a(W)`.
* `integral_respInd_arm_mul_stabilizedWeight`: `E[1{A = a} sw] = P(A = a)`.
* `integral_stabilizedWeight`: `E[sw] = 1`.
* `IndicatorIgnorable.stabilized_armMean_eq`: `E[1{A = a} sw Y] / E[1{A = a} sw] = E[Y(a)]`.

## References

* J. M. Robins, M. A. Hernán and B. Brumback, *Marginal structural models and causal inference
  in epidemiology*, Epidemiology 11 (2000).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ}

/-- The **stabilized weight** `P(A = 1) 1{A = 1} / e(W) + P(A = 0) 1{A = 0} / (1 - e(W))`. -/
noncomputable def stabilizedWeight (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲) (e : 𝒲 → ℝ) :
    Ω → ℝ :=
  fun ω => μ.real (A ⁻¹' {true}) * ipwWeight A W e true ω +
    μ.real (A ⁻¹' {false}) * ipwWeight A W e false ω

omit [MeasurableSpace 𝒲] in
/-- On the arm `a` the stabilized weight is `P(A = a) / π_a(W)`:
`1{A = a} sw = P(A = a) 1{A = a} / π_a(W)`. -/
theorem respInd_arm_mul_stabilizedWeight (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲)
    (e : 𝒲 → ℝ) (a : Bool) (ω : Ω) :
    respInd (arm A a) ω * stabilizedWeight μ A W e ω =
      μ.real (A ⁻¹' {a}) * ipwWeight A W e a ω := by
  simp only [stabilizedWeight, ipwWeight, respInd_arm_apply]
  cases a <;> cases A ω <;> simp

/-- **The stabilized weights of an arm have mean the arm probability**: at the true propensity
score, with positivity of the arm, `E[1{A = a} sw] = P(A = a)`. -/
theorem integral_respInd_arm_mul_stabilizedWeight [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) :
    ∫ ω, respInd (arm A a) ω * stabilizedWeight μ A W e ω ∂μ = μ.real (A ⁻¹' {a}) := by
  simp_rw [respInd_arm_mul_stabilizedWeight]
  rw [integral_const_mul, (ipwWeight_integral hW hA hps a hpos).2, mul_one]

/-- **The stabilized weights have mean one** at the true propensity score under positivity
`0 < e(W) < 1` almost surely: `E[sw] = P(A = 1) + P(A = 0) = 1`. -/
theorem integral_stabilizedWeight [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (hov : OverlapAE e (μ.map W)) :
    ∫ ω, stabilizedWeight μ A W e ω ∂μ = 1 := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  obtain ⟨hi1, e1⟩ := ipwWeight_integral hW hA hps true (hpos true)
  obtain ⟨hi0, e0⟩ := ipwWeight_integral hW hA hps false (hpos false)
  simp only [stabilizedWeight]
  rw [integral_add (hi1.const_mul _) (hi0.const_mul _), integral_const_mul,
    integral_const_mul, e1, e0, mul_one, mul_one, measureReal_false_eq_one_sub hA]
  ring

/-- **The stabilized weighted arm mean.** Under the indicator form of ignorability, positivity
of the arm, an arm of positive probability and integrable `Y(a)`,
`E[1{A = a} sw Y] / E[1{A = a} sw] = E[Y(a)]`. -/
theorem IndicatorIgnorable.stabilized_armMean_eq [IsProbabilityMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hYi : Integrable (Y a) μ) (ha : μ (A ⁻¹' {a}) ≠ 0) :
    (∫ ω, respInd (arm A a) ω * stabilizedWeight μ A W e ω * obsOutcome A Y ω ∂μ) /
        ∫ ω, respInd (arm A a) ω * stabilizedWeight μ A W e ω ∂μ = armMean μ Y a := by
  have hne : μ.real (A ⁻¹' {a}) ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 ha
  have hnum : (fun ω => respInd (arm A a) ω * stabilizedWeight μ A W e ω * obsOutcome A Y ω) =
      fun ω => μ.real (A ⁻¹' {a}) *
        (respInd (arm A a) ω * obsOutcome A Y ω / armProb e a (W ω)) := by
    funext ω
    rw [respInd_arm_mul_stabilizedWeight, ipwWeight]
    ring
  rw [integral_respInd_arm_mul_stabilizedWeight hW hA hps a hpos, hnum, integral_const_mul,
    ← hign.armMean_eq_ipw hW hA hY hps a hpos hYi, mul_div_cancel_left₀ _ hne]

end PointTreatment

end CausalInference
