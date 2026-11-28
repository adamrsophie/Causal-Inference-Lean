/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Assumptions
public import Mathlib.Probability.ConditionalExpectation

/-!
# Point treatment: a randomized trial is ignorable with a constant propensity score

In a randomized trial the treatment is assigned independently of the units: `A` is independent of
the covariates and of the pair of potential outcomes, `A ⫫ (W, (Y(0), Y(1)))`. Then the
treatment carries no information on anything measurable for `(W, Y(0), Y(1))`: its conditional
probability given `W` and given `(W, Y(0), Y(1))` is the constant `p = P(A = 1)`. So
ignorability holds given every covariate `W`, the constant `p` is the propensity score, and when
`0 < p < 1` strict positivity holds with `ε = min p (1 - p)`.

## Main results

* `condExp_respInd_of_indepFun`: `E[1{A} | V] = P(A = 1)` when `A ⫫ V`.
* `isPropensityScore_const_of_indepFun`: under `A ⫫ W` the constant `P(A = 1)` is the propensity
  score given `W`.
* `indicatorIgnorable_of_indepFun`, `ignorable_of_indepFun`: under `A ⫫ (W, (Y(0), Y(1)))` the
  indicator form and the full form of ignorability given `W` hold.
* `strictOverlap_const`: a constant score `p` with `0 < p < 1` satisfies strict positivity with
  `ε = min p (1 - p)`.

## References

* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70 (1983).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ}

/-- The mean of the treatment indicator is the probability of the treated arm. -/
theorem integral_respInd (hA : Measurable A) : ∫ ω, respInd A ω ∂μ = μ.real (A ⁻¹' {true}) :=
  integral_indicator_one (hA (measurableSet_singleton true))

/-- **The treatment probability given an independent variable is constant**: if `A ⫫ V`, then
`E[1{A} | V] = P(A = 1)` almost surely. -/
theorem condExp_respInd_of_indepFun [IsFiniteMeasure μ] {β : Type*} [MeasurableSpace β]
    {V : Ω → β} (hA : Measurable A) (hV : Measurable V) (hind : IndepFun A V μ) :
    μ[respInd A | MeasurableSpace.comap V inferInstance] =ᵐ[μ]
      fun _ => μ.real (A ⁻¹' {true}) := by
  have hsm : StronglyMeasurable[MeasurableSpace.comap A inferInstance] (respInd A) := by
    have h : respInd A = (fun b : Bool => if b = true then (1 : ℝ) else 0) ∘ A :=
      funext fun ω => respInd_apply A ω
    rw [h]
    exact (Measurable.of_discrete.comp (comap_measurable A)).stronglyMeasurable
  refine (condExp_indep_eq hA.comap_le hV.comap_le hsm hind).trans
    (Filter.Eventually.of_forall fun _ => ?_)
  exact integral_respInd hA

/-- **Randomization gives a constant propensity score.** If `A ⫫ W`, the constant
`P(A = 1)` is the propensity score given `W`. -/
theorem isPropensityScore_const_of_indepFun [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hind : IndepFun A W μ) :
    IsPropensityScore μ A W (fun _ => μ.real (A ⁻¹' {true})) :=
  ⟨measurable_const, condExp_respInd_of_indepFun hA hW hind⟩

/-- **A randomized trial is ignorable given any covariate**, indicator form: if
`A ⫫ (W, (Y(0), Y(1)))`, then `E[1{A} | W, (Y(0), Y(1))] = E[1{A} | W]`, both being the
constant `P(A = 1)`. -/
theorem indicatorIgnorable_of_indepFun [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hind : IndepFun A (fun ω => (W ω, potentialPair Y ω)) μ) :
    IndicatorIgnorable μ A W Y :=
  (condExp_respInd_of_indepFun hA (hW.prodMk (measurable_potentialPair hY)) hind).trans
    (condExp_respInd_of_indepFun hA hW (hind.comp measurable_id measurable_fst)).symm

/-- **A randomized trial is ignorable given any covariate**, full form: if
`A ⫫ (W, (Y(0), Y(1)))`, then `A ⫫ (Y(0), Y(1)) | W`. -/
theorem ignorable_of_indepFun [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hind : IndepFun A (fun ω => (W ω, potentialPair Y ω)) μ) : Ignorable μ A hW Y :=
  (ignorable_iff_indicatorIgnorable hW hA hY).2 (indicatorIgnorable_of_indepFun hW hA hY hind)

omit [MeasurableSpace 𝒲] in
/-- A constant score `p` with `0 < p < 1` satisfies strict positivity with
`ε = min p (1 - p)`. -/
theorem strictOverlap_const {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    StrictOverlap (fun _ : 𝒲 => p) (min p (1 - p)) :=
  ⟨lt_min h0 (by linarith), fun _ => ⟨min_le_left _ _, by linarith [min_le_right p (1 - p)]⟩⟩

end PointTreatment

end CausalInference
