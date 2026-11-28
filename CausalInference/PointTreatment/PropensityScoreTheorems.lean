/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.BalancingScore
public import CausalInference.PointTreatment.Identification

/-!
# Identification through a balancing score

Under ignorability and positivity given the covariates `W`, the arm means and the average
treatment effect are identified by adjusting for any balancing score `b(W)` in place of `W`:
the g-formula with the regression of the outcome on `(b(W), A)`, and the weighting identity with
the propensity score `f(b(W))` on the scale of the score. In particular one may adjust for the
propensity score `e(W)` alone. Every hypothesis is stated at the level of the covariates; the
corresponding statements at the score are consequences (`BalancingScore`).

The statements in indicator form need no `StandardBorelSpace Ω`; they take the factorization
`E[1{A} | W] = f(b(W))` of the propensity score, which is the balancing property in regression
form (`isBalancingScore_iff_exists_comp`).

With `b = e` and `f = id` the weighting identity at the score has the same integrand as the one
at the covariates (`Ignorable.ate_eq_ipw`), so it is not restated.

## Main results

* `IndicatorIgnorable.armMean_eq_integral_regression_score`,
  `IndicatorIgnorable.ate_eq_integral_regression_score`: the g-formula with the regression on
  `(b(W), A)`.
* `IndicatorIgnorable.armMean_eq_ipw_score`, `IndicatorIgnorable.ate_eq_ipw_score`: the
  weighting identity with weights `f(b(W))` and `1 - f(b(W))`.
* `IsBalancingScore.ate_eq_integral_regression`: the g-formula given a balancing score under
  `A ⫫ (Y(0), Y(1)) | W`.
* `IsPropensityScore.ate_eq_integral_regression_score`: the g-formula with the regression on
  `(e(W), A)`.

## References

* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70 (1983).
* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986) (the g-formula).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 𝒷 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] [MeasurableSpace 𝒷]
  {μ : Measure Ω} {A : Ω → Bool} {W : Ω → 𝒲} {b : 𝒲 → 𝒷} {e : 𝒲 → ℝ} {f : 𝒷 → ℝ}
  {Y : Bool → Ω → ℝ} {m : Bool → 𝒷 → ℝ}

/-! ### Indicator form -/

/-- **The g-formula for an arm mean with a score.** Under the indicator form of ignorability
given `W`, a propensity score `e` with `e(W) = f(b(W))` almost surely, and positivity of the arm
`0 < P(A = a | W)` almost surely, the regression `m` of the outcome on `(b(W), A)` gives
`E[Y(a)] = E[m(a, b(W))]`. -/
theorem IndicatorIgnorable.armMean_eq_integral_regression_score [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hign : IndicatorIgnorable μ A W Y)
    (he : IsPropensityScore μ A W e) (hf : Measurable f)
    (hfe : ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω)))
    (hreg : IsOutcomeRegression μ A (fun ω => b (W ω)) (obsOutcome A Y) m) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) :
    armMean μ Y a = ∫ ω, m a (b (W ω)) ∂μ := by
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb f a (b (W ω)) := by
    filter_upwards [hpos, hfe] with ω h1 h2
    simpa [armProb, h2] using h1
  exact (hign.score hW hb hY hf (he.2.trans hfe)).armMean_eq_integral_regression
    (hb.comp hW) hA hY hYi hreg (he.isPropensityScore_comp hW hb hf hfe) a hpos'

/-- **The g-formula for the average effect with a score**: under the indicator form of
ignorability given `W`, a propensity score with `e(W) = f(b(W))` and `0 < e(W) < 1` almost
surely, `E[Y(1) - Y(0)] = E[m(1, b(W)) - m(0, b(W))]` for the regression `m` of the outcome on
`(b(W), A)`. -/
theorem IndicatorIgnorable.ate_eq_integral_regression_score [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hign : IndicatorIgnorable μ A W Y)
    (he : IsPropensityScore μ A W e) (hf : Measurable f)
    (hfe : ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω)))
    (hreg : IsOutcomeRegression μ A (fun ω => b (W ω)) (obsOutcome A Y) m)
    (hov : OverlapAE e (μ.map W)) :
    ate μ Y = ∫ ω, (m true (b (W ω)) - m false (b (W ω))) ∂μ := by
  have hbW : Measurable fun ω => b (W ω) := hb.comp hW
  have hign' := hign.score hW hb hY hf (he.2.trans hfe)
  exact PointTreatment.ate_eq_integral_regression hbW hA hYi hreg
    (he.isPropensityScore_comp hW hb hf hfe)
    (fun a => hign'.meanIgnorable hbW hA hY a (hYi a)) (hov.score hW hb he.1 hf hfe)

/-- **The weighting identity for an arm mean with a score**: under the indicator form of
ignorability given `W`, a propensity score with `e(W) = f(b(W))` almost surely, positivity of the
arm and integrability of `Y(a)`, `E[Y(a)] = E[1{A = a} Y / P(A = a | b(W))]` with
`P(A = 1 | b(W)) = f(b(W))`. -/
theorem IndicatorIgnorable.armMean_eq_ipw_score [IsFiniteMeasure μ] (hW : Measurable W)
    (hb : Measurable b) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hign : IndicatorIgnorable μ A W Y) (he : IsPropensityScore μ A W e) (hf : Measurable f)
    (hfe : ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω))) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) (hYi : Integrable (Y a) μ) :
    armMean μ Y a =
      ∫ ω, respInd (arm A a) ω * obsOutcome A Y ω / armProb f a (b (W ω)) ∂μ := by
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb f a (b (W ω)) := by
    filter_upwards [hpos, hfe] with ω h1 h2
    simpa [armProb, h2] using h1
  exact (hign.score hW hb hY hf (he.2.trans hfe)).armMean_eq_ipw (hb.comp hW) hA hY
    (he.isPropensityScore_comp hW hb hf hfe) a hpos' hYi

/-- **The weighting identity for the average effect with a score**: under the indicator form of
ignorability given `W`, a propensity score with `e(W) = f(b(W))` and `0 < e(W) < 1` almost
surely, `E[Y(1) - Y(0)] = E[1{A = 1} Y / f(b(W)) - 1{A = 0} Y / (1 - f(b(W)))]`. -/
theorem IndicatorIgnorable.ate_eq_ipw_score [IsFiniteMeasure μ] (hW : Measurable W)
    (hb : Measurable b) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hign : IndicatorIgnorable μ A W Y)
    (he : IsPropensityScore μ A W e) (hf : Measurable f)
    (hfe : ∀ᵐ ω ∂μ, e (W ω) = f (b (W ω))) (hov : OverlapAE e (μ.map W)) :
    ate μ Y = ∫ ω, (respInd (arm A true) ω * obsOutcome A Y ω / armProb f true (b (W ω)) -
      respInd (arm A false) ω * obsOutcome A Y ω / armProb f false (b (W ω))) ∂μ := by
  have hbW : Measurable fun ω => b (W ω) := hb.comp hW
  have hii := hign.score hW hb hY hf (he.2.trans hfe)
  have hps := he.isPropensityScore_comp hW hb hf hfe
  have hpos := armProb_pos_of_ae ((hov.score hW hb he.1 hf hfe).ae_comp hbW.aemeasurable)
  rw [ate_eq_armMean_sub (hYi true) (hYi false),
    hii.armMean_eq_ipw hbW hA hY hps true (hpos true) (hYi true),
    hii.armMean_eq_ipw hbW hA hY hps false (hpos false) (hYi false),
    integral_sub (hii.integrable_ipw hbW hA hY hps true (hpos true) (hYi true))
      (hii.integrable_ipw hbW hA hY hps false (hpos false) (hYi false))]

/-! ### Full form -/

/-- **The g-formula given a balancing score** (Rosenbaum and Rubin 1983): under
`A ⫫ (Y(0), Y(1)) | W` and `0 < e(W) < 1` almost surely, for every balancing score `b` and the
regression `m` of the outcome on `(b(W), A)`, `E[Y(1) - Y(0)] = E[m(1, b(W)) - m(0, b(W))]`. -/
theorem IsBalancingScore.ate_eq_integral_regression [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hb : Measurable b) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hbal : IsBalancingScore μ A hW hb)
    (hign : Ignorable μ A hW Y) (he : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A (fun ω => b (W ω)) (obsOutcome A Y) m)
    (hov : OverlapAE e (μ.map W)) :
    ate μ Y = ∫ ω, (m true (b (W ω)) - m false (b (W ω))) ∂μ := by
  obtain ⟨f, hf, hfe⟩ := (he.isBalancingScore_iff hW hb hA).1 hbal
  exact ((ignorable_iff_indicatorIgnorable hW hA hY).1 hign).ate_eq_integral_regression_score
    hW hb hA hY hYi he hf hfe hreg hov

/-- **The g-formula with the propensity score** (Rosenbaum and Rubin 1983): under
`A ⫫ (Y(0), Y(1)) | W` and `0 < e(W) < 1` almost surely, for the regression `m` of the outcome
on `(e(W), A)`, `E[Y(1) - Y(0)] = E[m(1, e(W)) - m(0, e(W))]`. -/
theorem IsPropensityScore.ate_eq_integral_regression_score [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] {m : Bool → ℝ → ℝ} (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ) (hign : Ignorable μ A hW Y)
    (he : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A (fun ω => e (W ω)) (obsOutcome A Y) m)
    (hov : OverlapAE e (μ.map W)) :
    ate μ Y = ∫ ω, (m true (e (W ω)) - m false (e (W ω))) ∂μ :=
  ((ignorable_iff_indicatorIgnorable hW hA hY).1 hign).ate_eq_integral_regression_score
    hW he.1 hA hY hYi he measurable_id (Filter.Eventually.of_forall fun _ => rfl) hreg hov

end PointTreatment

end CausalInference
