/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Identification

/-!
# Point treatment: outcome regression (g-computation)

The g-computation functional of a fitted regression `m̂ : Bool → 𝒲 → ℝ` averages its value at
the arm `a` over the conditioning variable, `E[m̂(a, W)]`. When `m̂(A, W)` is a version of the
observed regression `E[Y | W, A]` (a correct regression), ignorability and positivity make it
equal to `E[Y(a)]`; under a wrong regression its bias is `E[m̂(a, W) - m(a, W)]`.

The conditional average effect `E[Y(1) - Y(0) | W]` averages to the average effect, and under
ignorability and positivity the observed contrast `m(1, W) - m(0, W)` is a version of it.

## Main definitions

* `orArmMean μ W m a`: the g-computation functional `E[m(a, W)]`.
* `orAte μ W m`: `E[m(1, W)] - E[m(0, W)]`.
* `cate μ W Y`: the conditional average effect, a version of `E[Y(1) - Y(0) | W]`.

## Main results

* `ate_eq_integral_cate`: the average effect is the mean of the conditional average effect.
* `IsOutcomeRegression.sub_ae_eq_cate`: the observed contrast is a version of the conditional
  average effect (mean ignorability of both arms and positivity).
* `orArmMean_eq_armMean`, `orAte_eq_ate`, and the full form versions
  `Ignorable.orArmMean_eq_armMean`, `Ignorable.orAte_eq_ate`: g-computation with a correct
  regression.
* `orArmMean_sub_armMean`, `orAte_sub_ate`: the bias under a wrong regression.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}

/-- The g-computation functional `E[m(a, W)]` of a regression `m` at the arm `a`. -/
noncomputable def orArmMean (μ : Measure Ω) (W : Ω → 𝒲) (m : Bool → 𝒲 → ℝ) (a : Bool) : ℝ :=
  ∫ ω, m a (W ω) ∂μ

/-- The g-computation form of the average effect, `E[m(1, W)] - E[m(0, W)]`. -/
noncomputable def orAte (μ : Measure Ω) (W : Ω → 𝒲) (m : Bool → 𝒲 → ℝ) : ℝ :=
  orArmMean μ W m true - orArmMean μ W m false

/-- The conditional average effect: the conditional expectation `E[Y(1) - Y(0) | W]` (a random
variable measurable for the σ-algebra of `W`). -/
noncomputable def cate (μ : Measure Ω) (W : Ω → 𝒲) (Y : Bool → Ω → ℝ) : Ω → ℝ :=
  μ[indivEffect Y | MeasurableSpace.comap W inferInstance]

/-- **The average effect is the mean of the conditional average effect**: `E[Y(1) - Y(0)] =
E[E[Y(1) - Y(0) | W]]`, for any measurable `W` and any finite measure. It is a statement about
means when `Y(1) - Y(0)` is integrable; otherwise both sides are `0` by convention (the
conditional expectation of a non integrable function is `0`). -/
theorem ate_eq_integral_cate [IsFiniteMeasure μ] (hW : Measurable W) :
    ate μ Y = ∫ ω, cate μ W Y ω ∂μ :=
  (integral_condExp hW.comap_le).symm

/-- The conditional average effect is the difference of the arm regressions,
`E[Y(1) - Y(0) | W] = E[Y(1) | W] - E[Y(0) | W]`. -/
theorem cate_ae_eq_sub (W : Ω → 𝒲) (hYi : ∀ a, Integrable (Y a) μ) :
    cate μ W Y =ᵐ[μ] μ[Y true | MeasurableSpace.comap W inferInstance] -
      μ[Y false | MeasurableSpace.comap W inferInstance] :=
  condExp_sub (hYi true) (hYi false) _

/-- **The observed contrast is the conditional average effect.** Under mean ignorability of both
arms and positivity `0 < e(W) < 1`, if `m(A, W)` is a version of `E[Y | W, A]` then
`m(1, W) - m(0, W)` is a version of `E[Y(1) - Y(0) | W]`. -/
theorem IsOutcomeRegression.sub_ae_eq_cate [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hYi : ∀ a, Integrable (Y a) μ)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hps : IsPropensityScore μ A W e)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) (hov : OverlapAE e (μ.map W)) :
    (fun ω => m true (W ω) - m false (W ω)) =ᵐ[μ] cate μ W Y := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  filter_upwards [hreg.ae_eq_condExp hW hA hYi hps true (hmi true) (hpos true),
    hreg.ae_eq_condExp hW hA hYi hps false (hmi false) (hpos false), cate_ae_eq_sub W hYi]
    with ω h1 h0 hc
  rw [h1, h0, hc]
  rfl

/-- **g-computation with a correct regression**, mean form: under mean ignorability and
positivity of the arm, `E[m(a, W)] = E[Y(a)]`. -/
theorem orArmMean_eq_armMean [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hmi : MeanIgnorable μ A W Y a)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) : orArmMean μ W m a = armMean μ Y a :=
  (armMean_eq_integral_regression hW hA hYi hreg hps a hmi hpos).symm

/-- **g-computation of the average effect with a correct regression**, mean form. -/
theorem orAte_eq_ate [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    (hov : OverlapAE e (μ.map W)) : orAte μ W m = ate μ Y := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  rw [orAte, orArmMean_eq_armMean hW hA hYi hreg hps true (hmi true) (hpos true),
    orArmMean_eq_armMean hW hA hYi hreg hps false (hmi false) (hpos false),
    ate_eq_armMean_sub (hYi true) (hYi false)]

/-- **g-computation with a correct regression under ignorability.** -/
theorem Ignorable.orArmMean_eq_armMean [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hign : Ignorable μ A hW Y)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hps : IsPropensityScore μ A W e)
    (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) : orArmMean μ W m a = armMean μ Y a :=
  PointTreatment.orArmMean_eq_armMean hW hA hYi hreg hps a
    (hign.meanIgnorable hW hA hY a (hYi a)) hpos

/-- **g-computation of the average effect with a correct regression under ignorability** and
positivity. -/
theorem Ignorable.orAte_eq_ate [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (hov : OverlapAE e (μ.map W)) : orAte μ W m = ate μ Y :=
  PointTreatment.orAte_eq_ate hW hA hYi hreg hps
    (fun a => hign.meanIgnorable hW hA hY a (hYi a)) hov

/-- **Bias of g-computation under a wrong regression.** If `m` is a correct regression and the
fitted `m̂(a, W)` is integrable, then `E[m̂(a, W)] - E[Y(a)] = E[m̂(a, W) - m(a, W)]` (mean
ignorability and positivity of the arm). -/
theorem orArmMean_sub_armMean [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hmi : MeanIgnorable μ A W Y a)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) {m' : Bool → 𝒲 → ℝ}
    (hm' : Integrable (fun ω => m' a (W ω)) μ) :
    orArmMean μ W m' a - armMean μ Y a = ∫ ω, (m' a (W ω) - m a (W ω)) ∂μ := by
  rw [← orArmMean_eq_armMean hW hA hYi hreg hps a hmi hpos, orArmMean, orArmMean,
    integral_sub hm' (integrable_regression hW hA hYi hreg hps a hmi hpos)]

/-- **Bias of the g-computation average effect under a wrong regression**:
`E[m̂(1, W) - m̂(0, W)] - E[Y(1) - Y(0)] = E[(m̂ - m)(1, W)] - E[(m̂ - m)(0, W)]`. -/
theorem orAte_sub_ate [IsFiniteMeasure μ] (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    (hov : OverlapAE e (μ.map W)) {m' : Bool → 𝒲 → ℝ}
    (hm' : ∀ a, Integrable (fun ω => m' a (W ω)) μ) :
    orAte μ W m' - ate μ Y = ∫ ω, (m' true (W ω) - m true (W ω)) ∂μ -
      ∫ ω, (m' false (W ω) - m false (W ω)) ∂μ := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  rw [ate_eq_armMean_sub (hYi true) (hYi false),
    ← orArmMean_sub_armMean hW hA hYi hreg hps true (hmi true) (hpos true) (hm' true),
    ← orArmMean_sub_armMean hW hA hYi hreg hps false (hmi false) (hpos false) (hm' false),
    orAte]
  ring

end PointTreatment

end CausalInference
