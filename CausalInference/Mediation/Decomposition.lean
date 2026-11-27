/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Mediation.Basic

/-!
# Mediation: decompositions of the total effect

Pure algebra on expectations of potential outcomes, with integrability as the only analytic
assumption. No identification assumption appears here. Every theorem assumes a probability
measure, under which the effects are means of potential outcomes.

## Main results

* `MediationModel.te_eq_nde_false_add_nie_true`: `TE = NDE(0) + NIE(1)`, assuming integrability
  of the two component contrasts.
* `MediationModel.te_eq_nde_true_add_nie_false`: `TE = NDE(1) + NIE(0)`, likewise.
* `MediationModel.nde_eq_cde_of_no_interaction`: without treatment and mediator interaction at
  the individual level, every natural direct effect equals every controlled direct effect.
* `MediationModel.nde_true_eq_nde_false_of_no_interaction`: under the same assumption the two
  natural direct effects coincide.
* `MediationModel.interventionalTotal_eq_add`: the interventional (randomized analogue) total
  effect is the sum of the interventional direct and indirect effects.

Sources: J. Pearl (2001), Direct and indirect effects; T. J. VanderWeele (2015), Explanation in
Causal Inference. The interventional effects follow VanderWeele, Vansteelandt and Robins (2014),
Effect decomposition in the presence of an exposure-induced mediator-outcome confounder.
-/

@[expose] public section

namespace CausalInference

namespace Mediation

open MeasureTheory ProbabilityTheory

namespace MediationModel

variable {Ω 𝓜 : Type*} [MeasurableSpace Ω] (P : MediationModel Ω 𝓜) {μ : Measure Ω}

/-- The total effect is the pure natural direct effect plus the total natural indirect effect:
`TE = NDE(0) + NIE(1)`, assuming the two component contrasts `Y 1 (M 0) - Y 0 (M 0)` and
`Y 1 (M 1) - Y 1 (M 0)` are integrable. The total effect contrast is their pointwise sum. -/
theorem te_eq_nde_false_add_nie_true [IsProbabilityMeasure μ]
    (hd : Integrable (fun ω => P.nested true false ω - P.nested false false ω) μ)
    (hi : Integrable (fun ω => P.nested true true ω - P.nested true false ω) μ) :
    P.te μ = P.nde μ false + P.nie μ true := by
  rw [te, nde, nie, ← integral_add hd hi]
  congr 1
  funext ω
  ring

/-- The total effect is the total natural direct effect plus the pure natural indirect effect:
`TE = NDE(1) + NIE(0)`, assuming the two component contrasts `Y 1 (M 1) - Y 0 (M 1)` and
`Y 0 (M 1) - Y 0 (M 0)` are integrable. The total effect contrast is their pointwise sum. -/
theorem te_eq_nde_true_add_nie_false [IsProbabilityMeasure μ]
    (hd : Integrable (fun ω => P.nested true true ω - P.nested false true ω) μ)
    (hi : Integrable (fun ω => P.nested false true ω - P.nested false false ω) μ) :
    P.te μ = P.nde μ true + P.nie μ false := by
  rw [te, nde, nie, ← integral_add hd hi]
  congr 1
  funext ω
  ring

/-- `TE = NDE(0) + NIE(1)` when `Y 1 (M 1)`, `Y 1 (M 0)` and `Y 0 (M 0)` are integrable. A
corollary of `te_eq_nde_false_add_nie_true`. -/
theorem te_eq_nde_false_add_nie_true_of_integrable_nested [IsProbabilityMeasure μ]
    (h11 : Integrable (P.nested true true) μ) (h10 : Integrable (P.nested true false) μ)
    (h00 : Integrable (P.nested false false) μ) :
    P.te μ = P.nde μ false + P.nie μ true :=
  P.te_eq_nde_false_add_nie_true (h10.sub h00) (h11.sub h10)

/-- `TE = NDE(1) + NIE(0)` when `Y 1 (M 1)`, `Y 0 (M 1)` and `Y 0 (M 0)` are integrable. A
corollary of `te_eq_nde_true_add_nie_false`. -/
theorem te_eq_nde_true_add_nie_false_of_integrable_nested [IsProbabilityMeasure μ]
    (h11 : Integrable (P.nested true true) μ) (h01 : Integrable (P.nested false true) μ)
    (h00 : Integrable (P.nested false false) μ) :
    P.te μ = P.nde μ true + P.nie μ false :=
  P.te_eq_nde_true_add_nie_false (h11.sub h01) (h01.sub h00)

/-- No treatment and mediator interaction: for almost every unit the individual controlled
direct effect `Y 1 m - Y 0 m` does not depend on the mediator value `m`. -/
def NoInteraction (μ : Measure Ω) : Prop :=
  ∀ᵐ ω ∂μ, ∀ m m' : 𝓜, P.Y true m ω - P.Y false m ω = P.Y true m' ω - P.Y false m' ω

/-- Without treatment and mediator interaction, the natural direct effect contrast
`Y 1 (M a') - Y 0 (M a')` is integrable as soon as one controlled contrast `Y 1 m - Y 0 m` is:
the two agree almost everywhere. -/
theorem integrable_nde_contrast_of_no_interaction (h : P.NoInteraction μ) (a' : Bool) (m : 𝓜)
    (hint : Integrable (fun ω => P.Y true m ω - P.Y false m ω) μ) :
    Integrable (fun ω => P.nested true a' ω - P.nested false a' ω) μ := by
  refine hint.congr ?_
  filter_upwards [h] with ω hω
  exact hω m (P.M a' ω)

/-- Without treatment and mediator interaction, the natural direct effect `NDE(a')` equals the
controlled direct effect `CDE(m)` for every `a'` and every `m`. The two integrands agree almost
everywhere, so the equality itself needs no analytic hypothesis; the integrability `_hint` of
the controlled contrast `Y 1 m - Y 0 m` is required so that both sides are finite means rather
than the value `0` that the Bochner integral assigns to a non-integrable function (the natural
direct effect contrast is then integrable too, by
`integrable_nde_contrast_of_no_interaction`). -/
theorem nde_eq_cde_of_no_interaction [IsProbabilityMeasure μ] (h : P.NoInteraction μ) (a' : Bool)
    (m : 𝓜) (_hint : Integrable (fun ω => P.Y true m ω - P.Y false m ω) μ) :
    P.nde μ a' = P.cde μ m := by
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  exact hω (P.M a' ω) m

/-- Without treatment and mediator interaction, the total natural direct effect contrast is
integrable when the pure one is: the two agree almost everywhere. -/
theorem integrable_nde_true_contrast_of_no_interaction (h : P.NoInteraction μ)
    (hint : Integrable (fun ω => P.nested true false ω - P.nested false false ω) μ) :
    Integrable (fun ω => P.nested true true ω - P.nested false true ω) μ := by
  refine hint.congr ?_
  filter_upwards [h] with ω hω
  exact hω (P.M false ω) (P.M true ω)

/-- Without treatment and mediator interaction, the pure and total natural direct effects
coincide. As in `nde_eq_cde_of_no_interaction` the integrands agree almost everywhere; the
integrability `_hint` of the pure natural direct effect contrast is required so that both sides
are finite means (the other contrast is then integrable, by
`integrable_nde_true_contrast_of_no_interaction`). -/
theorem nde_true_eq_nde_false_of_no_interaction [IsProbabilityMeasure μ]
    (h : P.NoInteraction μ)
    (_hint : Integrable (fun ω => P.nested true false ω - P.nested false false ω) μ) :
    P.nde μ true = P.nde μ false := by
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  exact hω (P.M true ω) (P.M false ω)

/-- The interventional mean `Σ m, E[Y a m] P(M a' = m)` for a finite mediator: the mean outcome
under treatment `a` when the mediator is drawn at random, independently of everything else, from
the law of `M a'`. It equals `E[Y a (M a')]` under cross world independence (see
`MediationModel.integral_nested_eq_interventionalMean`). It is the mean of that random draw only
when `μ` is a probability measure and `M a'` is measurable (so that the weights are probabilities
summing to one); every theorem that interprets it assumes both. -/
noncomputable def interventionalMean [Fintype 𝓜] (μ : Measure Ω) (a a' : Bool) : ℝ :=
  ∑ m, (∫ ω, P.Y a m ω ∂μ) * μ.real (P.M a' ⁻¹' {m})

/-- The interventional direct effect: change of treatment from `0` to `1` with the mediator drawn
from the law of `M 0`. -/
noncomputable def interventionalDirect [Fintype 𝓜] (μ : Measure Ω) : ℝ :=
  P.interventionalMean μ true false - P.interventionalMean μ false false

/-- The interventional indirect effect: change of the mediator law from that of `M 0` to that of
`M 1`, with treatment held at `1`. -/
noncomputable def interventionalIndirect [Fintype 𝓜] (μ : Measure Ω) : ℝ :=
  P.interventionalMean μ true true - P.interventionalMean μ true false

/-- The interventional overall effect: treatment `1` with the mediator drawn from the law of
`M 1`, against treatment `0` with the mediator drawn from the law of `M 0`. -/
noncomputable def interventionalTotal [Fintype 𝓜] (μ : Measure Ω) : ℝ :=
  P.interventionalMean μ true true - P.interventionalMean μ false false

/-- The interventional overall effect is the interventional direct effect plus the interventional
indirect effect. -/
theorem interventionalTotal_eq_add [Fintype 𝓜] [IsProbabilityMeasure μ] :
    P.interventionalTotal μ = P.interventionalDirect μ + P.interventionalIndirect μ := by
  rw [interventionalTotal, interventionalDirect, interventionalIndirect]
  ring

end MediationModel

end Mediation

end CausalInference
