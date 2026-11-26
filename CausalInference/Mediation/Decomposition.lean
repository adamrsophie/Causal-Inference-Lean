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
assumption. No identification assumption appears here.

## Main results

* `MediationModel.te_eq_nde_false_add_nie_true`: `TE = NDE(0) + NIE(1)`.
* `MediationModel.te_eq_nde_true_add_nie_false`: `TE = NDE(1) + NIE(0)`.
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
`TE = NDE(0) + NIE(1)`, assuming `Y 1 (M 1)`, `Y 1 (M 0)` and `Y 0 (M 0)` are integrable. -/
theorem te_eq_nde_false_add_nie_true (h11 : Integrable (P.nested true true) μ)
    (h10 : Integrable (P.nested true false) μ) (h00 : Integrable (P.nested false false) μ) :
    P.te μ = P.nde μ false + P.nie μ true := by
  rw [te, nde, nie, integral_sub h11 h00, integral_sub h10 h00, integral_sub h11 h10]
  ring

/-- The total effect is the total natural direct effect plus the pure natural indirect effect:
`TE = NDE(1) + NIE(0)`, assuming `Y 1 (M 1)`, `Y 0 (M 1)` and `Y 0 (M 0)` are integrable. -/
theorem te_eq_nde_true_add_nie_false (h11 : Integrable (P.nested true true) μ)
    (h01 : Integrable (P.nested false true) μ) (h00 : Integrable (P.nested false false) μ) :
    P.te μ = P.nde μ true + P.nie μ false := by
  rw [te, nde, nie, integral_sub h11 h00, integral_sub h11 h01, integral_sub h01 h00]
  ring

/-- No treatment and mediator interaction: for almost every unit the individual controlled
direct effect `Y 1 m - Y 0 m` does not depend on the mediator value `m`. -/
def NoInteraction (μ : Measure Ω) : Prop :=
  ∀ᵐ ω ∂μ, ∀ m m' : 𝓜, P.Y true m ω - P.Y false m ω = P.Y true m' ω - P.Y false m' ω

/-- Without treatment and mediator interaction, the natural direct effect `NDE(a')` equals the
controlled direct effect `CDE(m)` for every `a'` and every `m`. No integrability is needed: the
two integrands agree almost everywhere. -/
theorem nde_eq_cde_of_no_interaction (h : P.NoInteraction μ) (a' : Bool) (m : 𝓜) :
    P.nde μ a' = P.cde μ m := by
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  exact hω (P.M a' ω) m

/-- Without treatment and mediator interaction, the pure and total natural direct effects
coincide. -/
theorem nde_true_eq_nde_false_of_no_interaction (h : P.NoInteraction μ) :
    P.nde μ true = P.nde μ false := by
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  exact hω (P.M true ω) (P.M false ω)

/-- The interventional mean `Σ m, E[Y a m] P(M a' = m)` for a finite mediator: the mean outcome
under treatment `a` when the mediator is drawn at random, independently of everything else, from
the law of `M a'`. It equals `E[Y a (M a')]` under cross world independence (see
`MediationModel.integral_nested_eq_interventionalMean`). -/
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
theorem interventionalTotal_eq_add [Fintype 𝓜] :
    P.interventionalTotal μ = P.interventionalDirect μ + P.interventionalIndirect μ := by
  rw [interventionalTotal, interventionalDirect, interventionalIndirect]
  ring

end MediationModel

end Mediation

end CausalInference
