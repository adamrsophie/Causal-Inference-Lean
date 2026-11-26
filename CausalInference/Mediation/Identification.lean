/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Mediation.Decomposition

/-!
# Mediation: identification with a finite mediator

Identification of controlled direct effects, interventional effects and natural effects from
the observed law of `(A, Mobs, Yobs)`, for a finite mediator, first without covariates and then
with a finite covariate. The observed
variables are defined from the potential outcomes, so consistency and composition hold by
construction.

The assumptions are separate named hypotheses, all stated with Mathlib's `IndepFun`:

* treatment ignorability for the outcome: `Y a m ⫫ A`;
* treatment ignorability for the mediator: `M a' ⫫ A`;
* mediator ignorability given treatment: `Y a m ⫫ M a` under `μ[|A = a]`;
* cross world independence: `Y a m ⫫ M a'` under `μ`. When `a ≠ a'` this relates potential
  outcomes from two incompatible worlds and cannot be checked by any experiment.

Only the last one is cross world. It is used once, in
`MediationModel.integral_nested_eq_interventionalMean`, and the counterexample in
`CausalInference.Mediation.Counterexamples` shows that it cannot be dropped.

## Main results

* `MediationModel.integral_Y_eq_condMean`: `E[Y a m] = E[Yobs | A = a, Mobs = m]` under the two
  single world ignorability assumptions and positivity.
* `MediationModel.cde_eq_condMean_sub`: identification of the controlled direct effect under
  single world assumptions only.
* `MediationModel.measureReal_M_eq_cond`: `P(M a' = m) = P(Mobs = m | A = a')`.
* `MediationModel.interventionalMean_eq_mediationFormula`: identification of the interventional
  mean by the mediation formula, under single world assumptions only.
* `MediationModel.integral_nested_eq_interventionalMean`: under cross world independence,
  `E[Y a (M a')]` is the interventional mean.
* `MediationModel.integral_nested_eq_mediationFormula`: the mediation formula
  `E[Y a (M a')] = Σ m, E[Yobs | A = a, Mobs = m] P(Mobs = m | A = a')`.
* `MediationModel.nde_eq_mediationFormula`, `MediationModel.nie_eq_mediationFormula`: the
  resulting identification of natural direct and indirect effects.
* `MediationModel.integral_nested_eq_sum_mediationFormula`: the mediation formula with a finite
  covariate, all assumptions holding conditionally on each covariate value.

Sources: J. M. Robins and S. Greenland (1992), Identifiability and exchangeability for direct and
indirect effects; J. Pearl (2001), Direct and indirect effects; T. J. VanderWeele (2015),
Explanation in Causal Inference.
-/

@[expose] public section

namespace CausalInference

namespace Mediation

open MeasureTheory ProbabilityTheory

section Independence

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]
  {ν : Measure Ω} {f : Ω → ℝ} {X : Ω → 𝓧}

/-- If `f` is independent of `X`, the integral of `f` over the event `X = x` is the probability
of that event times the mean of `f`. -/
theorem setIntegral_preimage_singleton_of_indepFun (hfX : IndepFun f X ν) (hX : Measurable X)
    (hf : AEStronglyMeasurable f ν) (x : 𝓧) :
    ∫ ω in X ⁻¹' {x}, f ω ∂ν = ν.real (X ⁻¹' {x}) * ∫ ω, f ω ∂ν := by
  have hS : MeasurableSet (X ⁻¹' {x}) := hX (measurableSet_singleton x)
  have hind : (X ⁻¹' {x}).indicator f = ({x} : Set 𝓧).indicator (1 : 𝓧 → ℝ) ∘ X * f := by
    ext ω
    by_cases h : X ω = x <;> simp [Set.indicator, h]
  have hindep : IndepFun (({x} : Set 𝓧).indicator (1 : 𝓧 → ℝ) ∘ X) f ν :=
    (hfX.symm.comp ((measurable_const.indicator (measurableSet_singleton x))) measurable_id)
  have hcomp : ({x} : Set 𝓧).indicator (1 : 𝓧 → ℝ) ∘ X = (X ⁻¹' {x}).indicator 1 := by
    ext ω
    by_cases h : X ω = x <;> simp [Set.indicator, h]
  rw [← integral_indicator hS, hind, hindep.integral_mul_eq_mul_integral _ hf, hcomp,
    integral_indicator_one hS]
  exact ((measurable_const.indicator (measurableSet_singleton x)).comp hX).aestronglyMeasurable

/-- If `f` is independent of `X` and the event `X = x` has positive probability, conditioning on
that event does not change the mean of `f`. -/
theorem condMean_preimage_singleton_of_indepFun [IsFiniteMeasure ν] (hfX : IndepFun f X ν)
    (hX : Measurable X) (hf : AEStronglyMeasurable f ν) {x : 𝓧} (hpos : ν (X ⁻¹' {x}) ≠ 0) :
    condMean ν (X ⁻¹' {x}) f = ∫ ω, f ω ∂ν := by
  rw [condMean_eq, setIntegral_preimage_singleton_of_indepFun hfX hX hf, ← mul_assoc,
    inv_mul_cancel₀, one_mul]
  rw [measureReal_def]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos, measure_ne_top _ _⟩

/-- Law of total expectation over a finite partition: if `C` takes finitely many values and `f`
is integrable, then `E[f] = Σ c, P(C = c) E[f | C = c]`. Cells of probability zero contribute
`0` on both sides. -/
theorem integral_eq_sum_condMean [IsFiniteMeasure ν] {𝓒 : Type*} [Fintype 𝓒] [MeasurableSpace 𝓒]
    [MeasurableSingletonClass 𝓒] {C : Ω → 𝓒} (hC : Measurable C) (hf : Integrable f ν) :
    ∫ ω, f ω ∂ν = ∑ c, ν.real (C ⁻¹' {c}) * condMean ν (C ⁻¹' {c}) f := by
  have hsum : f = fun ω => ∑ c, (C ⁻¹' {c}).indicator f ω := by
    funext ω
    rw [Finset.sum_eq_single (C ω)]
    · simp
    · intro c _ hc
      exact Set.indicator_of_notMem (fun h => hc (Eq.symm h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  conv_lhs => rw [hsum]
  rw [integral_finsetSum _ fun c _ => hf.indicator (hC (measurableSet_singleton c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_indicator (hC (measurableSet_singleton c))]
  by_cases h : ν (C ⁻¹' {c}) = 0
  · simp [setIntegral_measure_zero _ h, measureReal_def, h]
  · rw [condMean_eq, ← mul_assoc, mul_inv_cancel₀, one_mul]
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨h, measure_ne_top _ _⟩

end Independence

namespace MediationModel

variable {Ω 𝓜 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓜] [MeasurableSingletonClass 𝓜]
  (P : MediationModel Ω 𝓜) {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Single world identification of `E[Y a m]`: if treatment is ignorable for `Y a m`
(`Y a m ⫫ A`), the mediator is ignorable for `Y a m` given `A = a`
(`Y a m ⫫ M a` under `μ[|A = a]`) and the cell `A = a, Mobs = m` has positive probability, then
`E[Y a m] = E[Yobs | A = a, Mobs = m]`. -/
theorem integral_Y_eq_condMean {a : Bool} {m : 𝓜} (hA : Measurable P.A)
    (hM : Measurable (P.M a)) (hY : Integrable (P.Y a m) μ)
    (hrandY : IndepFun (P.Y a m) P.A μ)
    (hmed : IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hpos : μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    ∫ ω, P.Y a m ω ∂μ = condMean μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) P.Yobs := by
  have hSA : MeasurableSet (P.A ⁻¹' {a}) := hA (measurableSet_singleton a)
  have hSM : MeasurableSet (P.M a ⁻¹' {m}) := hM (measurableSet_singleton m)
  have hcell : condMean μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) P.Yobs =
      condMean μ (P.A ⁻¹' {a} ∩ P.M a ⁻¹' {m}) (P.Y a m) := by
    rw [P.A_inter_Mobs_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem (hSA.inter hSM)] with ω hω
    have hω' : ω ∈ P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m} := by rwa [P.A_inter_Mobs_eq]
    exact P.Yobs_of_A_eq_of_Mobs_eq hω'.1 hω'.2
  rw [P.A_inter_Mobs_eq] at hpos
  have hposA : μ (P.A ⁻¹' {a}) ≠ 0 :=
    fun h => hpos (measure_mono_null Set.inter_subset_left h)
  have hposM : μ[|P.A ⁻¹' {a}] (P.M a ⁻¹' {m}) ≠ 0 := by
    rw [cond_apply hSA]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hpos
  have hYc : AEStronglyMeasurable (P.Y a m) μ[|P.A ⁻¹' {a}] :=
    hY.aestronglyMeasurable.mono_ac cond_absolutelyContinuous
  rw [hcell, condMean, ← cond_cond_eq_cond_inter hSA hSM μ, ← condMean,
    condMean_preimage_singleton_of_indepFun hmed hM hYc hposM, ← condMean,
    condMean_preimage_singleton_of_indepFun hrandY hA hY.aestronglyMeasurable hposA]

/-- Identification of the controlled direct effect under single world assumptions only: for each
treatment level `a`, treatment ignorability `Y a m ⫫ A`, mediator ignorability
`Y a m ⫫ M a` under `μ[|A = a]` and positivity of the cell `A = a, Mobs = m` give
`CDE(m) = E[Yobs | A = 1, Mobs = m] - E[Yobs | A = 0, Mobs = m]`. No cross world assumption is
used. -/
theorem cde_eq_condMean_sub {m : 𝓜} (hA : Measurable P.A) (hM : ∀ a, Measurable (P.M a))
    (hY : ∀ a, Integrable (P.Y a m) μ) (hrandY : ∀ a, IndepFun (P.Y a m) P.A μ)
    (hmed : ∀ a, IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hpos : ∀ a, μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.cde μ m = condMean μ (P.A ⁻¹' {true} ∩ P.Mobs ⁻¹' {m}) P.Yobs -
      condMean μ (P.A ⁻¹' {false} ∩ P.Mobs ⁻¹' {m}) P.Yobs := by
  rw [cde, integral_sub (hY true) (hY false),
    P.integral_Y_eq_condMean hA (hM true) (hY true) (hrandY true) (hmed true) (hpos true),
    P.integral_Y_eq_condMean hA (hM false) (hY false) (hrandY false) (hmed false) (hpos false)]

/-- Single world identification of the mediator law: if treatment is ignorable for the mediator
(`M a' ⫫ A`) and `P(A = a') > 0`, then `P(M a' = m) = P(Mobs = m | A = a')`. -/
theorem measureReal_M_eq_cond {a' : Bool} (hA : Measurable P.A)
    (hrandM : IndepFun (P.M a') P.A μ) (hposA : μ (P.A ⁻¹' {a'}) ≠ 0) (m : 𝓜) :
    μ.real (P.M a' ⁻¹' {m}) = (μ[|P.A ⁻¹' {a'}]).real (P.Mobs ⁻¹' {m}) := by
  rw [measureReal_def, measureReal_def, cond_apply (hA (measurableSet_singleton a')),
    P.A_inter_Mobs_eq, Set.inter_comm,
    hrandM.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton m)
      (measurableSet_singleton a'),
    mul_comm (μ _), ← mul_assoc, ENNReal.inv_mul_cancel hposA (measure_ne_top _ _), one_mul]

/-- The mediation formula, a functional of the observed law only:
`Σ m, E[Yobs | A = a, Mobs = m] P(Mobs = m | A = a')`. -/
noncomputable def mediationFormula [Fintype 𝓜] (μ : Measure Ω) (a a' : Bool) : ℝ :=
  ∑ m, condMean μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) P.Yobs *
    (μ[|P.A ⁻¹' {a'}]).real (P.Mobs ⁻¹' {m})

/-- Identification of the interventional mean by the mediation formula under single world
assumptions only: treatment ignorability for `Y a m` and for `M a'`, mediator ignorability
`Y a m ⫫ M a` under `μ[|A = a]`, `P(A = a') > 0`, and positivity of the cell `A = a, Mobs = m`
whenever `P(Mobs = m | A = a') > 0`. -/
theorem interventionalMean_eq_mediationFormula [Fintype 𝓜] {a a' : Bool} (hA : Measurable P.A)
    (hMa : Measurable (P.M a)) (hY : ∀ m, Integrable (P.Y a m) μ)
    (hrandY : ∀ m, IndepFun (P.Y a m) P.A μ) (hrandM : IndepFun (P.M a') P.A μ)
    (hmed : ∀ m, IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ m, μ[|P.A ⁻¹' {a'}] (P.Mobs ⁻¹' {m}) ≠ 0 →
      μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.interventionalMean μ a a' = P.mediationFormula μ a a' := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [P.measureReal_M_eq_cond hA hrandM hposA m]
  by_cases hw : μ[|P.A ⁻¹' {a'}] (P.Mobs ⁻¹' {m}) = 0
  · simp [measureReal_def, hw]
  · rw [P.integral_Y_eq_condMean hA hMa (hY m) (hrandY m) (hmed m) (hpos m hw)]

omit [IsProbabilityMeasure μ] in
/-- Under cross world independence `Y a m ⫫ M a'` for every `m`, the nested mean
`E[Y a (M a')]` equals the interventional mean `Σ m, E[Y a m] P(M a' = m)`. This is the only
place where a cross world assumption enters. -/
theorem integral_nested_eq_interventionalMean [Fintype 𝓜] {a a' : Bool}
    (hM : Measurable (P.M a')) (hY : ∀ m, Integrable (P.Y a m) μ)
    (hcross : ∀ m, IndepFun (P.Y a m) (P.M a') μ) :
    ∫ ω, P.nested a a' ω ∂μ = P.interventionalMean μ a a' := by
  simp_rw [P.nested_eq_sum a a']
  rw [integral_finsetSum _ fun m _ => (hY m).indicator (hM (measurableSet_singleton m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_indicator (hM (measurableSet_singleton m)),
    setIntegral_preimage_singleton_of_indepFun (hcross m) hM (hY m).aestronglyMeasurable,
    mul_comm]

/-- The mediation formula (Pearl 2001), finite mediator, no covariates. Assume treatment
ignorability for every `Y a m` and for `M a'`, mediator ignorability `Y a m ⫫ M a` under
`μ[|A = a]`, the cross world independence `Y a m ⫫ M a'` under `μ`, `P(A = a') > 0`, positivity
of the cell `A = a, Mobs = m` whenever `P(Mobs = m | A = a') > 0`, and integrability of every
`Y a m`. Then
`E[Y a (M a')] = Σ m, E[Yobs | A = a, Mobs = m] P(Mobs = m | A = a')`. -/
theorem integral_nested_eq_mediationFormula [Fintype 𝓜] {a a' : Bool} (hA : Measurable P.A)
    (hMa : Measurable (P.M a)) (hMa' : Measurable (P.M a')) (hY : ∀ m, Integrable (P.Y a m) μ)
    (hrandY : ∀ m, IndepFun (P.Y a m) P.A μ) (hrandM : IndepFun (P.M a') P.A μ)
    (hmed : ∀ m, IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hcross : ∀ m, IndepFun (P.Y a m) (P.M a') μ)
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ m, μ[|P.A ⁻¹' {a'}] (P.Mobs ⁻¹' {m}) ≠ 0 →
      μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    ∫ ω, P.nested a a' ω ∂μ = P.mediationFormula μ a a' := by
  rw [P.integral_nested_eq_interventionalMean hMa' hY hcross,
    P.interventionalMean_eq_mediationFormula hA hMa hY hrandY hrandM hmed hposA hpos]

/-- Identification of the natural direct effect `NDE(a')` by the mediation formula:
`NDE(a') = Σ m, (E[Yobs | A = 1, Mobs = m] - E[Yobs | A = 0, Mobs = m]) P(Mobs = m | A = a')`,
written as a difference of two mediation formulas. The hypotheses are those of
`integral_nested_eq_mediationFormula` for both treatment levels `a`, with the mediator world
`a'` fixed; in particular the cross world independence `Y a m ⫫ M a'` for every `a` and `m`. -/
theorem nde_eq_mediationFormula [Fintype 𝓜] {a' : Bool} (hA : Measurable P.A)
    (hM : ∀ a, Measurable (P.M a)) (hY : ∀ a m, Integrable (P.Y a m) μ)
    (hrandY : ∀ a m, IndepFun (P.Y a m) P.A μ) (hrandM : IndepFun (P.M a') P.A μ)
    (hmed : ∀ a m, IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hcross : ∀ a m, IndepFun (P.Y a m) (P.M a') μ)
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ a m, μ[|P.A ⁻¹' {a'}] (P.Mobs ⁻¹' {m}) ≠ 0 →
      μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nde μ a' = P.mediationFormula μ true a' - P.mediationFormula μ false a' := by
  rw [nde, integral_sub (P.integrable_nested (hM a') (hY true))
      (P.integrable_nested (hM a') (hY false)),
    P.integral_nested_eq_mediationFormula hA (hM true) (hM a') (hY true) (hrandY true) hrandM
      (hmed true) (hcross true) hposA (hpos true),
    P.integral_nested_eq_mediationFormula hA (hM false) (hM a') (hY false) (hrandY false) hrandM
      (hmed false) (hcross false) hposA (hpos false)]

/-- Identification of the natural indirect effect `NIE(a)` by the mediation formula:
`NIE(a) = Σ m, E[Yobs | A = a, Mobs = m] (P(Mobs = m | A = 1) - P(Mobs = m | A = 0))`, written
as a difference of two mediation formulas. The hypotheses are those of
`integral_nested_eq_mediationFormula` for both mediator worlds `a'`, with the treatment `a`
fixed; in particular the cross world independence `Y a m ⫫ M a'` for every `a'` and `m`. -/
theorem nie_eq_mediationFormula [Fintype 𝓜] {a : Bool} (hA : Measurable P.A)
    (hM : ∀ a', Measurable (P.M a')) (hY : ∀ m, Integrable (P.Y a m) μ)
    (hrandY : ∀ m, IndepFun (P.Y a m) P.A μ) (hrandM : ∀ a', IndepFun (P.M a') P.A μ)
    (hmed : ∀ m, IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hcross : ∀ a' m, IndepFun (P.Y a m) (P.M a') μ)
    (hposA : ∀ a', μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ a' m, μ[|P.A ⁻¹' {a'}] (P.Mobs ⁻¹' {m}) ≠ 0 →
      μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nie μ a = P.mediationFormula μ a true - P.mediationFormula μ a false := by
  rw [nie, integral_sub (P.integrable_nested (hM true) hY) (P.integrable_nested (hM false) hY),
    P.integral_nested_eq_mediationFormula hA (hM a) (hM true) hY hrandY (hrandM true) hmed
      (hcross true) (hposA true) (hpos true),
    P.integral_nested_eq_mediationFormula hA (hM a) (hM false) hY hrandY (hrandM false) hmed
      (hcross false) (hposA false) (hpos false)]

/-- The mediation formula with a finite covariate `C`. Assume that for every covariate value `c`
with `P(C = c) > 0` the hypotheses of `integral_nested_eq_mediationFormula` hold under the
conditioned measure `μ[|C = c]`: treatment ignorability for every `Y a m` and for `M a'`,
mediator ignorability `Y a m ⫫ M a` given `A = a`, the cross world independence `Y a m ⫫ M a'`,
`P(A = a' | C = c) > 0` and positivity of the cells `A = a, Mobs = m`. Assume also that every
`Y a m` is integrable under `μ`. Then
`E[Y a (M a')] = Σ c, P(C = c) Σ m, E[Yobs | C = c, A = a, Mobs = m] P(Mobs = m | C = c, A = a')`,
where the inner sum is `mediationFormula` under `μ[|C = c]`. -/
theorem integral_nested_eq_sum_mediationFormula [Fintype 𝓜] {𝓒 : Type*} [Fintype 𝓒]
    [MeasurableSpace 𝓒] [MeasurableSingletonClass 𝓒] {a a' : Bool} (C : Ω → 𝓒)
    (hC : Measurable C) (hA : Measurable P.A) (hMa : Measurable (P.M a))
    (hMa' : Measurable (P.M a')) (hY : ∀ m, Integrable (P.Y a m) μ)
    (hrandY : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, IndepFun (P.Y a m) P.A μ[|C ⁻¹' {c}])
    (hrandM : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → IndepFun (P.M a') P.A μ[|C ⁻¹' {c}])
    (hmed : ∀ c, μ (C ⁻¹' {c}) ≠ 0 →
      ∀ m, IndepFun (P.Y a m) (P.M a) μ[|C ⁻¹' {c}][|P.A ⁻¹' {a}])
    (hcross : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, IndepFun (P.Y a m) (P.M a') μ[|C ⁻¹' {c}])
    (hposA : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → μ[|C ⁻¹' {c}] (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m,
      μ[|C ⁻¹' {c}][|P.A ⁻¹' {a'}] (P.Mobs ⁻¹' {m}) ≠ 0 →
        μ[|C ⁻¹' {c}] (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    ∫ ω, P.nested a a' ω ∂μ =
      ∑ c, μ.real (C ⁻¹' {c}) * P.mediationFormula μ[|C ⁻¹' {c}] a a' := by
  rw [integral_eq_sum_condMean hC (P.integrable_nested hMa' hY)]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : μ (C ⁻¹' {c}) = 0
  · simp [measureReal_def, hc]
  · have : IsProbabilityMeasure μ[|C ⁻¹' {c}] := cond_isProbabilityMeasure hc
    have hYc : ∀ m, Integrable (P.Y a m) μ[|C ⁻¹' {c}] := fun m =>
      ((hY m).restrict).smul_measure (ENNReal.inv_ne_top.mpr hc)
    rw [condMean, P.integral_nested_eq_mediationFormula hA hMa hMa' hYc (hrandY c hc)
      (hrandM c hc) (hmed c hc) (hcross c hc) (hposA c hc) (hpos c hc)]

end MediationModel

end Mediation

end CausalInference
