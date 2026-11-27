/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Mediation.Decomposition

/-!
# Mediation: identification with a finite mediator

Identification of controlled direct effects, the total effect, interventional effects and
natural effects from the observed law of `(A, Mobs, Yobs)`, for a finite mediator, first without
covariates and then with a finite covariate. The observed variables are defined from the
potential outcomes, so consistency and composition hold by construction. Every theorem that
interprets an effect or a conditional mean assumes a probability measure.

The assumptions are separate named hypotheses, all stated with Mathlib's `IndepFun`:

* treatment ignorability for the outcome: `Y a m ⫫ A`, or for the same world nested outcome
  `Y a (M a) ⫫ A`;
* treatment ignorability for the mediator: `M a' ⫫ A`;
* mediator ignorability given treatment: `Y a m ⫫ M a` under `μ[|A = a]`;
* cross world independence: `Y a m ⫫ M a'` under `μ`. When `a ≠ a'` this relates potential
  outcomes from two incompatible worlds and cannot be checked by any experiment.

Only the last one is cross world. It enters only through
`MediationModel.integral_nested_eq_interventionalMean`, and only for the cross world nested
mean `E[Y a (M a')]` with `a ≠ a'`: the same world mean `E[Y a (M a)]` is identified by the arm
mean `E[Yobs | A = a]`. The counterexample in `CausalInference.Mediation.Counterexamples` shows
that, in a class of models with randomized treatment in which every other hypothesis of the
mediation formula holds, the natural direct effect is not identified without it.

Outcome hypotheses are required only for the mediator values `m` with `P(M a' = m) > 0`, the
values that carry weight in the formula. Each mediator `M a'` whose law enters is measurable.

## Main results

* `MediationModel.integral_Y_eq_condMean`: `E[Y a m] = E[Yobs | A = a, Mobs = m]` under the two
  single world ignorability assumptions and positivity.
* `MediationModel.cde_eq_condMean_sub`: identification of the controlled direct effect under
  single world assumptions only.
* `MediationModel.integral_nested_self_eq_mediationFormula`,
  `MediationModel.te_eq_condMean_sub`: `E[Y a (M a)] = E[Yobs | A = a] = mediationFormula μ a a`
  and identification of the total effect from the two arms.
* `MediationModel.measureReal_M_eq_cond`: `P(M a' = m) = P(Mobs = m | A = a')`.
* `MediationModel.interventionalMean_eq_mediationFormula`: identification of the interventional
  mean by the mediation formula, under single world assumptions only.
* `MediationModel.integral_nested_eq_interventionalMean`: under cross world independence,
  `E[Y a (M a')]` is the interventional mean; hence
  `MediationModel.nde_false_eq_interventionalDirect`,
  `MediationModel.nie_true_eq_interventionalIndirect` and
  `MediationModel.te_eq_interventionalTotal`.
* `MediationModel.integral_nested_eq_mediationFormula`: the mediation formula
  `E[Y a (M a')] = Σ m, E[Yobs | A = a, Mobs = m] P(Mobs = m | A = a')`.
* `MediationModel.nde_eq_mediationFormula`, `MediationModel.nie_eq_mediationFormula`: the
  resulting identification of natural direct and indirect effects, with the cross world
  assumptions imposed on the cross world term only.
* `MediationModel.mediationFormula_eq_observedMediationFormula`,
  `MediationModel.mediationFormula_eq_of_map_eq`: for an almost everywhere measurable observed
  triple, the mediation formula is a functional of its law.
* `MediationModel.integral_nested_eq_sum_mediationFormula`,
  `MediationModel.cde_eq_sum_condMean_sub`, `MediationModel.nde_eq_sum_mediationFormula`,
  `MediationModel.nie_eq_sum_mediationFormula`: versions with a finite covariate, all
  assumptions holding conditionally on each covariate value.

Sources: J. M. Robins and S. Greenland (1992), Identifiability and exchangeability for direct and
indirect effects; J. Pearl (2001), Direct and indirect effects; T. J. VanderWeele (2015),
Explanation in Causal Inference; T. J. VanderWeele, S. Vansteelandt and J. M. Robins (2014),
Effect decomposition in the presence of an exposure-induced mediator-outcome confounder.
-/

@[expose] public section

namespace CausalInference

namespace Mediation

open MeasureTheory ProbabilityTheory

section Independence

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSingletonClass 𝓧]
  {ν : Measure Ω} {f : Ω → ℝ} {X : Ω → 𝓧}

/-- A function integrable under `ν` is integrable under `ν` conditioned on an event of positive
measure. -/
theorem integrable_cond_of_integrable {s : Set Ω} (hf : Integrable f ν) (hs : ν s ≠ 0) :
    Integrable f ν[|s] :=
  hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hs)

/-- If an integrable `f` is independent of `X`, the integral of `f` over the event `X = x` is
the probability of that event times the mean of `f`. -/
theorem setIntegral_preimage_singleton_of_indepFun (hfX : IndepFun f X ν) (hX : Measurable X)
    (hf : Integrable f ν) (x : 𝓧) :
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
  rw [← integral_indicator hS, hind, hindep.integral_mul_eq_mul_integral _ hf.aestronglyMeasurable,
    hcomp, integral_indicator_one hS]
  exact ((measurable_const.indicator (measurableSet_singleton x)).comp hX).aestronglyMeasurable

/-- If an integrable `f` is independent of `X` and the event `X = x` has positive probability,
conditioning on that event does not change the mean of `f`. -/
theorem condMean_preimage_singleton_of_indepFun [IsFiniteMeasure ν] (hfX : IndepFun f X ν)
    (hX : Measurable X) (hf : Integrable f ν) {x : 𝓧} (hpos : ν (X ⁻¹' {x}) ≠ 0) :
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

/-- Conditioning twice is conditioning on the intersection: for measurable events `s` and `t`,
`E[f | s][| t] = E[f | s ∩ t]`, that is `condMean ν[|s] t f = condMean ν (s ∩ t) f`. -/
theorem condMean_cond_eq_condMean_inter [IsFiniteMeasure ν] {s t : Set Ω} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (f : Ω → ℝ) : condMean ν[|s] t f = condMean ν (s ∩ t) f := by
  rw [condMean, condMean, cond_cond_eq_cond_inter hs ht ν]

end Independence

/-- The mediation formula computed from a law `ρ` of a triple (treatment, mediator, outcome)
on `Bool × 𝓜 × ℝ`: `Σ m, E_ρ[y | a, m] ρ(m | a')`. -/
noncomputable def observedMediationFormula {𝓜 : Type*} [MeasurableSpace 𝓜] [Fintype 𝓜]
    (ρ : Measure (Bool × 𝓜 × ℝ)) (a a' : Bool) : ℝ :=
  ∑ m, condMean ρ ({a} ×ˢ {m} ×ˢ Set.univ) (fun x => x.2.2) *
    (ρ[|{a'} ×ˢ Set.univ]).real (Set.univ ×ˢ {m} ×ˢ Set.univ)

namespace MediationModel

variable {Ω 𝓜 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓜] [MeasurableSingletonClass 𝓜]
  (P : MediationModel Ω 𝓜) {μ : Measure Ω}

/-- Single world identification of `E[Y a m]`: if treatment is ignorable for `Y a m`
(`Y a m ⫫ A`), the mediator is ignorable for `Y a m` given `A = a`
(`Y a m ⫫ M a` under `μ[|A = a]`) and the cell `A = a, Mobs = m` has positive probability, then
`E[Y a m] = E[Yobs | A = a, Mobs = m]`. -/
theorem integral_Y_eq_condMean [IsProbabilityMeasure μ] {a : Bool} {m : 𝓜} (hA : Measurable P.A)
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
  rw [hcell, ← condMean_cond_eq_condMean_inter hSA hSM,
    condMean_preimage_singleton_of_indepFun hmed hM (integrable_cond_of_integrable hY hposA)
      hposM, ← condMean, condMean_preimage_singleton_of_indepFun hrandY hA hY hposA]

/-- Identification of the controlled direct effect under single world assumptions only: for each
treatment level `a`, treatment ignorability `Y a m ⫫ A`, mediator ignorability
`Y a m ⫫ M a` under `μ[|A = a]` and positivity of the cell `A = a, Mobs = m` give
`CDE(m) = E[Yobs | A = 1, Mobs = m] - E[Yobs | A = 0, Mobs = m]`. No cross world assumption is
used. -/
theorem cde_eq_condMean_sub [IsProbabilityMeasure μ] {m : 𝓜} (hA : Measurable P.A)
    (hM : ∀ a, Measurable (P.M a))
    (hY : ∀ a, Integrable (P.Y a m) μ) (hrandY : ∀ a, IndepFun (P.Y a m) P.A μ)
    (hmed : ∀ a, IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hpos : ∀ a, μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.cde μ m = condMean μ (P.A ⁻¹' {true} ∩ P.Mobs ⁻¹' {m}) P.Yobs -
      condMean μ (P.A ⁻¹' {false} ∩ P.Mobs ⁻¹' {m}) P.Yobs := by
  rw [cde, integral_sub (hY true) (hY false),
    P.integral_Y_eq_condMean hA (hM true) (hY true) (hrandY true) (hmed true) (hpos true),
    P.integral_Y_eq_condMean hA (hM false) (hY false) (hrandY false) (hmed false) (hpos false)]

/-- Single world identification of the mediator law: if treatment is ignorable for the mediator
(`M a' ⫫ A`) and `P(A = a') > 0`, then `P(M a' = m) = P(Mobs = m | A = a')`. The identity itself
holds for any `M a'`, because Mathlib's `IndepFun` factorizes the (outer) measure of preimages;
the measurability `_hMa'` of `M a'` is required so that `P(M a' = m)` is the probability of an
event and these weights sum to one (`sum_measureReal_M_eq_one`). Without it the mediation formula
can assign total weight larger than one. -/
theorem measureReal_M_eq_cond [IsProbabilityMeasure μ] {a' : Bool} (hA : Measurable P.A)
    (_hMa' : Measurable (P.M a')) (hrandM : IndepFun (P.M a') P.A μ)
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0) (m : 𝓜) :
    μ.real (P.M a' ⁻¹' {m}) = (μ[|P.A ⁻¹' {a'}]).real (P.Mobs ⁻¹' {m}) := by
  rw [measureReal_def, measureReal_def, cond_apply (hA (measurableSet_singleton a')),
    P.A_inter_Mobs_eq, Set.inter_comm,
    hrandM.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton m)
      (measurableSet_singleton a'),
    mul_comm (μ _), ← mul_assoc, ENNReal.inv_mul_cancel hposA (measure_ne_top _ _), one_mul]

/-- For a probability measure and a measurable mediator `M a'` with finitely many values, the
probabilities `P(M a' = m)` sum to one. -/
theorem sum_measureReal_M_eq_one [Fintype 𝓜] [IsProbabilityMeasure μ] {a' : Bool}
    (hM : Measurable (P.M a')) : ∑ m, μ.real (P.M a' ⁻¹' {m}) = 1 := by
  rw [sum_measureReal_preimage_singleton _ fun m _ => hM (measurableSet_singleton m)]
  simp

/-- The mediation formula `Σ m, E[Yobs | A = a, Mobs = m] P(Mobs = m | A = a')`. It is defined
for every measure; it is a functional of the observed law of `(A, Mobs, Yobs)` when this triple
is almost everywhere measurable (`mediationFormula_eq_observedMediationFormula`). -/
noncomputable def mediationFormula [Fintype 𝓜] (μ : Measure Ω) (a a' : Bool) : ℝ :=
  ∑ m, condMean μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) P.Yobs *
    (μ[|P.A ⁻¹' {a'}]).real (P.Mobs ⁻¹' {m})

omit [MeasurableSpace 𝓜] [MeasurableSingletonClass 𝓜] in
open Classical in
/-- Only mediator values with `P(Mobs = m | A = a') > 0` contribute to the mediation formula.
Under treatment ignorability for `M a'` these are the values with `P(M a' = m) > 0`
(`measureReal_M_eq_cond`). -/
theorem mediationFormula_eq_sum_filter [Fintype 𝓜] (μ : Measure Ω) (a a' : Bool) :
    P.mediationFormula μ a a' =
      ∑ m ∈ Finset.univ.filter (fun m => μ[|P.A ⁻¹' {a'}] (P.Mobs ⁻¹' {m}) ≠ 0),
        condMean μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) P.Yobs *
          (μ[|P.A ⁻¹' {a'}]).real (P.Mobs ⁻¹' {m}) := by
  rw [mediationFormula, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with h
  · rfl
  · simp [measureReal_def, not_not.mp h]

/-- Identification of the interventional mean by the mediation formula under single world
assumptions only. Assume treatment ignorability for `M a'` with `M a'` measurable,
`P(A = a') > 0`, and, for every mediator value `m` with `P(M a' = m) > 0`: integrability of
`Y a m`, treatment ignorability `Y a m ⫫ A`, mediator ignorability `Y a m ⫫ M a` under
`μ[|A = a]`, and positivity of the cell `A = a, Mobs = m`. -/
theorem interventionalMean_eq_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ]
    {a a' : Bool} (hA : Measurable P.A) (hMa : Measurable (P.M a)) (hMa' : Measurable (P.M a'))
    (hY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hrandY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) P.A μ)
    (hrandM : IndepFun (P.M a') P.A μ)
    (hmed : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.interventionalMean μ a a' = P.mediationFormula μ a a' := by
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hw : μ (P.M a' ⁻¹' {m}) = 0
  · rw [← P.measureReal_M_eq_cond hA hMa' hrandM hposA m]
    simp [measureReal_def, hw]
  · rw [P.measureReal_M_eq_cond hA hMa' hrandM hposA m,
      P.integral_Y_eq_condMean hA hMa (hY m hw) (hrandY m hw) (hmed m hw) (hpos m hw)]

/-- Under cross world independence `Y a m ⫫ M a'` for every mediator value `m` with
`P(M a' = m) > 0`, the nested mean `E[Y a (M a')]` equals the interventional mean
`Σ m, E[Y a m] P(M a' = m)`. This is the only place where a cross world assumption enters. -/
theorem integral_nested_eq_interventionalMean [Fintype 𝓜] [IsProbabilityMeasure μ] {a a' : Bool}
    (hM : Measurable (P.M a')) (hY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hcross : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a') μ) :
    ∫ ω, P.nested a a' ω ∂μ = P.interventionalMean μ a a' := by
  simp_rw [P.nested_eq_sum a a']
  rw [integral_finsetSum _ fun m _ => P.integrable_indicator_of_ne_zero hM (hY m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_indicator (hM (measurableSet_singleton m))]
  by_cases hm : μ (P.M a' ⁻¹' {m}) = 0
  · simp [setIntegral_measure_zero _ hm, measureReal_def, hm]
  · rw [setIntegral_preimage_singleton_of_indepFun (hcross m hm) hM (hY m hm), mul_comm]

/-- The mediation formula (Pearl 2001), finite mediator, no covariates. Assume treatment
ignorability for `M a'` with `M a'` measurable, `P(A = a') > 0`, and, for every mediator value
`m` with `P(M a' = m) > 0`: integrability of `Y a m`, treatment ignorability `Y a m ⫫ A`,
mediator ignorability `Y a m ⫫ M a` under `μ[|A = a]`, the cross world independence
`Y a m ⫫ M a'` under `μ`, and positivity of the cell `A = a, Mobs = m`. Then
`E[Y a (M a')] = Σ m, E[Yobs | A = a, Mobs = m] P(Mobs = m | A = a')`. For `a = a'` the
weaker hypotheses of `integral_nested_self_eq_mediationFormula` suffice. -/
theorem integral_nested_eq_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ] {a a' : Bool}
    (hA : Measurable P.A) (hMa : Measurable (P.M a)) (hMa' : Measurable (P.M a'))
    (hY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hrandY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) P.A μ)
    (hrandM : IndepFun (P.M a') P.A μ)
    (hmed : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hcross : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a') μ)
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    ∫ ω, P.nested a a' ω ∂μ = P.mediationFormula μ a a' := by
  rw [P.integral_nested_eq_interventionalMean hMa' hY hcross,
    P.interventionalMean_eq_mediationFormula hA hMa hMa' hY hrandY hrandM hmed hposA hpos]

omit [MeasurableSpace 𝓜] [MeasurableSingletonClass 𝓜] in
/-- Identification of the same world nested mean `E[Y a (M a)]` by the observed arm mean
`E[Yobs | A = a]`, under treatment ignorability for the nested outcome (`Y a (M a) ⫫ A`), its
integrability, and `P(A = a) > 0`. No mediator assumption is used. -/
theorem integral_nested_self_eq_condMean [IsProbabilityMeasure μ] {a : Bool} (hA : Measurable P.A)
    (hrand : IndepFun (P.nested a a) P.A μ) (hint : Integrable (P.nested a a) μ)
    (hposA : μ (P.A ⁻¹' {a}) ≠ 0) :
    ∫ ω, P.nested a a ω ∂μ = condMean μ (P.A ⁻¹' {a}) P.Yobs := by
  rw [← condMean_preimage_singleton_of_indepFun hrand hA hint hposA]
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem (hA (measurableSet_singleton a))] with ω hω
  exact (P.Yobs_of_A_eq hω).symm

/-- The observed arm mean is the mediation formula on the diagonal:
`E[Yobs | A = a] = Σ m, E[Yobs | A = a, Mobs = m] P(Mobs = m | A = a)`, for measurable `A` and
`M a`, `P(A = a) > 0` and integrable `Y a (M a)`. This is the law of total expectation within
the arm; no ignorability assumption is used. -/
theorem condMean_A_eq_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ] {a : Bool}
    (hA : Measurable P.A) (hMa : Measurable (P.M a)) (hint : Integrable (P.nested a a) μ)
    (hposA : μ (P.A ⁻¹' {a}) ≠ 0) :
    condMean μ (P.A ⁻¹' {a}) P.Yobs = P.mediationFormula μ a a := by
  have hSA : MeasurableSet (P.A ⁻¹' {a}) := hA (measurableSet_singleton a)
  have : IsProbabilityMeasure μ[|P.A ⁻¹' {a}] := cond_isProbabilityMeasure hposA
  have hYobs : Integrable P.Yobs μ[|P.A ⁻¹' {a}] := by
    refine (integrable_cond_of_integrable hint hposA).congr ?_
    filter_upwards [ae_cond_mem hSA] with ω hω
    exact (P.Yobs_of_A_eq hω).symm
  rw [condMean, integral_eq_sum_condMean hMa hYobs, mediationFormula]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hSM : MeasurableSet (P.M a ⁻¹' {m}) := hMa (measurableSet_singleton m)
  rw [condMean_cond_eq_condMean_inter hSA hSM, ← P.A_inter_Mobs_eq, mul_comm]
  congr 1
  rw [measureReal_def, measureReal_def, cond_apply hSA, cond_apply hSA, P.A_inter_Mobs_eq]

/-- Identification of the same world nested mean by the mediation formula on the diagonal:
`E[Y a (M a)] = E[Yobs | A = a] = mediationFormula μ a a`, under treatment ignorability for the
nested outcome, its integrability, `P(A = a) > 0` and measurability of `M a`. Neither mediator
ignorability nor any cross world assumption is needed. -/
theorem integral_nested_self_eq_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ] {a : Bool}
    (hA : Measurable P.A) (hMa : Measurable (P.M a)) (hrand : IndepFun (P.nested a a) P.A μ)
    (hint : Integrable (P.nested a a) μ) (hposA : μ (P.A ⁻¹' {a}) ≠ 0) :
    ∫ ω, P.nested a a ω ∂μ = P.mediationFormula μ a a := by
  rw [P.integral_nested_self_eq_condMean hA hrand hint hposA,
    P.condMean_A_eq_mediationFormula hA hMa hint hposA]

omit [MeasurableSpace 𝓜] [MeasurableSingletonClass 𝓜] in
/-- Identification of the total effect from the two treatment arms:
`TE = E[Yobs | A = 1] - E[Yobs | A = 0]`, under treatment ignorability `Y a (M a) ⫫ A`,
integrability of `Y a (M a)` and `P(A = a) > 0` for both `a`. -/
theorem te_eq_condMean_sub [IsProbabilityMeasure μ] (hA : Measurable P.A)
    (hrand : ∀ a, IndepFun (P.nested a a) P.A μ) (hint : ∀ a, Integrable (P.nested a a) μ)
    (hposA : ∀ a, μ (P.A ⁻¹' {a}) ≠ 0) :
    P.te μ = condMean μ (P.A ⁻¹' {true}) P.Yobs - condMean μ (P.A ⁻¹' {false}) P.Yobs := by
  rw [te, integral_sub (hint true) (hint false),
    P.integral_nested_self_eq_condMean hA (hrand true) (hint true) (hposA true),
    P.integral_nested_self_eq_condMean hA (hrand false) (hint false) (hposA false)]

/-- The total effect as a difference of diagonal mediation formulas:
`TE = mediationFormula μ 1 1 - mediationFormula μ 0 0`, under the hypotheses of
`te_eq_condMean_sub` and measurability of both mediators. -/
theorem te_eq_mediationFormula_sub [Fintype 𝓜] [IsProbabilityMeasure μ] (hA : Measurable P.A)
    (hM : ∀ a, Measurable (P.M a)) (hrand : ∀ a, IndepFun (P.nested a a) P.A μ)
    (hint : ∀ a, Integrable (P.nested a a) μ) (hposA : ∀ a, μ (P.A ⁻¹' {a}) ≠ 0) :
    P.te μ = P.mediationFormula μ true true - P.mediationFormula μ false false := by
  rw [P.te_eq_condMean_sub hA hrand hint hposA,
    P.condMean_A_eq_mediationFormula hA (hM true) (hint true) (hposA true),
    P.condMean_A_eq_mediationFormula hA (hM false) (hint false) (hposA false)]

/-- Identification of the natural direct effect `NDE(a')` by the mediation formula:
`NDE(a') = Σ m, (E[Yobs | A = 1, Mobs = m] - E[Yobs | A = 0, Mobs = m]) P(Mobs = m | A = a')`,
written as a difference of two mediation formulas. Of the two nested means, `E[Y a' (M a')]` is
same world and is identified by `integral_nested_self_eq_mediationFormula` (hypotheses `hrandD`,
`hintD`); only the cross world mean `E[Y (!a') (M a')]` uses the hypotheses of
`integral_nested_eq_mediationFormula` for the treatment `!a'`, required for the mediator values
`m` with `P(M a' = m) > 0`. -/
theorem nde_eq_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ] {a' : Bool}
    (hA : Measurable P.A) (hM : ∀ a, Measurable (P.M a))
    (hrandD : IndepFun (P.nested a' a') P.A μ) (hintD : Integrable (P.nested a' a') μ)
    (hY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y (!a') m) μ)
    (hrandY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y (!a') m) P.A μ)
    (hrandM : IndepFun (P.M a') P.A μ)
    (hmed : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y (!a') m) (P.M (!a')) μ[|P.A ⁻¹' {!a'}])
    (hcross : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y (!a') m) (P.M a') μ)
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → μ (P.A ⁻¹' {!a'} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nde μ a' = P.mediationFormula μ true a' - P.mediationFormula μ false a' := by
  cases a' <;> simp only [Bool.not_false, Bool.not_true] at hY hrandY hmed hcross hpos
  · rw [nde, integral_sub (P.integrable_nested_of_ne_zero (hM false) hY) hintD,
      P.integral_nested_eq_mediationFormula hA (hM true) (hM false) hY hrandY hrandM hmed hcross
        hposA hpos,
      P.integral_nested_self_eq_mediationFormula hA (hM false) hrandD hintD hposA]
  · rw [nde, integral_sub hintD (P.integrable_nested_of_ne_zero (hM true) hY),
      P.integral_nested_self_eq_mediationFormula hA (hM true) hrandD hintD hposA,
      P.integral_nested_eq_mediationFormula hA (hM false) (hM true) hY hrandY hrandM hmed hcross
        hposA hpos]

/-- Identification of the natural indirect effect `NIE(a)` by the mediation formula:
`NIE(a) = Σ m, E[Yobs | A = a, Mobs = m] (P(Mobs = m | A = 1) - P(Mobs = m | A = 0))`, written
as a difference of two mediation formulas. Of the two nested means, `E[Y a (M a)]` is same world
and is identified by `integral_nested_self_eq_mediationFormula` (hypotheses `hrandD`, `hintD`,
`hposD`); only the cross world mean `E[Y a (M (!a))]` uses the hypotheses of
`integral_nested_eq_mediationFormula` for the mediator world `!a`, required for the mediator
values `m` with `P(M (!a) = m) > 0`. -/
theorem nie_eq_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ] {a : Bool}
    (hA : Measurable P.A) (hM : ∀ a', Measurable (P.M a'))
    (hrandD : IndepFun (P.nested a a) P.A μ) (hintD : Integrable (P.nested a a) μ)
    (hposD : μ (P.A ⁻¹' {a}) ≠ 0)
    (hY : ∀ m, μ (P.M (!a) ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hrandY : ∀ m, μ (P.M (!a) ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) P.A μ)
    (hrandM : IndepFun (P.M (!a)) P.A μ)
    (hmed : ∀ m, μ (P.M (!a) ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hcross : ∀ m, μ (P.M (!a) ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M (!a)) μ)
    (hposA : μ (P.A ⁻¹' {!a}) ≠ 0)
    (hpos : ∀ m, μ (P.M (!a) ⁻¹' {m}) ≠ 0 → μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nie μ a = P.mediationFormula μ a true - P.mediationFormula μ a false := by
  cases a <;> simp only [Bool.not_false, Bool.not_true] at hY hrandY hrandM hmed hcross hposA hpos
  · rw [nie, integral_sub (P.integrable_nested_of_ne_zero (hM true) hY) hintD,
      P.integral_nested_eq_mediationFormula hA (hM false) (hM true) hY hrandY hrandM hmed hcross
        hposA hpos,
      P.integral_nested_self_eq_mediationFormula hA (hM false) hrandD hintD hposD]
  · rw [nie, integral_sub hintD (P.integrable_nested_of_ne_zero (hM false) hY),
      P.integral_nested_self_eq_mediationFormula hA (hM true) hrandD hintD hposD,
      P.integral_nested_eq_mediationFormula hA (hM true) (hM false) hY hrandY hrandM hmed hcross
        hposA hpos]

/-- Identification of the natural direct effect `NDE(a')` by the mediation formula with the
hypotheses of `integral_nested_eq_mediationFormula` imposed on both treatment levels `a` (the
mediator world `a'` fixed), in place of treatment ignorability of the same world nested outcome
used by `nde_eq_mediationFormula`. -/
theorem nde_eq_mediationFormula_of_forall_arms [Fintype 𝓜] [IsProbabilityMeasure μ] {a' : Bool}
    (hA : Measurable P.A) (hM : ∀ a, Measurable (P.M a))
    (hY : ∀ a m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hrandY : ∀ a m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) P.A μ)
    (hrandM : IndepFun (P.M a') P.A μ)
    (hmed : ∀ a m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hcross : ∀ a m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a') μ)
    (hposA : μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ a m, μ (P.M a' ⁻¹' {m}) ≠ 0 → μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nde μ a' = P.mediationFormula μ true a' - P.mediationFormula μ false a' := by
  rw [nde, integral_sub (P.integrable_nested_of_ne_zero (hM a') (hY true))
      (P.integrable_nested_of_ne_zero (hM a') (hY false)),
    P.integral_nested_eq_mediationFormula hA (hM true) (hM a') (hY true) (hrandY true) hrandM
      (hmed true) (hcross true) hposA (hpos true),
    P.integral_nested_eq_mediationFormula hA (hM false) (hM a') (hY false) (hrandY false) hrandM
      (hmed false) (hcross false) hposA (hpos false)]

/-- Identification of the natural indirect effect `NIE(a)` by the mediation formula with the
hypotheses of `integral_nested_eq_mediationFormula` imposed on both mediator worlds `a'` (the
treatment `a` fixed), in place of treatment ignorability of the same world nested outcome used
by `nie_eq_mediationFormula`. -/
theorem nie_eq_mediationFormula_of_forall_worlds [Fintype 𝓜] [IsProbabilityMeasure μ] {a : Bool}
    (hA : Measurable P.A) (hM : ∀ a', Measurable (P.M a'))
    (hY : ∀ a' m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hrandY : ∀ a' m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) P.A μ)
    (hrandM : ∀ a', IndepFun (P.M a') P.A μ)
    (hmed : ∀ a' m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a) μ[|P.A ⁻¹' {a}])
    (hcross : ∀ a' m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a') μ)
    (hposA : ∀ a', μ (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ a' m, μ (P.M a' ⁻¹' {m}) ≠ 0 → μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nie μ a = P.mediationFormula μ a true - P.mediationFormula μ a false := by
  rw [nie, integral_sub (P.integrable_nested_of_ne_zero (hM true) (hY true))
      (P.integrable_nested_of_ne_zero (hM false) (hY false)),
    P.integral_nested_eq_mediationFormula hA (hM a) (hM true) (hY true) (hrandY true)
      (hrandM true) (hmed true) (hcross true) (hposA true) (hpos true),
    P.integral_nested_eq_mediationFormula hA (hM a) (hM false) (hY false) (hrandY false)
      (hrandM false) (hmed false) (hcross false) (hposA false) (hpos false)]

/-! ### Natural and interventional effects -/

/-- Under cross world independence `Y a m ⫫ M 0` for both treatment levels `a`, the pure natural
direct effect equals the interventional direct effect: `NDE(0) = interventionalDirect`. -/
theorem nde_false_eq_interventionalDirect [Fintype 𝓜] [IsProbabilityMeasure μ]
    (hM : Measurable (P.M false))
    (hY : ∀ a m, μ (P.M false ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hcross : ∀ a m, μ (P.M false ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M false) μ) :
    P.nde μ false = P.interventionalDirect μ := by
  rw [nde, integral_sub (P.integrable_nested_of_ne_zero hM (hY true))
      (P.integrable_nested_of_ne_zero hM (hY false)),
    P.integral_nested_eq_interventionalMean hM (hY true) (hcross true),
    P.integral_nested_eq_interventionalMean hM (hY false) (hcross false), interventionalDirect]

/-- Under cross world independence `Y 1 m ⫫ M a'` for both mediator worlds `a'`, the total
natural indirect effect equals the interventional indirect effect:
`NIE(1) = interventionalIndirect`. -/
theorem nie_true_eq_interventionalIndirect [Fintype 𝓜] [IsProbabilityMeasure μ]
    (hM : ∀ a', Measurable (P.M a'))
    (hY : ∀ a' m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y true m) μ)
    (hcross : ∀ a' m, μ (P.M a' ⁻¹' {m}) ≠ 0 → IndepFun (P.Y true m) (P.M a') μ) :
    P.nie μ true = P.interventionalIndirect μ := by
  rw [nie, integral_sub (P.integrable_nested_of_ne_zero (hM true) (hY true))
      (P.integrable_nested_of_ne_zero (hM false) (hY false)),
    P.integral_nested_eq_interventionalMean (hM true) (hY true) (hcross true),
    P.integral_nested_eq_interventionalMean (hM false) (hY false) (hcross false),
    interventionalIndirect]

/-- Under the independence `Y a m ⫫ M a` for both treatment levels `a`, the total effect equals
the interventional overall effect: `TE = interventionalTotal`. -/
theorem te_eq_interventionalTotal [Fintype 𝓜] [IsProbabilityMeasure μ]
    (hM : ∀ a, Measurable (P.M a))
    (hY : ∀ a m, μ (P.M a ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hcross : ∀ a m, μ (P.M a ⁻¹' {m}) ≠ 0 → IndepFun (P.Y a m) (P.M a) μ) :
    P.te μ = P.interventionalTotal μ := by
  rw [te, integral_sub (P.integrable_nested_of_ne_zero (hM true) (hY true))
      (P.integrable_nested_of_ne_zero (hM false) (hY false)),
    P.integral_nested_eq_interventionalMean (hM true) (hY true) (hcross true),
    P.integral_nested_eq_interventionalMean (hM false) (hY false) (hcross false),
    interventionalTotal]

/-! ### Dependence on the observed law -/

/-- The mediation formula depends on `μ` only through the observed law of `(A, Mobs, Yobs)`,
provided this triple is almost everywhere measurable: it equals `observedMediationFormula` of
the pushforward of `μ` by the triple. -/
theorem mediationFormula_eq_observedMediationFormula [Fintype 𝓜] (a a' : Bool)
    (hobs : AEMeasurable (fun ω => (P.A ω, P.Mobs ω, P.Yobs ω)) μ) :
    P.mediationFormula μ a a' =
      observedMediationFormula (μ.map fun ω => (P.A ω, P.Mobs ω, P.Yobs ω)) a a' := by
  set g : Ω → Bool × 𝓜 × ℝ := fun ω => (P.A ω, P.Mobs ω, P.Yobs ω) with hg
  refine Finset.sum_congr rfl fun m _ => ?_
  have hS1 : MeasurableSet ({a} ×ˢ {m} ×ˢ Set.univ : Set (Bool × 𝓜 × ℝ)) :=
    (measurableSet_singleton a).prod ((measurableSet_singleton m).prod MeasurableSet.univ)
  have hS2 : MeasurableSet ({a'} ×ˢ Set.univ : Set (Bool × 𝓜 × ℝ)) :=
    (measurableSet_singleton a').prod MeasurableSet.univ
  have hS3 : MeasurableSet (Set.univ ×ˢ {m} ×ˢ Set.univ : Set (Bool × 𝓜 × ℝ)) :=
    MeasurableSet.univ.prod ((measurableSet_singleton m).prod MeasurableSet.univ)
  have hpre1 : g ⁻¹' ({a} ×ˢ {m} ×ˢ Set.univ) = P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m} := by
    ext ω
    simp [g]
  have hpre2 : g ⁻¹' ({a'} ×ˢ Set.univ) = P.A ⁻¹' {a'} := by
    ext ω
    simp [g]
  have hpre3 : g ⁻¹' (Set.univ ×ˢ {m} ×ˢ Set.univ) = P.Mobs ⁻¹' {m} := by
    ext ω
    simp [g]
  have hnull : NullMeasurableSet (P.A ⁻¹' {a'}) μ := hpre2 ▸ hobs.nullMeasurable hS2
  congr 1
  · rw [condMean_eq, condMean_eq, measureReal_def, measureReal_def,
      Measure.map_apply_of_aemeasurable hobs hS1, hpre1,
      setIntegral_map hS1 measurable_snd.snd.aestronglyMeasurable hobs, hpre1]
  · rw [measureReal_def, measureReal_def, ProbabilityTheory.cond, ProbabilityTheory.cond,
      smul_apply, smul_apply, Measure.restrict_apply₀' hnull,
      Measure.restrict_apply hS3, Measure.map_apply_of_aemeasurable hobs hS2,
      Measure.map_apply_of_aemeasurable hobs (hS3.inter hS2), Set.preimage_inter, hpre2, hpre3]

/-- Two mediation models with almost everywhere measurable observed triples and the same
observed law of `(A, Mobs, Yobs)` have the same mediation formula. -/
theorem mediationFormula_eq_of_map_eq [Fintype 𝓜] {Ω' : Type*} [MeasurableSpace Ω']
    (Q : MediationModel Ω' 𝓜) {μ' : Measure Ω'} (a a' : Bool)
    (hP : AEMeasurable (fun ω => (P.A ω, P.Mobs ω, P.Yobs ω)) μ)
    (hQ : AEMeasurable (fun ω => (Q.A ω, Q.Mobs ω, Q.Yobs ω)) μ')
    (h : μ.map (fun ω => (P.A ω, P.Mobs ω, P.Yobs ω)) =
      μ'.map (fun ω => (Q.A ω, Q.Mobs ω, Q.Yobs ω))) :
    P.mediationFormula μ a a' = Q.mediationFormula μ' a a' := by
  rw [P.mediationFormula_eq_observedMediationFormula a a' hP,
    Q.mediationFormula_eq_observedMediationFormula a a' hQ, h]

/-! ### A finite covariate -/

/-- Conditioning the mediation formula on a measurable event `s` gives the flat form
`Σ m, E[Yobs | s, A = a, Mobs = m] P(Mobs = m | s, A = a')`. -/
theorem mediationFormula_cond_eq [Fintype 𝓜] [IsProbabilityMeasure μ] {s : Set Ω} {a a' : Bool}
    (hs : MeasurableSet s) (hA : Measurable P.A) (hMa : Measurable (P.M a)) :
    P.mediationFormula μ[|s] a a' =
      ∑ m, condMean μ (s ∩ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m})) P.Yobs *
        (μ[|s ∩ P.A ⁻¹' {a'}]).real (P.Mobs ⁻¹' {m}) := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [P.A_inter_Mobs_eq a m, condMean_cond_eq_condMean_inter hs
      ((hA (measurableSet_singleton a)).inter (hMa (measurableSet_singleton m))),
    cond_cond_eq_cond_inter hs (hA (measurableSet_singleton a')) μ]

/-- The mediation formula with a finite covariate `C`. Assume that every `Y a m` with
`P(M a' = m) > 0` is integrable under `μ`, and that for every covariate value `c` with
`P(C = c) > 0` the hypotheses of `integral_nested_eq_mediationFormula` hold under the conditioned
measure `μ[|C = c]`: treatment ignorability for `M a'`, `P(A = a' | C = c) > 0` and, for every
`m` with `P(M a' = m | C = c) > 0`, treatment ignorability for `Y a m`, mediator ignorability
`Y a m ⫫ M a` given `A = a`, the cross world independence `Y a m ⫫ M a'` and positivity of the
cell `A = a, Mobs = m`. Then
`E[Y a (M a')] = Σ c, P(C = c) Σ m, E[Yobs | C = c, A = a, Mobs = m] P(Mobs = m | C = c, A = a')`,
where the inner sum is `mediationFormula` under `μ[|C = c]` (written in this flat form by
`mediationFormula_cond_eq`). -/
theorem integral_nested_eq_sum_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ]
    {𝓒 : Type*} [Fintype 𝓒] [MeasurableSpace 𝓒] [MeasurableSingletonClass 𝓒] {a a' : Bool}
    (C : Ω → 𝓒) (hC : Measurable C) (hA : Measurable P.A) (hMa : Measurable (P.M a))
    (hMa' : Measurable (P.M a')) (hY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hrandY : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y a m) P.A μ[|C ⁻¹' {c}])
    (hrandM : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → IndepFun (P.M a') P.A μ[|C ⁻¹' {c}])
    (hmed : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y a m) (P.M a) μ[|C ⁻¹' {c}][|P.A ⁻¹' {a}])
    (hcross : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y a m) (P.M a') μ[|C ⁻¹' {c}])
    (hposA : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → μ[|C ⁻¹' {c}] (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      μ[|C ⁻¹' {c}] (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    ∫ ω, P.nested a a' ω ∂μ =
      ∑ c, μ.real (C ⁻¹' {c}) * P.mediationFormula μ[|C ⁻¹' {c}] a a' := by
  rw [integral_eq_sum_condMean hC (P.integrable_nested_of_ne_zero hMa' hY)]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : μ (C ⁻¹' {c}) = 0
  · simp [measureReal_def, hc]
  · have : IsProbabilityMeasure μ[|C ⁻¹' {c}] := cond_isProbabilityMeasure hc
    have hYc : ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ[|C ⁻¹' {c}] :=
      fun m hm => integrable_cond_of_integrable (hY m fun h => hm (cond_absolutelyContinuous h)) hc
    rw [condMean, P.integral_nested_eq_mediationFormula hA hMa hMa' hYc (hrandY c hc)
      (hrandM c hc) (hmed c hc) (hcross c hc) (hposA c hc) (hpos c hc)]

/-- Identification of the controlled direct effect with a finite covariate `C`, under single
world assumptions holding within each covariate value `c` with `P(C = c) > 0`: treatment
ignorability `Y a m ⫫ A` and mediator ignorability `Y a m ⫫ M a` given `A = a` under
`μ[|C = c]`, and positivity of the cells `C = c, A = a, Mobs = m`, for both `a`. Then
`CDE(m) = Σ c, P(C = c) (E[Yobs | C = c, A = 1, Mobs = m] - E[Yobs | C = c, A = 0, Mobs = m])`. -/
theorem cde_eq_sum_condMean_sub [IsProbabilityMeasure μ] {𝓒 : Type*} [Fintype 𝓒]
    [MeasurableSpace 𝓒] [MeasurableSingletonClass 𝓒] {m : 𝓜} (C : Ω → 𝓒) (hC : Measurable C)
    (hA : Measurable P.A) (hM : ∀ a, Measurable (P.M a)) (hY : ∀ a, Integrable (P.Y a m) μ)
    (hrandY : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ a, IndepFun (P.Y a m) P.A μ[|C ⁻¹' {c}])
    (hmed : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ a,
      IndepFun (P.Y a m) (P.M a) μ[|C ⁻¹' {c}][|P.A ⁻¹' {a}])
    (hpos : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ a,
      μ (C ⁻¹' {c} ∩ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m})) ≠ 0) :
    P.cde μ m = ∑ c, μ.real (C ⁻¹' {c}) *
      (condMean μ (C ⁻¹' {c} ∩ (P.A ⁻¹' {true} ∩ P.Mobs ⁻¹' {m})) P.Yobs -
        condMean μ (C ⁻¹' {c} ∩ (P.A ⁻¹' {false} ∩ P.Mobs ⁻¹' {m})) P.Yobs) := by
  rw [cde, integral_eq_sum_condMean (f := fun ω => P.Y true m ω - P.Y false m ω) hC
    ((hY true).sub (hY false))]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : μ (C ⁻¹' {c}) = 0
  · simp [measureReal_def, hc]
  · have hSc : MeasurableSet (C ⁻¹' {c}) := hC (measurableSet_singleton c)
    have : IsProbabilityMeasure μ[|C ⁻¹' {c}] := cond_isProbabilityMeasure hc
    have hcell : ∀ a, MeasurableSet (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) := fun a => by
      rw [P.A_inter_Mobs_eq]
      exact (hA (measurableSet_singleton a)).inter (hM a (measurableSet_singleton m))
    have h := P.cde_eq_condMean_sub (μ := μ[|C ⁻¹' {c}]) hA hM
      (fun a => integrable_cond_of_integrable (hY a) hc) (hrandY c hc) (hmed c hc)
      (fun a => by
        rw [cond_apply hSc]
        exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hpos c hc a))
    rw [condMean_cond_eq_condMean_inter hSc (hcell true),
      condMean_cond_eq_condMean_inter hSc (hcell false)] at h
    rw [← h]
    rfl

/-- Identification of the natural direct effect `NDE(a')` with a finite covariate `C`:
`NDE(a') = Σ c, P(C = c) (mediationFormula μ[|C = c] 1 a' - mediationFormula μ[|C = c] 0 a')`.
The global hypotheses are integrability of `Y a' (M a')` and of every `Y (!a') m` with
`P(M a' = m) > 0`; for every `c` with `P(C = c) > 0` the hypotheses of
`nde_eq_mediationFormula` hold under `μ[|C = c]`, the mediator conditions being required for
the values `m` with `P(M a' = m | C = c) > 0`. -/
theorem nde_eq_sum_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ] {𝓒 : Type*}
    [Fintype 𝓒] [MeasurableSpace 𝓒] [MeasurableSingletonClass 𝓒] {a' : Bool} (C : Ω → 𝓒)
    (hC : Measurable C) (hA : Measurable P.A) (hM : ∀ a, Measurable (P.M a))
    (hintD : Integrable (P.nested a' a') μ)
    (hY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y (!a') m) μ)
    (hrandD : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → IndepFun (P.nested a' a') P.A μ[|C ⁻¹' {c}])
    (hrandY : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y (!a') m) P.A μ[|C ⁻¹' {c}])
    (hrandM : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → IndepFun (P.M a') P.A μ[|C ⁻¹' {c}])
    (hmed : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y (!a') m) (P.M (!a')) μ[|C ⁻¹' {c}][|P.A ⁻¹' {!a'}])
    (hcross : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y (!a') m) (P.M a') μ[|C ⁻¹' {c}])
    (hposA : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → μ[|C ⁻¹' {c}] (P.A ⁻¹' {a'}) ≠ 0)
    (hpos : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M a' ⁻¹' {m}) ≠ 0 →
      μ[|C ⁻¹' {c}] (P.A ⁻¹' {!a'} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nde μ a' = ∑ c, μ.real (C ⁻¹' {c}) *
      (P.mediationFormula μ[|C ⁻¹' {c}] true a' - P.mediationFormula μ[|C ⁻¹' {c}] false a') := by
  have hint : Integrable (fun ω => P.nested true a' ω - P.nested false a' ω) μ := by
    have hoff := P.integrable_nested_of_ne_zero (hM a') hY
    cases a' <;> simp only [Bool.not_false, Bool.not_true] at hoff
    exacts [hoff.sub hintD, hintD.sub hoff]
  rw [nde, integral_eq_sum_condMean (f := fun ω => P.nested true a' ω - P.nested false a' ω) hC
    hint]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : μ (C ⁻¹' {c}) = 0
  · simp [measureReal_def, hc]
  · have : IsProbabilityMeasure μ[|C ⁻¹' {c}] := cond_isProbabilityMeasure hc
    rw [← P.nde_eq_mediationFormula (μ := μ[|C ⁻¹' {c}]) hA hM (hrandD c hc)
      (integrable_cond_of_integrable hintD hc)
      (fun m hm => integrable_cond_of_integrable (hY m fun h => hm (cond_absolutelyContinuous h))
        hc)
      (hrandY c hc) (hrandM c hc) (hmed c hc) (hcross c hc) (hposA c hc) (hpos c hc)]
    rfl

/-- Identification of the natural indirect effect `NIE(a)` with a finite covariate `C`:
`NIE(a) = Σ c, P(C = c) (mediationFormula μ[|C = c] a 1 - mediationFormula μ[|C = c] a 0)`.
The global hypotheses are integrability of `Y a (M a)` and of every `Y a m` with
`P(M (!a) = m) > 0`; for every `c` with `P(C = c) > 0` the hypotheses of
`nie_eq_mediationFormula` hold under `μ[|C = c]`, the mediator conditions being required for
the values `m` with `P(M (!a) = m | C = c) > 0`. -/
theorem nie_eq_sum_mediationFormula [Fintype 𝓜] [IsProbabilityMeasure μ] {𝓒 : Type*}
    [Fintype 𝓒] [MeasurableSpace 𝓒] [MeasurableSingletonClass 𝓒] {a : Bool} (C : Ω → 𝓒)
    (hC : Measurable C) (hA : Measurable P.A) (hM : ∀ a', Measurable (P.M a'))
    (hintD : Integrable (P.nested a a) μ)
    (hY : ∀ m, μ (P.M (!a) ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ)
    (hrandD : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → IndepFun (P.nested a a) P.A μ[|C ⁻¹' {c}])
    (hposD : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → μ[|C ⁻¹' {c}] (P.A ⁻¹' {a}) ≠ 0)
    (hrandY : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M (!a) ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y a m) P.A μ[|C ⁻¹' {c}])
    (hrandM : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → IndepFun (P.M (!a)) P.A μ[|C ⁻¹' {c}])
    (hmed : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M (!a) ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y a m) (P.M a) μ[|C ⁻¹' {c}][|P.A ⁻¹' {a}])
    (hcross : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M (!a) ⁻¹' {m}) ≠ 0 →
      IndepFun (P.Y a m) (P.M (!a)) μ[|C ⁻¹' {c}])
    (hposA : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → μ[|C ⁻¹' {c}] (P.A ⁻¹' {!a}) ≠ 0)
    (hpos : ∀ c, μ (C ⁻¹' {c}) ≠ 0 → ∀ m, μ[|C ⁻¹' {c}] (P.M (!a) ⁻¹' {m}) ≠ 0 →
      μ[|C ⁻¹' {c}] (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m}) ≠ 0) :
    P.nie μ a = ∑ c, μ.real (C ⁻¹' {c}) *
      (P.mediationFormula μ[|C ⁻¹' {c}] a true - P.mediationFormula μ[|C ⁻¹' {c}] a false) := by
  have hint : Integrable (fun ω => P.nested a true ω - P.nested a false ω) μ := by
    have hoff := P.integrable_nested_of_ne_zero (hM (!a)) hY
    cases a <;> simp only [Bool.not_false, Bool.not_true] at hoff
    exacts [hoff.sub hintD, hintD.sub hoff]
  rw [nie, integral_eq_sum_condMean (f := fun ω => P.nested a true ω - P.nested a false ω) hC
    hint]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : μ (C ⁻¹' {c}) = 0
  · simp [measureReal_def, hc]
  · have : IsProbabilityMeasure μ[|C ⁻¹' {c}] := cond_isProbabilityMeasure hc
    rw [← P.nie_eq_mediationFormula (μ := μ[|C ⁻¹' {c}]) hA hM (hrandD c hc)
      (integrable_cond_of_integrable hintD hc) (hposD c hc)
      (fun m hm => integrable_cond_of_integrable (hY m fun h => hm (cond_absolutelyContinuous h))
        hc)
      (hrandY c hc) (hrandM c hc) (hmed c hc) (hcross c hc) (hposA c hc) (hpos c hc)]
    rfl

end MediationModel

end Mediation

end CausalInference
