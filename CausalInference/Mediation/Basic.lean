/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Integration

/-!
# Mediation: potential outcomes and effect definitions

We fix a binary treatment `A : Ω → Bool` (`false` is control, `true` is treatment), mediator
potential outcomes `M a : Ω → 𝓜` and joint potential outcomes `Y a m : Ω → ℝ`. The nested
(cross world) potential outcome is `Y a (M a') ω = Y a (M a' ω) ω`.

The observed mediator and outcome are *defined* as `Mobs ω = M (A ω) ω` and
`Yobs ω = Y (A ω) (Mobs ω) ω`. Consistency and composition are therefore built into the
definitions rather than assumed as separate hypotheses.

## Main definitions

* `CausalInference.Mediation.MediationModel`: the triple `(A, M, Y)`.
* `MediationModel.cde`: controlled direct effect `E[Y 1 m - Y 0 m]`.
* `MediationModel.te`: total effect `E[Y 1 (M 1) - Y 0 (M 0)]`.
* `MediationModel.nde`: natural direct effect `E[Y 1 (M a') - Y 0 (M a')]`.
* `MediationModel.nie`: natural indirect effect `E[Y a (M 1) - Y a (M 0)]`.
* `CausalInference.Mediation.condMean`: the mean of `f` under `μ` conditioned on an event.

## Main results

* `MediationModel.nested_eq_sum`: for a finite mediator, the nested outcome is the sum over
  mediator values of `Y a m` restricted to the event `M a' = m`.
* `MediationModel.integrable_nested`: integrability of the nested outcome from integrability of
  every `Y a m`; `MediationModel.integrable_nested_of_ne_zero` needs it only for the mediator
  values `m` with `P(M a' = m) > 0`.

The effects `cde`, `te`, `nde` and `nie` are defined for an arbitrary measure, but they are means
of potential outcomes only under a probability measure. Every theorem of the library that
interprets them assumes `[IsProbabilityMeasure μ]`.

Sources: J. M. Robins and S. Greenland (1992), Identifiability and exchangeability for direct and
indirect effects; J. Pearl (2001), Direct and indirect effects; T. J. VanderWeele (2015),
Explanation in Causal Inference.
-/

@[expose] public section

namespace CausalInference

namespace Mediation

open MeasureTheory ProbabilityTheory

/-- A mediation model on a sample space `Ω` with mediator space `𝓜`: a binary treatment `A`,
mediator potential outcomes `M a` and joint potential outcomes `Y a m`. No assumption is attached
to the structure; every assumption is a hypothesis of the theorem that needs it. -/
structure MediationModel (Ω 𝓜 : Type*) where
  /-- The observed binary treatment. -/
  A : Ω → Bool
  /-- The mediator potential outcome `M a` under treatment `a`. -/
  M : Bool → Ω → 𝓜
  /-- The outcome potential outcome `Y a m` under treatment `a` and mediator value `m`. -/
  Y : Bool → 𝓜 → Ω → ℝ

/-- The mean of `f` under `μ` conditioned on the event `s`, that is `∫ f ∂μ[|s]`. The value is
a conditional mean only when `s` is measurable with `0 < μ s < ∞` and `f` is integrable on `s`.
When `μ s = 0` (or `μ s = ∞`) the conditioned measure is zero and this value is `0`. Every theorem
of the library that interprets `condMean μ s f` assumes a finite measure (in fact a probability
measure), a measurable event `s`, and positivity of `s` whenever the conditional mean enters
with a nonzero weight, so this convention never carries a result. -/
noncomputable def condMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set Ω)
    (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω ∂μ[|s]

/-- The conditional mean is the restricted integral divided by the probability of the event. -/
theorem condMean_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set Ω) (f : Ω → ℝ) :
    condMean μ s f = (μ.real s)⁻¹ * ∫ ω in s, f ω ∂μ := by
  rw [condMean, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    measureReal_def]

namespace MediationModel

variable {Ω 𝓜 : Type*} (P : MediationModel Ω 𝓜)

/-- The nested potential outcome `Y a (M a')`: the outcome under treatment `a` with the mediator
set to the value it would take under treatment `a'`. It is cross world when `a ≠ a'`. -/
def nested (a a' : Bool) (ω : Ω) : ℝ :=
  P.Y a (P.M a' ω) ω

/-- The observed mediator `M A`. -/
def Mobs (ω : Ω) : 𝓜 :=
  P.M (P.A ω) ω

/-- The observed outcome `Y A (M A)`. -/
def Yobs (ω : Ω) : ℝ :=
  P.Y (P.A ω) (P.Mobs ω) ω

theorem Mobs_of_A_eq {a : Bool} {ω : Ω} (h : P.A ω = a) : P.Mobs ω = P.M a ω := by
  simp [Mobs, h]

theorem Yobs_of_A_eq {a : Bool} {ω : Ω} (h : P.A ω = a) : P.Yobs ω = P.nested a a ω := by
  simp [Yobs, Mobs, nested, h]

/-- On the event `A = a`, `Mobs = m` the observed outcome equals `Y a m`. -/
theorem Yobs_of_A_eq_of_Mobs_eq {a : Bool} {m : 𝓜} {ω : Ω} (h : P.A ω = a)
    (hm : P.Mobs ω = m) : P.Yobs ω = P.Y a m ω := by
  simp only [Yobs, hm, h]

/-- The events `A = a, Mobs = m` and `A = a, M a = m` coincide. -/
theorem A_inter_Mobs_eq (a : Bool) (m : 𝓜) :
    P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {m} = P.A ⁻¹' {a} ∩ P.M a ⁻¹' {m} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hm⟩
    exact ⟨h, by rw [← P.Mobs_of_A_eq h, hm]⟩
  · rintro ⟨h, hm⟩
    exact ⟨h, by rw [P.Mobs_of_A_eq h, hm]⟩

/-- For a finite mediator, the nested outcome `Y a (M a')` is the sum over mediator values `m`
of `Y a m` restricted to the event `M a' = m`. -/
theorem nested_eq_sum [Fintype 𝓜] (a a' : Bool) (ω : Ω) :
    P.nested a a' ω = ∑ m, (P.M a' ⁻¹' {m}).indicator (P.Y a m) ω := by
  rw [Finset.sum_eq_single (P.M a' ω)]
  · simp [nested]
  · intro m _ hm
    exact Set.indicator_of_notMem (fun h => hm (Eq.symm h)) _
  · intro h
    exact absurd (Finset.mem_univ _) h

variable [MeasurableSpace Ω]

/-- The controlled direct effect `CDE(m) = E[Y 1 m - Y 0 m]`. It is a causal mean only when `μ`
is a probability measure; every theorem that interprets it assumes so. -/
noncomputable def cde (μ : Measure Ω) (m : 𝓜) : ℝ :=
  ∫ ω, P.Y true m ω - P.Y false m ω ∂μ

/-- The total effect `TE = E[Y 1 (M 1) - Y 0 (M 0)]`. It is a causal mean only when `μ` is a
probability measure; every theorem that interprets it assumes so. -/
noncomputable def te (μ : Measure Ω) : ℝ :=
  ∫ ω, P.nested true true ω - P.nested false false ω ∂μ

/-- The natural direct effect `NDE(a') = E[Y 1 (M a') - Y 0 (M a')]`, with the mediator held at
its value under `a'`. `nde μ false` is the pure natural direct effect and `nde μ true` the total
natural direct effect. It is a causal mean only when `μ` is a probability measure; every theorem
that interprets it assumes so. -/
noncomputable def nde (μ : Measure Ω) (a' : Bool) : ℝ :=
  ∫ ω, P.nested true a' ω - P.nested false a' ω ∂μ

/-- The natural indirect effect `NIE(a) = E[Y a (M 1) - Y a (M 0)]`, with the treatment held at
`a`. `nie μ true` is the total natural indirect effect and `nie μ false` the pure one. It is a
causal mean only when `μ` is a probability measure; every theorem that interprets it assumes
so. -/
noncomputable def nie (μ : Measure Ω) (a : Bool) : ℝ :=
  ∫ ω, P.nested a true ω - P.nested a false ω ∂μ

/-- For a finite mediator with measurable `M a'`, the nested outcome `Y a (M a')` is integrable
when every `Y a m` is. -/
theorem integrable_nested [Finite 𝓜] [MeasurableSpace 𝓜] [MeasurableSingletonClass 𝓜]
    {μ : Measure Ω} {a a' : Bool} (hM : Measurable (P.M a'))
    (hY : ∀ m, Integrable (P.Y a m) μ) : Integrable (P.nested a a') μ := by
  have := Fintype.ofFinite 𝓜
  have h : P.nested a a' = fun ω => ∑ m, (P.M a' ⁻¹' {m}).indicator (P.Y a m) ω :=
    funext (P.nested_eq_sum a a')
  rw [h]
  exact integrable_finsetSum _ fun m _ => (hY m).indicator (hM (measurableSet_singleton m))

/-- The restriction of `Y a m` to the fiber `M a' = m` is integrable when `Y a m` is integrable
or the fiber is null. -/
theorem integrable_indicator_of_ne_zero [MeasurableSpace 𝓜] [MeasurableSingletonClass 𝓜]
    {μ : Measure Ω} {a a' : Bool} {m : 𝓜} (hM : Measurable (P.M a'))
    (hY : μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ) :
    Integrable ((P.M a' ⁻¹' {m}).indicator (P.Y a m)) μ := by
  have hS : MeasurableSet (P.M a' ⁻¹' {m}) := hM (measurableSet_singleton m)
  by_cases hm : μ (P.M a' ⁻¹' {m}) = 0
  · refine (integrable_indicator_iff hS).mpr ?_
    rw [IntegrableOn, Measure.restrict_eq_zero.mpr hm]
    exact integrable_zero_measure
  · exact (hY hm).indicator hS

/-- For a finite mediator with measurable `M a'`, the nested outcome `Y a (M a')` is integrable
when `Y a m` is integrable for every mediator value `m` with `P(M a' = m) > 0`: on a null fiber
of `M a'` the nested outcome vanishes almost everywhere. -/
theorem integrable_nested_of_ne_zero [Finite 𝓜] [MeasurableSpace 𝓜]
    [MeasurableSingletonClass 𝓜] {μ : Measure Ω} {a a' : Bool} (hM : Measurable (P.M a'))
    (hY : ∀ m, μ (P.M a' ⁻¹' {m}) ≠ 0 → Integrable (P.Y a m) μ) :
    Integrable (P.nested a a') μ := by
  have := Fintype.ofFinite 𝓜
  have h : P.nested a a' = fun ω => ∑ m, (P.M a' ⁻¹' {m}).indicator (P.Y a m) ω :=
    funext (P.nested_eq_sum a a')
  rw [h]
  exact integrable_finsetSum _ fun m _ => P.integrable_indicator_of_ne_zero hM (hY m)

end MediationModel

end Mediation

end CausalInference
