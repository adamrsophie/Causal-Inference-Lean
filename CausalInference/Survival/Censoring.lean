/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Discrete-time survival under censoring: identification by the product-limit functional

An event time `T : Ω → ℕ` and a censoring time `C : Ω → ℕ` on a probability space. Only the
observed data `(min T C, 1{T ≤ C})` are available: the follow-up time and the indicator that
the event was observed. An individual is at risk and uncensored at time `k` when
`T ≥ k` and `C ≥ k`; an event at time `k` is observed when `T = k ≤ C`.

## Main definitions

* `observed T C`: the observed-data map `ω ↦ (min (T ω) (C ω), decide (T ω ≤ C ω))`.
* `observedHazard ν k`: for a law `ν` of the observed data, the proportion of observed events
  at `k` among those with follow-up time at least `k`.
* `productLimit ν k = ∏_{m = 0}^{k} (1 - observedHazard ν m)`: the product-limit
  (Kaplan-Meier) functional. It depends on the observed-data law `ν` only.

## Main results

* `hazard_eq_of_indepFun`: under independent censoring (`T` independent of `C`), the hazard
  among those at risk and uncensored equals the true hazard:
  `P(T = k | T ≥ k, C ≥ k) = h k` whenever `P(T ≥ k, C ≥ k) > 0`.
* `productLimit_map_observed_eq_survival_of_hazard_eq`: if the hazard among those at risk and
  uncensored equals the true hazard, `P(T = m | T ≥ m, C ≥ m) = P(T = m | T ≥ m)`, at every
  `m ≤ k`, then the product-limit functional of the observed-data law equals the survival
  `P(T > k)` at every `k` at which the at-risk probability `P(min T C ≥ k)` is positive. This
  is the condition the proof uses.
* `productLimit_map_observed_eq_survival`: the corollary under independent censoring. Both are
  identification of the survival function from the population law of the observed data; they
  say nothing about sampling.
* `measureReal_survivor_uncensored_of_indepFun`: under independent censoring the fraction of
  uncensored survivors is `P(T > k, C ≥ k) = S k * P(C ≥ k)`, not `S k`.

Counterexamples (namespace `CensoringExample`):

* the book's example: `P(T > 1) = 0.9`, a random half of the survivors censored after time
  `1`, `P(T > 2 | T > 1) = 0.9`. The fraction of uncensored survivors at time `2` is `0.405`
  while the survival is `0.81` (`indepModel_uncensoredSurvivors`, `indepModel_survival_two`),
  and the product-limit functional recovers `0.81` (`indepModel_productLimit`).
* dependent censoring: a second model `depModel` with exactly the same observed-data law
  (`map_observed_depModel`) but survival `0.405` at time `2`, so that the product-limit
  functional no longer equals the survival (`depModel_productLimit_ne_survival`), and `T` and
  `C` are not independent there (`not_indepFun_depModel`). Hence without the independence
  assumption the survival function is not identified from the observed-data law
  (`survival_not_identified_without_independence`). The condition that fails is the hazard
  equality at time `2`: `P(T = 2 | T ≥ 2, C ≥ 2) = 1/10` but `h 2 = 11/20`
  (`depModel_hazard_two_ne`).
* loss of risk-set support: two models with `T` independent of `C`, `(T, C) = (2, 1)` and
  `(T, C) = (3, 1)` surely, have the same observed-data law and no one at risk and uncensored
  at time `2`, but survival `0` and `1` at time `2`
  (`survival_not_identified_without_support`). So the positivity hypothesis is needed even
  under independent censoring.

## Source

M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Chapter 17, Section 17.3
(why censoring matters), including the numerical example with `0.405` and `0.81`. Here the
censoring time is a single variable `C` and "uncensored at `m`" means `C ≥ m` (the book's
`C_m = 0`); the book's assumption that censoring is as if randomly assigned is the
independence of `T` and `C`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace Survival

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The observed data: the follow-up time `min T C` and the indicator `1{T ≤ C}` that the
event was observed (an event at the censoring time counts as observed). -/
def observed (T C : Ω → ℕ) (ω : Ω) : ℕ × Bool :=
  (min (T ω) (C ω), decide (T ω ≤ C ω))

/-- The observed hazard at `k` of a law `ν` of the observed data `(X, Δ)`: the probability of
an observed event at `k` among those with follow-up time at least `k`,
`ν(X = k, Δ = true) / ν(X ≥ k)`. It is a conditional probability only when
`ν(X ≥ k) > 0`. -/
noncomputable def observedHazard (ν : Measure (ℕ × Bool)) (k : ℕ) : ℝ :=
  ν.real {x | x.1 = k ∧ x.2 = true} / ν.real {x | k ≤ x.1}

/-- The product-limit (Kaplan-Meier) functional of a law `ν` of the observed data:
`∏_{m = 0}^{k} (1 - observedHazard ν m)`. -/
noncomputable def productLimit (ν : Measure (ℕ × Bool)) (k : ℕ) : ℝ :=
  ∏ m ∈ Finset.range (k + 1), (1 - observedHazard ν m)

variable {μ : Measure Ω} {T C : Ω → ℕ}

theorem measurable_observed (hT : Measurable T) (hC : Measurable C) :
    Measurable (observed T C) :=
  (Measurable.of_discrete (f := fun p : ℕ × ℕ => (min p.1 p.2, decide (p.1 ≤ p.2)))).comp
    (hT.prodMk hC)

/-- Under independence of `T` and `C`, events about `T` and events about `C` multiply. -/
theorem measureReal_and_of_indepFun (hind : IndepFun T C μ) (p q : ℕ → Prop) :
    μ.real {ω | p (T ω) ∧ q (C ω)} = μ.real {ω | p (T ω)} * μ.real {ω | q (C ω)} := by
  have := hind.measure_inter_preimage_eq_mul {x | p x} {x | q x} MeasurableSet.of_discrete
    MeasurableSet.of_discrete
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal this

/-- Independent censoring preserves the hazard: if `T` and `C` are independent and the
at-risk, uncensored event `{T ≥ k, C ≥ k}` has positive probability, then
`P(T = k | T ≥ k, C ≥ k) = P(T = k | T ≥ k) = h k`. -/
theorem hazard_eq_of_indepFun (hind : IndepFun T C μ) (k : ℕ)
    (hk : 0 < μ.real {ω | k ≤ T ω ∧ k ≤ C ω}) :
    μ.real {ω | T ω = k ∧ k ≤ C ω} / μ.real {ω | k ≤ T ω ∧ k ≤ C ω} = hazard μ T k := by
  rw [measureReal_and_of_indepFun hind (· = k) (k ≤ ·),
    measureReal_and_of_indepFun hind (k ≤ ·) (k ≤ ·)] at *
  have hC : 0 < μ.real {ω | k ≤ C ω} :=
    lt_of_le_of_ne measureReal_nonneg fun h => by rw [← h, mul_zero] at hk; exact lt_irrefl _ hk
  rw [mul_div_mul_right _ _ hC.ne']
  rfl

/-- The observed hazard of the law of the observed data is the hazard among those at risk and
uncensored: `observedHazard (law of (min T C, 1{T ≤ C})) k
= P(T = k, C ≥ k) / P(T ≥ k, C ≥ k)`. -/
theorem observedHazard_map_observed (hT : Measurable T) (hC : Measurable C) (k : ℕ) :
    observedHazard (μ.map (observed T C)) k =
      μ.real {ω | T ω = k ∧ k ≤ C ω} / μ.real {ω | k ≤ T ω ∧ k ≤ C ω} := by
  rw [observedHazard, map_measureReal_apply (measurable_observed hT hC)
      MeasurableSet.of_discrete,
    map_measureReal_apply (measurable_observed hT hC) MeasurableSet.of_discrete]
  congr 2 <;> ext ω <;> simp only [observed, Set.mem_preimage, Set.mem_ofPred_eq,
    decide_eq_true_eq] <;> omega

/-- Identification of survival by the product-limit functional, general form: if at every
time `m ≤ k` with `P(T ≥ m, C ≥ m) > 0` the hazard among those at risk and uncensored equals
the true hazard, `P(T = m | T ≥ m, C ≥ m) = P(T = m | T ≥ m)`, and the at-risk probability
`P(min T C ≥ k)` is positive, then the product-limit functional of the observed-data law equals
the survival `P(T > k)`. Positivity at `k` gives positivity at every `m ≤ k`, so the hazard
condition is required, and used, at every `m ≤ k`. Without positivity the conclusion fails
even under independent censoring (`CensoringExample.survival_not_identified_without_support`).
-/
theorem productLimit_map_observed_eq_survival_of_hazard_eq [IsProbabilityMeasure μ]
    (hT : Measurable T) (hC : Measurable C) (k : ℕ)
    (hk : 0 < μ.real {ω | k ≤ T ω ∧ k ≤ C ω})
    (h : ∀ m ≤ k, 0 < μ.real {ω | m ≤ T ω ∧ m ≤ C ω} →
      μ.real {ω | T ω = m ∧ m ≤ C ω} / μ.real {ω | m ≤ T ω ∧ m ≤ C ω} = hazard μ T m) :
    productLimit (μ.map (observed T C)) k = survival μ T k := by
  rw [survival_eq_prod_one_sub_hazard' hT, productLimit]
  refine Finset.prod_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  have hpos : 0 < μ.real {ω | m ≤ T ω ∧ m ≤ C ω} :=
    lt_of_lt_of_le hk (measureReal_mono fun ω (h : k ≤ T ω ∧ k ≤ C ω) =>
      ⟨hmk.trans h.1, hmk.trans h.2⟩)
  rw [observedHazard_map_observed hT hC, h m hmk hpos]

/-- Identification of survival under independent censoring (Hernán and Robins, Section 17.3):
if `T` and `C` are independent then, at every time `k` at which the at-risk probability
`P(min T C ≥ k)` is positive, the product-limit functional of the observed-data law equals the
survival `P(T > k)`. Every factor of the product is one minus a genuine conditional
probability, since `P(min T C ≥ m) ≥ P(min T C ≥ k) > 0` for `m ≤ k`. This is the corollary of
`productLimit_map_observed_eq_survival_of_hazard_eq` through `hazard_eq_of_indepFun`. -/
theorem productLimit_map_observed_eq_survival [IsProbabilityMeasure μ] (hT : Measurable T)
    (hC : Measurable C) (hind : IndepFun T C μ) (k : ℕ)
    (hk : 0 < μ.real {ω | k ≤ T ω ∧ k ≤ C ω}) :
    productLimit (μ.map (observed T C)) k = survival μ T k :=
  productLimit_map_observed_eq_survival_of_hazard_eq hT hC k hk fun m _ hm =>
    hazard_eq_of_indepFun hind m hm

/-- Under independent censoring the fraction of individuals who survived through `k` and were
uncensored through `k` is `P(T > k, C ≥ k) = S k * P(C ≥ k)`. It differs from the survival
`S k` whenever `0 < S k` and `P(C ≥ k) < 1`. -/
theorem measureReal_survivor_uncensored_of_indepFun (hind : IndepFun T C μ) (k : ℕ) :
    μ.real {ω | k < T ω ∧ k ≤ C ω} = survival μ T k * μ.real {ω | k ≤ C ω} :=
  measureReal_and_of_indepFun hind (k < ·) (k ≤ ·)

namespace CensoringExample

open scoped ENNReal

/-- The law of the event time in the book's example: `P(T = 1) = 0.1`, `P(T = 2) = 0.09` and
`P(T = 3) = 0.81`, where `T = 3` stands for survival beyond the end of follow-up at `2`. So
`P(T > 1) = 0.9` and `P(T > 2 | T > 1) = 0.9`. -/
noncomputable def lawT : Measure ℕ :=
  (100 : ℝ≥0∞)⁻¹ • ((10 : ℝ≥0∞) • Measure.dirac 1 + (9 : ℝ≥0∞) • Measure.dirac 2 +
    (81 : ℝ≥0∞) • Measure.dirac 3)

/-- The law of the censoring time in the book's example: nobody is censored at time `1`
(`C ≥ 1`), and half of the population is censored after time `1` (`C = 1`, uncensored at
`1` but not at `2`) while the other half is followed through time `2` (`C = 2`). -/
noncomputable def lawC : Measure ℕ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 1 + Measure.dirac 2)

/-- The book's example (Hernán and Robins, Section 17.3) as a joint law of `(T, C)` on
`ℕ × ℕ`: the product of `lawT` and `lawC`, so that censoring is independent of the event
time. -/
noncomputable def indepModel : Measure (ℕ × ℕ) := lawT.prod lawC

/-- A model with dependent censoring and the same observed-data law as `indepModel`: with
probabilities in units of `1/200`, `(T, C) = (1, 1)` with weight `20`, `(2, 1)` with weight
`90`, `(2, 2)` with weight `9` and `(3, 2)` with weight `81`. Everyone censored after time `1`
has the event at time `2`. -/
noncomputable def depModel : Measure (ℕ × ℕ) :=
  (2 : ℝ≥0∞)⁻¹ • (100 : ℝ≥0∞)⁻¹ • ((20 : ℝ≥0∞) • Measure.dirac (1, 1) +
    (90 : ℝ≥0∞) • Measure.dirac (2, 1) + (9 : ℝ≥0∞) • Measure.dirac (2, 2) +
    (81 : ℝ≥0∞) • Measure.dirac (3, 2))

instance : IsProbabilityMeasure lawT := ⟨by
  simp only [lawT, smul_apply, add_apply, measure_univ, smul_eq_mul, mul_one]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

instance : IsProbabilityMeasure lawC := ⟨by
  simp only [lawC, smul_apply, add_apply, measure_univ, smul_eq_mul]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

instance : IsProbabilityMeasure indepModel := by
  unfold indepModel; infer_instance

instance : IsProbabilityMeasure depModel := ⟨by
  simp only [depModel, smul_apply, add_apply, measure_univ, smul_eq_mul,
    mul_one]
  norm_num
  rw [← mul_assoc, ← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- Censoring is independent of the event time in the book's example. -/
theorem indepFun_indepModel : IndepFun Prod.fst Prod.snd indepModel :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- `indepModel` written as a weighted sum of point masses (weights in units of `1/200`). -/
theorem indepModel_eq : indepModel =
    (2 : ℝ≥0∞)⁻¹ • (100 : ℝ≥0∞)⁻¹ • ((10 : ℝ≥0∞) • Measure.dirac (1, 1) +
      (10 : ℝ≥0∞) • Measure.dirac (1, 2) + (9 : ℝ≥0∞) • Measure.dirac (2, 1) +
      (9 : ℝ≥0∞) • Measure.dirac (2, 2) + (81 : ℝ≥0∞) • Measure.dirac (3, 1) +
      (81 : ℝ≥0∞) • Measure.dirac (3, 2)) := by
  simp only [indepModel, lawT, lawC, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.add_prod, Measure.prod_add, Measure.dirac_prod_dirac, smul_add]
  abel

theorem measurable_observed_fst_snd :
    Measurable (observed (Prod.fst : ℕ × ℕ → ℕ) Prod.snd) :=
  measurable_observed measurable_fst measurable_snd

/-- The two models have the same law of the observed data `(min T C, 1{T ≤ C})`. -/
theorem map_observed_depModel :
    depModel.map (observed Prod.fst Prod.snd) = indepModel.map (observed Prod.fst Prod.snd) := by
  rw [indepModel_eq, depModel]
  ext s hs
  rw [Measure.map_apply measurable_observed_fst_snd hs,
    Measure.map_apply measurable_observed_fst_snd hs]
  simp only [add_apply, smul_apply, Measure.dirac_apply, smul_eq_mul]
  have key : ∀ x, (observed Prod.fst Prod.snd ⁻¹' s).indicator (1 : ℕ × ℕ → ℝ≥0∞) x =
      s.indicator 1 (observed Prod.fst Prod.snd x) := fun _ => rfl
  have h11 : observed Prod.fst Prod.snd ((1, 1) : ℕ × ℕ) = (1, true) := rfl
  have h12 : observed Prod.fst Prod.snd ((1, 2) : ℕ × ℕ) = (1, true) := rfl
  have h21 : observed Prod.fst Prod.snd ((2, 1) : ℕ × ℕ) = (1, false) := rfl
  have h22 : observed Prod.fst Prod.snd ((2, 2) : ℕ × ℕ) = (2, true) := rfl
  have h31 : observed Prod.fst Prod.snd ((3, 1) : ℕ × ℕ) = (1, false) := rfl
  have h32 : observed Prod.fst Prod.snd ((3, 2) : ℕ × ℕ) = (2, false) := rfl
  simp only [key, h11, h12, h21, h22, h31, h32]
  ring

/-- In the book's example the survival at time `2` is `0.81`. -/
theorem indepModel_survival_two : survival indepModel Prod.fst 2 = 81 / 100 := by
  rw [indepModel_eq]
  simp only [survival, smul_add, measureReal_def, add_apply, smul_apply, Measure.dirac_apply,
    Set.indicator, Pi.one_apply,
    Set.mem_ofPred_eq, Nat.not_ofNat_lt_one, ↓reduceIte, smul_eq_mul, mul_zero,
    add_zero, lt_self_iff_false, Nat.lt_add_one, mul_one, zero_add]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-- In the book's example the fraction of individuals who survived and were uncensored through
time `2` is `1 × 0.9 × 0.5 × 0.9 = 0.405`. -/
theorem indepModel_uncensoredSurvivors :
    indepModel.real {p | 2 < p.1 ∧ 2 ≤ p.2} = 81 / 200 := by
  rw [indepModel_eq]
  simp [measureReal_def, add_apply, smul_apply, Measure.dirac_apply, Set.indicator,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-- With dependent censoring the survival at time `2` is `0.405`. -/
theorem depModel_survival_two : survival depModel Prod.fst 2 = 81 / 200 := by
  simp [depModel, survival, measureReal_def, add_apply, smul_apply, Measure.dirac_apply,
    Set.indicator, ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

theorem indepModel_atRisk_two_pos : 0 < indepModel.real {p | 2 ≤ p.1 ∧ 2 ≤ p.2} := by
  rw [indepModel_eq]
  simp only [smul_add, measureReal_def, add_apply, smul_apply, Measure.dirac_apply,
    Set.indicator, Pi.one_apply,
    Set.mem_ofPred_eq, Nat.not_ofNat_le_one, and_self, ↓reduceIte, smul_eq_mul,
    mul_zero, Std.le_refl, and_true, add_zero, and_false, mul_one,
    zero_add, Nat.reduceLeDiff]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

theorem depModel_atRisk_two_pos : 0 < depModel.real {p | 2 ≤ p.1 ∧ 2 ≤ p.2} := by
  simp only [depModel, smul_add, measureReal_def, add_apply, smul_apply, Measure.dirac_apply,
    Set.indicator, Pi.one_apply,
    Set.mem_ofPred_eq, Nat.not_ofNat_le_one, and_self, ↓reduceIte, smul_eq_mul,
    mul_zero, Std.le_refl, and_false, add_zero, mul_one, zero_add,
    Nat.reduceLeDiff]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-- In the book's example the product-limit functional of the observed-data law at time `2` is
`0.81`, the survival, while the fraction of uncensored survivors is `0.405`
(`indepModel_uncensoredSurvivors`). -/
theorem indepModel_productLimit :
    productLimit (indepModel.map (observed Prod.fst Prod.snd)) 2 = 81 / 100 := by
  rw [productLimit_map_observed_eq_survival measurable_fst measurable_snd indepFun_indepModel 2
    indepModel_atRisk_two_pos, indepModel_survival_two]

/-- With dependent censoring the product-limit functional of the observed-data law
(`0.81`) differs from the survival at time `2` (`0.405`), although the at-risk probability at
time `2` is positive. -/
theorem depModel_productLimit_ne_survival :
    productLimit (depModel.map (observed Prod.fst Prod.snd)) 2 ≠ survival depModel Prod.fst 2 := by
  rw [map_observed_depModel, indepModel_productLimit, depModel_survival_two]
  norm_num

/-- Censoring is not independent of the event time in `depModel`. -/
theorem not_indepFun_depModel : ¬ IndepFun Prod.fst Prod.snd depModel := fun h =>
  depModel_productLimit_ne_survival
    (productLimit_map_observed_eq_survival measurable_fst measurable_snd h 2
      depModel_atRisk_two_pos)

/-- Non-identification without independent censoring: two laws of `(T, C)` with the same
observed-data law and different survival at time `2`. -/
theorem survival_not_identified_without_independence :
    depModel.map (observed Prod.fst Prod.snd) = indepModel.map (observed Prod.fst Prod.snd) ∧
      survival depModel Prod.fst 2 ≠ survival indepModel Prod.fst 2 := by
  refine ⟨map_observed_depModel, ?_⟩
  rw [depModel_survival_two, indepModel_survival_two]
  norm_num

/-- The hazard condition of `productLimit_map_observed_eq_survival_of_hazard_eq` fails in
`depModel` at time `2`: among those at risk and uncensored at `2`, the proportion with the event
at `2` is `P(T = 2 | T ≥ 2, C ≥ 2) = 9/90 = 1/10`, while the true hazard is
`h 2 = P(T = 2 | T ≥ 2) = 99/180 = 11/20`. (At times `0` and `1` the two agree.) -/
theorem depModel_hazard_two_ne :
    depModel.real {p | p.1 = 2 ∧ 2 ≤ p.2} / depModel.real {p | 2 ≤ p.1 ∧ 2 ≤ p.2} = 1 / 10 ∧
      hazard depModel Prod.fst 2 = 11 / 20 := by
  constructor <;>
  simp [depModel, hazard, atRisk, measureReal_def, add_apply, smul_apply, Measure.dirac_apply,
    Set.indicator, ENNReal.toReal_add, ENNReal.mul_eq_top, ENNReal.toReal_mul,
    ENNReal.toReal_inv] <;>
  norm_num

/-- A model with independent censoring and no observed risk set at time `2`: `(T, C) = (2, 1)`
surely, written as a product law. -/
noncomputable def supportModel₂ : Measure (ℕ × ℕ) := (Measure.dirac 2).prod (Measure.dirac 1)

/-- A second such model: `(T, C) = (3, 1)` surely. -/
noncomputable def supportModel₃ : Measure (ℕ × ℕ) := (Measure.dirac 3).prod (Measure.dirac 1)

instance : IsProbabilityMeasure supportModel₂ := by unfold supportModel₂; infer_instance

instance : IsProbabilityMeasure supportModel₃ := by unfold supportModel₃; infer_instance

/-- Loss of risk-set support: two laws of `(T, C)`, both with `T` independent of `C`, with the
same observed-data law (the observation `(1, censored)` surely) and with probability zero of
being at risk and uncensored at time `2`, yet with survival `0` and `1` at time `2`. So the
positivity hypothesis of `productLimit_map_observed_eq_survival` cannot be dropped: independent
censoring alone does not identify the survival at a time with no observed risk set. -/
theorem survival_not_identified_without_support :
    IndepFun Prod.fst Prod.snd supportModel₂ ∧ IndepFun Prod.fst Prod.snd supportModel₃ ∧
      supportModel₂.map (observed Prod.fst Prod.snd) =
        supportModel₃.map (observed Prod.fst Prod.snd) ∧
      supportModel₂.real {p | 2 ≤ p.1 ∧ 2 ≤ p.2} = 0 ∧
      supportModel₃.real {p | 2 ≤ p.1 ∧ 2 ≤ p.2} = 0 ∧
      survival supportModel₂ Prod.fst 2 = 0 ∧ survival supportModel₃ Prod.fst 2 = 1 := by
  refine ⟨indepFun_prod (X := id) (Y := id) measurable_id measurable_id,
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id, ?_, ?_, ?_, ?_, ?_⟩
  · rw [supportModel₂, supportModel₃, Measure.dirac_prod_dirac, Measure.dirac_prod_dirac,
      Measure.map_dirac' measurable_observed_fst_snd,
      Measure.map_dirac' measurable_observed_fst_snd]
    rfl
  all_goals simp [supportModel₂, supportModel₃, survival, Measure.dirac_prod_dirac,
    measureReal_def, Measure.dirac_apply, Set.indicator]

end CensoringExample

end Survival

end CausalInference
