/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.Collapsibility

/-!
# The sure-thing principle and Simpson's reversal

A population is partitioned into finitely many strata `v` (subpopulations `F`, `¬F` in Pearl's
notation). Under each action `a` (treatment `C` or control `¬C`) the strata have probabilities
`q a v` and the event `E` has stratum probabilities `e a v`; the overall probability of `E` under
action `a` is the standardized risk `∑ v, q a v * e a v`.

## Main results

* `sure_thing_principle` (Pearl 2009, Theorem 6.1.1, algebraic form of (6.7) to (6.9)): if the
  action does not change the distribution of the strata (`q₁ = q₀`), an action that increases the
  probability of `E` in every stratum increases it in the population. `sure_thing_principle_le`
  is the non-strict version.
* `ne_of_reversal`: a reversal (higher in every stratum, not higher overall) forces the stratum
  distribution to differ between the two arms. When the arms are observed treatment groups
  (`q a = P(V | A = a)`, `e a v = P(E | A = a, V = v)`), this is dependence of the stratum on
  the observed treatment. `interventional_reversal_balanced` shows that this observational
  dependence is not necessary for a reversal of interventional quantities: there the
  standardizing distributions are the interventional ones `P(V^a)`.
* `simpson_figure61`: the reversal of Pearl's Figure 6.1, stated with the published rates and
  the arm-specific sex distributions they determine.
* `simpson_table11`: Simpson's reversal in the counts of Table 1.1 of Pearl, Glymour and Jewell
  (2016): the drug has a higher recovery rate among men (`81/87` against `234/270`) and among
  women (`192/263` against `55/80`) but a lower one in the combined data (`273/350` against
  `289/350`); `table11_dependent` shows that the sex distribution differs between the arms, as
  `ne_of_reversal` requires.
* `simpson_table12`: Table 1.2 of the same book has the same numbers with the treatment columns
  exchanged and the stratum read as post-treatment blood pressure: the drug has the lower
  recovery rate in each blood pressure stratum (`234/270` against `81/87`, `55/80` against
  `192/263`) and the higher one overall (`289/350` against `273/350`). Here the stratum is
  affected by the treatment, the situation Pearl discusses right after Theorem 6.1.1: when `F`
  is affected by `C`, the stratified and the aggregate comparisons may disagree.

## References

* J. Pearl, *Causality*, 2nd ed. (2009), Section 6.1.1 and Section 6.1.4, Theorem 6.1.1.
* J. Pearl, M. Glymour and N. P. Jewell, *Causal Inference in Statistics: A Primer* (2016),
  Section 1.2, Tables 1.1 and 1.2.
-/

@[expose] public section

namespace CausalInference

namespace EffectMeasure

open Finset

variable {V : Type*} [Fintype V]

theorem standardizedRisk_sub (q e₁ e₀ : V → ℝ) :
    standardizedRisk q e₁ - standardizedRisk q e₀ = standardizedRisk q (fun v => e₁ v - e₀ v) := by
  simp only [standardizedRisk, mul_sub, Finset.sum_sub_distrib]

/-- **Sure-thing principle** (Pearl 2009, Theorem 6.1.1), algebraic form. Let `q₁`, `q₀` be the
distributions of the strata under the action and under its absence, and `e₁ v`, `e₀ v` the
stratum probabilities of `E`. If the action does not change the distribution of the strata
(`q₁ = q₀`, a probability vector), and increases the probability of `E` in every stratum, then
it increases the probability of `E` in the population. -/
theorem sure_thing_principle {q₁ q₀ e₁ e₀ : V → ℝ} (hq : IsWeights q₀) (hno : q₁ = q₀)
    (h : ∀ v, e₀ v < e₁ v) : standardizedRisk q₀ e₀ < standardizedRisk q₁ e₁ := by
  subst hno
  have := lt_standardizedRisk (r := fun v => e₁ v - e₀ v) (m := 0) hq fun v => sub_pos.2 (h v)
  rw [← standardizedRisk_sub] at this
  linarith

/-- **Sure-thing principle**, non-strict version: a weak increase in every stratum gives a weak
increase in the population, when the action does not change the distribution of the strata. -/
theorem sure_thing_principle_le {q₁ q₀ e₁ e₀ : V → ℝ} (hq : IsWeights q₀) (hno : q₁ = q₀)
    (h : ∀ v, e₀ v ≤ e₁ v) : standardizedRisk q₀ e₀ ≤ standardizedRisk q₁ e₁ := by
  subst hno
  exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h v) (hq.1 v)

/-- **Simpson's reversal requires dependence between treatment and stratum.** If the action
increases the probability of `E` in every stratum but not in the population, then the
distribution of the strata differs between the two arms. Read observationally, with
`q a v = P(V = v | A = a)` and `e a v = P(E | A = a, V = v)` (so that the aggregate is
`P(E | A = a)`), the conclusion is that the stratum distribution `P(V | A = a)` depends on the
observed treatment `a`. The theorem says nothing about interventional margins `P(V^a)` unless
those are the `q a` (see `interventional_reversal_balanced`). -/
theorem ne_of_reversal {q₁ q₀ e₁ e₀ : V → ℝ} (hq : IsWeights q₀) (h : ∀ v, e₀ v < e₁ v)
    (hrev : standardizedRisk q₁ e₁ ≤ standardizedRisk q₀ e₀) : q₁ ≠ q₀ := fun hno =>
  absurd hrev (not_le.2 (sure_thing_principle hq hno h))

/-! ### Pearl, Glymour and Jewell (2016), Table 1.1 -/

/-- Recovered patients in Table 1.1, by sex (`true` for men) and treatment (`true` for drug). -/
def recovered11 : Bool → Bool → ℕ
  | true, true => 81
  | true, false => 234
  | false, true => 192
  | false, false => 55

/-- Patients in Table 1.1, by sex (`true` for men) and treatment (`true` for drug). -/
def patients11 : Bool → Bool → ℕ
  | true, true => 87
  | true, false => 270
  | false, true => 263
  | false, false => 80

/-- The stratum recovery rate `P(recovery | treatment a, sex v)` in Table 1.1. -/
noncomputable def risk11 (a v : Bool) : ℝ := (recovered11 v a : ℝ) / patients11 v a

/-- The sex distribution `P(sex v | treatment a)` in Table 1.1. -/
noncomputable def condSex11 (a v : Bool) : ℝ :=
  (patients11 v a : ℝ) / ∑ u, (patients11 u a : ℝ)

/-- The combined recovery rate `P(recovery | treatment a)` in Table 1.1. -/
noncomputable def margRisk11 (a : Bool) : ℝ :=
  (∑ v, (recovered11 v a : ℝ)) / ∑ v, (patients11 v a : ℝ)

theorem isWeights_condSex11 (a : Bool) : IsWeights (condSex11 a) := by
  constructor
  · intro v; unfold condSex11; positivity
  · cases a <;> norm_num [condSex11, patients11, Fintype.sum_bool]

/-- In Table 1.1 the combined rate is the standardized rate with the arm-specific sex
distribution (law of total probability). -/
theorem margRisk11_eq (a : Bool) :
    margRisk11 a = standardizedRisk (condSex11 a) (risk11 a) := by
  cases a <;> norm_num [margRisk11, standardizedRisk, condSex11, risk11, recovered11, patients11,
    Fintype.sum_bool]

/-- **Simpson's reversal** in Table 1.1: the drug has the higher recovery rate among men and
among women, and the lower recovery rate in the combined data (`273/350 < 289/350`). -/
theorem simpson_table11 :
    (∀ v, risk11 false v < risk11 true v) ∧ margRisk11 true < margRisk11 false ∧
      margRisk11 true = 273 / 350 ∧ margRisk11 false = 289 / 350 := by
  refine ⟨fun v => ?_, ?_, ?_, ?_⟩
  · cases v <;> norm_num [risk11, recovered11, patients11]
  all_goals norm_num [margRisk11, recovered11, patients11, Fintype.sum_bool]

/-- In Table 1.1 treatment and sex are dependent: the sex distribution differs between the arms
(`87/350` men among the treated, `270/350` among the untreated), as `ne_of_reversal` demands. -/
theorem table11_dependent : condSex11 true ≠ condSex11 false := by
  refine ne_of_reversal (isWeights_condSex11 false) simpson_table11.1 ?_
  rw [← margRisk11_eq, ← margRisk11_eq]
  exact simpson_table11.2.1.le

/-! ### Pearl, Glymour and Jewell (2016), Table 1.2

Table 1.2 has the numbers of Table 1.1 with the treatment columns exchanged; the stratum is
posttreatment blood pressure (`true` for low blood pressure, the row of `81/87` and
`234/270`). -/

/-- The stratum recovery rate `P(recovery | treatment a, blood pressure v)` in Table 1.2. -/
noncomputable def risk12 (a v : Bool) : ℝ := risk11 (!a) v

/-- The combined recovery rate `P(recovery | treatment a)` in Table 1.2. -/
noncomputable def margRisk12 (a : Bool) : ℝ := margRisk11 (!a)

/-- **Table 1.2**: the drug has the lower recovery rate in each blood pressure stratum and the
higher recovery rate in the combined data (`289/350 > 273/350`). -/
theorem simpson_table12 :
    (∀ v, risk12 true v < risk12 false v) ∧ margRisk12 false < margRisk12 true ∧
      margRisk12 true = 289 / 350 ∧ margRisk12 false = 273 / 350 := by
  obtain ⟨h, hm, h₁, h₀⟩ := simpson_table11
  exact ⟨h, hm, h₀, h₁⟩

/-! ### Pearl (2009), Figure 6.1, in rates

This version uses the recovery rates of Figure 6.1 rather than cell counts: under
treatment `C`, `0.6` for males, `0.2` for females, `0.5` combined; under control `¬C`, `0.7`,
`0.3`, `0.4`. These rates determine the arm-specific sex distributions uniquely: the share of
females is `1/4` among the treated (`0.6 * 3/4 + 0.2 * 1/4 = 0.5`) and `3/4` among the controls
(`0.7 * 1/4 + 0.3 * 3/4 = 0.4`). Strata are indexed by `F` (`true` for female). -/

/-- Stratum recovery rates of Figure 6.1: `rate61 c f = P(E | c, f)`, `c = true` for `C`. -/
noncomputable def rate61 (c f : Bool) : ℝ :=
  if c then (if f then 2 / 10 else 6 / 10) else (if f then 3 / 10 else 7 / 10)

/-- The sex distribution `P(f | c)` implied by the rates of Figure 6.1. -/
noncomputable def sex61 (c f : Bool) : ℝ :=
  if c then (if f then 1 / 4 else 3 / 4) else (if f then 3 / 4 else 1 / 4)

/-- **Simpson's reversal, Figure 6.1** (Pearl 2009, (6.1) to (6.3)): the treatment has the
lower recovery rate among males and among females but the higher one combined (`0.5 > 0.4`); the
sex distribution differs between the arms. -/
theorem simpson_figure61 :
    (∀ f, rate61 true f < rate61 false f) ∧
      standardizedRisk (sex61 true) (rate61 true) = 1 / 2 ∧
      standardizedRisk (sex61 false) (rate61 false) = 2 / 5 ∧
      sex61 false ≠ sex61 true := by
  have hw : IsWeights (sex61 true) :=
    ⟨fun f => by cases f <;> norm_num [sex61], by norm_num [sex61, Fintype.sum_bool]⟩
  have hlt : ∀ f, rate61 true f < rate61 false f := fun f => by cases f <;> norm_num [rate61]
  have h₁ : standardizedRisk (sex61 true) (rate61 true) = 1 / 2 := by
    norm_num [standardizedRisk, sex61, rate61, Fintype.sum_bool]
  have h₀ : standardizedRisk (sex61 false) (rate61 false) = 2 / 5 := by
    norm_num [standardizedRisk, sex61, rate61, Fintype.sum_bool]
  exact ⟨hlt, h₁, h₀, ne_of_reversal hw hlt (by rw [h₁, h₀]; norm_num)⟩

/-! ### A reversal of interventional quantities with observational balance

Two independent fair bits `L`, `W` (uniform law on `Bool × Bool`). The natural treatment is
`A = L`; the potential stratum is `V^a = W` if `a = L` and `V^a = ¬a` otherwise. The observed
stratum is `V = V^A = W`, independent of `A`. -/

/-- The potential stratum `V^a` at the outcome `ω = (L, W)`. -/
def potStratum (a : Bool) (ω : Bool × Bool) : Bool := if a = ω.1 then ω.2 else !a

/-- The observed stratum distribution `P(V = v | A = a)`, with `A = L` and `V = W`. -/
noncomputable def obsStratum (a v : Bool) : ℝ :=
  (∑ ω : Bool × Bool, if ω.1 = a ∧ potStratum ω.1 ω = v then (1 : ℝ) / 4 else 0) /
    ∑ ω : Bool × Bool, if ω.1 = a then (1 : ℝ) / 4 else 0

/-- The interventional stratum distribution `P(V^a = v)`. -/
noncomputable def intStratum (a v : Bool) : ℝ :=
  ∑ ω : Bool × Bool, if potStratum a ω = v then (1 : ℝ) / 4 else 0

/-- **Observational balance does not exclude a reversal of interventional quantities.** In the
model above the stratum is observationally independent of treatment (`P(V = v | A = a) = 1/2`
for all `a`, `v`), while the interventional stratum distributions `P(V^a)` are the arm-specific
sex distributions of Figure 6.1 (`V = true` for female). Standardizing the stratum rates of
Figure 6.1 (taken as given) with `P(V^a)` gives a reversal: lower in each stratum under
treatment, higher overall. So the dependence that `ne_of_reversal` concludes concerns the
distributions used for standardization, which need not be `P(V | A = a)`. -/
theorem interventional_reversal_balanced :
    (∀ a v, obsStratum a v = 1 / 2) ∧ (∀ a v, intStratum a v = sex61 a v) ∧
      (∀ f, rate61 true f < rate61 false f) ∧
      standardizedRisk (intStratum false) (rate61 false) <
        standardizedRisk (intStratum true) (rate61 true) := by
  have hi : ∀ a v, intStratum a v = sex61 a v := fun a v => by
    cases a <;> cases v <;> norm_num [intStratum, potStratum, sex61, Fintype.sum_prod_type]
  refine ⟨fun a v => ?_, hi, simpson_figure61.1, ?_⟩
  · cases a <;> cases v <;> norm_num [obsStratum, potStratum, Fintype.sum_prod_type]
  · rw [show intStratum = sex61 from funext fun a => funext (hi a), simpson_figure61.2.1,
      simpson_figure61.2.2.1]
    norm_num

end EffectMeasure

end CausalInference
