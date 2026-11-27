/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.EffectMeasures
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.NormNum

/-!
# Collapsibility and effect-measure modification

A binary treatment `A`, a binary outcome `Y`, and a stratifying variable `V` with finitely many
levels. The data are the stratum risks `p₁ v = Pr[Y = 1 | A = 1, V = v]` and
`p₀ v = Pr[Y = 1 | A = 0, V = v]` and the stratum distributions `π₁ v = Pr[V = v | A = 1]`,
`π₀ v = Pr[V = v | A = 0]`. By the law of total probability the marginal risk in arm `a` is the
standardized risk `∑ v, π_a v * p_a v`. When `V` is independent of `A` (no confounding by `V`,
as in a marginally randomized experiment) `π₁ = π₀`.

## Main definitions

* `IsWeights w`: nonnegative weights summing to one.
* `IsCollapsible g π₁ π₀ p₁ p₀`: the population effect measure `g` is a weighted average of the
  stratum-specific measures (Hernán and Robins, Fine Point 4.3).
* `IsCollapsibleOver g π π₁ π₀ p₁ p₀`: Pearl's Definition 6.5.1, `E_z g[P(x, y | z)] = g[P(x, y)]`,
  where the expectation is taken with the marginal distribution `π` of the stratifier.
* `AdditiveModification`, `MultiplicativeModification`, `QualitativeModification`: effect
  modification by `V` on the risk difference scale, on the risk ratio scale, and with stratum
  effects in opposite directions (Hernán and Robins, Section 4.1).

## Main results

* `riskDiff_isCollapsibleOver_of_indep`, `riskDiff_isCollapsibleOver_of_const`: the risk
  difference is collapsible over `V` when `V` is unassociated with `A` (Pearl's (U1)), and when
  `V` is unassociated with `Y` given `A` (Pearl's (U2)); Pearl, Section 6.5.1.
* `riskRatio_eq_sum_rrWeight`: with `V` independent of `A`, the marginal risk ratio equals
  `∑ v, w v * RR v` with the weights `w v = π v * p₀ v / ∑ u, π u * p₀ u` (Hernán and Robins,
  Technical Point 4.3); `riskRatio_isCollapsible`, `riskRatio_mem_Icc` give collapsibility and
  the range bound of Fine Point 4.3.
* `marginal_riskRatio_lt_one_iff`: the Technical Point 4.3 criterion for conditional risk
  ratios `1/2` and `2`.
* `oddsRatio_not_collapsible_table44`: the odds ratio is not collapsible. In the data of Table
  4.4, `V` is independent of `A`, both stratum odds ratios equal `6`, and the marginal odds ratio
  is `49/9`, outside the range of the stratum values; the stratum risk ratios are `2` and `3`
  and the marginal risk ratio is `7/3`.
* `oddsRatio_isCollapsible_of_sharpNull`: under the null in every stratum the odds ratio is
  collapsible (all odds ratios equal `1`).
* `qualitative_imp_additive_and_multiplicative`: qualitative modification shows on both scales.
* `null_or_const_of_no_modification` and `modification_of_baseline_varies`: Hernán and Robins,
  Section 4.3: if the baseline risk varies across strata and the effect is nonnull in some
  stratum, there is effect modification on the additive or on the multiplicative scale.
* `scaleDependence_example`: multiplicative without additive modification (risks `0.8`, `0.9`,
  `0.1`, `0.2`, Section 4.1).

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Sections 4.1 and 4.3,
  Technical Point 4.3, Fine Point 4.3, Table 4.4.
* J. Pearl, *Causality*, 2nd ed. (2009), Section 6.5.1, Definition 6.5.1.
-/

@[expose] public section

namespace CausalInference

namespace EffectMeasure

open Finset

variable {V : Type*} [Fintype V]

/-- Nonnegative weights summing to one: a probability vector on the strata. -/
def IsWeights (w : V → ℝ) : Prop := (∀ v, 0 ≤ w v) ∧ ∑ v, w v = 1

/-- **Collapsibility** (Hernán and Robins, Fine Point 4.3). The effect measure `g`, applied to
the marginal risks `∑ π₁ p₁` and `∑ π₀ p₀`, is a weighted average, with some nonnegative
weights summing to one, of the stratum measures `g (p₁ v) (p₀ v)`. -/
def IsCollapsible (g : ℝ → ℝ → ℝ) (π₁ π₀ p₁ p₀ : V → ℝ) : Prop :=
  ∃ w, IsWeights w ∧
    g (standardizedRisk π₁ p₁) (standardizedRisk π₀ p₀) = ∑ v, w v * g (p₁ v) (p₀ v)

/-- **Collapsibility over `Z`** (Pearl 2009, Definition 6.5.1). The expectation of the stratum
measures under the marginal distribution `π` of the stratifier equals the measure applied to the
marginal risks: `E_z g[P(x, y | z)] = g[P(x, y)]`. -/
def IsCollapsibleOver (g : ℝ → ℝ → ℝ) (π π₁ π₀ p₁ p₀ : V → ℝ) : Prop :=
  g (standardizedRisk π₁ p₁) (standardizedRisk π₀ p₀) = ∑ v, π v * g (p₁ v) (p₀ v)

/-- Pearl's collapsibility implies collapsibility in the weighted-average sense. -/
theorem IsCollapsibleOver.isCollapsible {g : ℝ → ℝ → ℝ} {π π₁ π₀ p₁ p₀ : V → ℝ}
    (h : IsCollapsibleOver g π π₁ π₀ p₁ p₀) (hπ : IsWeights π) :
    IsCollapsible g π₁ π₀ p₁ p₀ :=
  ⟨π, hπ, h⟩

/-- A weighted average of values all strictly above `m` is strictly above `m`. -/
theorem lt_standardizedRisk {π r : V → ℝ} {m : ℝ} (hπ : IsWeights π) (hr : ∀ v, m < r v) :
    m < standardizedRisk π r := by
  have hex : ∃ v, 0 < π v := by
    by_contra h
    push Not at h
    have : ∑ v, π v = 0 := Finset.sum_eq_zero fun v _ => le_antisymm (h v) (hπ.1 v)
    linarith [hπ.2]
  obtain ⟨v₀, hv₀⟩ := hex
  have hpos : 0 < ∑ v, π v * (r v - m) :=
    Finset.sum_pos' (fun v _ => mul_nonneg (hπ.1 v) (sub_nonneg.2 (hr v).le))
      ⟨v₀, Finset.mem_univ _, mul_pos hv₀ (sub_pos.2 (hr v₀))⟩
  have : ∑ v, π v * (r v - m) = standardizedRisk π r - m := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2, one_mul,
      standardizedRisk]
  linarith

/-- A weighted average of values all strictly below `M` is strictly below `M`. -/
theorem standardizedRisk_lt {π r : V → ℝ} {M : ℝ} (hπ : IsWeights π) (hr : ∀ v, r v < M) :
    standardizedRisk π r < M := by
  have h := lt_standardizedRisk (r := fun v => -r v) (m := -M) hπ (fun v => neg_lt_neg (hr v))
  have : standardizedRisk π (fun v => -r v) = -standardizedRisk π r := by
    simp [standardizedRisk, Finset.sum_neg_distrib]
  linarith

/-! ### The risk difference -/

/-- **The risk difference is collapsible under (U1).** If the stratifier has the same
distribution `π` in both arms, the marginal risk difference is the `π`-average of the stratum
risk differences (Pearl, Section 6.5.1). -/
theorem riskDiff_isCollapsibleOver_of_indep (π p₁ p₀ : V → ℝ) :
    IsCollapsibleOver riskDiff π π π p₁ p₀ := by
  simp only [IsCollapsibleOver, riskDiff, standardizedRisk, mul_sub, Finset.sum_sub_distrib]

/-- **The risk difference is collapsible under (U2).** If the stratum risks do not depend on the
stratum (`V` is unassociated with `Y` given `A`), the marginal risk difference equals the
average of the stratum risk differences, whatever the stratum distributions in the two arms
(Pearl, Section 6.5.1). -/
theorem riskDiff_isCollapsibleOver_of_const {π π₁ π₀ p₁ p₀ : V → ℝ} {c₁ c₀ : ℝ}
    (hπ : ∑ v, π v = 1) (hπ₁ : ∑ v, π₁ v = 1) (hπ₀ : ∑ v, π₀ v = 1)
    (h₁ : ∀ v, p₁ v = c₁) (h₀ : ∀ v, p₀ v = c₀) :
    IsCollapsibleOver riskDiff π π₁ π₀ p₁ p₀ := by
  simp only [IsCollapsibleOver, riskDiff, standardizedRisk, h₁, h₀, ← Finset.sum_mul, hπ, hπ₁,
    hπ₀, one_mul]

/-- With `V` independent of `A`, the risk difference is collapsible, and the marginal risk
difference lies between the smallest and the largest stratum risk difference. -/
theorem riskDiff_mem_Icc {π p₁ p₀ : V → ℝ} {m M : ℝ} (hπ : IsWeights π)
    (h : ∀ v, riskDiff (p₁ v) (p₀ v) ∈ Set.Icc m M) :
    riskDiff (standardizedRisk π p₁) (standardizedRisk π p₀) ∈ Set.Icc m M := by
  rw [riskDiff_isCollapsibleOver_of_indep π p₁ p₀]
  exact standardizedRisk_mem_Icc hπ.1 hπ.2 h

/-! ### The risk ratio -/

/-- The weights of the risk ratio (Hernán and Robins, Technical Point 4.3):
`w v = Pr[Y = 1 | A = 0, V = v] Pr[V = v] / Pr[Y = 1 | A = 0]`, the share of stratum `v` among
the outcome events of the untreated arm. -/
noncomputable def rrWeight (π p₀ : V → ℝ) (v : V) : ℝ := π v * p₀ v / standardizedRisk π p₀

/-- The risk ratio weights are weights when the baseline risks are positive. -/
theorem isWeights_rrWeight {π p₀ : V → ℝ} (hπ : IsWeights π) (h₀ : ∀ v, 0 < p₀ v) :
    IsWeights (rrWeight π p₀) := by
  have hS : 0 < standardizedRisk π p₀ := lt_standardizedRisk hπ h₀
  refine ⟨fun v => div_nonneg (mul_nonneg (hπ.1 v) (h₀ v).le) hS.le, ?_⟩
  simp only [rrWeight, ← Finset.sum_div]
  exact div_self hS.ne'

/-- **Marginal versus conditional risk ratio** (Hernán and Robins, Technical Point 4.3). With
`V` independent of `A` (stratum distribution `π` in both arms) and positive baseline risks, the
marginal risk ratio is the `rrWeight`-weighted average of the stratum risk ratios. -/
theorem riskRatio_eq_sum_rrWeight {π p₁ p₀ : V → ℝ} (hπ : IsWeights π) (h₀ : ∀ v, 0 < p₀ v) :
    riskRatio (standardizedRisk π p₁) (standardizedRisk π p₀) =
      ∑ v, rrWeight π p₀ v * riskRatio (p₁ v) (p₀ v) := by
  have hS : 0 < standardizedRisk π p₀ := lt_standardizedRisk hπ h₀
  have : ∀ v, rrWeight π p₀ v * riskRatio (p₁ v) (p₀ v) =
      π v * p₁ v / standardizedRisk π p₀ := by
    intro v
    have := (h₀ v).ne'
    unfold rrWeight riskRatio
    field_simp
  rw [Finset.sum_congr rfl fun v _ => this v, ← Finset.sum_div]
  rfl

/-- **The risk ratio is collapsible** (Hernán and Robins, Fine Point 4.3), when `V` is
independent of `A` and the baseline risks are positive. -/
theorem riskRatio_isCollapsible {π p₁ p₀ : V → ℝ} (hπ : IsWeights π) (h₀ : ∀ v, 0 < p₀ v) :
    IsCollapsible riskRatio π π p₁ p₀ :=
  ⟨rrWeight π p₀, isWeights_rrWeight hπ h₀, riskRatio_eq_sum_rrWeight hπ h₀⟩

/-- The marginal risk ratio lies between the smallest and the largest stratum risk ratio
(Hernán and Robins, Fine Point 4.3). -/
theorem riskRatio_mem_Icc {π p₁ p₀ : V → ℝ} {m M : ℝ} (hπ : IsWeights π)
    (h₀ : ∀ v, 0 < p₀ v) (h : ∀ v, riskRatio (p₁ v) (p₀ v) ∈ Set.Icc m M) :
    riskRatio (standardizedRisk π p₁) (standardizedRisk π p₀) ∈ Set.Icc m M := by
  rw [riskRatio_eq_sum_rrWeight hπ h₀]
  have hw := isWeights_rrWeight hπ h₀
  exact standardizedRisk_mem_Icc hw.1 hw.2 h

/-- **Technical Point 4.3 criterion.** Two strata `L = true` and `L = false` with
`Pr[L = l] = π l > 0`, positive baseline risks, conditional risk ratio `1/2` in stratum `true`
and `2` in stratum `false`. Then the marginal risk ratio is below `1` if and only if
`p₀ true / p₀ false > 2 π false / π true`. -/
theorem marginal_riskRatio_lt_one_iff {π p₁ p₀ : Bool → ℝ} (hπ : IsWeights π)
    (hπt : 0 < π true) (h₀ : ∀ l, 0 < p₀ l)
    (hRR₁ : riskRatio (p₁ true) (p₀ true) = 1 / 2)
    (hRR₀ : riskRatio (p₁ false) (p₀ false) = 2) :
    riskRatio (standardizedRisk π p₁) (standardizedRisk π p₀) < 1 ↔
      2 * π false / π true < p₀ true / p₀ false := by
  have ht := h₀ true
  have hf := h₀ false
  have e₁ : p₁ true = p₀ true / 2 := by
    unfold riskRatio at hRR₁; field_simp at hRR₁; linarith
  have e₀ : p₁ false = 2 * p₀ false := by
    unfold riskRatio at hRR₀; field_simp at hRR₀; linarith
  have hS : 0 < standardizedRisk π p₀ := lt_standardizedRisk hπ h₀
  rw [riskRatio_lt_one_iff hS, riskDiff, sub_neg, div_lt_div_iff₀ hπt hf]
  simp only [standardizedRisk, Fintype.sum_bool, e₁, e₀]
  constructor <;> intro h <;> nlinarith

/-! ### The odds ratio -/

/-- **The odds ratio is collapsible under the sharp null** (Hernán and Robins, Fine Point 4.3).
If treatment has no effect in any stratum and the baseline risks are in `(0, 1)`, the odds ratio
is collapsible: every stratum odds ratio and the marginal odds ratio equal `1`. -/
theorem oddsRatio_isCollapsible_of_sharpNull {π p₁ p₀ : V → ℝ} (hπ : IsWeights π)
    (hnull : ∀ v, p₁ v = p₀ v) (h0 : ∀ v, 0 < p₀ v) (h1 : ∀ v, p₀ v < 1) :
    IsCollapsibleOver oddsRatio π π π p₁ p₀ ∧
      oddsRatio (standardizedRisk π p₁) (standardizedRisk π p₀) = 1 := by
  have hp : p₁ = p₀ := funext hnull
  subst hp
  have hS0 : 0 < standardizedRisk π p₁ := lt_standardizedRisk hπ h0
  have hS1 : standardizedRisk π p₁ < 1 := standardizedRisk_lt hπ h1
  have hm : oddsRatio (standardizedRisk π p₁) (standardizedRisk π p₁) = 1 :=
    (oddsRatio_eq_one_iff hS1 hS0 hS1).2 rfl
  refine ⟨?_, hm⟩
  unfold IsCollapsibleOver
  rw [hm]
  have : ∀ v, oddsRatio (p₁ v) (p₁ v) = 1 := fun v =>
    (oddsRatio_eq_one_iff (h1 v) (h0 v) (h1 v)).2 rfl
  simp [this, hπ.2]

/-! #### Hernán and Robins, Table 4.4

Twenty individuals; `V` is sex (`true` for women), `A` is moving to a high altitude, `Y` is
depression. `table44 v a y` is the number of individuals with `V = v`, `A = a`, `Y = y`, read
off the individual rows of Table 4.4. -/

/-- The counts of Hernán and Robins, Table 4.4, indexed by `V`, `A`, `Y`. -/
def table44 : Bool → Bool → Bool → ℕ
  | true, false, false => 4
  | true, false, true => 1
  | true, true, false => 2
  | true, true, true => 3
  | false, false, false => 3
  | false, false, true => 2
  | false, true, false => 1
  | false, true, true => 4

/-- The stratum risk `Pr[Y = 1 | A = a, V = v]` in Table 4.4. -/
noncomputable def risk44 (a v : Bool) : ℝ :=
  (table44 v a true : ℝ) / ((table44 v a true : ℝ) + table44 v a false)

/-- The stratum distribution `Pr[V = v | A = a]` in Table 4.4. -/
noncomputable def condV44 (a v : Bool) : ℝ :=
  ((table44 v a true : ℝ) + table44 v a false) / ∑ u, ∑ y, (table44 u a y : ℝ)

/-- The marginal distribution `Pr[V = v]` in Table 4.4. -/
noncomputable def margV44 (v : Bool) : ℝ :=
  (∑ a, ∑ y, (table44 v a y : ℝ)) / ∑ u, ∑ a, ∑ y, (table44 u a y : ℝ)

/-- The marginal risk `Pr[Y = 1 | A = a]` in Table 4.4, computed from the counts. -/
noncomputable def margRisk44 (a : Bool) : ℝ :=
  (∑ v, (table44 v a true : ℝ)) / ∑ v, ∑ y, (table44 v a y : ℝ)

/-- In Table 4.4 the stratifier is independent of treatment: `Pr[V = v | A = a] = Pr[V = v]`
(both equal `1/2`). There is no confounding by `V`. -/
theorem table44_indep (a v : Bool) : condV44 a v = margV44 v := by
  cases a <;> cases v <;> norm_num [condV44, margV44, table44, Fintype.sum_bool]

/-- In Table 4.4 the marginal risk is the standardized risk (law of total probability). -/
theorem margRisk44_eq (a : Bool) :
    margRisk44 a = standardizedRisk (condV44 a) (risk44 a) := by
  cases a <;> norm_num [margRisk44, standardizedRisk, condV44, risk44, table44, Fintype.sum_bool]

theorem isWeights_condV44 (a : Bool) : IsWeights (condV44 a) := by
  constructor
  · intro v; unfold condV44; positivity
  · cases a <;> norm_num [condV44, table44, Fintype.sum_bool]

/-- Table 4.4: both stratum odds ratios are `6`. -/
theorem table44_stratum_oddsRatio (v : Bool) : oddsRatio (risk44 true v) (risk44 false v) = 6 := by
  cases v <;> norm_num [oddsRatio, odds, risk44, table44]

/-- Table 4.4: the stratum risk ratios are `2` for men and `3` for women. -/
theorem table44_stratum_riskRatio :
    riskRatio (risk44 true false) (risk44 false false) = 2 ∧
      riskRatio (risk44 true true) (risk44 false true) = 3 := by
  norm_num [riskRatio, risk44, table44]

/-- Table 4.4: the marginal odds ratio is `49/9`. -/
theorem table44_marginal_oddsRatio : oddsRatio (margRisk44 true) (margRisk44 false) = 49 / 9 := by
  norm_num [oddsRatio, odds, margRisk44, table44, Fintype.sum_bool]

/-- Table 4.4: the marginal risk ratio is `7/3`, between the stratum values `2` and `3`. -/
theorem table44_marginal_riskRatio : riskRatio (margRisk44 true) (margRisk44 false) = 7 / 3 := by
  norm_num [riskRatio, margRisk44, table44, Fintype.sum_bool]

/-- **The odds ratio is not collapsible** (Hernán and Robins, Fine Point 4.3 and Table 4.4;
Pearl, Section 6.5). In Table 4.4 the stratifier `V` is independent of treatment
(`table44_indep`), both stratum odds ratios equal `6`, yet the marginal odds ratio `49/9` is not
a weighted average of the stratum odds ratios. Hence neither collapsibility notion holds. -/
theorem oddsRatio_not_collapsible_table44 :
    ¬ IsCollapsible oddsRatio (condV44 true) (condV44 false) (risk44 true) (risk44 false) ∧
      ¬ IsCollapsibleOver oddsRatio margV44 (condV44 true) (condV44 false)
        (risk44 true) (risk44 false) := by
  have key : ∀ w : Bool → ℝ, IsWeights w →
      oddsRatio (standardizedRisk (condV44 true) (risk44 true))
          (standardizedRisk (condV44 false) (risk44 false)) ≠
        ∑ v, w v * oddsRatio (risk44 true v) (risk44 false v) := by
    intro w hw
    rw [← margRisk44_eq, ← margRisk44_eq, table44_marginal_oddsRatio]
    simp only [table44_stratum_oddsRatio, ← Finset.sum_mul, hw.2]
    norm_num
  refine ⟨fun ⟨w, hw, h⟩ => key w hw h, fun h => key margV44 ?_ h⟩
  refine ⟨fun v => by rw [← table44_indep true]; exact (isWeights_condV44 true).1 v, ?_⟩
  simp only [← table44_indep true]
  exact (isWeights_condV44 true).2

/-! ### Effect-measure modification -/

/-- **Additive effect modification** by `V`: the stratum risk difference varies across
strata. -/
def AdditiveModification (p₁ p₀ : V → ℝ) : Prop :=
  ∃ v w, riskDiff (p₁ v) (p₀ v) ≠ riskDiff (p₁ w) (p₀ w)

/-- **Multiplicative effect modification** by `V`: the stratum risk ratio varies across
strata. -/
def MultiplicativeModification (p₁ p₀ : V → ℝ) : Prop :=
  ∃ v w, riskRatio (p₁ v) (p₀ v) ≠ riskRatio (p₁ w) (p₀ w)

/-- **Qualitative effect modification** by `V`: the effect is harmful in some stratum and
beneficial in another. -/
def QualitativeModification (p₁ p₀ : V → ℝ) : Prop :=
  ∃ v w, 0 < riskDiff (p₁ v) (p₀ v) ∧ riskDiff (p₁ w) (p₀ w) < 0

omit [Fintype V] in
/-- **Qualitative modification shows on both scales** (Hernán and Robins, Section 4.1). With
positive baseline risks, qualitative effect modification is both additive and multiplicative
effect modification. -/
theorem qualitative_imp_additive_and_multiplicative {p₁ p₀ : V → ℝ} (h₀ : ∀ v, 0 < p₀ v)
    (hq : QualitativeModification p₁ p₀) :
    AdditiveModification p₁ p₀ ∧ MultiplicativeModification p₁ p₀ := by
  obtain ⟨v, w, hv, hw⟩ := hq
  refine ⟨⟨v, w, by linarith⟩, ⟨v, w, ?_⟩⟩
  have := (one_lt_riskRatio_iff (h₀ v)).2 hv
  have := (riskRatio_lt_one_iff (h₀ w)).2 hw
  linarith

omit [Fintype V] in
/-- **No modification on either scale.** With positive baseline risks, if neither the risk
difference nor the risk ratio varies across strata, then either the effect is null in every
stratum or the baseline risk is the same in every stratum. -/
theorem null_or_const_of_no_modification {p₁ p₀ : V → ℝ} (h₀ : ∀ v, 0 < p₀ v)
    (hA : ¬ AdditiveModification p₁ p₀) (hM : ¬ MultiplicativeModification p₁ p₀) :
    (∀ v, p₁ v = p₀ v) ∨ ∀ v w, p₀ v = p₀ w := by
  simp only [AdditiveModification, MultiplicativeModification, not_exists, not_not] at hA hM
  by_cases hnull : ∀ v, p₁ v = p₀ v
  · exact Or.inl hnull
  right
  push Not at hnull
  obtain ⟨u, hu⟩ := hnull
  intro v w
  -- in every stratum `p₁ = r p₀` and `p₁ = p₀ + d` with common `r`, `d`
  have key : ∀ x, (riskRatio (p₁ u) (p₀ u) - 1) * p₀ x = riskDiff (p₁ u) (p₀ u) := by
    intro x
    have hr := hM u x
    have hd := hA u x
    unfold riskRatio at hr ⊢
    unfold riskDiff at hd ⊢
    have := (h₀ x).ne'
    rw [hr, hd]
    field_simp
  have hr1 : riskRatio (p₁ u) (p₀ u) - 1 ≠ 0 := by
    intro h
    have := key u
    rw [h, zero_mul] at this
    exact hu (sub_eq_zero.1 this.symm)
  have hv := key v
  have hw := key w
  exact mul_left_cancel₀ hr1 (hv.trans hw.symm)

omit [Fintype V] in
/-- **Effect modification is guaranteed on some scale** (Hernán and Robins, Section 4.3). If the
baseline risk `Pr[Y^{a=0} = 1 | V = v] > 0` varies with `v` and the effect is nonnull in at least
one stratum, there is additive or multiplicative effect modification by `V`. -/
theorem modification_of_baseline_varies {p₁ p₀ : V → ℝ} (h₀ : ∀ v, 0 < p₀ v)
    (hvar : ∃ v w, p₀ v ≠ p₀ w) (heff : ∃ v, p₁ v ≠ p₀ v) :
    AdditiveModification p₁ p₀ ∨ MultiplicativeModification p₁ p₀ := by
  by_contra h
  push Not at h
  obtain ⟨u, hu⟩ := heff
  obtain ⟨v, w, hvw⟩ := hvar
  rcases null_or_const_of_no_modification h₀ h.1 h.2 with h' | h'
  · exact hu (h' u)
  · exact hvw (h' v w)

/-- **Scale dependence** (Hernán and Robins, Section 4.1). Baseline risks `0.8` and `0.1`,
treated risks `0.9` and `0.2`: the risk difference is `0.1` in both strata, the risk ratios are
`9/8` and `2`. There is multiplicative but no additive effect modification. -/
theorem scaleDependence_example :
    let p₀ : Bool → ℝ := fun v => if v then 8 / 10 else 1 / 10
    let p₁ : Bool → ℝ := fun v => if v then 9 / 10 else 2 / 10
    ¬ AdditiveModification p₁ p₀ ∧ MultiplicativeModification p₁ p₀ := by
  intro p₀ p₁
  refine ⟨?_, ⟨true, false, ?_⟩⟩
  · rintro ⟨v, w, h⟩
    cases v <;> cases w <;> norm_num [p₀, p₁, riskDiff] at h
  · norm_num [p₀, p₁, riskRatio]

end EffectMeasure

end CausalInference
