/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Effect measures for a binary outcome

For a binary outcome, an effect of a binary treatment is summarized by two risks: `p₁`, the risk
of the outcome under treatment, and `p₀`, the risk under no treatment. These may be causal risks
`Pr[Y^{a=1} = 1]`, `Pr[Y^{a=0} = 1]` or associational risks `Pr[Y = 1 | A = a]`; the algebra is
the same. This file defines the three standard effect measures and proves their elementary
relations.

## Main definitions

* `EffectMeasure.riskDiff p₁ p₀ = p₁ - p₀`: the risk difference (additive scale).
* `EffectMeasure.riskRatio p₁ p₀ = p₁ / p₀`: the risk ratio (multiplicative scale).
* `EffectMeasure.odds p = p / (1 - p)` and `EffectMeasure.oddsRatio p₁ p₀ = odds p₁ / odds p₀`.
* `EffectMeasure.standardizedRisk π r = ∑ v, π v * r v`: the marginal (standardized) risk as the
  average of the stratum risks `r v` with stratum weights `π v`.

## Main results

* `riskRatio_eq_one_iff`, `oddsRatio_eq_one_iff`, `null_iff`: the null values coincide:
  `RD = 0 ↔ RR = 1 ↔ OR = 1`, for `0 < p₀ < 1` and `p₁ < 1`.
* `one_lt_riskRatio_iff`, `one_lt_oddsRatio_iff`, `riskRatio_lt_one_iff`,
  `oddsRatio_lt_one_iff`: the three measures agree on the direction of the effect.
* `riskRatio_lt_oddsRatio`, `oddsRatio_lt_riskRatio`: the odds ratio is further from the null
  value `1` than the risk ratio.
* `standardizedRisk_mem_Icc`: a standardized risk lies between the smallest and the largest
  stratum risk; in particular it is a risk.

Every ratio carries a positivity hypothesis on its denominator; no result relies on the
convention `x / 0 = 0`.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Chapter 1 (effect measures)
  and Chapter 4, Fine Point 4.3.
-/

@[expose] public section

namespace CausalInference

namespace EffectMeasure

open Finset

/-- The risk difference `p₁ - p₀`: the effect on the additive scale. -/
def riskDiff (p₁ p₀ : ℝ) : ℝ := p₁ - p₀

/-- The risk ratio `p₁ / p₀`: the effect on the multiplicative scale. It is meaningful only when
`p₀ > 0`, which every result below assumes. -/
noncomputable def riskRatio (p₁ p₀ : ℝ) : ℝ := p₁ / p₀

/-- The odds `p / (1 - p)` of an event of probability `p`. It is meaningful only when `p < 1`. -/
noncomputable def odds (p : ℝ) : ℝ := p / (1 - p)

/-- The odds ratio `odds p₁ / odds p₀`. It is meaningful when `0 < p₀ < 1` and `p₁ < 1`. -/
noncomputable def oddsRatio (p₁ p₀ : ℝ) : ℝ := odds p₁ / odds p₀

theorem riskDiff_eq_zero_iff {p₁ p₀ : ℝ} : riskDiff p₁ p₀ = 0 ↔ p₁ = p₀ := sub_eq_zero

/-- The risk ratio is `1` exactly when the risks are equal (given a positive baseline risk). -/
theorem riskRatio_eq_one_iff {p₁ p₀ : ℝ} (h₀ : 0 < p₀) : riskRatio p₁ p₀ = 1 ↔ p₁ = p₀ :=
  div_eq_one_iff_eq h₀.ne'

theorem odds_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : 0 < odds p :=
  div_pos h0 (by linarith)

/-- The odds are strictly increasing on `(-∞, 1)`, in particular on `[0, 1)`. -/
theorem odds_lt_odds_iff {p q : ℝ} (hp1 : p < 1) (hq1 : q < 1) :
    odds p < odds q ↔ p < q := by
  unfold odds
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

theorem odds_injOn {p q : ℝ} (hp1 : p < 1) (hq1 : q < 1) (h : odds p = odds q) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hgt
  · exact absurd h ((odds_lt_odds_iff hp1 hq1).2 hlt).ne
  · exact heq
  · exact absurd h ((odds_lt_odds_iff hq1 hp1).2 hgt).ne'

/-- The odds ratio is `1` exactly when the risks are equal (given `0 < p₀ < 1` and
`p₁ < 1`). -/
theorem oddsRatio_eq_one_iff {p₁ p₀ : ℝ} (h₁1 : p₁ < 1) (h₀0 : 0 < p₀)
    (h₀1 : p₀ < 1) : oddsRatio p₁ p₀ = 1 ↔ p₁ = p₀ := by
  unfold oddsRatio
  rw [div_eq_one_iff_eq (odds_pos h₀0 h₀1).ne']
  exact ⟨odds_injOn h₁1 h₀1, fun h => h ▸ rfl⟩

/-- **The null values coincide.** If `0 < p₀ < 1` and `p₁ < 1`, the risk difference is `0` iff
the risk ratio is `1` iff the odds ratio is `1`. -/
theorem null_iff {p₁ p₀ : ℝ} (h₁1 : p₁ < 1) (h₀0 : 0 < p₀) (h₀1 : p₀ < 1) :
    (riskDiff p₁ p₀ = 0 ↔ riskRatio p₁ p₀ = 1) ∧
      (riskRatio p₁ p₀ = 1 ↔ oddsRatio p₁ p₀ = 1) := by
  rw [riskDiff_eq_zero_iff, riskRatio_eq_one_iff h₀0, oddsRatio_eq_one_iff h₁1 h₀0 h₀1]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- A positive risk difference is a risk ratio above `1`. -/
theorem one_lt_riskRatio_iff {p₁ p₀ : ℝ} (h₀ : 0 < p₀) :
    1 < riskRatio p₁ p₀ ↔ 0 < riskDiff p₁ p₀ := by
  unfold riskRatio riskDiff
  rw [one_lt_div h₀, sub_pos]

/-- A negative risk difference is a risk ratio below `1`. -/
theorem riskRatio_lt_one_iff {p₁ p₀ : ℝ} (h₀ : 0 < p₀) :
    riskRatio p₁ p₀ < 1 ↔ riskDiff p₁ p₀ < 0 := by
  unfold riskRatio riskDiff
  rw [div_lt_one h₀, sub_neg]

/-- A positive risk difference is an odds ratio above `1`. -/
theorem one_lt_oddsRatio_iff {p₁ p₀ : ℝ} (h₁1 : p₁ < 1) (h₀0 : 0 < p₀)
    (h₀1 : p₀ < 1) : 1 < oddsRatio p₁ p₀ ↔ 0 < riskDiff p₁ p₀ := by
  unfold oddsRatio riskDiff
  rw [one_lt_div (odds_pos h₀0 h₀1), odds_lt_odds_iff h₀1 h₁1, sub_pos]

/-- A negative risk difference is an odds ratio below `1`. -/
theorem oddsRatio_lt_one_iff {p₁ p₀ : ℝ} (h₁1 : p₁ < 1) (h₀0 : 0 < p₀)
    (h₀1 : p₀ < 1) : oddsRatio p₁ p₀ < 1 ↔ riskDiff p₁ p₀ < 0 := by
  unfold oddsRatio riskDiff
  rw [div_lt_one (odds_pos h₀0 h₀1), odds_lt_odds_iff h₁1 h₀1, sub_neg]

/-- The odds ratio factors as the risk ratio times `(1 - p₀) / (1 - p₁)`. -/
theorem oddsRatio_eq_riskRatio_mul {p₁ p₀ : ℝ} (h₁1 : p₁ < 1) (h₀0 : 0 < p₀) (h₀1 : p₀ < 1) :
    oddsRatio p₁ p₀ = riskRatio p₁ p₀ * ((1 - p₀) / (1 - p₁)) := by
  have : (1 - p₁) ≠ 0 := by linarith
  have : (1 - p₀) ≠ 0 := by linarith
  unfold oddsRatio odds riskRatio
  field_simp

/-- **The odds ratio exaggerates a harmful effect.** If `0 < p₀ < p₁ < 1`, then
`1 < RR < OR`: the odds ratio is further from the null than the risk ratio. -/
theorem riskRatio_lt_oddsRatio {p₁ p₀ : ℝ} (h₀0 : 0 < p₀) (h : p₀ < p₁) (h₁1 : p₁ < 1) :
    1 < riskRatio p₁ p₀ ∧ riskRatio p₁ p₀ < oddsRatio p₁ p₀ := by
  have hRR : 1 < riskRatio p₁ p₀ := (one_lt_riskRatio_iff h₀0).2 (sub_pos.2 h)
  refine ⟨hRR, ?_⟩
  rw [oddsRatio_eq_riskRatio_mul h₁1 h₀0 (h.trans h₁1)]
  have hf : 1 < (1 - p₀) / (1 - p₁) := (one_lt_div (by linarith)).2 (by linarith)
  nlinarith

/-- **The odds ratio exaggerates a protective effect.** If `0 < p₁ < p₀ < 1`, then
`OR < RR < 1`: the odds ratio is further from the null than the risk ratio. -/
theorem oddsRatio_lt_riskRatio {p₁ p₀ : ℝ} (h₁0 : 0 < p₁) (h : p₁ < p₀) (h₀1 : p₀ < 1) :
    oddsRatio p₁ p₀ < riskRatio p₁ p₀ ∧ riskRatio p₁ p₀ < 1 := by
  have h₀0 : 0 < p₀ := h₁0.trans h
  have hRR : riskRatio p₁ p₀ < 1 := (riskRatio_lt_one_iff h₀0).2 (sub_neg.2 h)
  refine ⟨?_, hRR⟩
  rw [oddsRatio_eq_riskRatio_mul (h.trans h₀1) h₀0 h₀1]
  have hf0 : 0 < (1 - p₀) / (1 - p₁) := div_pos (by linarith) (by linarith)
  have hf : (1 - p₀) / (1 - p₁) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hRR0 : 0 < riskRatio p₁ p₀ := div_pos h₁0 h₀0
  nlinarith

/-! ### Standardized risks -/

/-- The standardized (marginal) risk `∑ v, π v * r v`: the average of the stratum risks `r v`
weighted by the stratum probabilities `π v`. By the law of total probability this is the
marginal risk when `π` is the distribution of the stratifying variable in the relevant arm. -/
def standardizedRisk {V : Type*} [Fintype V] (π r : V → ℝ) : ℝ := ∑ v, π v * r v

/-- A weighted average with nonnegative weights summing to one lies between any lower and upper
bound of the averaged values. -/
theorem standardizedRisk_mem_Icc {V : Type*} [Fintype V] {π r : V → ℝ} {m M : ℝ}
    (hπ : ∀ v, 0 ≤ π v) (hsum : ∑ v, π v = 1) (hr : ∀ v, r v ∈ Set.Icc m M) :
    standardizedRisk π r ∈ Set.Icc m M := by
  unfold standardizedRisk
  constructor
  · calc m = ∑ v, π v * m := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ v, π v * r v :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hr v).1 (hπ v)
  · calc ∑ v, π v * r v ≤ ∑ v, π v * M :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hr v).2 (hπ v)
      _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A standardized risk of risks is a risk. -/
theorem standardizedRisk_mem_unitInterval {V : Type*} [Fintype V] {π r : V → ℝ}
    (hπ : ∀ v, 0 ≤ π v) (hsum : ∑ v, π v = 1) (hr : ∀ v, r v ∈ Set.Icc (0 : ℝ) 1) :
    standardizedRisk π r ∈ Set.Icc (0 : ℝ) 1 :=
  standardizedRisk_mem_Icc hπ hsum hr

end EffectMeasure

end CausalInference
