/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.EffectMeasures

/-!
# Number needed to treat

The number needed to treat as TSD 2 derives it from the absolute risks `T_k` of a treatment
and `T_1` of the reference: `NNT = 1 / (T_k - T_1)` when the events are "good" and
`1 / (T_1 - T_k)` when they are "bad" (TSD 2, Section 2.1.3, and the additional code given
after Program 1(c) in the Appendix: `NNT[k] <- 1/(T[k] - T[1])`). Both are the reciprocal of a
risk difference (`riskDiff` of `Measures/EffectMeasures.lean`) and are meaningful only for a
nonnull effect, `T_k ≠ T_1`, which every result below assumes.

## Main definitions

* `numberNeededToTreat p₁ p₀ = 1 / (p₁ - p₀)`: events are good (each treated patient gains the
  event with probability `p₁ - p₀` more).
* `numberNeededToTreatBad p₁ p₀ = 1 / (p₀ - p₁)`: events are bad (number needed to treat to
  prevent one event).

## Main results

* `numberNeededToTreat_mul_riskDiff`: `NNT × RD = 1`; treating `NNT` patients changes the
  expected number of events by exactly one.
* `numberNeededToTreatBad_eq_neg`: the two conventions differ by sign.
* `numberNeededToTreat_pos_iff`, `numberNeededToTreatBad_pos_iff`: the sign gives the direction.
* `one_le_abs_numberNeededToTreat`: for risks in `[0, 1]`, `|NNT| ≥ 1`.
* `numberNeededToTreat_not_function_of_ratios`: the number needed to treat is not a function of
  the odds ratio, nor of the risk ratio; it depends on the baseline risk. This is why TSD 2
  derives it from the absolute risks, given a baseline.
* `inv_mean_ne_mean_inv_example`: the reciprocal of a mean risk difference is not the mean of
  the reciprocals, so the posterior mean of `NNT` is not the reciprocal of the posterior mean
  of `RD`.

## References

* S. Dias, N. J. Welton, A. J. Sutton, A. E. Ades, *NICE DSU Technical Support Document 2: A
  Generalised Linear Modelling Framework for Pairwise and Network Meta-Analysis of Randomised
  Controlled Trials* (2011, updated 2016), Section 2.1.3 and the Appendix.
-/

@[expose] public section

namespace CausalInference

namespace EffectMeasure

/-- The number needed to treat when the events are good: `1 / (p₁ - p₀)`. It is meaningful
only for `p₁ ≠ p₀`. -/
noncomputable def numberNeededToTreat (p₁ p₀ : ℝ) : ℝ := 1 / riskDiff p₁ p₀

/-- The number needed to treat when the events are bad (to prevent one event):
`1 / (p₀ - p₁)`. It is meaningful only for `p₁ ≠ p₀`. -/
noncomputable def numberNeededToTreatBad (p₁ p₀ : ℝ) : ℝ := 1 / riskDiff p₀ p₁

/-- **Treating `NNT` patients changes the expected number of events by one.** For a nonnull
effect, `NNT × (p₁ - p₀) = 1`. -/
theorem numberNeededToTreat_mul_riskDiff {p₁ p₀ : ℝ} (h : p₁ ≠ p₀) :
    numberNeededToTreat p₁ p₀ * riskDiff p₁ p₀ = 1 :=
  one_div_mul_cancel (sub_ne_zero.2 h)

/-- The bad-event convention is the negative of the good-event one. -/
theorem numberNeededToTreatBad_eq_neg {p₁ p₀ : ℝ} (h : p₁ ≠ p₀) :
    numberNeededToTreatBad p₁ p₀ = -numberNeededToTreat p₁ p₀ := by
  have := sub_ne_zero.2 h
  have := sub_ne_zero.2 h.symm
  unfold numberNeededToTreatBad numberNeededToTreat riskDiff
  rw [← neg_sub, div_neg]

/-- With good events, the number needed to treat is positive exactly when the treatment raises
the risk of the event. -/
theorem numberNeededToTreat_pos_iff {p₁ p₀ : ℝ} (_h : p₁ ≠ p₀) :
    0 < numberNeededToTreat p₁ p₀ ↔ p₀ < p₁ := by
  rw [numberNeededToTreat, one_div_pos, riskDiff, sub_pos]

/-- With bad events, the number needed to treat is positive exactly when the treatment lowers
the risk of the event. -/
theorem numberNeededToTreatBad_pos_iff {p₁ p₀ : ℝ} (_h : p₁ ≠ p₀) :
    0 < numberNeededToTreatBad p₁ p₀ ↔ p₁ < p₀ := by
  rw [numberNeededToTreatBad, one_div_pos, riskDiff, sub_pos]

/-- For risks in `[0, 1]` and a nonnull effect, at least one patient must be treated:
`1 ≤ |NNT|`. -/
theorem one_le_abs_numberNeededToTreat {p₁ p₀ : ℝ} (h₁ : p₁ ∈ Set.Icc (0 : ℝ) 1)
    (h₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (h : p₁ ≠ p₀) : 1 ≤ |numberNeededToTreat p₁ p₀| := by
  have hne : riskDiff p₁ p₀ ≠ 0 := sub_ne_zero.2 h
  have hle : |riskDiff p₁ p₀| ≤ 1 := by
    rw [riskDiff, abs_le]; constructor <;> linarith [h₁.1, h₁.2, h₀.1, h₀.2]
  rw [numberNeededToTreat, abs_div, abs_one, le_div_iff₀ (abs_pos.2 hne), one_mul]
  exact hle

/-- **The number needed to treat depends on the baseline risk.** It is not a function of the
odds ratio: the risk pairs `(1/2, 1/3)` and `(1/3, 1/5)` both have odds ratio `2` but numbers
needed to treat `6` and `15/2`. Nor is it a function of the risk ratio: `(1/2, 1/4)` and
`(2/5, 1/5)` both have risk ratio `2` but numbers needed to treat `4` and `5`. -/
theorem numberNeededToTreat_not_function_of_ratios :
    (¬ ∃ f : ℝ → ℝ, ∀ p₁ p₀ : ℝ, 0 < p₁ → p₁ < 1 → 0 < p₀ → p₀ < 1 → p₁ ≠ p₀ →
      numberNeededToTreat p₁ p₀ = f (oddsRatio p₁ p₀)) ∧
    ¬ ∃ f : ℝ → ℝ, ∀ p₁ p₀ : ℝ, 0 < p₁ → p₁ < 1 → 0 < p₀ → p₀ < 1 → p₁ ≠ p₀ →
      numberNeededToTreat p₁ p₀ = f (riskRatio p₁ p₀) := by
  constructor
  · rintro ⟨f, hf⟩
    have h₁ := hf (1 / 2) (1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have h₂ := hf (1 / 3) (1 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have e₁ : oddsRatio (1 / 2) (1 / 3) = 2 := by norm_num [oddsRatio, odds]
    have e₂ : oddsRatio (1 / 3) (1 / 5) = 2 := by norm_num [oddsRatio, odds]
    rw [e₁] at h₁
    rw [e₂, ← h₁] at h₂
    norm_num [numberNeededToTreat, riskDiff] at h₂
  · rintro ⟨f, hf⟩
    have h₁ := hf (1 / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have h₂ := hf (2 / 5) (1 / 5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have e₁ : riskRatio (1 / 2) (1 / 4) = 2 := by norm_num [riskRatio]
    have e₂ : riskRatio (2 / 5) (1 / 5) = 2 := by norm_num [riskRatio]
    rw [e₁] at h₁
    rw [e₂, ← h₁] at h₂
    norm_num [numberNeededToTreat, riskDiff] at h₂

/-- **A summary of `NNT` is not the reciprocal of the summary of `RD`.** TSD 2 computes `NNT`
from each simulated pair of risks. With two equally likely risk differences `1/10` and `1/5`,
the mean number needed to treat is `15/2`, while the reciprocal of the mean risk difference
`3/20` is `20/3`. -/
theorem inv_mean_ne_mean_inv_example :
    (numberNeededToTreat (1 / 10) 0 + numberNeededToTreat (1 / 5) 0) / 2 = 15 / 2 ∧
      1 / ((riskDiff (1 / 10) 0 + riskDiff (1 / 5) 0) / 2) = 20 / 3 := by
  norm_num [numberNeededToTreat, riskDiff]

end EffectMeasure

end CausalInference
