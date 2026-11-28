/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.LinkScaleExamples
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Ordered categorical outcomes: the cumulative link model

An ordered outcome takes the categories `0, 1, …, n`. Given cut points `c_0, …, c_{n-1}`, a
linear predictor `η` and a distribution function `F`, the cumulative link model of McCullagh
(1980) sets `P(Y ≤ k) = F(c_k - η)` for `k < n` and `P(Y ≤ n) = 1`, and the category
probabilities are the increments `P(Y = k) = P(Y ≤ k) - P(Y ≤ k - 1)`. With the logistic `F`
this is the proportional odds model, used for ordered outcomes in the multilevel network
meta-regression of Phillippo et al. (2020).

* **The probabilities sum to one** (`sum_ordinalProb`) for any cut points: the sum telescopes.
* **Nonnegativity is exactly the ordering of the cut points** (`ordinalProb_nonneg_iff`): for a
  strictly increasing `F` with values in `[0, 1]`, every category probability is nonnegative if
  and only if `c_0 ≤ c_1 ≤ … ≤ c_{n-1}`. Under ordered cut points the probabilities define a
  probability law on the categories (`isProbabilityMeasure_ordinalLaw`).
* **Without the ordering the model fails** (`ordinalProb_unordered`): with the logistic `F`,
  `η = 0` and the reversed cut points `(1, 0)`, the middle category gets the probability
  `σ(0) - σ(1) < 0`, while the three values still sum to one.
* **Proportional odds** (`logit_ordinalCumulative_sub`): with the logistic `F`, the log odds of
  `Y ≤ k` at two predictors `η`, `η'` differ by `η' - η` for every `k < n`.
* **Instance** (`ordinalProb_ordered`): the cut points `(0, 1)` at `η = 0` give the probabilities
  `1/2`, `σ(1) - 1/2` and `1 - σ(1)`, all positive.

## Main definitions

* `ordinalCumulative`, `ordinalProb`, `ordinalLaw`.

## Main results

* `sum_ordinalProb`, `ordinalProb_nonneg_iff`, `isProbabilityMeasure_ordinalLaw`,
  `ordinalProb_unordered`, `logit_ordinalCumulative_sub`, `ordinalProb_ordered`.

## References

* P. McCullagh, *Regression models for ordinal data*, Journal of the Royal Statistical Society
  Series B 42 (1980).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory
open scoped ENNReal

/-- The **cumulative probabilities** of the cumulative link model with `n` cut points `c`, link
distribution `F` and predictor `η`, shifted by one: the value at `k + 1` is `P(Y ≤ k)`, equal to
`F(c_k - η)` for `k < n` and to `1` for `k ≥ n`; the value at `0` is `P(Y ≤ -1) = 0`. -/
noncomputable def ordinalCumulative (F : ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ) (η : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if k < n then F (c k - η) else 1

/-- The **category probability** `P(Y = k) = P(Y ≤ k) - P(Y ≤ k - 1)` of the cumulative link
model. -/
noncomputable def ordinalProb (F : ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  ordinalCumulative F c n η (k + 1) - ordinalCumulative F c n η k

/-- **The category probabilities sum to one**, for any link and any cut points, ordered or not:
the sum of the increments telescopes to `P(Y ≤ n) - 0 = 1`. -/
theorem sum_ordinalProb (F : ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ) (η : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ordinalProb F c n η k = 1 := by
  simp only [ordinalProb]
  rw [Finset.sum_range_sub (ordinalCumulative F c n η)]
  simp [ordinalCumulative]

/-- **Nonnegativity of the category probabilities is the ordering of the cut points.** For a
strictly increasing link distribution `F` with values in `[0, 1]`, every category probability of
the cumulative link model is nonnegative if and only if the cut points are ordered,
`c_k ≤ c_{k+1}` for `k + 1 < n`. -/
theorem ordinalProb_nonneg_iff {F : ℝ → ℝ} (hF : StrictMono F) (hF0 : ∀ x, 0 ≤ F x)
    (hF1 : ∀ x, F x ≤ 1) (c : ℕ → ℝ) (n : ℕ) (η : ℝ) :
    (∀ k ≤ n, 0 ≤ ordinalProb F c n η k) ↔ ∀ k, k + 1 < n → c k ≤ c (k + 1) := by
  constructor
  · intro h k hk
    have := h (k + 1) hk.le
    simp only [ordinalProb, ordinalCumulative, ite_eq_left hk, ite_eq_left (by omega : k < n),
      sub_nonneg] at this
    linarith [hF.le_iff_le.mp this]
  · intro h k hk
    rcases k with _ | j
    · simp only [ordinalProb, ordinalCumulative, sub_zero]
      split_ifs
      · exact hF0 _
      · exact zero_le_one
    · simp only [ordinalProb, ordinalCumulative, sub_nonneg, ite_eq_left (by omega : j < n)]
      split_ifs with hj
      · exact hF.monotone (by linarith [h j hj])
      · exact hF1 _

/-- The **law of the ordered outcome** on the categories `0, …, n`: the category probabilities
as a density with respect to the counting measure. -/
noncomputable def ordinalLaw (F : ℝ → ℝ) (c : ℕ → ℝ) (n : ℕ) (η : ℝ) : Measure (Fin (n + 1)) :=
  Measure.count.withDensity fun k => ENNReal.ofReal (ordinalProb F c n η k)

/-- **Under ordered cut points the cumulative link model is a probability law.** For a strictly
increasing link distribution `F` with values in `[0, 1]` and ordered cut points, the law of the
ordered outcome has total mass one. -/
theorem isProbabilityMeasure_ordinalLaw {F : ℝ → ℝ} (hF : StrictMono F) (hF0 : ∀ x, 0 ≤ F x)
    (hF1 : ∀ x, F x ≤ 1) {c : ℕ → ℝ} {n : ℕ} (hc : ∀ k, k + 1 < n → c k ≤ c (k + 1))
    (η : ℝ) : IsProbabilityMeasure (ordinalLaw F c n η) := by
  have hnn := (ordinalProb_nonneg_iff hF hF0 hF1 c n η).mpr hc
  constructor
  rw [ordinalLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count, tsum_fintype,
    Fin.sum_univ_eq_sum_range (fun k => ENNReal.ofReal (ordinalProb F c n η k)),
    ← ENNReal.ofReal_sum_of_nonneg
      (fun k hk => hnn k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))), sum_ordinalProb,
    ENNReal.ofReal_one]

/-- **Proportional odds.** With the logistic link, the log odds of `Y ≤ k` at the predictors `η`
and `η'` differ by `η' - η` for every `k < n`, whatever the cut points. This holds by the identity
`logit ∘ σ = id`. -/
theorem logit_ordinalCumulative_sub (c : ℕ → ℝ) {n k : ℕ} (hk : k < n) (η η' : ℝ) :
    EffectMeasure.logit (ordinalCumulative Real.sigmoid c n η (k + 1)) -
        EffectMeasure.logit (ordinalCumulative Real.sigmoid c n η' (k + 1)) = η' - η := by
  simp only [ordinalCumulative, ite_eq_left hk, EffectMeasure.logit_sigmoid]
  ring

/-- The reversed cut points `(1, 0)`. -/
noncomputable def reversedCuts (k : ℕ) : ℝ := if k = 0 then 1 else 0

/-- **The cumulative link model fails without ordered cut points.** With the logistic link, the
predictor `η = 0` and the reversed cut points `c_0 = 1 > c_1 = 0`, the middle category gets the
probability `σ(0) - σ(1) < 0`, although the three values still sum to one. -/
theorem ordinalProb_unordered :
    ordinalProb Real.sigmoid reversedCuts 2 0 1 = Real.sigmoid 0 - Real.sigmoid 1 ∧
      ordinalProb Real.sigmoid reversedCuts 2 0 1 < 0 ∧
      ∑ k ∈ Finset.range 3, ordinalProb Real.sigmoid reversedCuts 2 0 k = 1 := by
  have h : ordinalProb Real.sigmoid reversedCuts 2 0 1 = Real.sigmoid 0 - Real.sigmoid 1 := by
    simp [ordinalProb, ordinalCumulative, reversedCuts]
  refine ⟨h, ?_, sum_ordinalProb _ _ 2 0⟩
  rw [h, sub_neg]
  exact Real.sigmoid_lt zero_lt_one

/-- The ordered cut points `(0, 1)`. -/
noncomputable def orderedCuts (k : ℕ) : ℝ := if k = 0 then 0 else 1

/-- **An ordered instance.** With the logistic link, `η = 0` and the cut points `(0, 1)`, the
category probabilities are `1/2`, `σ(1) - 1/2` and `1 - σ(1)`, all positive, and the law of the
outcome is a probability law. -/
theorem ordinalProb_ordered :
    ordinalProb Real.sigmoid orderedCuts 2 0 0 = 1 / 2 ∧
      ordinalProb Real.sigmoid orderedCuts 2 0 1 = Real.sigmoid 1 - 1 / 2 ∧
      ordinalProb Real.sigmoid orderedCuts 2 0 2 = 1 - Real.sigmoid 1 ∧
      (∀ k ≤ 2, 0 < ordinalProb Real.sigmoid orderedCuts 2 0 k) ∧
      IsProbabilityMeasure (ordinalLaw Real.sigmoid orderedCuts 2 0) := by
  have h0 : ordinalProb Real.sigmoid orderedCuts 2 0 0 = 1 / 2 := by
    simp [ordinalProb, ordinalCumulative, orderedCuts, Real.sigmoid_zero]
  have h1 : ordinalProb Real.sigmoid orderedCuts 2 0 1 = Real.sigmoid 1 - 1 / 2 := by
    simp [ordinalProb, ordinalCumulative, orderedCuts, Real.sigmoid_zero]
  have h2 : ordinalProb Real.sigmoid orderedCuts 2 0 2 = 1 - Real.sigmoid 1 := by
    simp [ordinalProb, ordinalCumulative, orderedCuts]
  have hs : (1 : ℝ) / 2 < Real.sigmoid 1 := by
    rw [one_div, ← Real.sigmoid_zero]; exact Real.sigmoid_lt zero_lt_one
  refine ⟨h0, h1, h2, fun k hk => ?_, isProbabilityMeasure_ordinalLaw Real.sigmoid_strictMono
    Real.sigmoid_nonneg Real.sigmoid_le_one (fun k hk => ?_) 0⟩
  · interval_cases k
    · rw [h0]; norm_num
    · rw [h1]; linarith
    · rw [h2]; linarith [Real.sigmoid_lt_one 1]
  · have : k = 0 := by omega
    subst this
    norm_num [orderedCuts]

end NetworkMetaRegression

end CausalInference
