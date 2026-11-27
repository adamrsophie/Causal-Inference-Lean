/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.MisclassificationTables
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Diagnostic accuracy measures

Summary measures of a binary diagnostic test with sensitivity `se` and specificity `sp`, and of a
continuous test read at a threshold, following NICE DSU Technical Support Document 25, Section 2.
The predictive values `ppvBayes` and `npvBayes` (equations (1) and (2) of TSD 25) are those of
`BiasAnalysis.MisclassificationTables`.

## Main definitions

* `lrPos se sp = se / (1 - sp)`, `lrNeg se sp = (1 - se) / sp`: the positive and negative
  likelihood ratios; `dor se sp = lrPos se sp / lrNeg se sp`: the diagnostic odds ratio;
  `youden se sp = se + sp - 1`: the Youden index. TSD 25, Section 2.4 names these measures ("can
  be calculated as functions of sensitivity and specificity") without printing formulas; the
  formulas used here are the standard ones.
* `dorExt`, `lrPosExt`, `lrNegExt`: the same ratios on the closed square `[0, 1]²` with values
  in `Option ℝ≥0∞` (`extDiv`): `some x` for a finite value, `some ⊤` for a positive numerator
  over a zero denominator, `none` for `0 / 0`. Zero cells are "not uncommon" (TSD 25, Section 3).
* `posFraction P c = P [c, ∞)`: the fraction testing positive at threshold `c` for a score law
  `P`. With the score law `PD` of the diseased it is the sensitivity `Se(c)`, with the score law
  `PND` of the disease free the false positive fraction `FPF(c)` (Section 2.3).
* `concordance PD PND = P(Y_D > Y_ND)` and `tieProb PD PND = P(Y_D = Y_ND)` for independent
  diseased and disease free scores; `auc PD PND = P(Y_D > Y_ND) + P(Y_D = Y_ND) / 2`: the
  concordance form of the area under the ROC curve (Section 2.4), with half weight on ties.

## Main results

* `odds_ppvBayes`, `odds_one_sub_npvBayes`: Bayes' theorem in odds form. The post-test odds of
  disease are the likelihood ratio times the pre-test odds `π / (1 - π)`.
* `dor_eq`: `DOR = (se / (1 - se)) (sp / (1 - sp))`; `one_lt_lrPos_iff`, `lrNeg_lt_one_iff`,
  `one_lt_dor_iff`, `dor_eq_one_iff`: the
  diagnostic odds ratio exceeds one exactly when the Youden index is positive, and equals one
  exactly when it vanishes; `youden_eq_det`: the Youden index is the determinant of the
  misclassification matrix (`Bias.misclassMatrix_det`), the quantity whose vanishing makes the
  prevalence unidentified (`Bias.prevalence_not_identified`).
* `dorExt_eq_ofReal_dor`, `lrPosExt_eq_ofReal_lrPos`, `lrNegExt_eq_ofReal_lrNeg`: agreement
  with the real formulas when the denominator is positive; `dorExt_eq_top_iff`,
  `dorExt_eq_zero_iff`, `dorExt_eq_none_iff`, `dorExt_eq_none_iff_of_mem`: the three boundary
  cases; `dorExt_perfect` (`se = sp = 1`: infinite, while the real `dor` is `0`) and
  `dorExt_one_zero` (`se = 1`, `sp = 0`: indeterminate); `dorExt_mono_se`, `dorExt_mono_sp`:
  monotone in sensitivity and in specificity where defined.
* `npvBayes_strictAntiOn`: the negative predictive value decreases with prevalence when
  `se < 1` and `0 < sp`, derived here from equation (2) of TSD 25, Section 2.2 (the document
  does not state the monotonicity); the counterpart of `ppvBayes_strictMonoOn`.
  `npvBayes_perfect_sensitivity` shows that `se < 1` is needed.
* `posFraction_antitone`, `roc_comonotone`: raising the threshold lowers both the
  sensitivity and the false positive fraction (Section 2.3), so the points of studies that share
  the score laws but use different thresholds are comonotone (Section 3: threshold variation
  makes sensitivity and specificity negatively correlated); `roc_not_comonotone_of_laws` shows
  that the shared laws are needed.
* `auc_eq_integral`: `auc PD PND = ∫ (PD (y, ∞) + PD {y} / 2) dPND(y)`; `auc_eq_average`:
  the area is the average of the strict concordance `P(Y_D > Y_ND)` and the weak one
  `∫ Se dPND`; `auc_eq_concordance_of_tieProb_eq_zero`: without ties it is the strict
  concordance; `auc_eq_integral_posFraction`: when every point has `PD` mass zero,
  `auc PD PND = ∫ Se dPND`, the Lebesgue Stieltjes form `∫ Se d(-FPF)` of the area under the
  ROC curve, since `FPF(c) = PND [c, ∞)`. `auc_ne_integral_posFraction_of_atom`: for two point
  masses at `0` the area is `1/2` while the strict form is `0` and the weak form `1`. The
  change of variables to `∫₀¹ ROC(t) dt` is not stated.

## Sources

* NICE DSU Technical Support Document 25: E. Derezea, A. E. Ades, G. Rogers, A. J. Sutton,
  N. J. Cooper, J. Hamilton and H. E. Jones (2024), Evidence synthesis of diagnostic test
  accuracy for decision making, Sections 2.1 to 2.4 and 3.
* M. S. Pepe (2003), The Statistical Evaluation of Medical Tests for Classification and
  Prediction, Oxford University Press (reference 10 of TSD 25, cited for the terminology).
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace DiagnosticAccuracy

open MeasureTheory MisclassificationTables EffectMeasure Set

/-! ### Likelihood ratios, diagnostic odds ratio, Youden index -/

/-- The positive likelihood ratio `LR+ = se / (1 - sp)`: the ratio of the probabilities of a
positive test in the diseased and in the disease free. This is the formula for `sp < 1`, which
every theorem using it assumes; at `sp = 1` (no false positives) Lean's totalized division
returns `0`. `lrPosExt` gives the honest value on the closed square. -/
noncomputable def lrPos (se sp : ℝ) : ℝ := se / (1 - sp)

/-- The negative likelihood ratio `LR- = (1 - se) / sp`: the ratio of the probabilities of a
negative test in the diseased and in the disease free. This is the formula for `0 < sp`, which
every theorem using it assumes; at `sp = 0` Lean's totalized division returns `0`. `lrNegExt`
gives the honest value on the closed square. -/
noncomputable def lrNeg (se sp : ℝ) : ℝ := (1 - se) / sp

/-- The diagnostic odds ratio `DOR = LR+ / LR-`, the interior formula: it is the diagnostic odds
ratio only when `se < 1` and `sp < 1` (and `0 ≤ se`), which every theorem using it assumes. On a
table with a zero false positive or false negative cell it returns the totalized `0`, also for a
perfect test whose ratio is infinite (`dorExt_perfect`). `dorExt` is the version on the closed
square that separates finite, infinite and indeterminate values, and agrees with this one when
the denominator is positive (`dorExt_eq_ofReal_dor`). -/
noncomputable def dor (se sp : ℝ) : ℝ := lrPos se sp / lrNeg se sp

/-- The Youden index `J = se + sp - 1`. -/
def youden (se sp : ℝ) : ℝ := se + sp - 1

/-- The diagnostic odds ratio is the product of the odds of a positive test in the diseased and
of a negative test in the disease free: `DOR = (se / (1 - se)) (sp / (1 - sp))`, for `se < 1`
and `0 < sp < 1`. -/
theorem dor_eq {se sp : ℝ} (hse : se < 1) (hsp0 : 0 < sp) (hsp1 : sp < 1) :
    dor se sp = odds se * odds sp := by
  have h1 : 1 - se ≠ 0 := by linarith
  have h2 : 1 - sp ≠ 0 := by linarith
  unfold dor lrPos lrNeg odds
  field_simp

/-- The diagnostic odds ratio exceeds one exactly when the Youden index is positive, that is
`se + sp > 1`, for `0 < se < 1` and `0 < sp < 1`. -/
theorem one_lt_dor_iff {se sp : ℝ} (hse0 : 0 < se) (hse1 : se < 1) (hsp0 : 0 < sp)
    (hsp1 : sp < 1) : 1 < dor se sp ↔ 0 < youden se sp := by
  have h1 : 0 < 1 - se := by linarith
  have h2 : 0 < 1 - sp := by linarith
  have e : dor se sp = (se * sp) / ((1 - se) * (1 - sp)) := by
    unfold dor lrPos lrNeg
    field_simp
  rw [e, one_lt_div (mul_pos h1 h2), youden]
  constructor <;> intro h <;> nlinarith

/-- The diagnostic odds ratio equals one exactly when the Youden index vanishes, that is the
test is uninformative, for `0 < se < 1` and `0 < sp < 1`. -/
theorem dor_eq_one_iff {se sp : ℝ} (hse1 : se < 1) (hsp0 : 0 < sp) (hsp1 : sp < 1) :
    dor se sp = 1 ↔ youden se sp = 0 := by
  have h1 : 0 < 1 - se := by linarith
  have h2 : 0 < 1 - sp := by linarith
  have e : dor se sp = (se * sp) / ((1 - se) * (1 - sp)) := by
    unfold dor lrPos lrNeg
    field_simp
  rw [e, div_eq_one_iff_eq (mul_pos h1 h2).ne', youden]
  constructor <;> intro h <;> linear_combination h

/-- The positive likelihood ratio exceeds one exactly when the Youden index is positive, for
`sp < 1`. -/
theorem one_lt_lrPos_iff {se sp : ℝ} (hsp : sp < 1) : 1 < lrPos se sp ↔ 0 < youden se sp := by
  rw [lrPos, one_lt_div (by linarith), youden]
  constructor <;> intro h <;> linarith

/-- The negative likelihood ratio is below one exactly when the Youden index is positive, for
`0 < sp`. -/
theorem lrNeg_lt_one_iff {se sp : ℝ} (hsp : 0 < sp) : lrNeg se sp < 1 ↔ 0 < youden se sp := by
  rw [lrNeg, div_lt_one hsp, youden]
  constructor <;> intro h <;> linarith

/-- The Youden index is the determinant of the misclassification matrix
(`Bias.misclassMatrix_det`); when it vanishes the observed prevalence does not depend on the
true prevalence (`Bias.prevalence_not_identified`). -/
theorem youden_eq_det (se sp : ℝ) : youden se sp = (Bias.misclassMatrix se sp).det := by
  rw [Bias.misclassMatrix_det, youden]

/-! ### Boundary values: zero cells

A valid 2×2 table may have a zero cell, so that sensitivity or specificity equals `0` or `1`;
TSD 25, Section 3 notes that "small or zero cell counts in 2×2 tables (very few FPs or very few
FNs in some studies) are not uncommon". The real-valued `lrPos`, `lrNeg` and `dor` then return
Lean's totalized `x / 0 = 0`, which is wrong for a perfect test (whose diagnostic odds ratio is
infinite). The versions below take values in `Option ℝ≥0∞`: `some x` with `x` finite for a
finite ratio, `some ⊤` for a positive numerator over a zero denominator, and `none` for the
indeterminate `0 / 0`. -/

open scoped ENNReal

/-- A ratio of extended nonnegative reals that keeps the indeterminate case apart:
`none` for `0 / 0`, and `some (a / b)` otherwise (so `some ⊤` for `a ≠ 0` over `b = 0`). -/
noncomputable def extDiv (a b : ℝ≥0∞) : Option ℝ≥0∞ :=
  open Classical in if a = 0 ∧ b = 0 then none else some (a / b)

theorem extDiv_eq_none_iff {a b : ℝ≥0∞} : extDiv a b = none ↔ a = 0 ∧ b = 0 := by
  unfold extDiv; split_ifs with h <;> simp [h]

theorem extDiv_of_ne_zero {a b : ℝ≥0∞} (hb : b ≠ 0) : extDiv a b = some (a / b) := by
  unfold extDiv; simp [hb]

/-- The ratio is infinite exactly when a finite positive numerator meets a zero denominator. -/
theorem extDiv_eq_some_top_iff {a b : ℝ≥0∞} (ha : a ≠ ⊤) :
    extDiv a b = some ⊤ ↔ a ≠ 0 ∧ b = 0 := by
  unfold extDiv
  split_ifs with h
  · simp [h.1]
  · rw [Option.some_inj, ENNReal.div_eq_top]
    constructor
    · rintro (h' | h'); exacts [h', absurd h'.1 ha]
    · exact Or.inl

/-- The ratio is zero exactly when the numerator is zero and a finite denominator is not. -/
theorem extDiv_eq_some_zero_iff {a b : ℝ≥0∞} (hb : b ≠ ⊤) :
    extDiv a b = some 0 ↔ a = 0 ∧ b ≠ 0 := by
  unfold extDiv
  split_ifs with h
  · simp [h.2]
  · rw [Option.some_inj, ENNReal.div_eq_zero_iff, or_iff_left hb]
    exact ⟨fun h' => ⟨h', fun hb0 => h ⟨h', hb0⟩⟩, And.left⟩

/-- The numerator `se · sp` of the diagnostic odds ratio, computed in `ℝ≥0∞`. -/
noncomputable def dorNum (se sp : ℝ) : ℝ≥0∞ := ENNReal.ofReal se * ENNReal.ofReal sp

/-- The denominator `(1 - se) (1 - sp)` of the diagnostic odds ratio, computed in `ℝ≥0∞`. -/
noncomputable def dorDen (se sp : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 - se) * ENNReal.ofReal (1 - sp)

/-- The diagnostic odds ratio on the closed square, with values in `Option ℝ≥0∞`:
`se · sp / ((1 - se) (1 - sp))` computed in `ℝ≥0∞`, `some ⊤` when the numerator is positive and
the denominator zero (a perfect test), and `none` when both vanish (for example `se = 1`,
`sp = 0`). It agrees with the interior formula `dor` whenever the denominator is positive
(`dorExt_eq_ofReal_dor`). -/
noncomputable def dorExt (se sp : ℝ) : Option ℝ≥0∞ := extDiv (dorNum se sp) (dorDen se sp)

/-- The positive likelihood ratio `se / (1 - sp)` with values in `Option ℝ≥0∞`, as for
`dorExt`: infinite for `se > 0`, `sp = 1`; indeterminate for `se = 0`, `sp = 1`. -/
noncomputable def lrPosExt (se sp : ℝ) : Option ℝ≥0∞ :=
  extDiv (ENNReal.ofReal se) (ENNReal.ofReal (1 - sp))

/-- The negative likelihood ratio `(1 - se) / sp` with values in `Option ℝ≥0∞`, as for
`dorExt`: infinite for `se < 1`, `sp = 0`; indeterminate for `se = 1`, `sp = 0`. -/
noncomputable def lrNegExt (se sp : ℝ) : Option ℝ≥0∞ :=
  extDiv (ENNReal.ofReal (1 - se)) (ENNReal.ofReal sp)

theorem dorNum_eq_zero_iff {se sp : ℝ} : dorNum se sp = 0 ↔ se ≤ 0 ∨ sp ≤ 0 := by
  simp [dorNum, ENNReal.ofReal_eq_zero]

theorem dorDen_eq_zero_iff {se sp : ℝ} : dorDen se sp = 0 ↔ 1 ≤ se ∨ 1 ≤ sp := by
  simp [dorDen, ENNReal.ofReal_eq_zero]

/-- The real-valued `dor` is `se · sp / ((1 - se) (1 - sp))` for all real `se` and `sp`, the
totalized division included. -/
theorem dor_eq_div (se sp : ℝ) : dor se sp = se * sp / ((1 - se) * (1 - sp)) := by
  simp only [dor, lrPos, lrNeg, div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- **Agreement with the interior formula.** Whenever the denominator is positive
(`se < 1`, `sp < 1`), with `0 ≤ se`, `dorExt` is the real `dor` (mapped to `ℝ≥0∞`); in
particular on the open square `0 < se < 1`, `0 < sp < 1`. -/
theorem dorExt_eq_ofReal_dor {se sp : ℝ} (hse0 : 0 ≤ se) (hse1 : se < 1) (hsp1 : sp < 1) :
    dorExt se sp = some (ENNReal.ofReal (dor se sp)) := by
  have hD : 0 < (1 - se) * (1 - sp) := mul_pos (by linarith) (by linarith)
  rw [dorExt, extDiv_of_ne_zero (by rw [Ne, dorDen_eq_zero_iff]; push Not; exact ⟨hse1, hsp1⟩),
    dor_eq_div, ENNReal.ofReal_div_of_pos hD, ENNReal.ofReal_mul hse0,
    ENNReal.ofReal_mul (by linarith), dorNum, dorDen]

/-- `dorExt` is infinite exactly when the numerator is positive and the denominator zero. -/
theorem dorExt_eq_top_iff {se sp : ℝ} :
    dorExt se sp = some ⊤ ↔ dorNum se sp ≠ 0 ∧ dorDen se sp = 0 :=
  extDiv_eq_some_top_iff (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- `dorExt` is zero exactly when the numerator is zero and the denominator positive. -/
theorem dorExt_eq_zero_iff {se sp : ℝ} :
    dorExt se sp = some 0 ↔ dorNum se sp = 0 ∧ dorDen se sp ≠ 0 :=
  extDiv_eq_some_zero_iff (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

/-- `dorExt` is indeterminate exactly when numerator and denominator both vanish. -/
theorem dorExt_eq_none_iff {se sp : ℝ} :
    dorExt se sp = none ↔ dorNum se sp = 0 ∧ dorDen se sp = 0 :=
  extDiv_eq_none_iff

/-- On the closed square the three cases in terms of `se` and `sp`: `dorExt` is indeterminate
exactly when one of `se`, `sp` is `0` and the other is `1`. -/
theorem dorExt_eq_none_iff_of_mem {se sp : ℝ} (hse : se ∈ Icc (0 : ℝ) 1)
    (hsp : sp ∈ Icc (0 : ℝ) 1) :
    dorExt se sp = none ↔ (se = 0 ∧ sp = 1) ∨ (se = 1 ∧ sp = 0) := by
  obtain ⟨a0, a1⟩ := hse; obtain ⟨b0, b1⟩ := hsp
  rw [dorExt_eq_none_iff, dorNum_eq_zero_iff, dorDen_eq_zero_iff]
  constructor
  · rintro ⟨h | h, h' | h'⟩
    · exact absurd h' (by linarith)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact absurd h (by linarith)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- **A perfect test** (`se = sp = 1`) has an infinite diagnostic odds ratio, while the
totalized real `dor 1 1` is `0`. -/
theorem dorExt_perfect : dorExt 1 1 = some ⊤ ∧ dor 1 1 = 0 := by
  refine ⟨dorExt_eq_top_iff.2 ⟨?_, ?_⟩, by simp [dor, lrPos, lrNeg]⟩
  · rw [Ne, dorNum_eq_zero_iff]; norm_num
  · rw [dorDen_eq_zero_iff]; norm_num

/-- A test that is positive in everyone (`se = 1`, `sp = 0`) has an indeterminate diagnostic
odds ratio: `0 / 0`. -/
theorem dorExt_one_zero : dorExt 1 0 = none :=
  dorExt_eq_none_iff.2 ⟨dorNum_eq_zero_iff.2 (Or.inr le_rfl), dorDen_eq_zero_iff.2 (Or.inl le_rfl)⟩

/-- Where defined, `dorExt` is monotone in the sensitivity. -/
theorem dorExt_mono_se {se se' sp : ℝ} {a b : ℝ≥0∞} (h : se ≤ se') (ha : dorExt se sp = some a)
    (hb : dorExt se' sp = some b) : a ≤ b := by
  unfold dorExt extDiv at ha hb
  split_ifs at ha hb
  cases ha; cases hb
  exact ENNReal.div_le_div (mul_le_mul_left (ENNReal.ofReal_le_ofReal h) _)
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _)

/-- Where defined, `dorExt` is monotone in the specificity. -/
theorem dorExt_mono_sp {se sp sp' : ℝ} {a b : ℝ≥0∞} (h : sp ≤ sp') (ha : dorExt se sp = some a)
    (hb : dorExt se sp' = some b) : a ≤ b := by
  unfold dorExt extDiv at ha hb
  split_ifs at ha hb
  cases ha; cases hb
  exact ENNReal.div_le_div (mul_le_mul_right (ENNReal.ofReal_le_ofReal h) _)
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal (by linarith)) _)

/-- `lrPosExt` agrees with `lrPos` (mapped to `ℝ≥0∞`) when `sp < 1`. -/
theorem lrPosExt_eq_ofReal_lrPos {se sp : ℝ} (hsp : sp < 1) :
    lrPosExt se sp = some (ENNReal.ofReal (lrPos se sp)) := by
  have hD : 0 < 1 - sp := by linarith
  rw [lrPosExt, extDiv_of_ne_zero (ENNReal.ofReal_pos.2 hD).ne', lrPos,
    ENNReal.ofReal_div_of_pos hD]

/-- `lrNegExt` agrees with `lrNeg` (mapped to `ℝ≥0∞`) when `0 < sp`. -/
theorem lrNegExt_eq_ofReal_lrNeg {se sp : ℝ} (hsp : 0 < sp) :
    lrNegExt se sp = some (ENNReal.ofReal (lrNeg se sp)) := by
  rw [lrNegExt, extDiv_of_ne_zero (ENNReal.ofReal_pos.2 hsp).ne', lrNeg,
    ENNReal.ofReal_div_of_pos hsp]

/-- Perfect specificity: `LR+` is infinite for `se > 0` (here `se = 1/2`) and indeterminate for
`se = 0`; the totalized real `lrPos (1/2) 1` is `0`. -/
theorem lrPosExt_perfect_specificity :
    lrPosExt (1 / 2) 1 = some ⊤ ∧ lrPosExt 0 1 = none ∧ lrPos (1 / 2) 1 = 0 := by
  refine ⟨(extDiv_eq_some_top_iff ENNReal.ofReal_ne_top).2 ⟨?_, ?_⟩,
    extDiv_eq_none_iff.2 ⟨by simp, by simp⟩, by simp [lrPos]⟩
  · simp
  · simp

/-- Zero specificity: `LR-` is infinite for `se < 1` (here `se = 1/2`) and indeterminate for
`se = 1`; the totalized real `lrNeg (1/2) 0` is `0`. -/
theorem lrNegExt_zero_specificity :
    lrNegExt (1 / 2) 0 = some ⊤ ∧ lrNegExt 1 0 = none ∧ lrNeg (1 / 2) 0 = 0 := by
  refine ⟨(extDiv_eq_some_top_iff ENNReal.ofReal_ne_top).2 ⟨?_, ?_⟩,
    extDiv_eq_none_iff.2 ⟨by simp, by simp⟩, by simp [lrNeg]⟩
  · norm_num
  · simp

/-! ### Bayes' theorem in odds form and predictive values (TSD 25, Section 2.2) -/

/-- Bayes' theorem in odds form for a positive test: the post-test odds of disease after a
positive result are `LR+` times the pre-test odds, `odds(PPV) = LR+ · odds(π)`, for a
prevalence `0 < π < 1`, `0 ≤ se` and `sp < 1`. -/
theorem odds_ppvBayes {se sp π : ℝ} (hse : 0 ≤ se) (hsp : sp < 1) (hπ0 : 0 < π)
    (hπ1 : π < 1) : odds (ppvBayes se sp π) = lrPos se sp * odds π := by
  have h1 : 0 < 1 - sp := by linarith
  have h2 : 0 < 1 - π := by linarith
  have hD : 0 < se * π + (1 - sp) * (1 - π) := by
    nlinarith [mul_pos h1 h2, mul_nonneg hse hπ0.le]
  unfold odds ppvBayes lrPos
  rw [one_sub_div hD.ne']
  field_simp
  ring

/-- Bayes' theorem in odds form for a negative test: the post-test odds of disease after a
negative result are `LR-` times the pre-test odds, `(1 - NPV) / NPV = LR- · odds(π)`, for a
prevalence `0 < π < 1`, `se ≤ 1` and `0 < sp`. -/
theorem odds_one_sub_npvBayes {se sp π : ℝ} (hse : se ≤ 1) (hsp : 0 < sp) (hπ0 : 0 < π)
    (hπ1 : π < 1) : odds (1 - npvBayes se sp π) = lrNeg se sp * odds π := by
  have h2 : 0 < 1 - π := by linarith
  have hD : 0 < sp * (1 - π) + (1 - se) * π := by
    nlinarith [mul_pos hsp h2, mul_nonneg (sub_nonneg.2 hse) hπ0.le]
  have e : 1 - npvBayes se sp π = (1 - se) * π / (sp * (1 - π) + (1 - se) * π) := by
    unfold npvBayes
    field_simp
    ring
  rw [odds, sub_sub_cancel, e, npvBayes, lrNeg, odds]
  field_simp

/-- The negative predictive value decreases with prevalence: for `se < 1` and `0 < sp`,
`npvBayes se sp` is strictly decreasing on `[0, 1]`. This is derived here from equation (2) of
TSD 25, Section 2.2, which prints the formula but not the monotonicity. It is the
counterpart of `MisclassificationTables.ppvBayes_strictMonoOn`. -/
theorem npvBayes_strictAntiOn {se sp : ℝ} (hse : se < 1) (hsp : 0 < sp) :
    StrictAntiOn (npvBayes se sp) (Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hfn : 0 < 1 - se := by linarith
  have hdx : 0 < sp * (1 - x) + (1 - se) * x := by
    nlinarith [mul_pos hsp (by linarith : (0 : ℝ) < 1 - x), mul_nonneg hfn.le hx0]
  have hdy : 0 < sp * (1 - y) + (1 - se) * y := by
    nlinarith [mul_pos hfn (by linarith : (0 : ℝ) < y), mul_nonneg hsp.le (by linarith :
      (0 : ℝ) ≤ 1 - y)]
  unfold npvBayes
  rw [div_lt_div_iff₀ hdy hdx]
  nlinarith [mul_pos (mul_pos hsp hfn) (sub_pos.mpr hxy)]

/-- The condition `se < 1` is needed in `npvBayes_strictAntiOn`: with perfect sensitivity a
negative result rules the disease out at every prevalence below one, so the negative predictive
value is constant there (`NPV = 1` at `π = 0` and at `π = 1/2` for `sp = 1/2`). -/
theorem npvBayes_perfect_sensitivity : ¬ StrictAntiOn (npvBayes 1 (1 / 2)) (Icc 0 1) := by
  intro h
  have := h (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
    (by norm_num)
  norm_num [npvBayes] at this

/-! ### Thresholds and the ROC curve (TSD 25, Sections 2.3 and 3) -/

/-- The fraction of a population with score law `P` that tests positive at threshold `c`, that
is `P [c, ∞)`. With the score law `PD` of the diseased it is the sensitivity `Se(c)`; with the
score law `PND` of the disease free it is the false positive fraction `FPF(c) = 1 - Sp(c)`.
The ROC curve is the set of points `(FPF(c), Se(c))`. -/
noncomputable def posFraction (P : Measure ℝ) (c : ℝ) : ℝ := P.real (Ici c)

/-- Raising the threshold lowers the fraction testing positive: `Se` and `FPF` are antitone in
the threshold (TSD 25, Section 2.3). -/
theorem posFraction_antitone (P : Measure ℝ) [IsFiniteMeasure P] : Antitone (posFraction P) :=
  fun _ _ h => measureReal_mono (Ici_subset_Ici.2 h)

/-- Threshold variation moves sensitivity and false positive fraction together (TSD 25,
Sections 2.3 and 3): for studies that share the score laws `PD` and `PND` but read the test at
thresholds `c` and `c'`, the differences in `Se` and in `FPF` have the same sign. So across such
studies sensitivity and specificity are negatively related. -/
theorem roc_comonotone (PD PND : Measure ℝ) [IsFiniteMeasure PD] [IsFiniteMeasure PND]
    (c c' : ℝ) :
    0 ≤ (posFraction PD c - posFraction PD c') * (posFraction PND c - posFraction PND c') := by
  rcases le_total c c' with h | h
  · exact mul_nonneg (sub_nonneg.2 (posFraction_antitone PD h))
      (sub_nonneg.2 (posFraction_antitone PND h))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (posFraction_antitone PD h))
      (sub_nonpos.2 (posFraction_antitone PND h))

/-- The shared score laws are needed in `roc_comonotone`: two studies at the same threshold
`1/2`, one with diseased scores `1` and disease free scores `0`, the other with the roles
reversed, have `(FPF, Se) = (0, 1)` and `(1, 0)`. -/
theorem roc_not_comonotone_of_laws :
    (posFraction (Measure.dirac 1) (1 / 2) - posFraction (Measure.dirac 0) (1 / 2)) *
      (posFraction (Measure.dirac 0) (1 / 2) - posFraction (Measure.dirac 1) (1 / 2)) < 0 := by
  simp only [posFraction, measureReal_def, Measure.dirac_apply' _ measurableSet_Ici,
    indicator, mem_Ici]
  norm_num

/-! ### The area under the ROC curve (TSD 25, Section 2.4) -/

/-- The strict concordance probability `P(Y_D > Y_ND)`: the probability that a diseased score
exceeds an independent disease free score, with score laws `PD` and `PND`. It is the area under
the ROC curve only when ties have probability zero (`auc_eq_concordance_of_tieProb_eq_zero`). -/
noncomputable def concordance (PD PND : Measure ℝ) : ℝ :=
  (PD.prod PND).real {p : ℝ × ℝ | p.2 < p.1}

/-- The tie probability `P(Y_D = Y_ND)` of independent diseased and disease free scores. -/
noncomputable def tieProb (PD PND : Measure ℝ) : ℝ :=
  (PD.prod PND).real {p : ℝ × ℝ | p.1 = p.2}

/-- The area under the ROC curve in concordance form with half weight on ties:
`AUC = P(Y_D > Y_ND) + P(Y_D = Y_ND) / 2`. With ties this is the area under the ROC curve whose
points `(FPF(c), Se(c))` are joined by straight segments; for identical score laws with an atom
it gives the chance value `1/2` (`auc_dirac_self`). -/
noncomputable def auc (PD PND : Measure ℝ) : ℝ := concordance PD PND + tieProb PD PND / 2

/-- The sensitivity at `y` splits into the atom at `y` and the mass above `y`:
`PD [y, ∞) = PD {y} + PD (y, ∞)`. -/
theorem posFraction_eq_add (P : Measure ℝ) [IsFiniteMeasure P] (y : ℝ) :
    posFraction P y = P.real {y} + P.real (Ioi y) := by
  rw [posFraction, ← insert_Ioi, insert_eq,
    measureReal_union (by simp) measurableSet_Ioi]

/-- Fubini for the strict concordance probability: `P(Y_D > Y_ND) = ∫ PD (y, ∞) dPND(y)`. -/
theorem concordance_eq_integral (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] : concordance PD PND = ∫ y, PD.real (Ioi y) ∂PND := by
  have hpre : ∀ y : ℝ, (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | p.2 < p.1} = Ioi y := by
    intro y; ext x; simp
  have hanti : Antitone fun y : ℝ => PD (Ioi y) := fun _ _ h => measure_mono (Ioi_subset_Ioi h)
  rw [concordance, measureReal_def, Measure.prod_apply_symm (measurableSet_lt measurable_snd
    measurable_fst)]
  simp_rw [hpre, measureReal_def]
  rw [integral_toReal hanti.measurable.aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)]

/-- Fubini for the weak concordance probability: `P(Y_D ≥ Y_ND) = ∫ Se dPND`, with
`Se(y) = PD [y, ∞)`. -/
theorem prod_real_le_eq_integral (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] :
    (PD.prod PND).real {p : ℝ × ℝ | p.2 ≤ p.1} = ∫ y, posFraction PD y ∂PND := by
  have hpre : ∀ y : ℝ, (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | p.2 ≤ p.1} = Ici y := by
    intro y; ext x; simp
  have hanti : Antitone fun y : ℝ => PD (Ici y) := fun _ _ h => measure_mono (Ici_subset_Ici.2 h)
  rw [measureReal_def, Measure.prod_apply_symm (measurableSet_le measurable_snd
    measurable_fst)]
  simp_rw [hpre, posFraction, measureReal_def]
  rw [integral_toReal hanti.measurable.aemeasurable (ae_of_all _ fun _ => measure_lt_top _ _)]

/-- The tie probability is the weak minus the strict concordance probability. -/
theorem tieProb_eq_sub (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] :
    tieProb PD PND = (PD.prod PND).real {p : ℝ × ℝ | p.2 ≤ p.1} - concordance PD PND := by
  have hdiff : {p : ℝ × ℝ | p.2 ≤ p.1} \ {p : ℝ × ℝ | p.2 < p.1} = {p : ℝ × ℝ | p.1 = p.2} := by
    ext p; simp only [mem_sdiff, mem_ofPred_eq, not_lt]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
    · intro h; exact ⟨h.ge, h.le⟩
  rw [tieProb, concordance, ← hdiff, measureReal_sdiff (fun p hp => le_of_lt hp)
    (measurableSet_lt measurable_snd measurable_fst)]

/-- Fubini for the tie probability: `P(Y_D = Y_ND) = ∫ PD {y} dPND(y)`. -/
theorem tieProb_eq_integral (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] : tieProb PD PND = ∫ y, PD.real {y} ∂PND := by
  have hint : ∀ s : ℝ → Set ℝ, Antitone (fun y => PD.real (s y)) →
      Integrable (fun y => PD.real (s y)) PND := fun s hs =>
    Integrable.of_bound hs.measurable.aestronglyMeasurable 1 (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hIci : Antitone (fun y => PD.real (Ici y)) :=
    fun _ _ h => measureReal_mono (Ici_subset_Ici.2 h)
  have hIoi : Antitone (fun y => PD.real (Ioi y)) :=
    fun _ _ h => measureReal_mono (Ioi_subset_Ioi h)
  rw [tieProb_eq_sub, prod_real_le_eq_integral, concordance_eq_integral]
  unfold posFraction
  rw [← integral_sub (hint _ hIci) (hint _ hIoi)]
  congr 1
  funext y
  rw [← posFraction, posFraction_eq_add, add_sub_cancel_right]

/-- **Integral form of the area under the ROC curve.**
`AUC = ∫ (PD (y, ∞) + PD {y} / 2) dPND(y)`. -/
theorem auc_eq_integral (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] :
    auc PD PND = ∫ y, (PD.real (Ioi y) + PD.real {y} / 2) ∂PND := by
  have hIoi : Integrable (fun y => PD.real (Ioi y)) PND :=
    Integrable.of_bound (Antitone.measurable (fun _ _ h => measureReal_mono (Ioi_subset_Ioi h) :
      Antitone fun y => PD.real (Ioi y))).aestronglyMeasurable 1
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have hsing : Integrable (fun y => PD.real {y}) PND := by
    have : (fun y => PD.real {y}) = fun y => posFraction PD y - PD.real (Ioi y) := by
      funext y
      rw [posFraction_eq_add, add_sub_cancel_right]
    rw [this]
    refine Integrable.sub (Integrable.of_bound
      (posFraction_antitone PD).measurable.aestronglyMeasurable 1 (ae_of_all _ fun y => ?_)) hIoi
    rw [Real.norm_eq_abs, posFraction, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  rw [auc, concordance_eq_integral, tieProb_eq_integral, integral_add hIoi (hsing.div_const 2),
    integral_div]

/-- The area under the ROC curve is the average of the strict and the weak concordance
probabilities: `AUC = (P(Y_D > Y_ND) + ∫ Se dPND) / 2`. -/
theorem auc_eq_average (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] :
    auc PD PND = (concordance PD PND + ∫ y, posFraction PD y ∂PND) / 2 := by
  rw [auc, tieProb_eq_sub, prod_real_le_eq_integral]; ring

/-- Without ties the area under the ROC curve is the strict concordance probability
`P(Y_D > Y_ND)`. -/
theorem auc_eq_concordance_of_tieProb_eq_zero {PD PND : Measure ℝ}
    (h : tieProb PD PND = 0) : auc PD PND = concordance PD PND := by
  rw [auc, h, zero_div, add_zero]

/-- If the diseased score law has no atoms, ties have probability zero. -/
theorem tieProb_eq_zero (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] [NullSingletonClass PD] : tieProb PD PND = 0 := by
  rw [tieProb_eq_integral]
  simp [measureReal_def]

/-- The area under the ROC curve as an integral of the sensitivity: if the diseased score law
has no atoms, `AUC = P(Y_D > Y_ND) = ∫ Se(y) dPND(y)`, which is the Lebesgue Stieltjes integral
`∫ Se d(-FPF)` since `FPF(c) = PND [c, ∞)`. -/
theorem auc_eq_integral_posFraction (PD PND : Measure ℝ) [IsProbabilityMeasure PD]
    [IsProbabilityMeasure PND] [NullSingletonClass PD] :
    auc PD PND = ∫ y, posFraction PD y ∂PND := by
  rw [auc_eq_concordance_of_tieProb_eq_zero (tieProb_eq_zero PD PND), concordance_eq_integral]
  congr 1
  funext y
  rw [posFraction, measureReal_def, measureReal_def, measure_congr Ioi_ae_eq_Ici]

/-- **Ties: the atom example.** With both scores equal to `0` the ROC points are `(0, 0)` and
`(1, 1)` and the area under the curve is the chance value `1/2`, while the strict concordance
probability is `0` and the weak one `∫ Se dPND = Se(0) = 1`. So neither one sided form is the
area when ties have positive probability. -/
theorem auc_ne_integral_posFraction_of_atom :
    auc (Measure.dirac 0) (Measure.dirac 0) = 1 / 2 ∧
      concordance (Measure.dirac 0) (Measure.dirac 0) = 0 ∧
      ∫ y, posFraction (Measure.dirac 0) y ∂(Measure.dirac (0 : ℝ)) = 1 := by
  have hc : concordance (Measure.dirac (0 : ℝ)) (Measure.dirac 0) = 0 := by
    rw [concordance, Measure.dirac_prod_dirac, measureReal_def,
      Measure.dirac_apply' _ (measurableSet_lt measurable_snd measurable_fst)]
    simp
  have hi : ∫ y, posFraction (Measure.dirac 0) y ∂(Measure.dirac (0 : ℝ)) = 1 := by
    rw [integral_dirac]
    simp [posFraction, measureReal_def]
  refine ⟨?_, hc, hi⟩
  rw [auc_eq_average, hc, hi]; norm_num

end DiagnosticAccuracy

end BiasAnalysis

end CausalInference
