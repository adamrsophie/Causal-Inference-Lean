/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Bias.Misclassification
public import CausalInference.Measures.EffectMeasures
public import Mathlib.Probability.Distributions.Binomial

/-!
# Misclassification on two by two tables

Simple bias analysis for a misclassified binary exposure or disease, following Fox, MacLehose
and Lash (2021), Chapter 6, with the validation designs of Chapter 3. The library file
`Bias.Misclassification` supplies the measurement model (`observedTable`, `binaryKernel`,
`exposureMisclassified`, `outcomeMisclassified`, `risk`) and the risk difference results; this
file states the book's table formulas as theorems about that model.

## Setting

A table `p e d` holds counts (or probabilities) by true exposure `e` and true disease `d`; in the
book's notation `A = p true true`, `B = p false true`, `C = p true false`, `D = p false false`. A
validation table `V e e'` holds counts by true value `e` and classified value `e'`. Sensitivity
and specificity may depend on the other variable (differential misclassification). Every ratio
carries the positivity hypothesis it needs.

## Main results

* Classification measures (Equations 6.1 to 6.6) and Bayes formulas: `ppv_eq_ppvBayes`,
  `npv_eq_npvBayes` (Equations 6.7, 6.8 hold in every validation table whose conditioning
  classes are nonempty); `ppvBayes_strictMonoOn` (PPV increases with prevalence) and
  `ppv_not_transportable` (Table 6.3).
* Validation designs (Table 3.2): sampling on the truth preserves sensitivity and specificity
  (`sensitivity_reweightTrue`), sampling on the classification preserves predictive values
  (`ppv_reweightObserved`), and the converse fails (`panelC_ppv_invalid`,
  `panelB_sensitivity_invalid`). All six printed tables and their 24 estimates:
  `panelA_values`, `panelB_values`, `panelC_values`.
* Forward map (Table 6.5, Equation 6.9) and correction (Table 6.8):
  `exposureCorrected_misclassified`, `exposureMisclassified_corrected`,
  `exposureMisclassifiedDiff_not_identified` and `correctedExposed_not_identified` (no
  correction when `SE + SP = 1`), and the direct odds ratio formula: the totalized identity
  `crossOddsRatio_exposureCorrected`, its guarded form `crossOddsRatio_exposureCorrected_of_ne`,
  the existence region `crossOddsRatio_exposureCorrected_pos`, and a zero denominator cell on
  the admissible region (`Examples.correctedOddsRatio_zero_cell`).
* Admissible bias parameters (section "Negative Expected Cell Frequencies"): `admissible_iff`,
  `admissible_nondifferential_iff` and its mirror `admissible_nondifferential_iff_of_neg`,
  `exposureCorrected_pos_iff_of_pos`, `correctedExposed_eq_zero`, `correctedUnexposed_eq_zero`.
* Toward the null on the ratio scales (section "Differential vs. Nondifferential
  Misclassification"): `exposure_riskRatio_toward_null`, `exposure_oddsRatio_toward_null` and
  their protective versions, with counterexamples for differential error
  (`Examples.table67_away_from_null`) and for `SE + SP < 1` (`Examples.table66_reversal`). The
  estimand is the effect measure computed from the expected observed counts (a ratio of expected
  counts), not the expected value of the ratio computed from a realized table. The book's
  summary is that the bias is toward the null "on average"; a realized table can lie away from
  the null (`realized_away_from_null`). The realized table has the law of two independent
  binomial counts (`realizationProb_eq_binomial`, Mathlib's `ProbabilityTheory.binomial`), and
  its expected cells are those of the expected table (`realized_exposed_expectation`). The odds
  ratio version for outcome misclassification is `outcome_tableOddsRatio_toward_null`.
* Differential and dependent errors as properties of a joint kernel: `productKernel_structure`,
  its statistical form `productKernel_isMeasurementKernel`, and `dependentKernel_structure`.
* Predictive value correction (Table 6.10): `pvCorrected_misclassified`.
* Brenner and Gefeller: `brenner_gefeller`. Perfect specificity:
  `outcome_riskRatio_perfect_specificity`, `outcome_riskDiff_perfect_specificity` and its
  inverse `outcome_riskDiff_perfect_specificity_inv`.
* Internal validation data (Tables 6.14, 6.15): `internalValidation_estimated` (parameters
  estimated from the validated subset, with a transport assumption for the remainder) and
  `internalValidation_recovers` (supplied parameters).
* Disease misclassification in case-control studies: `cc_correction`, `cc_eq_exposureCorrected`,
  the admissible region `cc_admissible_iff` with `cc_negative_examples`, and
  `specificity_ccStudyTable`.
* Worked examples (namespace `Examples`): Tables 3.1, 6.2, 6.6, 6.7, 6.9, 6.11, 6.12, 6.13,
  6.14, 6.15, 6.22; Tables 3.2 and 6.3 are checked next to the theorems they illustrate. Printed
  values are checked against exact recomputation; Table 6.11 reproduces only with the unrounded
  predictive values, and the "117%" of Table 6.13 uses rounded odds ratios. The validation
  cross-classification behind Table 6.15 is not printed; `Examples.table615Validation`
  reconstructs it from the printed margins and percentages.

## References

* M. P. Fox, R. F. MacLehose and T. L. Lash, *Applying Quantitative Bias Analysis to
  Epidemiologic Data*, second edition, Springer (2021), Chapters 3 and 6.
* H. Brenner and O. Gefeller (1993), cited there for the predictive value correction of the risk
  ratio.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace MisclassificationTables

open Bias Finset

section Validation

/-! ### Classification measures from a validation table -/

/-- The sensitivity `A / (A + C)` of a validation table `V e e'`, the count of individuals with
true value `e` and classified value `e'` (Equation 6.1). -/
noncomputable def sensitivity (V : Bool → Bool → ℝ) : ℝ :=
  V true true / (V true true + V true false)

/-- The specificity `D / (B + D)` of a validation table (Equation 6.2). -/
noncomputable def specificity (V : Bool → Bool → ℝ) : ℝ :=
  V false false / (V false false + V false true)

/-- The false negative proportion `C / (A + C)` (Equation 6.3). -/
noncomputable def falseNegative (V : Bool → Bool → ℝ) : ℝ :=
  V true false / (V true true + V true false)

/-- The false positive proportion `B / (B + D)` (Equation 6.4). -/
noncomputable def falsePositive (V : Bool → Bool → ℝ) : ℝ :=
  V false true / (V false false + V false true)

/-- The positive predictive value `A / (A + B)`: the proportion truly positive among those
classified positive (Equation 6.5). -/
noncomputable def ppv (V : Bool → Bool → ℝ) : ℝ :=
  V true true / (V true true + V false true)

/-- The negative predictive value `D / (C + D)` (Equation 6.6). -/
noncomputable def npv (V : Bool → Bool → ℝ) : ℝ :=
  V false false / (V false false + V true false)

/-- The true prevalence `(A + C) / N` of a validation table. -/
noncomputable def prevalence (V : Bool → Bool → ℝ) : ℝ :=
  (V true true + V true false) / (V true true + V true false + (V false true + V false false))

/-- The false negative proportion is one minus the sensitivity (Equation 6.3). -/
theorem falseNegative_eq (V : Bool → Bool → ℝ) (h : V true true + V true false ≠ 0) :
    falseNegative V = 1 - sensitivity V := by
  unfold falseNegative sensitivity
  field_simp
  ring

/-- The false positive proportion is one minus the specificity (Equation 6.4). -/
theorem falsePositive_eq (V : Bool → Bool → ℝ) (h : V false false + V false true ≠ 0) :
    falsePositive V = 1 - specificity V := by
  unfold falsePositive specificity
  field_simp
  ring

/-- The validation table of a population with `n e` individuals of true value `e`, classified
with sensitivity `se` and specificity `sp`. -/
def validationOf (n : Bool → ℝ) (se sp : ℝ) (e e' : Bool) : ℝ := n e * binaryKernel se sp e e'

theorem sensitivity_validationOf (n : Bool → ℝ) (se sp : ℝ) (h : n true ≠ 0) :
    sensitivity (validationOf n se sp) = se := by
  simp only [sensitivity, validationOf, binaryKernel, ↓reduceIte, Bool.false_eq_true]
  rw [← mul_add, add_sub_cancel, mul_one, mul_div_cancel_left₀ _ h]

theorem specificity_validationOf (n : Bool → ℝ) (se sp : ℝ) (h : n false ≠ 0) :
    specificity (validationOf n se sp) = sp := by
  simp only [specificity, validationOf, binaryKernel, Bool.false_eq_true, ↓reduceIte]
  rw [← mul_add, add_sub_cancel, mul_one, mul_div_cancel_left₀ _ h]

/-- The positive predictive value by Bayes theorem (Equation 6.7):
`SE π / (SE π + (1 - SP)(1 - π))` for true prevalence `π`. -/
noncomputable def ppvBayes (se sp π : ℝ) : ℝ := se * π / (se * π + (1 - sp) * (1 - π))

/-- The negative predictive value by Bayes theorem (Equation 6.8):
`SP (1 - π) / (SP (1 - π) + (1 - SE) π)`. -/
noncomputable def npvBayes (se sp π : ℝ) : ℝ := sp * (1 - π) / (sp * (1 - π) + (1 - se) * π)

/-- Equation 6.7 holds in every validation table with nonempty true classes and a nonempty
class of those classified positive: the positive predictive value equals the Bayes expression
in the table's own sensitivity, specificity and prevalence. The hypothesis `hP` makes both sides
real quotients; without it both reduce to `0 / 0`. -/
theorem ppv_eq_ppvBayes (V : Bool → Bool → ℝ) (h1 : V true true + V true false ≠ 0)
    (h0 : V false false + V false true ≠ 0)
    (hN : V true true + V true false + (V false true + V false false) ≠ 0)
    (hP : V true true + V false true ≠ 0) :
    ppv V = ppvBayes (sensitivity V) (specificity V) (prevalence V) ∧
      sensitivity V * prevalence V + (1 - specificity V) * (1 - prevalence V) ≠ 0 := by
  have hA : sensitivity V * prevalence V = V true true /
      (V true true + V true false + (V false true + V false false)) := by
    unfold sensitivity prevalence
    field_simp
  have hB : (1 - specificity V) * (1 - prevalence V) = V false true /
      (V true true + V true false + (V false true + V false false)) := by
    unfold specificity prevalence
    field_simp
    ring
  unfold ppvBayes
  rw [hA, hB, ← add_div, div_div_div_cancel_right₀ hN]
  exact ⟨rfl, div_ne_zero hP hN⟩

/-- Equation 6.8 holds in every validation table with nonempty true classes and a nonempty
class of those classified negative; the denominator of the Bayes form is then nonzero. -/
theorem npv_eq_npvBayes (V : Bool → Bool → ℝ) (h1 : V true true + V true false ≠ 0)
    (h0 : V false false + V false true ≠ 0)
    (hN : V true true + V true false + (V false true + V false false) ≠ 0)
    (hQ : V false false + V true false ≠ 0) :
    npv V = npvBayes (sensitivity V) (specificity V) (prevalence V) ∧
      specificity V * (1 - prevalence V) + (1 - sensitivity V) * prevalence V ≠ 0 := by
  have hD : specificity V * (1 - prevalence V) = V false false /
      (V true true + V true false + (V false true + V false false)) := by
    unfold specificity prevalence
    field_simp
    ring
  have hC : (1 - sensitivity V) * prevalence V = V true false /
      (V true true + V true false + (V false true + V false false)) := by
    unfold sensitivity prevalence
    field_simp
    ring
  unfold npvBayes
  rw [hD, hC, ← add_div, div_div_div_cancel_right₀ hN]
  exact ⟨rfl, div_ne_zero hQ hN⟩

/-- The positive predictive value increases with prevalence (Equations 6.7 and Table 6.3): for
`0 < SE` and `SP < 1`, `ppvBayes se sp` is strictly increasing on `[0, 1]`. -/
theorem ppvBayes_strictMonoOn (se sp : ℝ) (hse : 0 < se) (hsp : sp < 1) :
    StrictMonoOn (ppvBayes se sp) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hfp : 0 < 1 - sp := by linarith
  have hdx : 0 < se * x + (1 - sp) * (1 - x) := by
    rcases hx0.lt_or_eq with h | h
    · have := mul_pos hse h
      nlinarith
    · subst h
      simpa using hfp
  have hdy : 0 < se * y + (1 - sp) * (1 - y) := by nlinarith
  unfold ppvBayes
  rw [div_lt_div_iff₀ hdx hdy]
  nlinarith [mul_pos (mul_pos hse hfp) (sub_pos.mpr hxy)]

/-- The positive and negative predictive values are not transportable (Table 6.3): with the
same sensitivity `0.85` and specificity `0.99`, true prevalence `0.499` (Egypt) gives
`PPV ≈ 0.988`, `NPV ≈ 0.869`, while prevalence `0.195` (United States) gives `PPV ≈ 0.954`,
`NPV ≈ 0.965`. The printed counts of Table 6.3 are rounded and do not have exactly equal
sensitivities (`424/499` against `166/195`); the parameters are used here instead. -/
theorem ppv_not_transportable :
    0.988 < ppvBayes 0.85 0.99 0.499 ∧ ppvBayes 0.85 0.99 0.499 < 0.989 ∧
      0.953 < ppvBayes 0.85 0.99 0.195 ∧ ppvBayes 0.85 0.99 0.195 < 0.954 ∧
      0.868 < npvBayes 0.85 0.99 0.499 ∧ npvBayes 0.85 0.99 0.499 < 0.869 ∧
      0.964 < npvBayes 0.85 0.99 0.195 ∧ npvBayes 0.85 0.99 0.195 < 0.965 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [ppvBayes, npvBayes]

/-! ### Validation designs (Table 3.2) -/

/-- A validation sample drawn with sampling fraction `w e` depending only on the true value. -/
def reweightTrue (w : Bool → ℝ) (V : Bool → Bool → ℝ) (e e' : Bool) : ℝ := w e * V e e'

/-- A validation sample drawn with sampling fraction `w e'` depending only on the classified
value. -/
def reweightObserved (w : Bool → ℝ) (V : Bool → Bool → ℝ) (e e' : Bool) : ℝ := w e' * V e e'

/-- Sampling on the true value preserves the sensitivity (Table 3.2, Panel C). The truly
positive class is nonempty (`hV`) and sampled with a nonzero fraction, so it stays nonempty and
both sensitivities are real quotients. -/
theorem sensitivity_reweightTrue (w : Bool → ℝ) (V : Bool → Bool → ℝ) (hw : w true ≠ 0)
    (hV : V true true + V true false ≠ 0) :
    sensitivity (reweightTrue w V) = sensitivity V ∧
      reweightTrue w V true true + reweightTrue w V true false ≠ 0 := by
  simp only [sensitivity, reweightTrue]
  rw [← mul_add, mul_div_mul_left _ _ hw]
  exact ⟨rfl, mul_ne_zero hw hV⟩

/-- Sampling on the true value preserves the specificity (Table 3.2, Panel C), with a nonempty
truly negative class. -/
theorem specificity_reweightTrue (w : Bool → ℝ) (V : Bool → Bool → ℝ) (hw : w false ≠ 0)
    (hV : V false false + V false true ≠ 0) :
    specificity (reweightTrue w V) = specificity V ∧
      reweightTrue w V false false + reweightTrue w V false true ≠ 0 := by
  simp only [specificity, reweightTrue]
  rw [← mul_add, mul_div_mul_left _ _ hw]
  exact ⟨rfl, mul_ne_zero hw hV⟩

/-- Sampling on the classified value preserves the positive predictive value (Table 3.2,
Panel B), with a nonempty class of those classified positive. -/
theorem ppv_reweightObserved (w : Bool → ℝ) (V : Bool → Bool → ℝ) (hw : w true ≠ 0)
    (hV : V true true + V false true ≠ 0) :
    ppv (reweightObserved w V) = ppv V ∧
      reweightObserved w V true true + reweightObserved w V false true ≠ 0 := by
  simp only [ppv, reweightObserved]
  rw [← mul_add, mul_div_mul_left _ _ hw]
  exact ⟨rfl, mul_ne_zero hw hV⟩

/-- Sampling on the classified value preserves the negative predictive value (Table 3.2,
Panel B), with a nonempty class of those classified negative. -/
theorem npv_reweightObserved (w : Bool → ℝ) (V : Bool → Bool → ℝ) (hw : w false ≠ 0)
    (hV : V false false + V true false ≠ 0) :
    npv (reweightObserved w V) = npv V ∧
      reweightObserved w V false false + reweightObserved w V true false ≠ 0 := by
  simp only [npv, reweightObserved]
  rw [← mul_add, mul_div_mul_left _ _ hw]
  exact ⟨rfl, mul_ne_zero hw hV⟩

/-- The expected validation table of the cases of Table 3.1: of 90 truly exposed cases, 54 are
classified exposed and 36 unexposed; of 270 truly unexposed cases, 27 are classified exposed and
243 unexposed (sensitivity `0.6`, specificity `0.9`). -/
def table31Cases (e e' : Bool) : ℝ :=
  if e then (if e' then 54 else 36) else (if e' then 27 else 243)

/-- Sampling on the truth does not preserve predictive values (Table 3.2, Panel C). Sampling all
90 truly exposed cases and one third of the 270 truly unexposed cases gives exactly the printed
Panel C (`54, 36, 9, 81`). Sensitivity `0.6` and specificity `0.9` are preserved, but the
computed positive predictive value is `6/7 ≈ 0.857` against the population value `2/3`, and the
computed negative predictive value is `9/13 ≈ 0.692` against `27/31 ≈ 0.871`. -/
theorem panelC_ppv_invalid :
    reweightTrue (fun e ↦ if e then 1 else 1 / 3) table31Cases =
        (fun e e' ↦ if e then (if e' then 54 else 36) else (if e' then 9 else 81)) ∧
      sensitivity (reweightTrue (fun e ↦ if e then 1 else 1 / 3) table31Cases) = 3 / 5 ∧
      specificity (reweightTrue (fun e ↦ if e then 1 else 1 / 3) table31Cases) = 9 / 10 ∧
      ppv table31Cases = 2 / 3 ∧
      ppv (reweightTrue (fun e ↦ if e then 1 else 1 / 3) table31Cases) = 6 / 7 ∧
      npv table31Cases = 27 / 31 ∧
      npv (reweightTrue (fun e ↦ if e then 1 else 1 / 3) table31Cases) = 9 / 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext e e'
    cases e <;> cases e' <;> norm_num [reweightTrue, table31Cases]
  all_goals norm_num [sensitivity, specificity, ppv, npv, reweightTrue, table31Cases]

/-- Sampling on the classified value does not preserve sensitivity and specificity (Table 3.2,
Panel B). With all 81 cases classified exposed and `81` of the `279` classified unexposed, the
exact reweighted table keeps the positive predictive value `2/3` and the negative predictive
value `27/31`, but its sensitivity is `31/37 ≈ 0.838` instead of `0.6`. The printed Panel B
rounds the reweighted counts to integers (`54, 10, 27, 71`) and reports the sensitivity
`54/64 ≈ 0.844` and specificity `71/98 ≈ 0.724`. -/
theorem panelB_sensitivity_invalid :
    ppv (reweightObserved (fun e' ↦ if e' then 1 else 81 / 279) table31Cases) = 2 / 3 ∧
      npv (reweightObserved (fun e' ↦ if e' then 1 else 81 / 279) table31Cases) = 27 / 31 ∧
      sensitivity table31Cases = 3 / 5 ∧
      sensitivity (reweightObserved (fun e' ↦ if e' then 1 else 81 / 279) table31Cases) =
        31 / 37 ∧
      sensitivity (fun e e' ↦ if e then (if e' then 54 else 10) else (if e' then 27 else 71)) =
        54 / 64 ∧
      specificity (fun e e' ↦ if e then (if e' then 54 else 10) else (if e' then 27 else 71)) =
        71 / 98 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sensitivity, specificity, ppv, npv, reweightObserved, table31Cases]

/-! ### The six printed validation tables of Table 3.2

The book prints each panel with the classified exposure in the rows and the true exposure in the
columns; here they are stored as `V e e'` with the true value first. -/

/-- The expected validation table of the noncases of Table 3.1: of `9910` truly exposed noncases,
`5946` are classified exposed and `3964` unexposed; of `89730` truly unexposed, `8973` and
`80757`. -/
def table31Noncases (e e' : Bool) : ℝ :=
  if e then (if e' then 5946 else 3964) else (if e' then 8973 else 80757)

/-- Both expected validation tables of Table 3.1 are the classification of the true exposure
counts with sensitivity `0.6` and specificity `0.9`. -/
theorem table31_validation_eq :
    table31Cases = validationOf (fun e ↦ if e then 90 else 270) 0.6 0.9 ∧
      table31Noncases = validationOf (fun e ↦ if e then 9910 else 89730) 0.6 0.9 := by
  constructor <;> funext e e' <;> cases e <;> cases e' <;>
    norm_num [table31Cases, table31Noncases, validationOf, binaryKernel]

/-- Table 3.2, Panel A, cases (10% simple random sample): true exposed `5` classified exposed and
`4` unexposed; true unexposed `3` and `24`. -/
def panelACases (e e' : Bool) : ℝ := if e then (if e' then 5 else 4) else (if e' then 3 else 24)

/-- Table 3.2, Panel A, noncases: `595, 396` (true exposed) and `897, 8076` (true unexposed). -/
def panelANoncases (e e' : Bool) : ℝ :=
  if e then (if e' then 595 else 396) else (if e' then 897 else 8076)

/-- Table 3.2, Panel B, cases (balanced design sampling on the classification): `54, 10` and
`27, 71`. -/
def panelBCases (e e' : Bool) : ℝ := if e then (if e' then 54 else 10) else (if e' then 27 else 71)

/-- Table 3.2, Panel B, noncases: `32, 4` and `49, 77`. -/
def panelBNoncases (e e' : Bool) : ℝ :=
  if e then (if e' then 32 else 4) else (if e' then 49 else 77)

/-- Table 3.2, Panel C, cases and noncases (balanced design sampling on the truth; the two
printed tables are equal): `54, 36` and `9, 81`. -/
def panelC (e e' : Bool) : ℝ := if e then (if e' then 54 else 36) else (if e' then 9 else 81)

/-- Table 3.2, Panel A. Every printed cell is the nearest integer to the 10% sample of the
expected validation table (within `1/2` of it), and the eight printed estimates are the exact
ratios: cases `SE = 5/9 ≈ 0.556`, `SP = 24/27 ≈ 0.889`, `PPV = 5/8 = 0.625`,
`NPV = 24/28 ≈ 0.857`; noncases `SE = 595/991 ≈ 0.600`, `SP = 8076/8973 ≈ 0.900`,
`PPV = 595/1492 ≈ 0.399`, `NPV = 8076/8472 ≈ 0.953`. -/
theorem panelA_values :
    (∀ e e', |panelACases e e' - 1 / 10 * table31Cases e e'| ≤ 1 / 2) ∧
      (∀ e e', |panelANoncases e e' - 1 / 10 * table31Noncases e e'| ≤ 1 / 2) ∧
      sensitivity panelACases = 5 / 9 ∧ specificity panelACases = 24 / 27 ∧
      ppv panelACases = 5 / 8 ∧ npv panelACases = 24 / 28 ∧
      sensitivity panelANoncases = 595 / 991 ∧ specificity panelANoncases = 8076 / 8973 ∧
      ppv panelANoncases = 595 / 1492 ∧ npv panelANoncases = 8076 / 8472 := by
  refine ⟨fun e e' ↦ ?_, fun e e' ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases e <;> cases e' <;> norm_num [abs_le, panelACases, table31Cases]
  · cases e <;> cases e' <;> norm_num [abs_le, panelANoncases, table31Noncases]
  all_goals norm_num [sensitivity, specificity, ppv, npv, panelACases, panelANoncases]

/-- Table 3.2, Panel B. The printed cells are the nearest integers to the expected validation
tables sampled with `81` of each classified exposure level (fractions `1` and `81/279` among
cases, `81/14919` and `81/84721` among noncases), and the eight printed estimates are the exact
ratios: cases `SE = 54/64 ≈ 0.844` (invalid), `SP = 71/98 ≈ 0.724` (invalid), `PPV = 54/81 ≈ 0.667`,
`NPV = 71/81 ≈ 0.877`; noncases `SE = 32/36 ≈ 0.889` (invalid), `SP = 77/126 ≈ 0.611` (invalid),
`PPV = 32/81 ≈ 0.395`, `NPV = 77/81 ≈ 0.951`. -/
theorem panelB_values :
    (∀ e e', |panelBCases e e' -
        reweightObserved (fun e' ↦ if e' then 1 else 81 / 279) table31Cases e e'| ≤ 1 / 2) ∧
      (∀ e e', |panelBNoncases e e' -
        reweightObserved (fun e' ↦ if e' then 81 / 14919 else 81 / 84721) table31Noncases e e'|
          ≤ 1 / 2) ∧
      sensitivity panelBCases = 54 / 64 ∧ specificity panelBCases = 71 / 98 ∧
      ppv panelBCases = 54 / 81 ∧ npv panelBCases = 71 / 81 ∧
      sensitivity panelBNoncases = 32 / 36 ∧ specificity panelBNoncases = 77 / 126 ∧
      ppv panelBNoncases = 32 / 81 ∧ npv panelBNoncases = 77 / 81 := by
  refine ⟨fun e e' ↦ ?_, fun e e' ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases e <;> cases e' <;> norm_num [abs_le, panelBCases, table31Cases, reweightObserved]
  · cases e <;> cases e' <;>
      norm_num [abs_le, panelBNoncases, table31Noncases, reweightObserved]
  all_goals norm_num [sensitivity, specificity, ppv, npv, panelBCases, panelBNoncases]

/-- Table 3.2, Panel C. The printed tables are exactly the expected validation tables sampled
with `90` of each true exposure level (fractions `1` and `1/3` among cases, `90/9910` and
`90/89730` among noncases), and the printed estimates, equal for cases and noncases, are the
exact ratios `SE = 54/90 = 0.6`, `SP = 81/90 = 0.9`, `PPV = 54/63 ≈ 0.857` (invalid) and
`NPV = 81/117 ≈ 0.692` (invalid). -/
theorem panelC_values :
    panelC = reweightTrue (fun e ↦ if e then 1 else 1 / 3) table31Cases ∧
      panelC = reweightTrue (fun e ↦ if e then 90 / 9910 else 90 / 89730) table31Noncases ∧
      sensitivity panelC = 54 / 90 ∧ specificity panelC = 81 / 90 ∧
      ppv panelC = 54 / 63 ∧ npv panelC = 81 / 117 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext e e'
    cases e <;> cases e' <;> norm_num [panelC, table31Cases, reweightTrue]
  · funext e e'
    cases e <;> cases e' <;> norm_num [panelC, table31Noncases, reweightTrue]
  all_goals norm_num [sensitivity, specificity, ppv, npv, panelC]

end Validation

section Exposure

/-! ### Exposure misclassification: forward and inverse maps

Tables are indexed as in `Bias.Misclassification`: `p e d` is the count (or probability) of true
exposure `e` and disease `d`. In the book's notation `A = p true true`, `B = p false true`,
`C = p true false`, `D = p false false` (Table 6.5). Sensitivity and specificity are functions
of the disease level, so differential misclassification is allowed. -/

/-- The expected observed table under exposure misclassification with sensitivity `se d` and
specificity `sp d` in disease row `d`, and disease measured without error (Table 6.5). -/
def exposureMisclassifiedDiff (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) : Bool → Bool → ℝ :=
  observedTable p fun e d e' d' ↦ binaryKernel (se d) (sp d) e e' * exactKernel d d'

theorem exposureMisclassifiedDiff_apply (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (e' d : Bool) :
    exposureMisclassifiedDiff p se sp e' d = ∑ e, p e d * binaryKernel (se d) (sp d) e e' := by
  cases d <;> simp [exposureMisclassifiedDiff, observedTable, exactKernel]

/-- With sensitivity and specificity constant across disease rows, the table is the
nondifferential `Bias.exposureMisclassified`. -/
theorem exposureMisclassifiedDiff_const (p : Bool → Bool → ℝ) (se sp : ℝ) :
    exposureMisclassifiedDiff p (fun _ ↦ se) (fun _ ↦ sp) = exposureMisclassified p se sp := by
  funext e' d
  rw [exposureMisclassifiedDiff_apply, exposureMisclassified_apply]

/-- The expected observed exposed count (Equation 6.9 and Table 6.5):
`a = A SE + B (1 - SP)`. -/
theorem exposureMisclassifiedDiff_exposed (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool) :
    exposureMisclassifiedDiff p se sp true d = p true d * se d + p false d * (1 - sp d) := by
  simp [exposureMisclassifiedDiff_apply, binaryKernel]

/-- The expected observed unexposed count (Table 6.5): `b = A (1 - SE) + B SP`. -/
theorem exposureMisclassifiedDiff_unexposed (p : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (d : Bool) :
    exposureMisclassifiedDiff p se sp false d = p true d * (1 - se d) + p false d * sp d := by
  simp [exposureMisclassifiedDiff_apply, binaryKernel]

/-- Exposure misclassification keeps each disease row total (Equation 6.10). -/
theorem exposureMisclassifiedDiff_row (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool) :
    exposureMisclassifiedDiff p se sp true d + exposureMisclassifiedDiff p se sp false d =
      p true d + p false d := by
  rw [exposureMisclassifiedDiff_exposed, exposureMisclassifiedDiff_unexposed]
  ring

/-- The count form is the row total times the observed prevalence of `Bias.observedPrevalence`
applied to the row's true exposure prevalence. -/
theorem exposureMisclassifiedDiff_exposed_eq_observedPrevalence (p : Bool → Bool → ℝ)
    (se sp : Bool → ℝ) (d : Bool) (hrow : p true d + p false d ≠ 0) :
    exposureMisclassifiedDiff p se sp true d =
      (p true d + p false d) *
        observedPrevalence (se d) (sp d) (p true d / (p true d + p false d)) := by
  rw [exposureMisclassifiedDiff_exposed, observedPrevalence_eq]
  field_simp
  ring

/-- The bias-adjusted exposed count of row `d` (Table 6.8):
`A = (a - D_d (1 - SP_d)) / (SE_d + SP_d - 1)` with `D_d = a + b` the observed row total. -/
noncomputable def correctedExposed (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool) : ℝ :=
  (q true d - (q true d + q false d) * (1 - sp d)) / (se d + sp d - 1)

/-- The bias-adjusted table of Table 6.8: exposed count `correctedExposed` and unexposed count
the row total minus it. -/
noncomputable def exposureCorrected (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) :
    Bool → Bool → ℝ :=
  fun e d ↦
    if e then correctedExposed q se sp d else q true d + q false d - correctedExposed q se sp d

/-- The correction of Table 6.8 recovers the true table from the expected observed table when
`SE_d + SP_d ≠ 1` in every row. -/
theorem exposureCorrected_misclassified (p : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (h : ∀ d, se d + sp d ≠ 1) :
    exposureCorrected (exposureMisclassifiedDiff p se sp) se sp = p := by
  funext e d
  have hk : se d + sp d - 1 ≠ 0 := sub_ne_zero.mpr (h d)
  have hA : correctedExposed (exposureMisclassifiedDiff p se sp) se sp d = p true d := by
    unfold correctedExposed
    rw [exposureMisclassifiedDiff_row, exposureMisclassifiedDiff_exposed, div_eq_iff hk]
    ring
  cases e
  · simp only [exposureCorrected, Bool.false_eq_true, ↓reduceIte, hA,
      exposureMisclassifiedDiff_row]
    ring
  · simp only [exposureCorrected, ↓reduceIte, hA]

/-- Conversely the bias-adjusted table is mapped back to the observed table: it is the unique
true table compatible with the observed table and the bias parameters. -/
theorem exposureMisclassified_corrected (q : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (h : ∀ d, se d + sp d ≠ 1) :
    exposureMisclassifiedDiff (exposureCorrected q se sp) se sp = q := by
  funext e' d
  have hk : se d + sp d - 1 ≠ 0 := sub_ne_zero.mpr (h d)
  cases e'
  · rw [exposureMisclassifiedDiff_unexposed]
    simp only [exposureCorrected, Bool.false_eq_true, ↓reduceIte, correctedExposed]
    field_simp
    ring
  · rw [exposureMisclassifiedDiff_exposed]
    simp only [exposureCorrected, Bool.false_eq_true, ↓reduceIte, correctedExposed]
    field_simp
    ring

/-- Two true tables with the same expected observed table are equal when `SE_d + SP_d ≠ 1`. -/
theorem exposureMisclassifiedDiff_injective (se sp : Bool → ℝ) (h : ∀ d, se d + sp d ≠ 1) :
    Function.Injective fun p ↦ exposureMisclassifiedDiff p se sp := by
  intro p p' hpp
  rw [← exposureCorrected_misclassified p se sp h, ← exposureCorrected_misclassified p' se sp h]
  exact congrArg (fun q ↦ exposureCorrected q se sp) hpp

/-- When `SE_d + SP_d = 1` in row `d` the expected observed row depends on the true row only
through its total, so no correction exists (`Bias.prevalence_not_identified`). -/
theorem exposureMisclassifiedDiff_not_identified (p p' : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (d : Bool) (h : se d + sp d = 1) (hrow : p true d + p false d = p' true d + p' false d) :
    exposureMisclassifiedDiff p se sp true d = exposureMisclassifiedDiff p' se sp true d := by
  rw [exposureMisclassifiedDiff_exposed, exposureMisclassifiedDiff_exposed]
  have hsp : 1 - sp d = se d := by linarith
  rw [hsp]
  linear_combination se d * hrow

/-- The odds ratio `A D / (B C)` of a table `p e d` (exposure `e`, disease `d`). -/
noncomputable def crossOddsRatio (q : Bool → Bool → ℝ) : ℝ :=
  q true true * q false false / (q false true * q true false)

/-- The observed exposed proportion `P_d = a / (a + b)` in disease row `d`. -/
noncomputable def exposedProportion (q : Bool → Bool → ℝ) (d : Bool) : ℝ :=
  q true d / (q true d + q false d)

/-- The bias-adjusted exposed count in terms of the observed exposed proportion:
`A = D_d (P_d + SP_d - 1) / (SE_d + SP_d - 1)`. This rewrites the numerator only; both sides
divide by the same `SE_d + SP_d - 1`, so at `SE_d + SP_d = 1` it is an identity between totalized
expressions (both are `0`) and carries no information. -/
theorem correctedExposed_eq (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hrow : q true d + q false d ≠ 0) :
    correctedExposed q se sp d =
      (q true d + q false d) * (exposedProportion q d + sp d - 1) / (se d + sp d - 1) := by
  unfold correctedExposed exposedProportion
  congr 1
  field_simp
  ring

/-- The bias-adjusted unexposed count `D_d (SE_d - P_d) / (SE_d + SP_d - 1)`. -/
theorem correctedUnexposed_eq (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hrow : q true d + q false d ≠ 0) (hk : se d + sp d ≠ 1) :
    q true d + q false d - correctedExposed q se sp d =
      (q true d + q false d) * (se d - exposedProportion q d) / (se d + sp d - 1) := by
  have hk' : se d + sp d - 1 ≠ 0 := sub_ne_zero.mpr hk
  rw [correctedExposed_eq q se sp d hrow, eq_div_iff hk', sub_mul, div_mul_cancel₀ _ hk']
  ring

/-- The direct odds ratio formula (section "Bias-Adjusting for Exposure Misclassification Using
Sensitivity and Specificity", unnumbered display): with `P_d` the observed exposed proportion in
disease row `d`, the cross product `A₁ D₀ / (B₁ C₀)` of the bias-adjusted table equals
`(P₁ + SP₁ - 1)(SE₀ - P₀) / ((P₀ + SP₀ - 1)(SE₁ - P₁))`.

This is an identity between totalized expressions: it does not assert that the bias-adjusted
odds ratio exists. When a bias-adjusted denominator cell `B₁` or `C₀` is zero both sides are
`x / 0 = 0` (`Examples.correctedOddsRatio_zero_cell`). The guarded version is
`crossOddsRatio_exposureCorrected_of_ne`, and `crossOddsRatio_exposureCorrected_pos` gives the
region where the bias-adjusted odds ratio is a positive real quotient. -/
theorem crossOddsRatio_exposureCorrected (q : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (h1 : q true true + q false true ≠ 0) (h0 : q true false + q false false ≠ 0)
    (hk : ∀ d, se d + sp d ≠ 1) :
    crossOddsRatio (exposureCorrected q se sp) =
      (exposedProportion q true + sp true - 1) * (se false - exposedProportion q false) /
        ((exposedProportion q false + sp false - 1) * (se true - exposedProportion q true)) := by
  simp only [crossOddsRatio, exposureCorrected, ↓reduceIte, Bool.false_eq_true]
  rw [correctedUnexposed_eq q se sp true h1 (hk true),
    correctedUnexposed_eq q se sp false h0 (hk false), correctedExposed_eq q se sp true h1,
    correctedExposed_eq q se sp false h0]
  have hk1 : se true + sp true - 1 ≠ 0 := sub_ne_zero.mpr (hk true)
  have hk0 : se false + sp false - 1 ≠ 0 := sub_ne_zero.mpr (hk false)
  have hc : (q true true + q false true) * (q true false + q false false) /
      ((se true + sp true - 1) * (se false + sp false - 1)) ≠ 0 := by positivity
  rw [show ∀ x1 y0 y1 x0 : ℝ,
      (q true true + q false true) * x1 / (se true + sp true - 1) *
          ((q true false + q false false) * y0 / (se false + sp false - 1)) /
        ((q true true + q false true) * y1 / (se true + sp true - 1) *
          ((q true false + q false false) * x0 / (se false + sp false - 1))) =
      ((q true true + q false true) * (q true false + q false false) /
          ((se true + sp true - 1) * (se false + sp false - 1)) * (x1 * y0)) /
        ((q true true + q false true) * (q true false + q false false) /
          ((se true + sp true - 1) * (se false + sp false - 1)) * (x0 * y1)) from by
      intro x1 y0 y1 x0
      congr 1 <;> field_simp]
  rw [mul_div_mul_left _ _ hc]

/-! ### Admissible bias parameters (section "Negative Expected Cell Frequencies") -/

/-- Admissibility when `SE + SP > 1`: in a disease row with positive observed total and observed
exposed proportion `P`, the bias-adjusted cells are both nonnegative if and only if `P ≤ SE`
and `1 - P ≤ SP`. -/
theorem admissible_iff_of_pos (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hn : 0 < q true d + q false d) (hk : 1 < se d + sp d) :
    (0 ≤ exposureCorrected q se sp true d ∧ 0 ≤ exposureCorrected q se sp false d) ↔
      (exposedProportion q d ≤ se d ∧ 1 - exposedProportion q d ≤ sp d) := by
  simp only [exposureCorrected, ↓reduceIte, Bool.false_eq_true]
  rw [correctedUnexposed_eq q se sp d hn.ne' hk.ne', correctedExposed_eq q se sp d hn.ne']
  have hk' : 0 < se d + sp d - 1 := by linarith
  rw [le_div_iff₀ hk', le_div_iff₀ hk', zero_mul,
    mul_nonneg_iff_of_pos_left hn, mul_nonneg_iff_of_pos_left hn]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- Admissibility when `SE + SP < 1`: the bias-adjusted cells are both nonnegative if and only
if `SE ≤ P` and `SP ≤ 1 - P`. -/
theorem admissible_iff_of_neg (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hn : 0 < q true d + q false d) (hk : se d + sp d < 1) :
    (0 ≤ exposureCorrected q se sp true d ∧ 0 ≤ exposureCorrected q se sp false d) ↔
      (se d ≤ exposedProportion q d ∧ sp d ≤ 1 - exposedProportion q d) := by
  simp only [exposureCorrected, ↓reduceIte, Bool.false_eq_true]
  rw [correctedUnexposed_eq q se sp d hn.ne' hk.ne, correctedExposed_eq q se sp d hn.ne']
  have hk' : se d + sp d - 1 < 0 := by linarith
  rw [le_div_iff_of_neg hk', le_div_iff_of_neg hk', zero_mul]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra! hc
      have := mul_pos hn (sub_pos.mpr hc)
      linarith
    · by_contra! hc
      have := mul_pos hn (show 0 < exposedProportion q d + sp d - 1 by linarith)
      linarith
  · rintro ⟨h1, h2⟩
    exact ⟨mul_nonpos_of_nonneg_of_nonpos hn.le (by linarith),
      mul_nonpos_of_nonneg_of_nonpos hn.le (by linarith)⟩

/-- The two admissible regions of the section "Negative Expected Cell Frequencies": for
`SE + SP ≠ 1`, both bias-adjusted cells of a disease row are nonnegative if and only if
`P ≤ SE` and `1 - P ≤ SP`, or `SE ≤ P` and `SP ≤ 1 - P`. -/
theorem admissible_iff (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hn : 0 < q true d + q false d) (hk : se d + sp d ≠ 1) :
    (0 ≤ exposureCorrected q se sp true d ∧ 0 ≤ exposureCorrected q se sp false d) ↔
      ((exposedProportion q d ≤ se d ∧ 1 - exposedProportion q d ≤ sp d) ∨
        (se d ≤ exposedProportion q d ∧ sp d ≤ 1 - exposedProportion q d)) := by
  rcases hk.lt_or_gt with hlt | hgt
  · rw [admissible_iff_of_neg q se sp d hn hlt]
    constructor
    · exact Or.inr
    · rintro (⟨h1, h2⟩ | h)
      · exact absurd hlt (by linarith)
      · exact h
  · rw [admissible_iff_of_pos q se sp d hn hgt]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · exact absurd hgt (by linarith)

/-- At the boundary `SP = 1 - P` the bias-adjusted exposed cell is zero, for bias parameters
with `SE + SP ≠ 1`, and zero is then the only true exposed count of a row with the observed
total that the classification maps to the observed exposed count. At `SE + SP = 1` the cell
would be `0 / 0` and no correction exists (`correctedExposed_not_identified`). -/
theorem correctedExposed_eq_zero (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hn : q true d + q false d ≠ 0) (hk : se d + sp d ≠ 1)
    (hb : sp d = 1 - exposedProportion q d) :
    correctedExposed q se sp d = 0 ∧
      ∀ x y : ℝ, x + y = q true d + q false d → x * se d + y * (1 - sp d) = q true d →
        x = 0 := by
  refine ⟨?_, fun x y hxy hobs ↦ ?_⟩
  · rw [correctedExposed_eq q se sp d hn, hb]
    simp
  · have hk' : se d + sp d - 1 ≠ 0 := sub_ne_zero.mpr hk
    have hP : (q true d + q false d) * (1 - sp d) = q true d := by
      rw [hb, exposedProportion]
      field_simp
      ring
    have hy : y = q true d + q false d - x := by linarith
    rw [hy] at hobs
    have : x * (se d + sp d - 1) = 0 := by linear_combination hobs - hP
    exact (mul_eq_zero.mp this).resolve_right hk'

/-- At the boundary `SE = P` the bias-adjusted unexposed cell is zero (for `SE + SP ≠ 1`), and
the exposed cell is the whole row. -/
theorem correctedUnexposed_eq_zero (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hn : q true d + q false d ≠ 0) (hk : se d + sp d ≠ 1)
    (hb : se d = exposedProportion q d) :
    exposureCorrected q se sp false d = 0 ∧
      exposureCorrected q se sp true d = q true d + q false d := by
  have h0 : exposureCorrected q se sp false d = 0 := by
    simp only [exposureCorrected, Bool.false_eq_true, ↓reduceIte]
    rw [correctedUnexposed_eq q se sp d hn hk, hb]
    simp
  refine ⟨h0, ?_⟩
  simp only [exposureCorrected, Bool.false_eq_true, ↓reduceIte] at h0 ⊢
  linarith

/-- At `SE + SP = 1` the observed row does not determine the true row, so the zero returned by
`correctedExposed` there is a totalized `0 / 0`. With `SE = SP = 1/2`, the true tables with every
cell `1` and with exposed cells `2` and unexposed cells `0` are distinct and nonnegative, have the
same expected observed table, and the observed exposed proportion `1/2` lies on the boundary
`SP = 1 - P` and `SE = P`. -/
theorem correctedExposed_not_identified :
    exposureMisclassifiedDiff (fun _ _ ↦ 1) (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2) =
        exposureMisclassifiedDiff (fun (e _ : Bool) ↦ if e then 2 else 0) (fun _ ↦ 1 / 2)
          (fun _ ↦ 1 / 2) ∧
      (fun (_ _ : Bool) ↦ (1 : ℝ)) ≠ (fun (e _ : Bool) ↦ if e then (2 : ℝ) else 0) ∧
      (∀ d, exposedProportion
        (exposureMisclassifiedDiff (fun _ _ ↦ 1) (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2)) d = 1 / 2) ∧
      ∀ d, correctedExposed
        (exposureMisclassifiedDiff (fun _ _ ↦ 1) (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2))
        (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2) d = 0 := by
  refine ⟨?_, fun h ↦ ?_, fun d ↦ ?_, fun d ↦ ?_⟩
  · funext e d
    cases e <;> norm_num [exposureMisclassifiedDiff_apply, binaryKernel]
  · have := congrFun (congrFun h false) true
    norm_num at this
  · norm_num [exposedProportion, exposureMisclassifiedDiff_apply, binaryKernel]
  · norm_num [correctedExposed]

/-- The nondifferential admissible region for `SE + SP > 1`: all four bias-adjusted cells are
nonnegative if and only if `max(P₁, P₀) ≤ SE` and `1 - min(P₁, P₀) ≤ SP`. -/
theorem admissible_nondifferential_iff (q : Bool → Bool → ℝ) (se sp : ℝ)
    (h1 : 0 < q true true + q false true) (h0 : 0 < q true false + q false false)
    (hk : 1 < se + sp) :
    (∀ e d, 0 ≤ exposureCorrected q (fun _ ↦ se) (fun _ ↦ sp) e d) ↔
      (max (exposedProportion q true) (exposedProportion q false) ≤ se ∧
        1 - min (exposedProportion q true) (exposedProportion q false) ≤ sp) := by
  have hT := admissible_iff_of_pos q (fun _ ↦ se) (fun _ ↦ sp) true h1 hk
  have hF := admissible_iff_of_pos q (fun _ ↦ se) (fun _ ↦ sp) false h0 hk
  have hmin : 1 - min (exposedProportion q true) (exposedProportion q false) ≤ sp ↔
      (1 - exposedProportion q true ≤ sp ∧ 1 - exposedProportion q false ≤ sp) := by
    constructor
    · intro hm
      exact ⟨by linarith [min_le_left (exposedProportion q true) (exposedProportion q false)],
        by linarith [min_le_right (exposedProportion q true) (exposedProportion q false)]⟩
    · rintro ⟨u, v⟩
      rcases min_choice (exposedProportion q true) (exposedProportion q false) with hm | hm <;>
        rw [hm] <;> assumption
  rw [max_le_iff, hmin]
  constructor
  · intro hall
    obtain ⟨a1, b1⟩ := hT.mp ⟨hall true true, hall false true⟩
    obtain ⟨a0, b0⟩ := hF.mp ⟨hall true false, hall false false⟩
    exact ⟨⟨a1, a0⟩, b1, b0⟩
  · rintro ⟨⟨a1, a0⟩, b1, b0⟩ e d
    cases d
    · obtain ⟨u, v⟩ := hF.mpr ⟨a0, b0⟩
      cases e
      · exact v
      · exact u
    · obtain ⟨u, v⟩ := hT.mpr ⟨a1, b1⟩
      cases e
      · exact v
      · exact u

/-- The mirrored nondifferential admissible region for `SE + SP < 1`: all four bias-adjusted
cells are nonnegative if and only if `SE ≤ min(P₁, P₀)` and `SP ≤ 1 - max(P₁, P₀)`. -/
theorem admissible_nondifferential_iff_of_neg (q : Bool → Bool → ℝ) (se sp : ℝ)
    (h1 : 0 < q true true + q false true) (h0 : 0 < q true false + q false false)
    (hk : se + sp < 1) :
    (∀ e d, 0 ≤ exposureCorrected q (fun _ ↦ se) (fun _ ↦ sp) e d) ↔
      (se ≤ min (exposedProportion q true) (exposedProportion q false) ∧
        sp ≤ 1 - max (exposedProportion q true) (exposedProportion q false)) := by
  have hT := admissible_iff_of_neg q (fun _ ↦ se) (fun _ ↦ sp) true h1 hk
  have hF := admissible_iff_of_neg q (fun _ ↦ se) (fun _ ↦ sp) false h0 hk
  have hmax : sp ≤ 1 - max (exposedProportion q true) (exposedProportion q false) ↔
      (sp ≤ 1 - exposedProportion q true ∧ sp ≤ 1 - exposedProportion q false) := by
    constructor
    · intro hm
      exact ⟨by linarith [le_max_left (exposedProportion q true) (exposedProportion q false)],
        by linarith [le_max_right (exposedProportion q true) (exposedProportion q false)]⟩
    · rintro ⟨u, v⟩
      rcases max_choice (exposedProportion q true) (exposedProportion q false) with hm | hm <;>
        rw [hm] <;> assumption
  rw [le_min_iff, hmax]
  constructor
  · intro hall
    obtain ⟨a1, b1⟩ := hT.mp ⟨hall true true, hall false true⟩
    obtain ⟨a0, b0⟩ := hF.mp ⟨hall true false, hall false false⟩
    exact ⟨⟨a1, a0⟩, b1, b0⟩
  · rintro ⟨⟨a1, a0⟩, b1, b0⟩ e d
    cases d
    · obtain ⟨u, v⟩ := hF.mpr ⟨a0, b0⟩
      cases e
      · exact v
      · exact u
    · obtain ⟨u, v⟩ := hT.mpr ⟨a1, b1⟩
      cases e
      · exact v
      · exact u

/-- Strict positivity of the bias-adjusted cells when `SE + SP > 1`: in a row with positive total
the exposed cell is positive exactly when `1 - P < SP`, and the unexposed cell exactly when
`P < SE`. -/
theorem exposureCorrected_pos_iff_of_pos (q : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (hn : 0 < q true d + q false d) (hk : 1 < se d + sp d) :
    (0 < exposureCorrected q se sp true d ↔ 1 - exposedProportion q d < sp d) ∧
      (0 < exposureCorrected q se sp false d ↔ exposedProportion q d < se d) := by
  simp only [exposureCorrected, ↓reduceIte, Bool.false_eq_true]
  rw [correctedUnexposed_eq q se sp d hn.ne' hk.ne', correctedExposed_eq q se sp d hn.ne']
  have hk' : 0 < se d + sp d - 1 := by linarith
  rw [lt_div_iff₀ hk', lt_div_iff₀ hk', zero_mul, mul_pos_iff_of_pos_left hn,
    mul_pos_iff_of_pos_left hn]
  constructor <;> constructor <;> intro h <;> linarith

/-- Existence of the bias-adjusted odds ratio when `SE_d + SP_d > 1` in both rows: if each
observed exposed proportion lies strictly inside the admissible region, `P_d < SE_d` and
`1 - P_d < SP_d`, then all four bias-adjusted cells are positive, the odds ratio
`A₁ D₀ / (B₁ C₀)` is a positive real quotient, and it equals the direct formula, whose numerator
and denominator are positive. -/
theorem crossOddsRatio_exposureCorrected_pos (q : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (h1 : 0 < q true true + q false true) (h0 : 0 < q true false + q false false)
    (hk : ∀ d, 1 < se d + sp d) (hse : ∀ d, exposedProportion q d < se d)
    (hsp : ∀ d, 1 - exposedProportion q d < sp d) :
    (∀ e d, 0 < exposureCorrected q se sp e d) ∧
      0 < crossOddsRatio (exposureCorrected q se sp) ∧
      0 < (exposedProportion q true + sp true - 1) * (se false - exposedProportion q false) ∧
      0 < (exposedProportion q false + sp false - 1) * (se true - exposedProportion q true) ∧
      crossOddsRatio (exposureCorrected q se sp) =
        (exposedProportion q true + sp true - 1) * (se false - exposedProportion q false) /
          ((exposedProportion q false + sp false - 1) *
            (se true - exposedProportion q true)) := by
  have hpos : ∀ e d, 0 < exposureCorrected q se sp e d := by
    intro e d
    have hn : 0 < q true d + q false d := by cases d <;> assumption
    obtain ⟨hA, hB⟩ := exposureCorrected_pos_iff_of_pos q se sp d hn (hk d)
    cases e
    · exact hB.mpr (hse d)
    · exact hA.mpr (hsp d)
  have hT := hse true
  have hF := hse false
  have hT' := hsp true
  have hF' := hsp false
  refine ⟨hpos, ?_, ?_, ?_, crossOddsRatio_exposureCorrected q se sp h1.ne' h0.ne'
    (fun d ↦ (hk d).ne')⟩
  · unfold crossOddsRatio
    have := hpos true true
    have := hpos false false
    have := hpos false true
    have := hpos true false
    positivity
  · exact mul_pos (by linarith) (by linarith)
  · exact mul_pos (by linarith) (by linarith)

/-- The direct odds ratio formula with its denominator cells guarded: if the bias-adjusted
unexposed cases `B₁` and exposed noncases `C₀` are nonzero (and `SE_d + SP_d ≠ 1`), the
denominator of the direct formula is nonzero and the formula is the real quotient. -/
theorem crossOddsRatio_exposureCorrected_of_ne (q : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (h1 : q true true + q false true ≠ 0) (h0 : q true false + q false false ≠ 0)
    (hk : ∀ d, se d + sp d ≠ 1) (hB : exposureCorrected q se sp false true ≠ 0)
    (hC : exposureCorrected q se sp true false ≠ 0) :
    (exposedProportion q false + sp false - 1) * (se true - exposedProportion q true) ≠ 0 ∧
      crossOddsRatio (exposureCorrected q se sp) =
        (exposedProportion q true + sp true - 1) * (se false - exposedProportion q false) /
          ((exposedProportion q false + sp false - 1) *
            (se true - exposedProportion q true)) := by
  refine ⟨?_, crossOddsRatio_exposureCorrected q se sp h1 h0 hk⟩
  simp only [exposureCorrected, ↓reduceIte, Bool.false_eq_true] at hB hC
  rw [correctedUnexposed_eq q se sp true h1 (hk true)] at hB
  rw [correctedExposed_eq q se sp false h0] at hC
  refine mul_ne_zero (fun h ↦ hC ?_) (fun h ↦ hB ?_) <;> rw [h, mul_zero, zero_div]

/-! ### Toward the null on the ratio scales

Every result of this part compares effect measures computed from the expected observed table
(the expected counts of `exposureMisclassified`), that is, the ratio of expected counts. It is
not a statement about the expected value of the ratio computed from a realized table, which can
differ and can be undefined (see `realized_away_from_null`). -/

/-- The risk ratio `P(D = 1 | E = 1) / P(D = 1 | E = 0)` of a table `q e d`. -/
noncomputable def tableRiskRatio (q : Bool → Bool → ℝ) : ℝ :=
  EffectMeasure.riskRatio (risk q true) (risk q false)

/-- The odds ratio of a table `q e d`, as the ratio of the odds of disease in the two exposure
levels. -/
noncomputable def tableOddsRatio (q : Bool → Bool → ℝ) : ℝ :=
  EffectMeasure.oddsRatio (risk q true) (risk q false)

/-- With all four cells positive, the odds ratio of risks is the cross product ratio
`A D / (B C)`. -/
theorem tableOddsRatio_eq_cross (q : Bool → Bool → ℝ) (hq : ∀ e d, 0 < q e d) :
    tableOddsRatio q = crossOddsRatio q := by
  have := hq true true
  have := hq true false
  have := hq false true
  have := hq false false
  simp only [tableOddsRatio, EffectMeasure.oddsRatio, EffectMeasure.odds, risk, crossOddsRatio]
  have e1 : 1 - q true true / (q true true + q true false) =
      q true false / (q true true + q true false) := by field_simp; ring
  have e0 : 1 - q false true / (q false true + q false false) =
      q false false / (q false true + q false false) := by field_simp; ring
  rw [e1, e0]
  field_simp

/-- Mixtures of two risks with nested weights are nested between them. -/
theorem mixture_nested {r0 r1 w0 w1 : ℝ} (h : r0 ≤ r1) (hw0 : 0 ≤ w0) (hw : w0 ≤ w1)
    (hw1 : w1 ≤ 1) :
    r0 ≤ w0 * r1 + (1 - w0) * r0 ∧ w0 * r1 + (1 - w0) * r0 ≤ w1 * r1 + (1 - w1) * r0 ∧
      w1 * r1 + (1 - w1) * r0 ≤ r1 := by
  have hd : 0 ≤ r1 - r0 := sub_nonneg.mpr h
  have := mul_nonneg hw0 hd
  have := mul_nonneg (sub_nonneg.mpr hw) hd
  have := mul_nonneg (sub_nonneg.mpr hw1) hd
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- Mixtures of two risks with nested weights are nested between them (decreasing case). -/
theorem mixture_nested' {r0 r1 w0 w1 : ℝ} (h : r1 ≤ r0) (hw0 : 0 ≤ w0) (hw : w0 ≤ w1)
    (hw1 : w1 ≤ 1) :
    r1 ≤ w1 * r1 + (1 - w1) * r0 ∧ w1 * r1 + (1 - w1) * r0 ≤ w0 * r1 + (1 - w0) * r0 ∧
      w0 * r1 + (1 - w0) * r0 ≤ r0 := by
  have hd : 0 ≤ r0 - r1 := sub_nonneg.mpr h
  have := mul_nonneg hw0 hd
  have := mul_nonneg (sub_nonneg.mpr hw) hd
  have := mul_nonneg (sub_nonneg.mpr hw1) hd
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- Nested positive quantities give a ratio between one and the outer ratio. -/
theorem ratio_nested {r0 m0 m1 r1 : ℝ} (hr0 : 0 < r0) (h0 : r0 ≤ m0) (h01 : m0 ≤ m1)
    (h1 : m1 ≤ r1) : 1 ≤ m1 / m0 ∧ m1 / m0 ≤ r1 / r0 := by
  have hm0 : 0 < m0 := lt_of_lt_of_le hr0 h0
  refine ⟨(one_le_div hm0).mpr h01, ?_⟩
  rw [div_le_div_iff₀ hm0 hr0]
  nlinarith

/-- The odds `p / (1 - p)` are monotone below one. -/
theorem odds_le_odds {p q : ℝ} (hpq : p ≤ q) (hq : q < 1) :
    EffectMeasure.odds p ≤ EffectMeasure.odds q := by
  unfold EffectMeasure.odds
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Under nondifferential exposure misclassification with `SE ≤ 1`, `SP ≤ 1` and `SE + SP > 1`,
both observed exposure levels have positive mass when both true levels do: the observed exposed
total `n₁ SE + n₀ (1 - SP)` and the observed unexposed total `n₁ (1 - SE) + n₀ SP` are
positive. -/
theorem exposure_obs_pos (p : Bool → Bool → ℝ) (se sp : ℝ) (hse : se ≤ 1) (hsp : sp ≤ 1)
    (h : 1 < se + sp) (h1 : 0 < p true true + p true false)
    (h0 : 0 < p false true + p false false) :
    0 < ∑ a, (p a true + p a false) * binaryKernel se sp a true ∧
      0 < ∑ a, (p a true + p a false) * binaryKernel se sp a false := by
  have hse0 : 0 < se := by linarith
  have hsp0 : 0 < sp := by linarith
  have : 0 ≤ 1 - sp := by linarith
  have : 0 ≤ 1 - se := by linarith
  simp only [Fintype.sum_bool, binaryKernel, ↓reduceIte, Bool.false_eq_true]
  constructor <;> positivity

/-- The predictive weights `w a' = P(E = 1 | E* = a')` of nondifferential exposure
misclassification with `SE + SP > 1` are nested: `0 ≤ w 0 ≤ w 1 ≤ 1`. -/
theorem exposureWeight_nested (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false) :
    0 ≤ exposureWeight p se sp false ∧
      exposureWeight p se sp false ≤ exposureWeight p se sp true ∧
      exposureWeight p se sp true ≤ 1 := by
  obtain ⟨hobs1, hobs0⟩ := exposure_obs_pos p se sp hse hsp h h1 h0
  refine ⟨?_, ?_, ?_⟩
  · unfold exposureWeight
    have : 0 ≤ binaryKernel se sp true false := by simp [binaryKernel]; linarith
    positivity
  · rw [← sub_nonneg, exposureWeight_sub p se sp hobs1.ne' hobs0.ne']
    have : 0 < se + sp - 1 := by linarith
    positivity
  · unfold exposureWeight
    rw [div_le_one hobs1]
    simp only [Fintype.sum_bool]
    have : 0 ≤ binaryKernel se sp false true := by simp [binaryKernel]; linarith
    have := hp false true
    have := hp false false
    nlinarith

/-- The weight `P(E = 1 | E* = 0)` is below one: with positive specificity some of those
classified unexposed are truly unexposed. -/
theorem exposureWeight_false_lt_one (p : Bool → Bool → ℝ) (se sp : ℝ) (hse : se ≤ 1)
    (hsp : sp ≤ 1) (h : 1 < se + sp) (h1 : 0 < p true true + p true false)
    (h0 : 0 < p false true + p false false) :
    exposureWeight p se sp false < 1 := by
  obtain ⟨-, hobs0⟩ := exposure_obs_pos p se sp hse hsp h h1 h0
  unfold exposureWeight
  rw [div_lt_one hobs0]
  simp only [Fintype.sum_bool, binaryKernel, ↓reduceIte, Bool.false_eq_true]
  have hsp0 : 0 < sp := by linarith
  nlinarith [mul_pos h0 hsp0]

/-- The expected observed risks of nondifferential exposure misclassification with
`SE + SP > 1` are nested between the true risks: if `r₀ ≤ r₁` then `r₀ ≤ r₀* ≤ r₁* ≤ r₁`. Here
`r*` is the risk computed from the expected observed counts. -/
theorem exposure_risk_nested (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false)
    (hle : risk p false ≤ risk p true) :
    risk p false ≤ risk (exposureMisclassified p se sp) false ∧
      risk (exposureMisclassified p se sp) false ≤ risk (exposureMisclassified p se sp) true ∧
      risk (exposureMisclassified p se sp) true ≤ risk p true := by
  obtain ⟨hobs1, hobs0⟩ := exposure_obs_pos p se sp hse hsp h h1 h0
  obtain ⟨w0, w01, w1⟩ := exposureWeight_nested p se sp hp hse hsp h h1 h0
  rw [exposure_risk_eq p se sp true h1.ne' h0.ne' hobs1.ne',
    exposure_risk_eq p se sp false h1.ne' h0.ne' hobs0.ne']
  exact mixture_nested hle w0 w01 w1

/-- The decreasing case of `exposure_risk_nested`: if `r₁ ≤ r₀` then `r₁ ≤ r₁* ≤ r₀* ≤ r₀`. -/
theorem exposure_risk_nested' (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false)
    (hle : risk p true ≤ risk p false) :
    risk p true ≤ risk (exposureMisclassified p se sp) true ∧
      risk (exposureMisclassified p se sp) true ≤ risk (exposureMisclassified p se sp) false ∧
      risk (exposureMisclassified p se sp) false ≤ risk p false := by
  obtain ⟨hobs1, hobs0⟩ := exposure_obs_pos p se sp hse hsp h h1 h0
  obtain ⟨w0, w01, w1⟩ := exposureWeight_nested p se sp hp hse hsp h h1 h0
  rw [exposure_risk_eq p se sp true h1.ne' h0.ne' hobs1.ne',
    exposure_risk_eq p se sp false h1.ne' h0.ne' hobs0.ne']
  exact mixture_nested' hle w0 w01 w1

/-- The expected observed reference risk is positive when the true reference risk is: it is a
mixture of the two true risks with positive weight `1 - w₀` on the reference risk. -/
theorem exposure_risk_false_pos (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false)
    (hr0 : 0 < risk p false) :
    0 < risk (exposureMisclassified p se sp) false := by
  obtain ⟨-, hobs0⟩ := exposure_obs_pos p se sp hse hsp h h1 h0
  have hr1 : 0 ≤ risk p true := by
    unfold risk
    have := hp true true
    have := hp true false
    positivity
  have hw := exposureWeight_false_lt_one p se sp hse hsp h h1 h0
  have hw0 := (exposureWeight_nested p se sp hp hse hsp h h1 h0).1
  rw [exposure_risk_eq p se sp false h1.ne' h0.ne' hobs0.ne']
  have := mul_nonneg hw0 hr1
  have := mul_pos (sub_pos.mpr hw) hr0
  linarith

/-- Toward the null on the risk ratio scale (section "Differential vs. Nondifferential
Misclassification" and the summary after Table 6.17): nondifferential, independent
misclassification of a binary exposure with `SE + SP > 1` moves the risk ratio computed from the
expected observed counts toward the null and never past it. If the true risk ratio is at least
one, `1 ≤ RR* ≤ RR`, where `RR*` is the ratio of the risks of the expected table (a ratio of
expected counts), not the expected value of the risk ratio of a realized table. -/
theorem exposure_riskRatio_toward_null (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false)
    (hr0 : 0 < risk p false) (hle : risk p false ≤ risk p true) :
    1 ≤ tableRiskRatio (exposureMisclassified p se sp) ∧
      tableRiskRatio (exposureMisclassified p se sp) ≤ tableRiskRatio p := by
  obtain ⟨n0, n01, n1⟩ := exposure_risk_nested p se sp hp hse hsp h h1 h0 hle
  exact ratio_nested hr0 n0 n01 n1

/-- Toward the null on the risk ratio scale, protective case: if the true risk ratio is at most
one, `RR ≤ RR* ≤ 1` for the risk ratio `RR*` of the expected observed counts. Only the reference
risk must be positive; a zero exposed risk (true risk ratio `0`) is allowed. -/
theorem exposure_riskRatio_toward_null' (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false)
    (hr0 : 0 < risk p false) (hle : risk p true ≤ risk p false) :
    tableRiskRatio p ≤ tableRiskRatio (exposureMisclassified p se sp) ∧
      tableRiskRatio (exposureMisclassified p se sp) ≤ 1 := by
  obtain ⟨n1, n10, n0⟩ := exposure_risk_nested' p se sp hp hse hsp h h1 h0 hle
  have hm0 := exposure_risk_false_pos p se sp hp hse hsp h h1 h0 hr0
  have hr1 : 0 ≤ risk p true := by
    unfold risk
    have := hp true true
    have := hp true false
    positivity
  unfold tableRiskRatio EffectMeasure.riskRatio
  refine ⟨?_, (div_le_one hm0).mpr n10⟩
  rw [div_le_div_iff₀ hr0 hm0]
  nlinarith [mul_le_mul_of_nonneg_left n0 hr1, mul_le_mul_of_nonneg_right n1 hr0.le]

/-- Toward the null on the odds ratio scale: under the hypotheses of
`exposure_riskRatio_toward_null` and with the exposed risk below one, `1 ≤ OR* ≤ OR`, where
`OR*` is the odds ratio of the expected observed counts. -/
theorem exposure_oddsRatio_toward_null (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false)
    (hr0 : 0 < risk p false) (hle : risk p false ≤ risk p true) (hr1 : risk p true < 1) :
    1 ≤ tableOddsRatio (exposureMisclassified p se sp) ∧
      tableOddsRatio (exposureMisclassified p se sp) ≤ tableOddsRatio p := by
  obtain ⟨n0, n01, n1⟩ := exposure_risk_nested p se sp hp hse hsp h h1 h0 hle
  have hm1 : risk (exposureMisclassified p se sp) true < 1 := lt_of_le_of_lt n1 hr1
  have hm0 : risk (exposureMisclassified p se sp) false < 1 := lt_of_le_of_lt n01 hm1
  exact ratio_nested (EffectMeasure.odds_pos hr0 (lt_of_le_of_lt hle hr1))
    (odds_le_odds n0 hm0) (odds_le_odds n01 hm1) (odds_le_odds n1 hr1)

/-- Toward the null on the odds ratio scale, protective case: `OR ≤ OR* ≤ 1` for the odds ratio
`OR*` of the expected observed counts, with reference risk in `(0, 1)`. A zero exposed risk (true
odds ratio `0`) is allowed. -/
theorem exposure_oddsRatio_toward_null' (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 ≤ p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (h1 : 0 < p true true + p true false) (h0 : 0 < p false true + p false false)
    (hr0 : 0 < risk p false) (hle : risk p true ≤ risk p false) (hr0' : risk p false < 1) :
    tableOddsRatio p ≤ tableOddsRatio (exposureMisclassified p se sp) ∧
      tableOddsRatio (exposureMisclassified p se sp) ≤ 1 := by
  obtain ⟨n1, n10, n0⟩ := exposure_risk_nested' p se sp hp hse hsp h h1 h0 hle
  have hm0 := exposure_risk_false_pos p se sp hp hse hsp h h1 h0 hr0
  have hr1 : 0 ≤ risk p true := by
    unfold risk
    have := hp true true
    have := hp true false
    positivity
  have hm0' : risk (exposureMisclassified p se sp) false < 1 := lt_of_le_of_lt n0 hr0'
  have hm1' : risk (exposureMisclassified p se sp) true < 1 := lt_of_le_of_lt n10 hm0'
  have hr1' : risk p true < 1 := lt_of_le_of_lt hle hr0'
  have o1 := odds_le_odds n1 hm1'
  have o10 := odds_le_odds n10 hm0'
  have o0 := odds_le_odds n0 hr0'
  have hO1 : 0 ≤ EffectMeasure.odds (risk p true) := by
    unfold EffectMeasure.odds
    exact div_nonneg hr1 (by linarith)
  have hOm0 : 0 < EffectMeasure.odds (risk (exposureMisclassified p se sp) false) :=
    EffectMeasure.odds_pos hm0 hm0'
  have hO0 : 0 < EffectMeasure.odds (risk p false) := EffectMeasure.odds_pos hr0 hr0'
  unfold tableOddsRatio EffectMeasure.oddsRatio
  refine ⟨?_, (div_le_one hOm0).mpr o10⟩
  rw [div_le_div_iff₀ hO0 hOm0]
  nlinarith [mul_le_mul_of_nonneg_left o0 hO1, mul_le_mul_of_nonneg_right o1 hO0.le]

/-- The transpose `(d, e) ↦ p e d` of a table, exchanging the roles of the two variables. -/
def transposeTable (p : Bool → Bool → ℝ) (d e : Bool) : ℝ := p e d

/-- Outcome misclassification of a table is exposure misclassification of its transpose,
transposed back. -/
theorem outcomeMisclassified_eq_transpose (p : Bool → Bool → ℝ) (se sp : ℝ) :
    outcomeMisclassified p se sp =
      transposeTable (exposureMisclassified (transposeTable p) se sp) := by
  funext e d'
  rw [transposeTable, outcomeMisclassified_apply, exposureMisclassified_apply]
  rfl

/-- The cross product ratio is invariant under transposition. -/
theorem crossOddsRatio_transpose (q : Bool → Bool → ℝ) :
    crossOddsRatio (transposeTable q) = crossOddsRatio q := by
  simp only [crossOddsRatio, transposeTable]
  ring

/-- Toward the null on the odds ratio scale for nondifferential outcome misclassification with
`SE ≤ 1`, `SP ≤ 1` and `SE + SP > 1`: for a table with all cells positive and true odds ratio at
least one, the odds ratio `OR*` of the expected observed counts satisfies `1 ≤ OR* ≤ OR`. The
odds ratio is symmetric in the two variables, so this is `exposure_oddsRatio_toward_null` for the
transposed table. The risk ratio companion is `Bias.outcome_riskRatio_toward_null`. -/
theorem outcome_tableOddsRatio_toward_null (p : Bool → Bool → ℝ) (se sp : ℝ)
    (hp : ∀ a y, 0 < p a y) (hse : se ≤ 1) (hsp : sp ≤ 1) (h : 1 < se + sp)
    (hOR : 1 ≤ tableOddsRatio p) :
    1 ≤ tableOddsRatio (outcomeMisclassified p se sp) ∧
      tableOddsRatio (outcomeMisclassified p se sp) ≤ tableOddsRatio p := by
  have hpT : ∀ a y, 0 < transposeTable p a y := fun a y ↦ hp y a
  have hse0 : 0 < se := by linarith
  have hsp0 : 0 < sp := by linarith
  have hobs : ∀ a y, 0 < exposureMisclassified (transposeTable p) se sp a y := by
    intro a y
    rw [exposureMisclassified_apply]
    have := hpT true y
    have := hpT false y
    have : 0 ≤ 1 - se := by linarith
    have : 0 ≤ 1 - sp := by linarith
    cases a <;> simp only [Fintype.sum_bool, binaryKernel, ↓reduceIte, Bool.false_eq_true] <;>
      positivity
  have hcross : ∀ q : Bool → Bool → ℝ, (∀ a y, 0 < q a y) →
      tableOddsRatio (transposeTable q) = tableOddsRatio q := by
    intro q hq
    rw [tableOddsRatio_eq_cross (transposeTable q) (fun a y ↦ hq y a),
      tableOddsRatio_eq_cross _ hq,
      crossOddsRatio_transpose]
  have hOR' : 1 ≤ tableOddsRatio (transposeTable p) := by rw [hcross p hp]; exact hOR
  rw [outcomeMisclassified_eq_transpose, hcross _ hobs, ← hcross p hp]
  have a1 := hpT true true
  have a2 := hpT true false
  have a3 := hpT false true
  have a4 := hpT false false
  have hr0 : 0 < risk (transposeTable p) false := by
    unfold risk
    positivity
  have hr1 : risk (transposeTable p) true < 1 := by
    unfold risk
    rw [div_lt_one (by positivity)]
    linarith
  have hle : risk (transposeTable p) false ≤ risk (transposeTable p) true := by
    rw [tableOddsRatio_eq_cross _ hpT] at hOR'
    unfold crossOddsRatio at hOR'
    unfold risk
    rw [one_le_div (by positivity)] at hOR'
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact exposure_oddsRatio_toward_null (transposeTable p) se sp (fun a y ↦ (hpT a y).le) hse
    hsp h (by linarith) (by linarith) hr0 hle hr1

end Exposure

section ErrorStructure

/-! ### Differential and dependent errors (sections "Differential vs. Nondifferential" and
"Dependent vs. Independent")

A joint classification kernel `K e d e' d' = P(E* = e', D* = d' | E = e, D = d)`. -/

/-- The exposure classification probabilities `P(E* = e' | E = e, D = d)` of a joint kernel. -/
def exposureRate (K : Bool → Bool → Bool → Bool → ℝ) (e d e' : Bool) : ℝ := ∑ d', K e d e' d'

/-- The disease classification probabilities `P(D* = d' | E = e, D = d)` of a joint kernel. -/
def outcomeRate (K : Bool → Bool → Bool → Bool → ℝ) (e d d' : Bool) : ℝ := ∑ e', K e d e' d'

/-- Exposure misclassification is nondifferential with respect to disease: the exposure
classification probabilities do not depend on the true disease. -/
def ExposureNondifferential (K : Bool → Bool → Bool → Bool → ℝ) : Prop :=
  ∀ e e', exposureRate K e true e' = exposureRate K e false e'

/-- Disease misclassification is nondifferential with respect to exposure. -/
def OutcomeNondifferential (K : Bool → Bool → Bool → Bool → ℝ) : Prop :=
  ∀ d d', outcomeRate K true d d' = outcomeRate K false d d'

/-- The exposure and disease errors are independent: given the true values, the joint
classification probability is the product of the two marginal classification probabilities. -/
def IndependentErrors (K : Bool → Bool → Bool → Bool → ℝ) : Prop :=
  ∀ e d e' d', K e d e' d' = exposureRate K e d e' * outcomeRate K e d d'

/-- The product kernel of an exposure classification with `(seE, spE)` and a disease
classification with `(seD, spD)` is nondifferential in both directions and has independent
errors. -/
theorem productKernel_structure (seE spE seD spD : ℝ) :
    ExposureNondifferential (fun e d e' d' ↦ binaryKernel seE spE e e' * binaryKernel seD spD d d')
      ∧ OutcomeNondifferential
        (fun e d e' d' ↦ binaryKernel seE spE e e' * binaryKernel seD spD d d') ∧
      IndependentErrors
        (fun e d e' d' ↦ binaryKernel seE spE e e' * binaryKernel seD spD d d') := by
  have hE : ∀ e d e', exposureRate
      (fun e d e' d' ↦ binaryKernel seE spE e e' * binaryKernel seD spD d d') e d e' =
        binaryKernel seE spE e e' := by
    intro e d e'
    rw [exposureRate, ← Finset.mul_sum, binaryKernel_sum, mul_one]
  have hD : ∀ e d d', outcomeRate
      (fun e d e' d' ↦ binaryKernel seE spE e e' * binaryKernel seD spD d d') e d d' =
        binaryKernel seD spD d d' := by
    intro e d d'
    rw [outcomeRate, ← Finset.sum_mul, binaryKernel_sum, one_mul]
  exact ⟨fun e e' ↦ by rw [hE, hE], fun d d' ↦ by rw [hD, hD],
    fun e d e' d' ↦ by rw [hE, hD]⟩

/-- The statistical reading of `productKernel_structure`: with sensitivities and specificities in
`[0, 1]` the product kernel is a measurement kernel (`Bias.IsMeasurementKernel`: nonnegative
entries, rows summing to one). The algebraic statement above holds for all real parameters. -/
theorem productKernel_isMeasurementKernel (seE spE seD spD : ℝ) (hseE : seE ∈ Set.Icc 0 1)
    (hspE : spE ∈ Set.Icc 0 1) (hseD : seD ∈ Set.Icc 0 1) (hspD : spD ∈ Set.Icc 0 1) :
    IsMeasurementKernel
      (fun e d e' d' ↦ binaryKernel seE spE e e' * binaryKernel seD spD d d') := by
  obtain ⟨a0, a1⟩ := hseE
  obtain ⟨b0, b1⟩ := hspE
  obtain ⟨c0, c1⟩ := hseD
  obtain ⟨d0, d1⟩ := hspD
  have hk : ∀ se sp : ℝ, 0 ≤ se → se ≤ 1 → 0 ≤ sp → sp ≤ 1 → ∀ b b',
      0 ≤ binaryKernel se sp b b' := by
    intro se sp h0 h1 h2 h3 b b'
    cases b <;> cases b' <;> simp only [binaryKernel, Bool.false_eq_true, ↓reduceIte] <;>
      linarith
  refine ⟨fun e d e' d' ↦ mul_nonneg (hk _ _ a0 a1 b0 b1 e e') (hk _ _ c0 c1 d0 d1 d d'),
    fun e d ↦ ?_⟩
  simp only [← Finset.mul_sum, binaryKernel_sum, mul_one]

/-- Outside `[0, 1]` the product kernel is not a measurement kernel: with exposure sensitivity
`2` the entry `P(E* = 0 | E = 1) = 1 - 2` is negative. -/
theorem productKernel_not_isMeasurementKernel :
    ¬ IsMeasurementKernel (fun e d e' d' ↦ binaryKernel 2 1 e e' * binaryKernel 1 1 d d') := by
  intro h
  have := h.1 true true false true
  norm_num [binaryKernel] at this

/-- The dependent kernel `Bias.dependentKernel` (a common error records both variables as
positive with probability `1/2`) is nondifferential in both directions but its errors are not
independent: dependent nondifferential misclassification. -/
theorem dependentKernel_structure :
    ExposureNondifferential dependentKernel ∧ OutcomeNondifferential dependentKernel ∧
      ¬ IndependentErrors dependentKernel := by
  refine ⟨fun e e' ↦ ?_, fun d d' ↦ ?_, fun h ↦ ?_⟩
  · cases e <;> cases e' <;>
      simp [exposureRate, dependentKernel, exactKernel]
  · cases d <;> cases d' <;>
      simp [outcomeRate, dependentKernel, exactKernel]
  · have := h false false true true
    norm_num [exposureRate, outcomeRate, dependentKernel, exactKernel] at this

end ErrorStructure

section PredictiveValues

/-! ### Correction with predictive values (Table 6.10) -/

/-- The validation table of disease row `d`: the count with true exposure `e` and classified
exposure `e'` among those with disease `d`. -/
def exposureJoint (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool) (e e' : Bool) : ℝ :=
  p e d * binaryKernel (se d) (sp d) e e'

theorem sensitivity_exposureJoint (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (h : p true d ≠ 0) : sensitivity (exposureJoint p se sp d) = se d :=
  sensitivity_validationOf (fun e ↦ p e d) (se d) (sp d) h

theorem specificity_exposureJoint (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (d : Bool)
    (h : p false d ≠ 0) : specificity (exposureJoint p se sp d) = sp d :=
  specificity_validationOf (fun e ↦ p e d) (se d) (sp d) h

/-- The bias-adjusted table of Table 6.10: `A = a PPV_d + b (1 - NPV_d)` and the unexposed count
is the row total minus `A`. -/
noncomputable def pvCorrected (q : Bool → Bool → ℝ) (ppvD npvD : Bool → ℝ) : Bool → Bool → ℝ :=
  fun e d ↦
    if e then q true d * ppvD d + q false d * (1 - npvD d)
    else q true d + q false d - (q true d * ppvD d + q false d * (1 - npvD d))

/-- Correction with predictive values (Table 6.10): if the observed table is the expected image
of a true table under exposure misclassification, and both observed cells of each row are
nonzero, then reallocating with the row-specific predictive values recovers the true table. -/
theorem pvCorrected_misclassified (p : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (h1 : ∀ d, exposureMisclassifiedDiff p se sp true d ≠ 0)
    (h0 : ∀ d, exposureMisclassifiedDiff p se sp false d ≠ 0) :
    pvCorrected (exposureMisclassifiedDiff p se sp) (fun d ↦ ppv (exposureJoint p se sp d))
      (fun d ↦ npv (exposureJoint p se sp d)) = p := by
  funext e d
  have hA : exposureMisclassifiedDiff p se sp true d * ppv (exposureJoint p se sp d) +
      exposureMisclassifiedDiff p se sp false d * (1 - npv (exposureJoint p se sp d)) =
        p true d := by
    have ht := h1 d
    have hf := h0 d
    rw [exposureMisclassifiedDiff_exposed] at ht ⊢
    rw [exposureMisclassifiedDiff_unexposed] at hf ⊢
    have hf' : p false d * sp d + p true d * (1 - se d) ≠ 0 := by rwa [add_comm]
    simp only [ppv, npv, exposureJoint, binaryKernel, ↓reduceIte, Bool.false_eq_true]
    rw [one_sub_div hf', mul_div_assoc', mul_div_assoc', div_add_div _ _ ht hf', div_eq_iff
      (mul_ne_zero ht hf')]
    ring
  cases e
  · simp only [pvCorrected, Bool.false_eq_true, ↓reduceIte, hA,
      exposureMisclassifiedDiff_row]
    ring
  · simp only [pvCorrected, ↓reduceIte, hA]

/-! ### Outcome misclassification: Brenner and Gefeller, perfect specificity -/

/-- The expected observed table when exposure is measured exactly and the disease is
misclassified with sensitivity `se e` and specificity `sp e` in exposure level `e` (Table
6.18). -/
def outcomeMisclassifiedDiff (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) : Bool → Bool → ℝ :=
  observedTable p fun e d e' d' ↦ exactKernel e e' * binaryKernel (se e) (sp e) d d'

theorem outcomeMisclassifiedDiff_apply (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (e d' : Bool) :
    outcomeMisclassifiedDiff p se sp e d' = ∑ d, p e d * binaryKernel (se e) (sp e) d d' := by
  cases e <;> simp [outcomeMisclassifiedDiff, observedTable, exactKernel]

/-- The positive predictive value of disease classification in exposure level `e`:
`P(D = 1 | D* = 1, E = e) = P(D = 1, D* = 1 | E = e) / P(D* = 1 | E = e)`. -/
noncomputable def outcomePPV (p : Bool → Bool → ℝ) (se sp : Bool → ℝ) (e : Bool) : ℝ :=
  p e true * se e / outcomeMisclassifiedDiff p se sp e true

/-- Brenner and Gefeller (section "Bias-Adjustment for Nondifferential Outcome Misclassification
Using Positive Predictive Values for the Risk Ratio Measure of Association"): if the sensitivity
of disease classification does not depend on exposure (the specificities `sp e` may), then
`RR = RR_obs · PPV₁ / PPV₀`. -/
theorem brenner_gefeller (p : Bool → Bool → ℝ) (se : ℝ) (sp : Bool → ℝ) (hse : se ≠ 0)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0)
    (hp0 : p false true ≠ 0)
    (hq1 : outcomeMisclassifiedDiff p (fun _ ↦ se) sp true true ≠ 0)
    (hq0 : outcomeMisclassifiedDiff p (fun _ ↦ se) sp false true ≠ 0) :
    tableRiskRatio p =
      tableRiskRatio (outcomeMisclassifiedDiff p (fun _ ↦ se) sp) *
        (outcomePPV p (fun _ ↦ se) sp true / outcomePPV p (fun _ ↦ se) sp false) := by
  have hrow : ∀ e, outcomeMisclassifiedDiff p (fun _ ↦ se) sp e true +
      outcomeMisclassifiedDiff p (fun _ ↦ se) sp e false = p e true + p e false := by
    intro e
    simp only [outcomeMisclassifiedDiff_apply, Fintype.sum_bool, binaryKernel, ↓reduceIte,
      Bool.false_eq_true]
    ring
  simp only [tableRiskRatio, EffectMeasure.riskRatio, risk, outcomePPV, hrow]
  field_simp

/-- Perfect specificity (section "Overreliance on Nondifferential Misclassification Biasing
Toward the Null"): with specificity one, nondifferential nonzero sensitivity and cases in the
reference group (`hr0`), the risk ratio of the expected observed counts equals the true one, and
its reference risk `SE · r₀` is nonzero, so both risk ratios are real quotients. Without cases in
the reference group both would be divisions by zero. -/
theorem outcome_riskRatio_perfect_specificity (p : Bool → Bool → ℝ) (se : ℝ) (hse : se ≠ 0)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0)
    (hr0 : p false true ≠ 0) :
    tableRiskRatio (outcomeMisclassified p se 1) = tableRiskRatio p ∧
      risk (outcomeMisclassified p se 1) false ≠ 0 := by
  refine ⟨?_, ?_⟩
  · simp only [tableRiskRatio, EffectMeasure.riskRatio, outcome_risk_eq p se 1 true h1,
      outcome_risk_eq p se 1 false h0, sub_self, add_sub_cancel_right, zero_add]
    exact mul_div_mul_left _ _ hse
  · rw [outcome_risk_eq p se 1 false h0, sub_self, add_sub_cancel_right, zero_add]
    exact mul_ne_zero hse (div_ne_zero hr0 h0)

/-- With specificity one the risk difference of the expected observed counts is the true one
times the sensitivity (`Bias.outcome_riskDiff_eq` at `sp = 1`). This forward identity holds for
every sensitivity, including `SE = 0`, where every observed risk difference is zero; the
inverse `RD = RD* / SE` needs `SE ≠ 0` (`outcome_riskDiff_perfect_specificity_inv`). -/
theorem outcome_riskDiff_perfect_specificity (p : Bool → Bool → ℝ) (se : ℝ)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0) :
    riskDiff (outcomeMisclassified p se 1) = se * riskDiff p := by
  rw [outcome_riskDiff_eq p se 1 h1 h0, add_sub_cancel_right]

/-- The inverse of `outcome_riskDiff_perfect_specificity`: with specificity one and nonzero
sensitivity the true risk difference is recovered by division, `RD = RD* / SE`. -/
theorem outcome_riskDiff_perfect_specificity_inv (p : Bool → Bool → ℝ) (se : ℝ) (hse : se ≠ 0)
    (h1 : p true true + p true false ≠ 0) (h0 : p false true + p false false ≠ 0) :
    riskDiff p = riskDiff (outcomeMisclassified p se 1) / se := by
  rw [outcome_riskDiff_perfect_specificity p se h1 h0, mul_div_cancel_left₀ _ hse]

/-! ### Internal validation data (Tables 6.14 and 6.15) -/

/-- Internal validation with supplied bias parameters: if the validated subset has known true
table `V` and the remainder's observed table is the expected image of its true table `pR` under
the supplied `se`, `sp`, then adding `V` to the bias-adjusted remainder gives the true table of the
whole study. The parameters are not linked to the validated subset here; the version with
parameters estimated from it is `internalValidation_estimated`. -/
theorem internalValidation_recovers (V pR : Bool → Bool → ℝ) (se sp : Bool → ℝ)
    (h : ∀ d, se d + sp d ≠ 1) :
    (fun e d ↦ V e d + exposureCorrected (exposureMisclassifiedDiff pR se sp) se sp e d) =
      fun e d ↦ V e d + pR e d := by
  rw [exposureCorrected_misclassified pR se sp h]

/-- The true table `(e, d)` of an internal validation table `V e e' d` (true exposure `e`,
classified exposure `e'`, disease `d`). -/
def validatedTrue (V : Bool → Bool → Bool → ℝ) (e d : Bool) : ℝ := V e true d + V e false d

/-- The classified table `(e', d)` of an internal validation table. -/
def validatedObserved (V : Bool → Bool → Bool → ℝ) (e' d : Bool) : ℝ :=
  V true e' d + V false e' d

/-- The sensitivity estimated in disease row `d` of an internal validation table. -/
noncomputable def validationSe (V : Bool → Bool → Bool → ℝ) (d : Bool) : ℝ :=
  sensitivity fun e e' ↦ V e e' d

/-- The specificity estimated in disease row `d` of an internal validation table. -/
noncomputable def validationSp (V : Bool → Bool → Bool → ℝ) (d : Bool) : ℝ :=
  specificity fun e e' ↦ V e e' d

/-- In the validated subset the classification is exactly the image of the true table under the
row-specific sensitivity and specificity estimated from it (both true classes nonempty in each
row). -/
theorem validatedObserved_eq (V : Bool → Bool → Bool → ℝ)
    (h1 : ∀ d, V true true d + V true false d ≠ 0)
    (h0 : ∀ d, V false false d + V false true d ≠ 0) :
    exposureMisclassifiedDiff (validatedTrue V) (validationSe V) (validationSp V) =
      validatedObserved V := by
  funext e' d
  have ht := h1 d
  have hf := h0 d
  cases e'
  · rw [exposureMisclassifiedDiff_unexposed]
    simp only [validatedTrue, validatedObserved, validationSe, validationSp, sensitivity,
      specificity]
    field_simp
    ring
  · rw [exposureMisclassifiedDiff_exposed]
    simp only [validatedTrue, validatedObserved, validationSe, validationSp, sensitivity,
      specificity]
    field_simp
    ring

/-- Internal validation with parameters estimated from the validated subset (section
"Bias-Adjustments Using Sensitivity and Specificity: Internal Validation Data", Tables 6.14 and
6.15). The sensitivity and specificity are computed in each disease row of the validation table
`V`. The transport assumption `hT` is that the observed table `qR` of the remainder, whose true
table is `pR`, is the expected image of `pR` under those same row-specific parameters. Then:
bias-adjusting the remainder with the estimated parameters and adding the validated true cells
gives the true table of the whole study; the whole observed table (validated classifications plus
`qR`) is the image of the whole true table; and bias-adjusting the whole observed table with the
estimated parameters gives the same true table. -/
theorem internalValidation_estimated (V : Bool → Bool → Bool → ℝ) (pR qR : Bool → Bool → ℝ)
    (h1 : ∀ d, V true true d + V true false d ≠ 0)
    (h0 : ∀ d, V false false d + V false true d ≠ 0)
    (hk : ∀ d, validationSe V d + validationSp V d ≠ 1)
    (hT : qR = exposureMisclassifiedDiff pR (validationSe V) (validationSp V)) :
    (fun e d ↦ validatedTrue V e d + exposureCorrected qR (validationSe V) (validationSp V) e d) =
        (fun e d ↦ validatedTrue V e d + pR e d) ∧
      (fun e' d ↦ validatedObserved V e' d + qR e' d) =
        exposureMisclassifiedDiff (fun e d ↦ validatedTrue V e d + pR e d) (validationSe V)
          (validationSp V) ∧
      exposureCorrected (fun e' d ↦ validatedObserved V e' d + qR e' d) (validationSe V)
          (validationSp V) = (fun e d ↦ validatedTrue V e d + pR e d) := by
  have hobs : (fun e' d ↦ validatedObserved V e' d + qR e' d) =
      exposureMisclassifiedDiff (fun e d ↦ validatedTrue V e d + pR e d) (validationSe V)
        (validationSp V) := by
    rw [← validatedObserved_eq V h1 h0, hT]
    funext e' d
    cases e'
    · simp only [exposureMisclassifiedDiff_unexposed]
      ring
    · simp only [exposureMisclassifiedDiff_exposed]
      ring
  refine ⟨?_, hobs, ?_⟩
  · rw [hT, exposureCorrected_misclassified pR _ _ hk]
  · rw [hobs, exposureCorrected_misclassified _ _ _ hk]

end PredictiveValues

section CaseControl

/-! ### Disease misclassification in case-control studies

Model: in exposure level `j` the source population has `N` true cases and `M` true noncases.
The disease is classified with sensitivity `se` and specificity `sp`; all apparent cases enter the
study and apparent noncases enter with sampling fraction `f`. The study observes `a` apparent
cases and a total `E = a + f · (apparent noncases)`. -/

/-- The apparent cases `SE N + (1 - SP) M`. -/
def apparentCases (N M se sp : ℝ) : ℝ := se * N + (1 - sp) * M

/-- The apparent noncases `(1 - SE) N + SP M`. -/
def apparentNoncases (N M se sp : ℝ) : ℝ := (1 - se) * N + sp * M

/-- The bias-adjusted number of cases (section "Disease Misclassification in Case-Control
Studies"): `A = (a - (1 - SP)(a + (E - a)/f)) / (SE + SP - 1)`. -/
noncomputable def ccCases (a E f se sp : ℝ) : ℝ :=
  (a - (1 - sp) * (a + (E - a) / f)) / (se + sp - 1)

/-- The bias-adjusted number of noncases: `B = ((E - a)/f - (1 - SE)(a + (E - a)/f)) / (SE + SP -
1)`; the bias-adjusted number of controls is `f B`. -/
noncomputable def ccNoncases (a E f se sp : ℝ) : ℝ :=
  ((E - a) / f - (1 - se) * (a + (E - a) / f)) / (se + sp - 1)

/-- The case-control correction recovers the source counts: with `f ≠ 0` and `SE + SP ≠ 1`, the
formulas applied to the study counts generated by the model give `N` cases and `M` noncases. -/
theorem cc_correction (N M se sp f : ℝ) (hf : f ≠ 0) (hk : se + sp ≠ 1) :
    ccCases (apparentCases N M se sp)
        (apparentCases N M se sp + f * apparentNoncases N M se sp) f se sp = N ∧
      ccNoncases (apparentCases N M se sp)
        (apparentCases N M se sp + f * apparentNoncases N M se sp) f se sp = M := by
  have hk' : se + sp - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hE : (apparentCases N M se sp + f * apparentNoncases N M se sp -
      apparentCases N M se sp) / f = apparentNoncases N M se sp := by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hf]
  unfold ccCases ccNoncases
  rw [hE]
  constructor <;> rw [div_eq_iff hk'] <;> unfold apparentCases apparentNoncases <;> ring

/-- The validation table of the case-control study: true cases `N` and noncases `M` of one
exposure level, classified with `(se, sp)`, apparent noncases sampled with fraction `f`. -/
def ccStudyTable (N M se sp f : ℝ) (e e' : Bool) : ℝ :=
  if e then (if e' then se * N else f * ((1 - se) * N))
  else (if e' then (1 - sp) * M else f * (sp * M))

/-- The case-control correction is the row correction of Table 6.8 applied to the row with `a`
apparent cases and `(E - a)/f` apparent noncases (the sampled apparent noncases scaled back by
the sampling fraction), for `SE + SP ≠ 1`. -/
theorem cc_eq_exposureCorrected (a E f se sp : ℝ) (hk : se + sp ≠ 1) :
    ccCases a E f se sp = exposureCorrected (fun e _ ↦ if e then a else (E - a) / f)
        (fun _ ↦ se) (fun _ ↦ sp) true true ∧
      ccNoncases a E f se sp = exposureCorrected (fun e _ ↦ if e then a else (E - a) / f)
        (fun _ ↦ se) (fun _ ↦ sp) false true := by
  have hk' : se + sp - 1 ≠ 0 := sub_ne_zero.mpr hk
  simp only [ccCases, ccNoncases, exposureCorrected, correctedExposed, ↓reduceIte,
    Bool.false_eq_true]
  generalize (E - a) / f = y
  constructor
  · ring
  · field_simp
    ring

/-- Admissibility in the case-control setting: with apparent-case total
`N* = a + (E - a)/f > 0` and `SE + SP ≠ 1`, both bias-adjusted counts `ccCases` and `ccNoncases`
are nonnegative exactly when the apparent case proportion `a / N*` lies between `1 - SP` and
`SE`, in either order. -/
theorem cc_admissible_iff (a E f se sp : ℝ) (hN : 0 < a + (E - a) / f) (hk : se + sp ≠ 1) :
    (0 ≤ ccCases a E f se sp ∧ 0 ≤ ccNoncases a E f se sp) ↔
      ((1 - sp ≤ a / (a + (E - a) / f) ∧ a / (a + (E - a) / f) ≤ se) ∨
        (se ≤ a / (a + (E - a) / f) ∧ a / (a + (E - a) / f) ≤ 1 - sp)) := by
  obtain ⟨hA, hB⟩ := cc_eq_exposureCorrected a E f se sp hk
  rw [hA, hB]
  have hn : 0 < (fun e (_ : Bool) ↦ if e then a else (E - a) / f) true true +
      (fun e (_ : Bool) ↦ if e then a else (E - a) / f) false true := by simpa using hN
  rw [admissible_iff _ (fun _ ↦ se) (fun _ ↦ sp) true hn hk]
  simp only [exposedProportion, ↓reduceIte, Bool.false_eq_true]
  constructor
  · rintro (⟨u, v⟩ | ⟨u, v⟩)
    · exact Or.inl ⟨by linarith, u⟩
    · exact Or.inr ⟨u, by linarith⟩
  · rintro (⟨u, v⟩ | ⟨u, v⟩)
    · exact Or.inl ⟨v, by linarith⟩
    · exact Or.inr ⟨u, by linarith⟩

/-- Negative bias-adjusted cases in a case-control study: with `a = 1` apparent case,
`E = 10`, `f = 0.1` and `SE = SP = 0.9`, the apparent case proportion `1/91` is below `1 - SP`
and `ccCases` is `-81/8`; with `E = 20`, `f = 0.2` it is `1/96` and `ccCases` is `-43/4`. -/
theorem cc_negative_examples :
    ccCases 1 10 0.1 0.9 0.9 = -81 / 8 ∧ ccCases 1 20 0.2 0.9 0.9 = -43 / 4 ∧
      (1 : ℝ) / (1 + (10 - 1) / 0.1) = 1 / 91 ∧ (1 : ℝ) / (1 + (20 - 1) / 0.2) = 1 / 96 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [ccCases]

/-- The study specificity differs from the population specificity: it is
`f SP / ((1 - SP) + f SP)`. The truly noncase class of the study table is nonempty when
`M ≠ 0` and `(1 - SP) + f SP ≠ 0`, so both sides are real quotients. -/
theorem specificity_ccStudyTable (N M se sp f : ℝ) (hM : M ≠ 0) (hden : 1 - sp + f * sp ≠ 0) :
    specificity (ccStudyTable N M se sp f) = f * sp / ((1 - sp) + f * sp) ∧
      ccStudyTable N M se sp f false false + ccStudyTable N M se sp f false true ≠ 0 := by
  simp only [specificity, ccStudyTable, Bool.false_eq_true, ↓reduceIte]
  rw [show f * (sp * M) = f * sp * M by ring, show f * sp * M + (1 - sp) * M =
    (1 - sp + f * sp) * M by ring, mul_div_mul_right _ _ hM]
  exact ⟨rfl, mul_ne_zero hden hM⟩

/-- The example of the section: with `SE = SP = 0.9` and controls a `1%` sample, the study
specificity is `9/109 ≈ 0.083`. -/
theorem ccStudy_specificity_example (N M : ℝ) (hM : M ≠ 0) :
    specificity (ccStudyTable N M 0.9 0.9 0.01) = 9 / 109 := by
  rw [(specificity_ccStudyTable N M _ _ _ hM (by norm_num)).1]
  norm_num

end CaseControl

section Realized

/-! ### Toward the null holds for the expected table, not for every realized table

The toward-the-null results compare effect measures computed from the expected observed counts.
A realized table can depart from the expected table, and its effect measure can lie on the other
side of the truth or be undefined (for instance when every case is recorded exposed, the realized
risk ratio divides by a zero unexposed risk). In disease row `d`, `kE d` of the truly exposed are
recorded unexposed and `kU d` of the truly unexposed are recorded exposed. -/

/-- The realized observed table after the stated integer moves within each disease row. -/
def realizedTable (p : Bool → Bool → ℝ) (kE kU : Bool → ℕ) : Bool → Bool → ℝ :=
  fun e d ↦ if e then p true d - kE d + kU d else p false d + kE d - kU d

/-- The probability, under independent classification of each individual with sensitivity `se`
and specificity `sp`, that exactly `kE` of `nE` truly exposed individuals are recorded unexposed
and exactly `kU` of `nU` truly unexposed are recorded exposed: the product of two binomial
probabilities. -/
noncomputable def realizationProb (nE nU kE kU : ℕ) (se sp : ℝ) : ℝ :=
  (nE.choose kE : ℝ) * se ^ (nE - kE) * (1 - se) ^ kE *
    ((nU.choose kU : ℝ) * sp ^ (nU - kU) * (1 - sp) ^ kU)

theorem realizationProb_pos (nE nU kE kU : ℕ) (se sp : ℝ) (hE : kE ≤ nE) (hU : kU ≤ nU)
    (hse0 : 0 < se) (hse1 : se < 1) (hsp0 : 0 < sp) (hsp1 : sp < 1) :
    0 < realizationProb nE nU kE kU se sp := by
  have h1 : (0 : ℝ) < nE.choose kE := by exact_mod_cast Nat.choose_pos hE
  have h2 : (0 : ℝ) < nU.choose kU := by exact_mod_cast Nat.choose_pos hU
  have h3 : 0 < 1 - se := by linarith
  have h4 : 0 < 1 - sp := by linarith
  unfold realizationProb
  positivity

/-- The binomial law has total mass one on `{0, …, n}`. -/
theorem sum_binomial_real (n : ℕ) (π : unitInterval) :
    ∑ k ∈ Finset.Iic n, (ProbabilityTheory.binomial n π).real {k} = 1 := by
  have h := ProbabilityTheory.integral_binomial (n := n) (p := π) (fun _ ↦ (1 : ℝ))
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one] at h
  simp_rw [ProbabilityTheory.binomial_real_singleton]
  rw [← h]
  simp

/-- The binomial mean: `∑_{k ≤ n} P(Bin(n, π) = k) k = π n`. -/
theorem sum_binomial_real_mul (n : ℕ) (π : unitInterval) :
    ∑ k ∈ Finset.Iic n, (ProbabilityTheory.binomial n π).real {k} * (k : ℝ) = π * n := by
  have h := ProbabilityTheory.integral_of_hasLaw_binomial
    (ProbabilityTheory.HasLaw.id (μ := (ProbabilityTheory.binomial n π).map (Nat.cast : ℕ → ℝ)))
  have h2 := ProbabilityTheory.integral_map_cast_binomial (R := ℝ) (n := n) (p := π)
    (fun x : ℝ ↦ x)
  simp only [id] at h
  rw [h] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [ProbabilityTheory.binomial_real_singleton, smul_eq_mul]

/-- `realizationProb` is the mass of the product of two independent binomial laws: with
`π_E = 1 - SE` and `π_U = 1 - SP`, the number of truly exposed recorded unexposed is
`Bin(n_E, π_E)` and the number of truly unexposed recorded exposed is `Bin(n_U, π_U)`. -/
theorem realizationProb_eq_binomial (nE nU kE kU : ℕ) (πE πU : unitInterval) :
    realizationProb nE nU kE kU (1 - πE) (1 - πU) =
      (ProbabilityTheory.binomial nE πE).real {kE} *
        (ProbabilityTheory.binomial nU πU).real {kU} := by
  rw [ProbabilityTheory.binomial_real_singleton, ProbabilityTheory.binomial_real_singleton]
  simp only [realizationProb, sub_sub_cancel]
  ring

/-- A double sum against two probability vectors with known means: the average of
`N - k_E + k_U` is `N - m₁ + m₂`. -/
theorem double_sum_aux (nE nU : ℕ) (f g : ℕ → ℝ) (N m1 m2 : ℝ)
    (hf : ∑ k ∈ Finset.Iic nE, f k = 1) (hf1 : ∑ k ∈ Finset.Iic nE, f k * k = m1)
    (hg : ∑ k ∈ Finset.Iic nU, g k = 1) (hg1 : ∑ k ∈ Finset.Iic nU, g k * k = m2) :
    ∑ kE ∈ Finset.Iic nE, ∑ kU ∈ Finset.Iic nU, f kE * g kU * (N - kE + kU) = N - m1 + m2 := by
  have : ∀ kE, ∑ kU ∈ Finset.Iic nU, f kE * g kU * (N - kE + kU) =
      f kE * N - f kE * kE + f kE * m2 := by
    intro kE
    have e : ∀ kU, f kE * g kU * (N - kE + kU) = f kE * (N - kE) * g kU + f kE * (g kU * kU) :=
      fun kU ↦ by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hg, hg1]
    ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hf, hf1]
  ring

/-- The expected realized exposed count of a disease row is the expected observed count. If row
`d` has `n_E` truly exposed and `n_U` truly unexposed individuals, each classified independently
with `SE = 1 - π_E` and `SP = 1 - π_U`, then averaging the realized exposed count over the
binomial law of the misclassification counts gives the cell of `exposureMisclassified`. This is
the formal sense of "in expectation" in this file: the expected counts are the counts of the
expected table, while the expected value of a ratio of realized counts is a different quantity. -/
theorem realized_exposed_expectation (p : Bool → Bool → ℝ) (d : Bool) (nE nU : ℕ)
    (hE : p true d = nE) (hU : p false d = nU) (πE πU : unitInterval) :
    ∑ kE ∈ Finset.Iic nE, ∑ kU ∈ Finset.Iic nU, realizationProb nE nU kE kU (1 - πE) (1 - πU) *
        realizedTable p (fun _ ↦ kE) (fun _ ↦ kU) true d =
      exposureMisclassified p (1 - πE) (1 - πU) true d := by
  simp only [realizationProb_eq_binomial, realizedTable, ↓reduceIte, hE]
  rw [double_sum_aux nE nU _ _ (nE : ℝ) (πE * nE) (πU * nU) (sum_binomial_real nE πE)
    (sum_binomial_real_mul nE πE) (sum_binomial_real nU πU) (sum_binomial_real_mul nU πU)]
  rw [exposureMisclassified_apply, Fintype.sum_bool]
  simp only [binaryKernel, ↓reduceIte, Bool.false_eq_true, hE, hU]
  ring

/-- The true table of the realized-table example: cases `10` exposed and `10` unexposed,
noncases `10` exposed and `30` unexposed (true risk ratio `2`). -/
def realizedExampleTruth (e d : Bool) : ℝ :=
  if d then 10 else (if e then 10 else 30)

/-- A realized table biased away from the null under nondifferential misclassification with
`SE = SP = 0.9`. This illustrates the book's refinement that nondifferential misclassification
biases toward the null "only in expectation" and "on average" (section "Overreliance on
Nondifferential Misclassification Biasing Toward the Null", which in the printed book follows
the internal validation example); the table itself is constructed here and is not printed in the
book. The true risk ratio is `2` and the risk ratio of the expected observed counts is
`19/11`, toward the null. With positive probability one unexposed case is recorded exposed and
one exposed noncase is recorded unexposed, and no other error occurs; the realized risk ratio is
`22/9 > 2`. -/
theorem realized_away_from_null :
    tableRiskRatio realizedExampleTruth = 2 ∧
      tableRiskRatio (exposureMisclassified realizedExampleTruth 0.9 0.9) = 19 / 11 ∧
      tableRiskRatio (realizedTable realizedExampleTruth (fun d ↦ if d then 0 else 1)
        (fun d ↦ if d then 1 else 0)) = 22 / 9 ∧
      0 < realizationProb 10 10 0 1 0.9 0.9 * realizationProb 10 30 1 0 0.9 0.9 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [tableRiskRatio, EffectMeasure.riskRatio, risk, realizedExampleTruth]
  · norm_num [tableRiskRatio, EffectMeasure.riskRatio, risk, realizedExampleTruth,
      exposureMisclassified_apply, binaryKernel]
  · norm_num [tableRiskRatio, EffectMeasure.riskRatio, risk, realizedExampleTruth,
      realizedTable]
  · exact mul_pos (realizationProb_pos _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (realizationProb_pos _ _ _ _ _ _ (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))

end Realized

namespace Examples

/-! ### Worked examples of Chapters 3 and 6 -/

/-- The validation data of Table 6.2 (birth certificate against medical record): true smokers
`128` classified smokers and `36` nonsmokers; true nonsmokers `5` and `465`. -/
def table62 (e e' : Bool) : ℝ :=
  if e then (if e' then 128 else 36) else (if e' then 5 else 465)

/-- Table 6.2: sensitivity `128/164 ≈ 0.78`, specificity `465/470 ≈ 0.99`, false negative
`36/164 ≈ 0.22`, false positive `5/470 ≈ 0.01`, PPV `128/133 ≈ 0.96`, NPV `465/501 ≈ 0.93`. -/
theorem table62_measures :
    sensitivity table62 = 128 / 164 ∧ specificity table62 = 465 / 470 ∧
      falseNegative table62 = 36 / 164 ∧ falsePositive table62 = 5 / 470 ∧
      ppv table62 = 128 / 133 ∧ npv table62 = 465 / 501 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sensitivity, specificity, falseNegative, falsePositive, ppv, npv, table62]

/-- The true table of Tables 6.6, 6.7 and 6.22: cases `200` exposed and `100` unexposed,
noncases `800` and `900`. -/
def table66 (e d : Bool) : ℝ :=
  if d then (if e then 200 else 100) else (if e then 800 else 900)

/-- Table 6.6: nondifferential exposure misclassification with `SE = 0.85`, `SP = 0.95` gives the
expected table `175, 125, 725, 975`; the risk ratio moves from `2` to `77/45 ≈ 1.71`, the odds
ratio from `9/4 = 2.25` to `273/145 ≈ 1.88` (printed 1.9) and the risk difference from `0.1` to
`8/99 ≈ 0.081`. -/
theorem table66_values :
    exposureMisclassified table66 0.85 0.95 true true = 175 ∧
      exposureMisclassified table66 0.85 0.95 false true = 125 ∧
      exposureMisclassified table66 0.85 0.95 true false = 725 ∧
      exposureMisclassified table66 0.85 0.95 false false = 975 ∧
      tableRiskRatio table66 = 2 ∧ tableOddsRatio table66 = 9 / 4 ∧ riskDiff table66 = 1 / 10 ∧
      tableRiskRatio (exposureMisclassified table66 0.85 0.95) = 77 / 45 ∧
      tableOddsRatio (exposureMisclassified table66 0.85 0.95) = 273 / 145 ∧
      riskDiff (exposureMisclassified table66 0.85 0.95) = 8 / 99 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureMisclassified_apply, binaryKernel, table66, tableRiskRatio, tableOddsRatio,
      EffectMeasure.riskRatio, EffectMeasure.oddsRatio, EffectMeasure.odds, riskDiff, risk]

/-- Table 6.7: differential exposure misclassification (`SE = 1` for cases and `0.7` for
noncases, `SP = 0.9`) biases away from the null: the expected table is `210, 90, 650, 1050`,
with risk ratio `133/43 ≈ 3.09 > 2` and odds ratio `49/13 ≈ 3.77 > 9/4`. The nondifferential
hypothesis of `exposure_riskRatio_toward_null` cannot be dropped. -/
theorem table67_away_from_null :
    exposureMisclassifiedDiff table66 (fun d ↦ if d then 1 else 0.7) (fun _ ↦ 0.9) true true =
        210 ∧
      exposureMisclassifiedDiff table66 (fun d ↦ if d then 1 else 0.7) (fun _ ↦ 0.9) true false =
        650 ∧
      tableRiskRatio
          (exposureMisclassifiedDiff table66 (fun d ↦ if d then 1 else 0.7) (fun _ ↦ 0.9)) =
        133 / 43 ∧
      tableOddsRatio
          (exposureMisclassifiedDiff table66 (fun d ↦ if d then 1 else 0.7) (fun _ ↦ 0.9)) =
        49 / 13 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureMisclassifiedDiff_apply, binaryKernel, table66, tableRiskRatio,
      tableOddsRatio, EffectMeasure.riskRatio, EffectMeasure.oddsRatio, EffectMeasure.odds, risk]

/-- Reversal when `SE + SP < 1` (text after Table 6.17): with `SE = 0.15`, `SP = 0.70` the
odds ratio of the expected counts of Table 6.6 is `131/156 ≈ 0.84 < 1` (printed 0.8) while the
true odds ratio is `9/4`; the hypothesis `SE + SP > 1` of `exposure_oddsRatio_toward_null`
cannot be dropped. -/
theorem table66_reversal :
    tableOddsRatio (exposureMisclassified table66 0.15 0.70) = 131 / 156 ∧
      tableRiskRatio (exposureMisclassified table66 0.15 0.70) = 31 / 36 := by
  constructor <;>
    norm_num [exposureMisclassified_apply, binaryKernel, table66, tableRiskRatio, tableOddsRatio,
      EffectMeasure.riskRatio, EffectMeasure.oddsRatio, EffectMeasure.odds, risk]

/-- The observed table of Table 6.9 (smoking during pregnancy and breast cancer): cases `215`
smokers and `1449` nonsmokers, controls `668` and `4296`. -/
def table69 (e d : Bool) : ℝ :=
  if d then (if e then 215 else 1449) else (if e then 668 else 4296)

/-- Table 6.9: with `SE = 128/164` and `SP = 465/470` the bias-adjusted cells are
`256.3, 1407.7, 799.1, 4164.9` and the odds ratio moves from `0.954` to `0.949`. The direct
formula `crossOddsRatio_exposureCorrected` gives the same value. -/
theorem table69_values :
    256.28 < exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) true true ∧
      exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) true true < 256.29 ∧
      1407.71 < exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) false true ∧
      exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) false true < 1407.72 ∧
      799.10 < exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) true false ∧
      exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) true false < 799.11 ∧
      4164.89 < exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) false false ∧
      exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470) false false < 4164.90 ∧
      0.9488 < crossOddsRatio (exposureCorrected table69 (fun _ ↦ 128 / 164)
        (fun _ ↦ 465 / 470)) ∧
      crossOddsRatio (exposureCorrected table69 (fun _ ↦ 128 / 164) (fun _ ↦ 465 / 470)) <
        0.9489 ∧
      0.9542 < crossOddsRatio table69 ∧ crossOddsRatio table69 < 0.9543 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureCorrected, correctedExposed, crossOddsRatio, table69]

/-- Admissibility in Table 6.9 (section "Negative Expected Cell Frequencies"): the observed
exposed proportion among cases is `215/1664 ≈ 12.9%`. At specificity `1 - 215/1664 ≈ 87.1%` the
bias-adjusted exposed cases are `0`; at specificity `0.87` (with `SE = 0.78`) they are negative.
-/
theorem table69_admissibility :
    correctedExposed table69 (fun _ ↦ 0.78) (fun _ ↦ 1 - 215 / 1664) true = 0 ∧
      correctedExposed table69 (fun _ ↦ 0.78) (fun _ ↦ 0.87) true < 0 := by
  constructor
  · exact (correctedExposed_eq_zero _ _ _ _ (by norm_num [table69]) (by norm_num)
      (by norm_num [exposedProportion, table69])).1
  · norm_num [correctedExposed, table69]

/-- The validation data of Table 6.12 for term births: `132, 47` classified underweight (true
underweight, true normal) and `2, 115` classified normal weight. -/
def table612Term (e e' : Bool) : ℝ :=
  if e then (if e' then 132 else 2) else (if e' then 47 else 115)

/-- The validation data of Table 6.12 for preterm births: `50, 27` classified underweight and
`0, 120` classified normal weight. -/
def table612Preterm (e e' : Bool) : ℝ :=
  if e then (if e' then 50 else 0) else (if e' then 27 else 120)

/-- The predictive values of Table 6.12: preterm `PPV = 50/77`, `NPV = 1`; term
`PPV = 132/179`, `NPV = 115/117`. -/
theorem table612_values :
    ppv table612Preterm = 50 / 77 ∧ npv table612Preterm = 1 ∧
      ppv table612Term = 132 / 179 ∧ npv table612Term = 115 / 117 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [ppv, npv, table612Preterm, table612Term]

/-- The observed table of Table 6.11 (underweight and early preterm birth): preterm `599`
underweight and `4978` normal weight, term `31175` and `391851`. -/
def table611 (e d : Bool) : ℝ :=
  if d then (if e then 599 else 4978) else (if e then 31175 else 391851)

/-- Table 6.11: with the unrounded predictive values of Table 6.12 the bias-adjusted cells are
`389.0, 5188.0, 29687.7, 393338.3` and the odds ratio is `≈ 0.993` (printed 1.0). With the
rounded caption values `PPV = 0.74`, `NPV = 0.98` for term births the adjusted term underweight
count would be `30906.52`, not the printed `29687.7`: the printed cells use the unrounded
values. -/
theorem table611_values :
    388.96 < pvCorrected table611 (fun d ↦ if d then 50 / 77 else 132 / 179)
        (fun d ↦ if d then 1 else 115 / 117) true true ∧
      pvCorrected table611 (fun d ↦ if d then 50 / 77 else 132 / 179)
        (fun d ↦ if d then 1 else 115 / 117) true true < 388.97 ∧
      29687.69 < pvCorrected table611 (fun d ↦ if d then 50 / 77 else 132 / 179)
        (fun d ↦ if d then 1 else 115 / 117) true false ∧
      pvCorrected table611 (fun d ↦ if d then 50 / 77 else 132 / 179)
        (fun d ↦ if d then 1 else 115 / 117) true false < 29687.70 ∧
      0.993 < crossOddsRatio (pvCorrected table611 (fun d ↦ if d then 50 / 77 else 132 / 179)
        (fun d ↦ if d then 1 else 115 / 117)) ∧
      crossOddsRatio (pvCorrected table611 (fun d ↦ if d then 50 / 77 else 132 / 179)
        (fun d ↦ if d then 1 else 115 / 117)) < 0.994 ∧
      pvCorrected table611 (fun d ↦ if d then 0.65 else 0.74)
        (fun d ↦ if d then 1 else 0.98) true false = 30906.52 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [pvCorrected, crossOddsRatio, table611]

/-- The observed table of Table 6.13 (family history and lymphoma): cases `57` with and `1148`
without family history, controls `26` and `1201`. -/
def table613 (e d : Bool) : ℝ :=
  if d then (if e then 57 else 1148) else (if e then 26 else 1201)

/-- Table 6.13, differential correction with `SE = 0.60, SP = 0.98` for cases and
`SE = 0.38, SP = 0.99` for controls: bias-adjusted cells `56.7` and `37.1`, odds ratio from
`2.29` to `1.584`. The printed relative change of `117%` uses the rounded odds ratios `2.3` and
`1.6`; with the unrounded values `(OR_obs - 1 - (OR_adj - 1)) / (OR_adj - 1)` is about `121%`.
-/
theorem table613_values :
    56.72 < exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
        (fun d ↦ if d then 0.98 else 0.99) true true ∧
      exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
        (fun d ↦ if d then 0.98 else 0.99) true true < 56.73 ∧
      37.10 < exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
        (fun d ↦ if d then 0.98 else 0.99) true false ∧
      exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
        (fun d ↦ if d then 0.98 else 0.99) true false < 37.11 ∧
      1.584 < crossOddsRatio (exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
        (fun d ↦ if d then 0.98 else 0.99)) ∧
      crossOddsRatio (exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
        (fun d ↦ if d then 0.98 else 0.99)) < 1.585 ∧
      2.293 < crossOddsRatio table613 ∧ crossOddsRatio table613 < 2.294 ∧
      ((2.3 : ℝ) - 1 - (1.6 - 1)) / (1.6 - 1) = 7 / 6 ∧
      1.21 < (crossOddsRatio table613 - 1 - (crossOddsRatio (exposureCorrected table613
        (fun d ↦ if d then 0.60 else 0.38) (fun d ↦ if d then 0.98 else 0.99)) - 1)) /
        (crossOddsRatio (exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
          (fun d ↦ if d then 0.98 else 0.99)) - 1) ∧
      (crossOddsRatio table613 - 1 - (crossOddsRatio (exposureCorrected table613
        (fun d ↦ if d then 0.60 else 0.38) (fun d ↦ if d then 0.98 else 0.99)) - 1)) /
        (crossOddsRatio (exposureCorrected table613 (fun d ↦ if d then 0.60 else 0.38)
          (fun d ↦ if d then 0.98 else 0.99)) - 1) < 1.22 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureCorrected, correctedExposed, crossOddsRatio, table613]

/-- The remainder of Table 6.14 (not validated): cases `18` near fields and `14` not, controls
`19` and `27`. -/
def table614Remainder (e d : Bool) : ℝ :=
  if d then (if e then 18 else 14) else (if e then 19 else 27)

/-- The validated subset of Table 6.15: cases `67, 160`, controls `116, 308`. -/
def table615Validated (e d : Bool) : ℝ :=
  if d then (if e then 67 else 160) else (if e then 116 else 308)

/-- Tables 6.14 and 6.15: the remainder corrected with `SE = 0.657, SP = 0.875` (cases) and
`SE = 0.5, SP = 0.893` (controls) has cells `26.3, 5.7, 35.8, 10.2` and odds ratio `≈ 1.32`
(printed 1.3); the validated odds ratio is `≈ 1.11`; the pooled cells give odds ratio `≈ 1.18`
(printed 1.2). -/
theorem table615_values :
    exposureCorrected table614Remainder (fun d ↦ if d then 0.657 else 0.5)
        (fun d ↦ if d then 0.875 else 0.893) true true = 500 / 19 ∧
      35.82 < exposureCorrected table614Remainder (fun d ↦ if d then 0.657 else 0.5)
        (fun d ↦ if d then 0.875 else 0.893) true false ∧
      exposureCorrected table614Remainder (fun d ↦ if d then 0.657 else 0.5)
        (fun d ↦ if d then 0.875 else 0.893) true false < 35.83 ∧
      1.315 < crossOddsRatio (exposureCorrected table614Remainder
        (fun d ↦ if d then 0.657 else 0.5) (fun d ↦ if d then 0.875 else 0.893)) ∧
      crossOddsRatio (exposureCorrected table614Remainder (fun d ↦ if d then 0.657 else 0.5)
        (fun d ↦ if d then 0.875 else 0.893)) < 1.316 ∧
      1.111 < crossOddsRatio table615Validated ∧ crossOddsRatio table615Validated < 1.112 ∧
      1.180 < crossOddsRatio (fun e d ↦ table615Validated e d + exposureCorrected
        table614Remainder (fun d ↦ if d then 0.657 else 0.5)
        (fun d ↦ if d then 0.875 else 0.893) e d) ∧
      crossOddsRatio (fun e d ↦ table615Validated e d + exposureCorrected
        table614Remainder (fun d ↦ if d then 0.657 else 0.5)
        (fun d ↦ if d then 0.875 else 0.893) e d) < 1.181 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureCorrected, correctedExposed, crossOddsRatio, table614Remainder,
      table615Validated]

/-- The bias-adjusted odds ratio need not exist on the admissible region. With `SE = SP = 0.8`,
observed cases `4` exposed and `1` unexposed and controls `5` and `5`, the bias-adjusted cells
are cases `5, 0` and controls `5, 5`: all nonnegative, but the unexposed case cell `B₁` is zero,
so `A₁ D₀ / (B₁ C₀)` is `25 / 0`, which Lean totalizes to `0`. The same happens with
`SE = SP = 0.9`, cases `9, 1` and controls `5, 5` (bias-adjusted cases `10, 0`). -/
theorem correctedOddsRatio_zero_cell :
    exposureCorrected (fun e d ↦ if d then (if e then 4 else 1) else 5) (fun _ ↦ 0.8)
        (fun _ ↦ 0.8) true true = 5 ∧
      exposureCorrected (fun e d ↦ if d then (if e then 4 else 1) else 5) (fun _ ↦ 0.8)
        (fun _ ↦ 0.8) false true = 0 ∧
      exposureCorrected (fun e d ↦ if d then (if e then 4 else 1) else 5) (fun _ ↦ 0.8)
        (fun _ ↦ 0.8) true false = 5 ∧
      exposureCorrected (fun e d ↦ if d then (if e then 4 else 1) else 5) (fun _ ↦ 0.8)
        (fun _ ↦ 0.8) false false = 5 ∧
      crossOddsRatio (exposureCorrected (fun e d ↦ if d then (if e then 4 else 1) else 5)
        (fun _ ↦ 0.8) (fun _ ↦ 0.8)) = 0 ∧
      exposureCorrected (fun e d ↦ if d then (if e then 9 else 1) else 5) (fun _ ↦ 0.9)
        (fun _ ↦ 0.9) true true = 10 ∧
      exposureCorrected (fun e d ↦ if d then (if e then 9 else 1) else 5) (fun _ ↦ 0.9)
        (fun _ ↦ 0.9) false true = 0 ∧
      crossOddsRatio (exposureCorrected (fun e d ↦ if d then (if e then 9 else 1) else 5)
        (fun _ ↦ 0.9) (fun _ ↦ 0.9)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureCorrected, correctedExposed, crossOddsRatio]

/-- The validation table of Tables 6.14 and 6.15 by true exposure `e` (residence within 0.25
miles by land-use maps), self-reported exposure `e'` and disease `d`: cases `44, 23` (truly
near) and `20, 140` (truly far); controls `58, 58` and `33, 275`. The book does not print this
cross-classification. It is reconstructed here as an integer table with the printed
margins (true `67, 160, 116, 308` of Table 6.15 and self-reported `64, 163, 91, 333` of Table
6.14) whose sensitivities and specificities round to the printed `65.7%`, `87.5%`, `50.0%` and
`89.3%`. -/
def table615Validation (e e' d : Bool) : ℝ :=
  if d then (if e then (if e' then 44 else 23) else (if e' then 20 else 140))
  else (if e then (if e' then 58 else 58) else (if e' then 33 else 275))

/-- The remainder of Table 6.14 bias-adjusted with the sensitivity and specificity estimated from
the reconstructed validation table `table615Validation`. -/
noncomputable def table615EstimatedRemainder : Bool → Bool → ℝ :=
  exposureCorrected table614Remainder (validationSe table615Validation)
    (validationSp table615Validation)

/-- Tables 6.14 and 6.15 with the bias parameters estimated from the validated subset
(`internalValidation_estimated`). The reconstructed validation table has the printed true and
self-reported margins; its row-specific estimates are `SE = 44/67`, `SP = 7/8` for cases and
`SE = 1/2`, `SP = 25/28` for controls, which round to the printed `65.7%`, `87.5%`, `50.0%`,
`89.3%`. The bias-adjusted remainder has cells rounding to the printed `26.3, 5.7, 35.8, 10.2`
and odds ratio rounding to `1.3`; adding the validated true cells gives cells rounding to the
printed totals `93.3, 165.7, 151.8, 318.2` and odds ratio rounding to `1.2`. -/
theorem table615_estimated :
    validatedTrue table615Validation = table615Validated ∧
      validatedObserved table615Validation =
        (fun e' d ↦ if d then (if e' then 64 else 163) else (if e' then 91 else 333)) ∧
      validationSe table615Validation true = 44 / 67 ∧
      validationSp table615Validation true = 7 / 8 ∧
      validationSe table615Validation false = 1 / 2 ∧
      validationSp table615Validation false = 25 / 28 ∧
      0.6565 < (44 : ℝ) / 67 ∧ (44 : ℝ) / 67 < 0.6575 ∧
      0.8925 < (25 : ℝ) / 28 ∧ (25 : ℝ) / 28 < 0.8935 ∧
      26.25 < table615EstimatedRemainder true true ∧
      table615EstimatedRemainder true true < 26.35 ∧
      5.65 < table615EstimatedRemainder false true ∧
      table615EstimatedRemainder false true < 5.75 ∧
      35.75 < table615EstimatedRemainder true false ∧
      table615EstimatedRemainder true false < 35.85 ∧
      10.15 < table615EstimatedRemainder false false ∧
      table615EstimatedRemainder false false < 10.25 ∧
      1.25 < crossOddsRatio table615EstimatedRemainder ∧
      crossOddsRatio table615EstimatedRemainder < 1.35 ∧
      93.25 < table615Validated true true + table615EstimatedRemainder true true ∧
      table615Validated true true + table615EstimatedRemainder true true < 93.35 ∧
      165.65 < table615Validated false true + table615EstimatedRemainder false true ∧
      table615Validated false true + table615EstimatedRemainder false true < 165.75 ∧
      151.75 < table615Validated true false + table615EstimatedRemainder true false ∧
      table615Validated true false + table615EstimatedRemainder true false < 151.85 ∧
      318.15 < table615Validated false false + table615EstimatedRemainder false false ∧
      table615Validated false false + table615EstimatedRemainder false false < 318.25 ∧
      1.15 < crossOddsRatio (fun e d ↦ table615Validated e d + table615EstimatedRemainder e d) ∧
      crossOddsRatio (fun e d ↦ table615Validated e d + table615EstimatedRemainder e d) <
        1.25 := by
  have hse1 : validationSe table615Validation true = 44 / 67 := by
    norm_num [validationSe, sensitivity, table615Validation]
  have hsp1 : validationSp table615Validation true = 7 / 8 := by
    norm_num [validationSp, specificity, table615Validation]
  have hse0 : validationSe table615Validation false = 1 / 2 := by
    norm_num [validationSe, sensitivity, table615Validation]
  have hsp0 : validationSp table615Validation false = 25 / 28 := by
    norm_num [validationSp, specificity, table615Validation]
  have hC : table615EstimatedRemainder = exposureCorrected table614Remainder
      (fun d ↦ if d then 44 / 67 else 1 / 2) (fun d ↦ if d then 7 / 8 else 25 / 28) := by
    unfold table615EstimatedRemainder
    congr 1 <;> funext d <;> cases d <;> simp [hse1, hsp1, hse0, hsp0]
  refine ⟨?_, ?_, hse1, hsp1, hse0, hsp0, ?_⟩
  · funext e d
    cases e <;> cases d <;> norm_num [validatedTrue, table615Validation, table615Validated]
  · funext e' d
    cases e' <;> cases d <;> norm_num [validatedObserved, table615Validation]
  rw [hC]
  norm_num [exposureCorrected, correctedExposed, crossOddsRatio, table614Remainder,
    table615Validated]

/-- The true cohort of Table 3.1: cases `90` exposed and `270` unexposed, noncases `9910` and
`89730`. -/
def table31 (e d : Bool) : ℝ :=
  if d then (if e then 90 else 270) else (if e then 9910 else 89730)

/-- Table 3.1: nondifferential misclassification with `SE = 0.6`, `SP = 0.9` gives the expected
table `81, 279, 14919, 84721`; the risk ratio moves from `3` to `51/31 ≈ 1.65`. The predictive
values differ between cases (`PPV = 2/3`, `NPV = 27/31 ≈ 0.871`) and noncases (`PPV ≈ 0.399`,
`NPV ≈ 0.953`) although SE and SP do not. -/
theorem table31_values :
    exposureMisclassified table31 0.6 0.9 true true = 81 ∧
      exposureMisclassified table31 0.6 0.9 false true = 279 ∧
      exposureMisclassified table31 0.6 0.9 true false = 14919 ∧
      exposureMisclassified table31 0.6 0.9 false false = 84721 ∧
      tableRiskRatio table31 = 3 ∧
      tableRiskRatio (exposureMisclassified table31 0.6 0.9) = 51 / 31 ∧
      ppv (exposureJoint table31 (fun _ ↦ 0.6) (fun _ ↦ 0.9) true) = 2 / 3 ∧
      npv (exposureJoint table31 (fun _ ↦ 0.6) (fun _ ↦ 0.9) true) = 27 / 31 ∧
      0.398 < ppv (exposureJoint table31 (fun _ ↦ 0.6) (fun _ ↦ 0.9) false) ∧
      ppv (exposureJoint table31 (fun _ ↦ 0.6) (fun _ ↦ 0.9) false) < 0.399 ∧
      0.953 < npv (exposureJoint table31 (fun _ ↦ 0.6) (fun _ ↦ 0.9) false) ∧
      npv (exposureJoint table31 (fun _ ↦ 0.6) (fun _ ↦ 0.9) false) < 0.954 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureMisclassified_apply, binaryKernel, table31, tableRiskRatio,
      EffectMeasure.riskRatio, risk, ppv, npv, exposureJoint]

/-- The large-population variant of Table 6.22 in the section "Overreliance on Nondifferential
Misclassification Biasing Toward the Null": `100800` exposed and `100900` unexposed noncases. -/
def table622Large (e d : Bool) : ℝ :=
  if d then (if e then 200 else 100) else (if e then 100800 else 100900)

/-- Near-perfect specificity is not enough (Figure 6.6 and text): with `SE = 1`, `SP = 0.99` the
risk ratio of the expected counts of Table 6.22 is `208/109 ≈ 1.91`; in the large population
with `SE = 0.53` the true risk ratio `2` is preserved at `SP = 1` but drops to `≈ 1.049` at
`SP = 0.99`. -/
theorem table622_specificity :
    tableRiskRatio (outcomeMisclassified table66 1 0.99) = 208 / 109 ∧
      tableRiskRatio table622Large = 2 ∧
      tableRiskRatio (outcomeMisclassified table622Large 0.53 1) = 2 ∧
      1.048 < tableRiskRatio (outcomeMisclassified table622Large 0.53 0.99) ∧
      tableRiskRatio (outcomeMisclassified table622Large 0.53 0.99) < 1.050 := by
  have hT : tableRiskRatio table622Large = 2 := by
    norm_num [tableRiskRatio, EffectMeasure.riskRatio, risk, table622Large]
  refine ⟨?_, hT, ?_, ?_, ?_⟩
  · norm_num [outcomeMisclassified_apply, binaryKernel, table66, tableRiskRatio,
      EffectMeasure.riskRatio, risk]
  · rw [(outcome_riskRatio_perfect_specificity _ _ (by norm_num) (by norm_num [table622Large])
      (by norm_num [table622Large]) (by norm_num [table622Large])).1, hT]
  all_goals norm_num [outcomeMisclassified_apply, binaryKernel, table622Large, tableRiskRatio,
      EffectMeasure.riskRatio, risk]

end Examples

end MisclassificationTables

end BiasAnalysis

end CausalInference
