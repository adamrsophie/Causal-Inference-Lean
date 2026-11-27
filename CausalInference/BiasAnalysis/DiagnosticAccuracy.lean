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
positive test in the diseased and in the disease free. It is a ratio only when `sp < 1`, which
every theorem using it assumes. -/
noncomputable def lrPos (se sp : ℝ) : ℝ := se / (1 - sp)

/-- The negative likelihood ratio `LR- = (1 - se) / sp`: the ratio of the probabilities of a
negative test in the diseased and in the disease free. It is a ratio only when `0 < sp`, which
every theorem using it assumes. -/
noncomputable def lrNeg (se sp : ℝ) : ℝ := (1 - se) / sp

/-- The diagnostic odds ratio `DOR = LR+ / LR-`. It is a ratio only when `sp < 1`, `0 < sp` and
`se < 1`, which every theorem using it assumes. -/
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
