/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Bias.Misclassification
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Data.Matrix.Block

/-!
# The matrix method for misclassification

The matrix method of Fox, MacLehose and Lash (2021), Chapter 6, section "Matrix Method for
Misclassification Adjustment": the cells of a table are enumerated, `P m t = P(Cell* = m |
Cell = t)` is a classification matrix whose columns sum to one, the expected observed counts are
`F* = P F` (Equation 6.11) and the correction is `F = P⁻¹ F*` (Equation 6.12). This generalizes
`Bias.misclassMatrix_correction` (one binary variable, row convention) to any finite set of
cells.

## Main results

* `sum_mulVec`, `inv_mulVec_mulVec`, `mulVec_inv_mulVec`, `not_identified_of_det_eq_zero`:
  classification keeps the total, the correction recovers the true counts when `P` is
  invertible, and the true counts are not identified when it is singular.
* `binaryMatrix_eq_reindex`, `binaryMatrix_det`: the book's 2 by 2 matrix is the transpose of
  `Bias.misclassMatrix`, with determinant `SE + SP - 1`.
* `jointMatrix`: the 4 by 4 matrix of independent exposure and disease errors, exposure
  classification possibly differential. `jointMatrix_const` (Kronecker product in the
  nondifferential case), `jointMatrix_factor`, `jointMatrix_det`, `jointMatrix_binary_det`
  (determinant `(SE_D + SP_D - 1)² (SE_{E,1} + SP_{E,1} - 1)(SE_{E,0} + SP_{E,0} - 1)`),
  `jointMatrix_mulVec_eq_observedTable` (agreement with `Bias.observedTable`).
* `exposure_inv_mulVec`, `outcome_inv_mulVec`: the matrix method reduces to the closed forms of
  Tables 6.8 and 6.19. `joint_inv_mulVec`: for independent errors the joint correction equals the
  disease correction followed by the exposure correction (sequential correction is valid).
* Polytomous exposure (Tables 6.16, 6.17): `bmi_values`, nondifferential misclassification of a
  three-level exposure biasing one odds ratio away from the null, under the matrix of the stated
  assumptions. The printed Table 6.17 is reproduced by a different matrix (`bmiPrinted_values`),
  which classifies `2.862%` of the truly obese as healthy, contrary to the text.
* Dependent errors (Table 6.27): `table627_nondifferential`, `table627_dependent`,
  `table627_null_association` (association under the null), `table627_mul_inv` (the matrix is
  invertible). `table628_values` checks Table 6.28.
* Worked examples (namespace `Examples`): Table 6.9 and Table 6.20 by the matrix method and the
  4 by 4 example with exposure and disease misclassification, recomputed with the exact
  sensitivities and specificities.

## References

* M. P. Fox, R. F. MacLehose and T. L. Lash, *Applying Quantitative Bias Analysis to
  Epidemiologic Data*, second edition, Springer (2021), Chapter 6.
-/

@[expose] public section

namespace CausalInference

namespace BiasAnalysis

namespace MisclassificationMatrix

open Matrix Bias

open scoped Kronecker

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A classification matrix: `P m t = P(Cell* = m | Cell = t)` is nonnegative and every column
sums to one (section "Matrix Method for Misclassification Adjustment"). -/
def IsClassificationMatrix (P : Matrix ι ι ℝ) : Prop :=
  (∀ m t, 0 ≤ P m t) ∧ ∀ t, ∑ m, P m t = 1

omit [DecidableEq ι] in
/-- Classification keeps the total count: if the columns of `P` sum to one, the expected observed
counts `F* = P F` (Equation 6.11) have the same total as the true counts. -/
theorem sum_mulVec (P : Matrix ι ι ℝ) (hP : IsClassificationMatrix P) (F : ι → ℝ) :
    ∑ m, (P *ᵥ F) m = ∑ t, F t := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [← Finset.sum_mul, hP.2 t, one_mul]

/-- The matrix correction (Equation 6.12): when `P` is invertible, the true counts are recovered
from the expected observed counts as `F = P⁻¹ F*`. -/
theorem inv_mulVec_mulVec (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (F : ι → ℝ) :
    P⁻¹ *ᵥ (P *ᵥ F) = F := by
  rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP), one_mulVec]

/-- The corrected counts `P⁻¹ F*` are mapped back to `F*`: they are the unique true counts
compatible with the observed counts. -/
theorem mulVec_inv_mulVec (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (Fs : ι → ℝ) :
    P *ᵥ (P⁻¹ *ᵥ Fs) = Fs := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), one_mulVec]

/-- To compute `P⁻¹ F*` it suffices to exhibit one `F` with `P F = F*`. -/
theorem inv_mulVec_eq_of_mulVec_eq (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (F Fs : ι → ℝ)
    (h : P *ᵥ F = Fs) : P⁻¹ *ᵥ Fs = F := by
  rw [← h, inv_mulVec_mulVec P hP]

/-- When `P` is singular the true counts are not identified: some nonzero `v` has `P v = 0`, so
`F` and `F + v` give the same expected observed counts. -/
theorem not_identified_of_det_eq_zero (P : Matrix ι ι ℝ) (hP : P.det = 0) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ ∀ F, P *ᵥ (F + v) = P *ᵥ F := by
  obtain ⟨v, hv, hPv⟩ := exists_mulVec_eq_zero_iff.mpr hP
  exact ⟨v, hv, fun F ↦ by rw [mulVec_add, hPv, add_zero]⟩

end General

section Binary

/-- The classification matrix of a binary variable in the book's convention: rows are the
classified value, columns the true value, `P e' e = P(E* = e' | E = e)` (the binary kernel of
`Bias.binaryKernel` read by columns). -/
def binaryMatrix (se sp : ℝ) : Matrix Bool Bool ℝ := fun e' e ↦ binaryKernel se sp e e'

theorem binaryMatrix_isClassificationMatrix (se sp : ℝ) (hse0 : 0 ≤ se) (hse1 : se ≤ 1)
    (hsp0 : 0 ≤ sp) (hsp1 : sp ≤ 1) : IsClassificationMatrix (binaryMatrix se sp) := by
  refine ⟨fun m t ↦ ?_, fun t ↦ binaryKernel_sum se sp t⟩
  cases m <;> cases t <;> simp [binaryMatrix, binaryKernel] <;> linarith

/-- The book's column convention is the transpose of `Bias.misclassMatrix` (row convention, index
`0` negative and `1` positive), reindexed along `Fin 2 ≃ Bool`. -/
theorem binaryMatrix_eq_reindex (se sp : ℝ) :
    binaryMatrix se sp = reindex finTwoEquiv finTwoEquiv (misclassMatrix se sp)ᵀ := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The determinant of the binary classification matrix is `SE + SP - 1`
(`Bias.misclassMatrix_det`). -/
theorem binaryMatrix_det (se sp : ℝ) : (binaryMatrix se sp).det = se + sp - 1 := by
  rw [binaryMatrix_eq_reindex, det_reindex_self, det_transpose, misclassMatrix_det]

end Binary

section Joint

/-! ### Two by two tables with independent exposure and disease errors

Cells of a two by two table are indexed by `(e, d)`: exposure first, disease second. In the
book's enumeration, cell 1 is `(true, true)`, cell 2 `(false, true)`, cell 3 `(true, false)` and
cell 4 `(false, false)`. -/

/-- The 4 by 4 classification matrix of independent exposure and disease errors, with exposure
classification `PE d` allowed to depend on the true disease `d` (differential) and disease
classification `PD` not depending on exposure (nondifferential):
`P((e', d'), (e, d)) = PE d e' e · PD d' d`. -/
def jointMatrix (PE : Bool → Matrix Bool Bool ℝ) (PD : Matrix Bool Bool ℝ) :
    Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun i j ↦ PE j.2 i.1 j.1 * PD i.2 j.2

@[simp]
theorem jointMatrix_apply (PE : Bool → Matrix Bool Bool ℝ) (PD : Matrix Bool Bool ℝ)
    (e' d' e d : Bool) : jointMatrix PE PD (e', d') (e, d) = PE d e' e * PD d' d := rfl

/-- With exposure classification not depending on disease, the joint matrix is the Kronecker
product of the two classification matrices (Equation 6.11 with independent nondifferential
errors). -/
theorem jointMatrix_const (PE PD : Matrix Bool Bool ℝ) :
    jointMatrix (fun _ ↦ PE) PD = PE ⊗ₖ PD := by
  ext i j
  rfl

/-- The disease-only part of the joint matrix is `1 ⊗ PD`. -/
theorem jointMatrix_one_left (PD : Matrix Bool Bool ℝ) :
    jointMatrix (fun _ ↦ 1) PD = 1 ⊗ₖ PD :=
  jointMatrix_const 1 PD

/-- The exposure-only part of the joint matrix is block diagonal in the true disease. -/
theorem jointMatrix_one_right (PE : Bool → Matrix Bool Bool ℝ) :
    jointMatrix PE 1 = blockDiagonal PE := by
  ext ⟨e', d'⟩ ⟨e, d⟩
  rw [jointMatrix_apply, blockDiagonal_apply]
  by_cases h : d' = d
  · subst h
    simp
  · simp [h]

/-- Independent errors factor the joint matrix: first exposure is classified within each true
disease level, then disease is classified. -/
theorem jointMatrix_factor (PE : Bool → Matrix Bool Bool ℝ) (PD : Matrix Bool Bool ℝ) :
    jointMatrix PE PD = jointMatrix (fun _ ↦ 1) PD * jointMatrix PE 1 := by
  ext ⟨e', d'⟩ ⟨e, d⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, jointMatrix_apply]
  cases e <;> cases e' <;> cases d <;> cases d' <;> simp [mul_comm]

/-- The determinant of the joint matrix: `det PD ^ 2 · det (PE true) · det (PE false)`. -/
theorem jointMatrix_det (PE : Bool → Matrix Bool Bool ℝ) (PD : Matrix Bool Bool ℝ) :
    (jointMatrix PE PD).det = PD.det ^ 2 * ((PE true).det * (PE false).det) := by
  rw [jointMatrix_factor, det_mul, jointMatrix_one_left, jointMatrix_one_right, det_kronecker,
    det_blockDiagonal, det_one, one_pow, one_mul, Fintype.prod_bool, Fintype.card_bool]

/-- For binary exposure and disease classification the determinant is
`(SE_D + SP_D - 1)² (SE_{E,1} + SP_{E,1} - 1)(SE_{E,0} + SP_{E,0} - 1)`; in the nondifferential
case it is `(SE_D + SP_D - 1)² (SE_E + SP_E - 1)²`. The matrix is invertible exactly when every
`SE + SP ≠ 1`. -/
theorem jointMatrix_binary_det (seE spE : Bool → ℝ) (seD spD : ℝ) :
    (jointMatrix (fun d ↦ binaryMatrix (seE d) (spE d)) (binaryMatrix seD spD)).det =
      (seD + spD - 1) ^ 2 * ((seE true + spE true - 1) * (seE false + spE false - 1)) := by
  rw [jointMatrix_det, binaryMatrix_det, binaryMatrix_det, binaryMatrix_det]

/-- The joint matrix of product kernels is the matrix form of `Bias.observedTable` with the
product kernel of independent errors. -/
theorem jointMatrix_mulVec_eq_observedTable (seE spE : Bool → ℝ) (seD spD : ℝ)
    (F : Bool × Bool → ℝ) (e' d' : Bool) :
    (jointMatrix (fun d ↦ binaryMatrix (seE d) (spE d)) (binaryMatrix seD spD) *ᵥ F) (e', d') =
      observedTable (fun e d ↦ F (e, d))
        (fun e d e' d' ↦ binaryKernel (seE d) (spE d) e e' * binaryKernel seD spD d d') e' d' := by
  simp only [mulVec, dotProduct, jointMatrix, binaryMatrix, observedTable,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
  ring

/-- The exposure correction of Table 6.8 on a vector of cells: in each disease row `d`,
`A = (a - D_d (1 - SP_d)) / (SE_d + SP_d - 1)` and the unexposed count is `D_d - A`. -/
noncomputable def exposureCorrectVec (se sp : Bool → ℝ) (G : Bool × Bool → ℝ) :
    Bool × Bool → ℝ :=
  fun i ↦
    if i.1 then (G (true, i.2) - (G (true, i.2) + G (false, i.2)) * (1 - sp i.2)) /
        (se i.2 + sp i.2 - 1)
    else G (true, i.2) + G (false, i.2) -
      (G (true, i.2) - (G (true, i.2) + G (false, i.2)) * (1 - sp i.2)) / (se i.2 + sp i.2 - 1)

/-- The disease correction of Table 6.19 on a vector of cells: in each exposure column `e`,
`A = (a - E_e (1 - SP)) / (SE + SP - 1)` and the noncase count is `E_e - A`. -/
noncomputable def outcomeCorrectVec (se sp : ℝ) (G : Bool × Bool → ℝ) : Bool × Bool → ℝ :=
  fun i ↦
    if i.2 then (G (i.1, true) - (G (i.1, true) + G (i.1, false)) * (1 - sp)) / (se + sp - 1)
    else G (i.1, true) + G (i.1, false) -
      (G (i.1, true) - (G (i.1, true) + G (i.1, false)) * (1 - sp)) / (se + sp - 1)

/-- The matrix method reduces to Table 6.8 for exposure misclassification: the inverse of the
block diagonal exposure matrix applied to the observed cells is the correction of Table 6.8. -/
theorem exposure_inv_mulVec (se sp : Bool → ℝ) (h : ∀ d, se d + sp d ≠ 1)
    (G : Bool × Bool → ℝ) :
    (jointMatrix (fun d ↦ binaryMatrix (se d) (sp d)) 1)⁻¹ *ᵥ G = exposureCorrectVec se sp G := by
  apply inv_mulVec_eq_of_mulVec_eq
  · rw [jointMatrix_det, det_one, one_pow, one_mul, binaryMatrix_det, binaryMatrix_det]
    exact mul_ne_zero (sub_ne_zero.mpr (h true)) (sub_ne_zero.mpr (h false))
  · funext ⟨e', d'⟩
    have hk : se d' + sp d' - 1 ≠ 0 := sub_ne_zero.mpr (h d')
    simp only [mulVec, dotProduct, jointMatrix, binaryMatrix, exposureCorrectVec,
      Fintype.sum_prod_type, Fintype.sum_bool, binaryKernel]
    cases e' <;> cases d' <;> simp <;> field_simp <;> ring

/-- The matrix method reduces to Table 6.19 for disease misclassification. -/
theorem outcome_inv_mulVec (se sp : ℝ) (h : se + sp ≠ 1) (G : Bool × Bool → ℝ) :
    (jointMatrix (fun _ ↦ 1) (binaryMatrix se sp))⁻¹ *ᵥ G = outcomeCorrectVec se sp G := by
  have hk : se + sp - 1 ≠ 0 := sub_ne_zero.mpr h
  apply inv_mulVec_eq_of_mulVec_eq
  · rw [jointMatrix_det, det_one, binaryMatrix_det, one_mul, mul_one]
    exact pow_ne_zero 2 hk
  · funext ⟨e', d'⟩
    simp only [mulVec, dotProduct, jointMatrix, binaryMatrix, outcomeCorrectVec,
      Fintype.sum_prod_type, Fintype.sum_bool, binaryKernel]
    cases e' <;> cases d' <;> simp <;> field_simp <;> ring

/-- Sequential correction is valid for independent errors (end of the section "Matrix Method for
Misclassification Adjustment"): the joint matrix correction equals the disease correction of
Table 6.19 followed by the exposure correction of Table 6.8 within each true disease level. -/
theorem joint_inv_mulVec (seE spE : Bool → ℝ) (seD spD : ℝ) (hE : ∀ d, seE d + spE d ≠ 1)
    (hD : seD + spD ≠ 1) (Fs : Bool × Bool → ℝ) :
    (jointMatrix (fun d ↦ binaryMatrix (seE d) (spE d)) (binaryMatrix seD spD))⁻¹ *ᵥ Fs =
      exposureCorrectVec seE spE (outcomeCorrectVec seD spD Fs) := by
  rw [jointMatrix_factor, Matrix.mul_inv_rev, ← mulVec_mulVec, outcome_inv_mulVec seD spD hD,
    exposure_inv_mulVec seE spE hE]

end Joint

section Polytomous

/-! ### Polytomous exposure (Tables 6.16 and 6.17) -/

/-- The classification matrix of body mass index (healthy `0`, overweight `1`, obese `2`) in the
example of the section "Misclassification of Polytomous Variables": no overreporting, `9%` of
the truly overweight classified healthy, and `68.2%` of the truly obese classified obese (the
proportion the book's arithmetic uses: true obese = observed obese / 0.682), the remaining
`31.8%` classified overweight. Rows are classified values, columns true values. -/
noncomputable def bmiMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0.09, 0; 0, 0.91, 0.318; 0, 0, 0.682]

theorem bmiMatrix_isClassificationMatrix : IsClassificationMatrix bmiMatrix := by
  refine ⟨fun m t ↦ ?_, fun t ↦ ?_⟩
  · fin_cases m <;> fin_cases t <;> norm_num [bmiMatrix]
  · fin_cases t <;> norm_num [bmiMatrix, Fin.sum_univ_three]

theorem bmiMatrix_det : bmiMatrix.det = 0.62062 := by
  rw [det_fin_three]
  norm_num [bmiMatrix]

/-- The back substitution that inverts `bmiMatrix`. -/
noncomputable def bmiCorrect (fs : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![fs 0 - 0.09 * ((fs 1 - 0.318 * (fs 2 / 0.682)) / 0.91),
    (fs 1 - 0.318 * (fs 2 / 0.682)) / 0.91, fs 2 / 0.682]

theorem bmiMatrix_inv_mulVec (fs : Fin 3 → ℝ) : bmiMatrix⁻¹ *ᵥ fs = bmiCorrect fs := by
  apply inv_mulVec_eq_of_mulVec_eq _ (by rw [bmiMatrix_det]; norm_num)
  funext i
  fin_cases i <;>
    simp [bmiMatrix, bmiCorrect, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The observed diabetics of Table 6.16 by body mass index category. -/
def bmiDiabetics : Fin 3 → ℝ := ![3053, 5127, 6491]

/-- The observed nondiabetics of Table 6.16. -/
def bmiNondiabetics : Fin 3 → ℝ := ![81416, 65104, 33814]

/-- The odds ratio of category `k` against the healthy category `0`, from the diabetic counts
`D` and nondiabetic counts `N`. -/
noncomputable def categoryOddsRatio (D N : Fin 3 → ℝ) (k : Fin 3) : ℝ := (D k / N k) / (D 0 / N 0)

/-- Polytomous misclassification can bias away from the null although it is nondifferential
(the same matrix for diabetics and nondiabetics). Correcting Table 6.16 with `bmiMatrix`, the
matrix of the stated assumptions, gives the obese cells `9517.6` and `49580.6` printed in Table
6.17, and odds ratios `≈ 1.145` (overweight) and `≈ 5.164` (obese). The observed overweight odds
ratio `≈ 2.100` is further from the null than the corrected one, while the obese odds ratio
`≈ 5.119` is closer. The printed odds ratios 1.4 and 5.7 come from a different matrix
(`bmiMatrixPrinted`). -/
theorem bmi_values :
    9517.59 < (bmiMatrix⁻¹ *ᵥ bmiDiabetics) 2 ∧ (bmiMatrix⁻¹ *ᵥ bmiDiabetics) 2 < 9517.60 ∧
      49580.64 < (bmiMatrix⁻¹ *ᵥ bmiNondiabetics) 2 ∧
      (bmiMatrix⁻¹ *ᵥ bmiNondiabetics) 2 < 49580.65 ∧
      1.145 < categoryOddsRatio (bmiMatrix⁻¹ *ᵥ bmiDiabetics) (bmiMatrix⁻¹ *ᵥ bmiNondiabetics) 1 ∧
      categoryOddsRatio (bmiMatrix⁻¹ *ᵥ bmiDiabetics) (bmiMatrix⁻¹ *ᵥ bmiNondiabetics) 1 < 1.146 ∧
      5.163 < categoryOddsRatio (bmiMatrix⁻¹ *ᵥ bmiDiabetics) (bmiMatrix⁻¹ *ᵥ bmiNondiabetics) 2 ∧
      categoryOddsRatio (bmiMatrix⁻¹ *ᵥ bmiDiabetics) (bmiMatrix⁻¹ *ᵥ bmiNondiabetics) 2 < 5.164 ∧
      2.100 < categoryOddsRatio bmiDiabetics bmiNondiabetics 1 ∧
      categoryOddsRatio bmiDiabetics bmiNondiabetics 1 < 2.101 ∧
      5.119 < categoryOddsRatio bmiDiabetics bmiNondiabetics 2 ∧
      categoryOddsRatio bmiDiabetics bmiNondiabetics 2 < 5.120 := by
  simp only [bmiMatrix_inv_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [bmiCorrect, categoryOddsRatio, bmiDiabetics, bmiNondiabetics]

/-- The classification matrix behind the printed Table 6.17. Its healthy weight correction moves
`0.09/0.91` of the observed, not the true, overweight count; inverting that arithmetic gives
this matrix, under which `0.09 · 0.318 = 2.862%` of the truly obese are classified healthy and
`0.91 · 0.318 = 28.938%` overweight. It is a valid classification matrix but contradicts the
text's assumption that no obese person is classified healthy. -/
noncomputable def bmiMatrixPrinted : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0.09, 0.09 * 0.318; 0, 0.91, 0.91 * 0.318; 0, 0, 0.682]

theorem bmiMatrixPrinted_isClassificationMatrix : IsClassificationMatrix bmiMatrixPrinted := by
  refine ⟨fun m t ↦ ?_, fun t ↦ ?_⟩
  · fin_cases m <;> fin_cases t <;> norm_num [bmiMatrixPrinted]
  · fin_cases t <;> norm_num [bmiMatrixPrinted, Fin.sum_univ_three]

/-- The printed arithmetic of Table 6.17 as a linear map. -/
noncomputable def bmiCorrectPrinted (fs : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![fs 0 - 0.09 / 0.91 * fs 1, fs 1 / 0.91 - 0.318 / 0.682 * fs 2, fs 2 / 0.682]

theorem bmiMatrixPrinted_inv_mulVec (fs : Fin 3 → ℝ) :
    bmiMatrixPrinted⁻¹ *ᵥ fs = bmiCorrectPrinted fs := by
  apply inv_mulVec_eq_of_mulVec_eq _ (by rw [det_fin_three]; norm_num [bmiMatrixPrinted])
  funext i
  fin_cases i <;>
    simp [bmiMatrixPrinted, bmiCorrectPrinted, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The printed Table 6.17 is reproduced by `bmiMatrixPrinted`: cells `2545.9, 2607.5` (diabetics)
and `74977.1` (nondiabetics, healthy), odds ratios `≈ 1.377` (printed 1.4) and `≈ 5.653`
(printed 5.7). -/
theorem bmiPrinted_values :
    2545.93 < (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 0 ∧
      (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 0 < 2545.94 ∧
      2607.47 < (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 1 ∧
      (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 1 < 2607.48 ∧
      74977.14 < (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 0 ∧
      (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 0 < 74977.15 ∧
      1.376 < categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 1 ∧
      categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 1 < 1.377 ∧
      5.653 < categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 2 ∧
      categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 2 < 5.654 := by
  simp only [bmiMatrixPrinted_inv_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [bmiCorrectPrinted, categoryOddsRatio, bmiDiabetics, bmiNondiabetics]

end Polytomous

section Dependent

/-! ### Dependent misclassification (Table 6.27) -/

/-- The joint classification matrix of Table 6.27: a cell is classified correctly with
probability `0.95`, misclassified on exactly one axis with probability `0.02` each, and on both
axes with probability `0.01`. Rows are classified cells `(e', d')`, columns true cells `(e, d)`. -/
noncomputable def table627 : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun i j ↦ if i = j then 0.95 else if i.1 ≠ j.1 ∧ i.2 ≠ j.2 then 0.01 else 0.02

theorem table627_isClassificationMatrix : IsClassificationMatrix table627 := by
  refine ⟨fun m t ↦ ?_, fun t ↦ ?_⟩
  · unfold table627
    split_ifs <;> norm_num
  · obtain ⟨e, d⟩ := t
    rw [Fintype.sum_prod_type]
    cases e <;> cases d <;> norm_num [table627, Fintype.sum_bool]

/-- Table 6.27 is nondifferential: in every true cell the probability that exposure is
classified correctly is `0.97`, and so is the probability that disease is classified correctly.
Hence the exposure sensitivity and specificity are `0.97` in both disease levels and the disease
sensitivity and specificity are `0.97` in both exposure levels. -/
theorem table627_nondifferential (e d : Bool) :
    ∑ d', table627 (e, d') (e, d) = 0.97 ∧ ∑ e', table627 (e', d) (e, d) = 0.97 := by
  cases e <;> cases d <;> norm_num [table627, Fintype.sum_bool]

/-- Table 6.27 is dependent: the probability of misclassification on both axes is `0.01`,
whereas independent errors with the marginal error rates `0.03` would give `0.03 · 0.03 =
0.0009`. -/
theorem table627_dependent (e d : Bool) :
    table627 (!e, !d) (e, d) = 0.01 ∧ table627 (!e, !d) (e, d) ≠ 0.03 * 0.03 := by
  cases e <;> cases d <;> norm_num [table627]

/-- A true table satisfying the null: exposure prevalence `0.2` and disease risk `0.1`,
independent. -/
noncomputable def nullTable (i : Bool × Bool) : ℝ :=
  (if i.1 then 0.2 else 0.8) * (if i.2 then 0.1 else 0.9)

/-- Dependent nondifferential errors create an association under the null: the true table is
independent while the expected observed table under Table 6.27 is not; its risk ratio is
`≈ 1.216`. -/
theorem table627_null_association :
    TableIndep (fun e d ↦ nullTable (e, d)) ∧
      ¬ TableIndep (fun e d ↦ (table627 *ᵥ nullTable) (e, d)) ∧
      1.216 < ((table627 *ᵥ nullTable) (true, true) /
          ((table627 *ᵥ nullTable) (true, true) + (table627 *ᵥ nullTable) (true, false))) /
        ((table627 *ᵥ nullTable) (false, true) /
          ((table627 *ᵥ nullTable) (false, true) + (table627 *ᵥ nullTable) (false, false))) ∧
      ((table627 *ᵥ nullTable) (true, true) /
          ((table627 *ᵥ nullTable) (true, true) + (table627 *ᵥ nullTable) (true, false))) /
        ((table627 *ᵥ nullTable) (false, true) /
          ((table627 *ᵥ nullTable) (false, true) + (table627 *ᵥ nullTable) (false, false))) <
        1.217 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tableIndep_bool_iff]
    norm_num [nullTable]
  all_goals
    try rw [tableIndep_bool_iff]
    norm_num [mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool, table627, nullTable]

/-- The inverse of Table 6.27, of the same form (coefficients `a` on the diagonal, `b` for one
axis, `c` for both axes). -/
noncomputable def table627Inv : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun i j ↦ if i = j then 1139 / 1081 else if i.1 ≠ j.1 ∧ i.2 ≠ j.2 then -11 / 1081 else -1 / 46

/-- The matrix of Table 6.27 is invertible, so the matrix method corrects for these dependent
errors although sequential corrections of the two variables do not apply. -/
theorem table627_mul_inv : table627 * table627Inv = 1 ∧ table627.det ≠ 0 := by
  have h : table627 * table627Inv = 1 := by
    ext ⟨e', d'⟩ ⟨e, d⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    cases e <;> cases d <;> cases e' <;> cases d' <;>
      norm_num [table627, table627Inv, Fintype.sum_bool, one_apply]
  exact ⟨h, det_ne_zero_of_right_inverse h⟩

/-- Table 6.28 (neighborhood problems and functional decline): the observed risk ratio is
`(20/172)/(28/667) ≈ 2.77`; the text describes it as a 2.2-fold association. The hypothetical
table after 1.6% dependent errors has risk ratio `≈ 1.0`. -/
theorem table628_values :
    2.769 < ((20 : ℝ) / 172) / (28 / 667) ∧ ((20 : ℝ) / 172) / (28 / 667) < 2.770 ∧
      0.998 < ((7.0 : ℝ) / 163.9) / (28.9 / 675.6) ∧
      ((7.0 : ℝ) / 163.9) / (28.9 / 675.6) < 0.999 := by
  norm_num

end Dependent

namespace Examples

/-! ### Worked examples of the matrix method -/

/-- The risk ratio `(F₁/(F₁ + F₃)) / (F₂/(F₂ + F₄))` of a vector of cells. -/
noncomputable def cellRiskRatio (F : Bool × Bool → ℝ) : ℝ :=
  (F (true, true) / (F (true, true) + F (true, false))) /
    (F (false, true) / (F (false, true) + F (false, false)))

/-- The observed cells of Table 6.9: `a = 215`, `b = 1449`, `c = 668`, `d = 4296`. -/
def cells69 (i : Bool × Bool) : ℝ :=
  if i.2 then (if i.1 then 215 else 1449) else (if i.1 then 668 else 4296)

/-- The matrix method reproduces Table 6.9: with the exposure matrix of sensitivity `128/164` and
specificity `465/470` in both disease levels, `P⁻¹ F*` is `(256.3, 1407.7, 799.1, 4164.9)`. The
text says that inverting `P` gives `A = (a - B(1 - SP))/(SE - (1 - SP))`; by
`exposure_inv_mulVec` the correct expression has the row total `D₁ = a + b` in place of `B`. -/
theorem matrix_table69 :
    256.28 < ((jointMatrix (fun _ ↦ binaryMatrix (128 / 164) (465 / 470)) 1)⁻¹ *ᵥ cells69)
        (true, true) ∧
      ((jointMatrix (fun _ ↦ binaryMatrix (128 / 164) (465 / 470)) 1)⁻¹ *ᵥ cells69)
        (true, true) < 256.29 ∧
      799.10 < ((jointMatrix (fun _ ↦ binaryMatrix (128 / 164) (465 / 470)) 1)⁻¹ *ᵥ cells69)
        (true, false) ∧
      ((jointMatrix (fun _ ↦ binaryMatrix (128 / 164) (465 / 470)) 1)⁻¹ *ᵥ cells69)
        (true, false) < 799.11 := by
  rw [exposure_inv_mulVec _ _ (fun _ ↦ by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [exposureCorrectVec, cells69]

/-- The observed cells of Table 6.20 (sex and death from acute myocardial infarction): AMI
deaths `4558` men and `3428` women, other deaths `46305` and `46085`. -/
def cells620 (i : Bool × Bool) : ℝ :=
  if i.2 then (if i.1 then 4558 else 3428) else (if i.1 then 46305 else 46085)

/-- The matrix method reproduces Table 6.20: with disease sensitivity `1750/3300` and specificity
`12075/12259`, `P⁻¹ F*` is `(7363.9, 5210.3, 43499.1, 44302.7)` and the risk ratio is
`≈ 1.376`. -/
theorem matrix_table620 :
    7363.91 < ((jointMatrix (fun _ ↦ 1) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (true, true) ∧
      ((jointMatrix (fun _ ↦ 1) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (true, true) < 7363.92 ∧
      5210.31 < ((jointMatrix (fun _ ↦ 1) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (false, true) ∧
      ((jointMatrix (fun _ ↦ 1) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (false, true) < 5210.32 ∧
      1.3758 < cellRiskRatio ((jointMatrix (fun _ ↦ 1)
        (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ cells620) ∧
      cellRiskRatio ((jointMatrix (fun _ ↦ 1)
        (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ cells620) < 1.3759 := by
  rw [outcome_inv_mulVec _ _ (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [outcomeCorrectVec, cellRiskRatio, cells620]

/-- The 4 by 4 example of the section "Matrix Method for Misclassification Adjustment": disease
classification as in Table 6.20 and independent differential exposure classification with
`SE = 0.99`, `SP = 0.97` among cases and `SE = 0.97`, `SP = 0.96` among noncases. With the exact
sensitivity `1750/3300` and specificity `12075/12259`, `P⁻¹ F*` is
`(7277.8, 5296.4, 42996.8, 44805.0)` and the risk ratio is `≈ 1.369`, slightly attenuated from
the `≈ 1.376` obtained by correcting the outcome only (`matrix_table620`); the text says
"exposure" where the comparison is with the outcome-only correction. The determinant is nonzero
by `jointMatrix_binary_det`. -/
theorem matrix_joint_example :
    7277.79 < ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (true, true) ∧
      ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (true, true) < 7277.80 ∧
      5296.42 < ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (false, true) ∧
      ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (false, true) < 5296.43 ∧
      42996.79 < ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (true, false) ∧
      ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (true, false) < 42996.80 ∧
      44804.98 < ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (false, false) ∧
      ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) (false, false) < 44804.99 ∧
      1.3693 < cellRiskRatio ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) ∧
      cellRiskRatio ((jointMatrix (fun d ↦ binaryMatrix (if d then 0.99 else 0.97)
        (if d then 0.97 else 0.96)) (binaryMatrix (1750 / 3300) (12075 / 12259)))⁻¹ *ᵥ
        cells620) < 1.3694 := by
  rw [joint_inv_mulVec _ _ _ _ (fun d ↦ by cases d <;> norm_num) (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exposureCorrectVec, outcomeCorrectVec, cellRiskRatio, cells620]

end Examples

end MisclassificationMatrix

end BiasAnalysis

end CausalInference
