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

* `sum_mulVec`, `inv_mulVec_mulVec`, `mulVec_inv_mulVec`: classification keeps the total and the
  correction recovers the true counts when `P` is invertible. `exists_nonneg_preimage_iff`: a
  nonnegative true table compatible with the observed counts exists exactly when `P⁻¹ F*` is
  componentwise nonnegative; `binary_inverse_negative` is an invertible case where it is not.
* `not_identified_of_det_eq_zero`, `not_identified_nonneg`: when `P` is singular, the map is not
  injective, and every positive true table has a second nonnegative table with the same total
  and the same expected observed counts. `singular_unique_nonneg_preimage`: singularity does not
  prevent a particular observed table from determining the nonnegative true table.
* `IsClassificationMatrix.mul`, `jointMatrix_isClassificationMatrix`: closure properties.
* `binaryMatrix_eq_reindex`, `binaryMatrix_det`, `binaryMatrix_det_eq_zero`: the book's 2 by 2
  matrix is the transpose of `Bias.misclassMatrix`, with determinant `SE + SP - 1`, singular
  when `SE + SP = 1`.
* `jointMatrix`: the 4 by 4 matrix of independent exposure and disease errors, exposure
  classification possibly differential. `jointMatrix_const` (Kronecker product in the
  nondifferential case), `jointMatrix_factor`, `jointMatrix_det`, `jointMatrix_binary_det`
  (determinant `(SE_D + SP_D - 1)² (SE_{E,1} + SP_{E,1} - 1)(SE_{E,0} + SP_{E,0} - 1)`),
  `jointMatrix_mulVec_eq_observedTable` (agreement with `Bias.observedTable`).
* `exposure_inv_mulVec`, `outcome_inv_mulVec`: the matrix method reduces to the closed forms of
  Tables 6.8 and 6.19. `joint_inv_mulVec`: for independent errors with disease classification
  not depending on the true exposure, the joint correction equals the disease correction
  followed by the exposure correction; `kronecker_inv_mulVec_totalized` is the general
  Kronecker form. `xorJoint_countermodel`: without the second condition, independence of the
  errors given the true cell does not make the joint matrix invertible.
* Polytomous exposure (Tables 6.16, 6.17): the assumptions printed on page 169 send `68.2%` of
  the truly obese to overweight; `bmiStated_infeasible` shows that no nonnegative true table is
  compatible with Table 6.16 under them. `bmiRepaired_values`, under the repaired matrix
  `bmiMatrixRepaired` (`68.2%` of the obese kept obese), shows nondifferential misclassification
  of a three-level exposure biasing one odds ratio away from the null. The printed Table 6.17 is
  reproduced, except one cell that differs in the last printed digit, by a third matrix
  (`bmiPrinted_values`), which classifies `2.862%` of the truly obese as healthy.
* Dependent errors (Table 6.27): `table627_nondifferential`, `table627_dependent`,
  `table627_null_association` (association under the null), `table627_mul_inv` (the matrix is
  invertible). `table628_values` is arithmetic on the printed Table 6.28, and `table628_totals`
  shows that its two tables (totals 839 and 839.5) are not related by any classification
  matrix.
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

/-- The corrected vector `P⁻¹ F*` is mapped back to `F*`: it is the unique real vector `F` with
`P F = F*`. It need not be a vector of counts: some entries can be negative
(`binary_inverse_negative`), and then no table of nonnegative counts is compatible with `F*`
(`exists_nonneg_preimage_iff`). -/
theorem mulVec_inv_mulVec (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (Fs : ι → ℝ) :
    P *ᵥ (P⁻¹ *ᵥ Fs) = Fs := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), one_mulVec]

/-- To compute `P⁻¹ F*` it suffices to exhibit one `F` with `P F = F*`. -/
theorem inv_mulVec_eq_of_mulVec_eq (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (F Fs : ι → ℝ)
    (h : P *ᵥ F = Fs) : P⁻¹ *ᵥ Fs = F := by
  rw [← h, inv_mulVec_mulVec P hP]

/-- Feasibility of the correction: when `P` is invertible, a vector of nonnegative true counts
compatible with the observed counts `F*` exists exactly when every entry of `P⁻¹ F*` is
nonnegative. -/
theorem exists_nonneg_preimage_iff (P : Matrix ι ι ℝ) (hP : P.det ≠ 0) (Fs : ι → ℝ) :
    (∃ F : ι → ℝ, 0 ≤ F ∧ P *ᵥ F = Fs) ↔ 0 ≤ P⁻¹ *ᵥ Fs := by
  constructor
  · rintro ⟨F, hF, rfl⟩
    rwa [inv_mulVec_mulVec P hP]
  · exact fun h ↦ ⟨_, h, mulVec_inv_mulVec P hP Fs⟩

/-- When `P` is singular the map `F ↦ P F` is not injective on real vectors: some nonzero `v` has
`P v = 0`, so `F` and `F + v` give the same expected observed counts. This is a statement about
real vectors; `not_identified_nonneg` gives two tables of nonnegative counts, and
`singular_unique_nonneg_preimage` shows that a particular observed table can still determine the
nonnegative true table uniquely. -/
theorem not_identified_of_det_eq_zero (P : Matrix ι ι ℝ) (hP : P.det = 0) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ ∀ F, P *ᵥ (F + v) = P *ᵥ F := by
  obtain ⟨v, hv, hPv⟩ := exists_mulVec_eq_zero_iff.mpr hP
  exact ⟨v, hv, fun F ↦ by rw [mulVec_add, hPv, add_zero]⟩

/-- Nonidentification for counts: when the classification matrix `P` is singular, every true
table `F` with all cells positive has a second table `F'` of nonnegative counts, with the same
total, that gives the same expected observed counts. -/
theorem not_identified_nonneg (P : Matrix ι ι ℝ) (hP : IsClassificationMatrix P)
    (hdet : P.det = 0) (F : ι → ℝ) (hF : ∀ t, 0 < F t) :
    ∃ F' : ι → ℝ, 0 ≤ F' ∧ F' ≠ F ∧ P *ᵥ F' = P *ᵥ F ∧ ∑ t, F' t = ∑ t, F t := by
  obtain ⟨v, hv, hPv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨t₀, ht₀⟩ := Function.ne_iff.mp hv
  set S := ∑ s, |v s| / F s with hS
  have hterm : ∀ s, 0 ≤ |v s| / F s := fun s ↦ div_nonneg (abs_nonneg _) (hF s).le
  have hle : ∀ t, |v t| / F t ≤ S := fun t ↦
    Finset.single_le_sum (fun s _ ↦ hterm s) (Finset.mem_univ t)
  have hSpos : 0 < S :=
    lt_of_lt_of_le (div_pos (abs_pos.mpr ht₀) (hF t₀)) (hle t₀)
  have hPF' : P *ᵥ (F + S⁻¹ • v) = P *ᵥ F := by
    rw [mulVec_add, mulVec_smul, hPv, smul_zero, add_zero]
  refine ⟨F + S⁻¹ • v, fun t ↦ ?_, fun h ↦ ?_, hPF', ?_⟩
  · have h1 : |v t| ≤ S * F t := by
      have := hle t
      rwa [div_le_iff₀ (hF t)] at this
    have h2 : |S⁻¹ * v t| ≤ F t := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hSpos), inv_mul_le_iff₀ hSpos]
      exact h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linarith [neg_abs_le (S⁻¹ * v t)]
  · have h0 : S⁻¹ • v = 0 := by
      have := congrArg (· - F) h
      simpa using this
    exact hv ((smul_eq_zero.mp h0).resolve_left (inv_ne_zero hSpos.ne'))
  · rw [← sum_mulVec P hP, hPF', sum_mulVec P hP]

/-- What singularity does not imply: the classification matrix with columns `e₀, e₁, e₁`
(categories `1` and `2` are both classified `1`) is singular, yet the observed table `e₀` has
exactly one nonnegative true table, `e₀` itself. Singularity rules out identification for every
positive true table (`not_identified_nonneg`), not for every observed table. -/
theorem singular_unique_nonneg_preimage :
    IsClassificationMatrix !![(1 : ℝ), 0, 0; 0, 1, 1; 0, 0, 0] ∧
      (!![(1 : ℝ), 0, 0; 0, 1, 1; 0, 0, 0]).det = 0 ∧
      ∀ F : Fin 3 → ℝ, 0 ≤ F → !![(1 : ℝ), 0, 0; 0, 1, 1; 0, 0, 0] *ᵥ F = ![1, 0, 0] →
        F = ![1, 0, 0] := by
  refine ⟨⟨fun m t ↦ ?_, fun t ↦ ?_⟩, ?_, fun F hF h ↦ ?_⟩
  · fin_cases m <;> fin_cases t <;> norm_num
  · fin_cases t <;> norm_num [Fin.sum_univ_three]
  · rw [det_fin_three]
    norm_num
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    have g1 : 0 ≤ F 1 := hF 1
    have g2 : 0 ≤ F 2 := hF 2
    simp [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    funext i
    fin_cases i <;> simp <;> linarith

omit [DecidableEq ι] in
/-- Classification in two stages is classification: the product of two classification matrices
is a classification matrix. -/
theorem IsClassificationMatrix.mul {P Q : Matrix ι ι ℝ} (hP : IsClassificationMatrix P)
    (hQ : IsClassificationMatrix Q) : IsClassificationMatrix (P * Q) := by
  refine ⟨fun m t ↦ Finset.sum_nonneg fun k _ ↦ mul_nonneg (hP.1 m k) (hQ.1 k t), fun t ↦ ?_⟩
  have h : ∑ m, (P * Q) m t = ∑ k, (∑ m, P m k) * Q k t := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [h]
  simp only [hP.2, one_mul, hQ.2 t]

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

/-- A concrete singular classification matrix: when `SP = 1 - SE` the classified value is
independent of the true value and the determinant vanishes. -/
theorem binaryMatrix_det_eq_zero (se : ℝ) : (binaryMatrix se (1 - se)).det = 0 := by
  rw [binaryMatrix_det]
  ring

/-- An invertible classification matrix whose inverse produces a negative cell: with
`SE = SP = 0.9`, the observed proportions `(1/20, 19/20)` (classified positive, negative) are
mapped by the inverse to `(-1/16, 17/16)`, so no nonnegative true distribution is compatible with
them. -/
theorem binary_inverse_negative :
    (binaryMatrix 0.9 0.9)⁻¹ *ᵥ (fun e ↦ if e then 1 / 20 else 19 / 20) =
        (fun e ↦ if e then -1 / 16 else 17 / 16) ∧
      ¬ ∃ F : Bool → ℝ, 0 ≤ F ∧
        binaryMatrix 0.9 0.9 *ᵥ F = (fun e ↦ if e then 1 / 20 else 19 / 20) := by
  have hdet : (binaryMatrix 0.9 0.9).det ≠ 0 := by
    rw [binaryMatrix_det]
    norm_num
  have hinv : (binaryMatrix 0.9 0.9)⁻¹ *ᵥ (fun e ↦ if e then (1 : ℝ) / 20 else 19 / 20) =
      (fun e ↦ if e then -1 / 16 else 17 / 16) := by
    apply inv_mulVec_eq_of_mulVec_eq _ hdet
    funext e
    cases e <;> norm_num [mulVec, dotProduct, binaryMatrix, binaryKernel, Fintype.sum_bool]
  refine ⟨hinv, fun h ↦ ?_⟩
  have h1 := (exists_nonneg_preimage_iff _ hdet _).mp h true
  rw [hinv] at h1
  norm_num at h1

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

/-- Sequential correction (end of the section "Matrix Method for Misclassification Adjustment"):
the joint matrix correction equals the disease correction of Table 6.19 followed by the exposure
correction of Table 6.8 within each true disease level. The hypotheses are more than
independence of the errors given the true cell: the matrix `jointMatrix PE PD` also requires the
disease classification `PD` not to depend on the true exposure (exposure classification may
depend on the true disease). The order of inversion is fixed by the factorization
`jointMatrix_factor`: the disease correction is applied first. Without the extra condition
sequential correction can fail even when every one-axis correction exists
(`xorJoint_countermodel`). -/
theorem joint_inv_mulVec (seE spE : Bool → ℝ) (seD spD : ℝ) (hE : ∀ d, seE d + spE d ≠ 1)
    (hD : seD + spD ≠ 1) (Fs : Bool × Bool → ℝ) :
    (jointMatrix (fun d ↦ binaryMatrix (seE d) (spE d)) (binaryMatrix seD spD))⁻¹ *ᵥ Fs =
      exposureCorrectVec seE spE (outcomeCorrectVec seD spD Fs) := by
  rw [jointMatrix_factor, Matrix.mul_inv_rev, ← mulVec_mulVec, outcome_inv_mulVec seD spD hD,
    exposure_inv_mulVec seE spE hE]

/-- The joint matrix of classification matrices is a classification matrix. -/
theorem jointMatrix_isClassificationMatrix (PE : Bool → Matrix Bool Bool ℝ)
    (PD : Matrix Bool Bool ℝ) (hE : ∀ d, IsClassificationMatrix (PE d))
    (hD : IsClassificationMatrix PD) : IsClassificationMatrix (jointMatrix PE PD) := by
  refine ⟨fun i j ↦ mul_nonneg ((hE _).1 _ _) (hD.1 _ _), fun ⟨e, d⟩ ↦ ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [jointMatrix_apply, ← Finset.mul_sum, hD.2 d, mul_one, (hE d).2 e]

/-- The Kronecker product of classification matrices on any finite index types is a
classification matrix. -/
theorem isClassificationMatrix_kronecker {κ μ : Type*} [Fintype κ] [Fintype μ]
    (A : Matrix κ κ ℝ) (B : Matrix μ μ ℝ) (hA : IsClassificationMatrix A)
    (hB : IsClassificationMatrix B) : IsClassificationMatrix (A ⊗ₖ B) := by
  refine ⟨fun i j ↦ mul_nonneg (hA.1 _ _) (hB.1 _ _), fun ⟨a, b⟩ ↦ ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [kronecker_apply, ← Finset.mul_sum, hB.2 b, mul_one, hA.2 a]

/-- Sequential correction for a Kronecker product on any finite index types: `(PE ⊗ PD)⁻¹ F*` is
the correction of the second variable by `1 ⊗ PD⁻¹` followed by the correction of the first by
`PE⁻¹ ⊗ 1`. This is an identity of Lean's totalized inverses; when `PE` and `PD` are invertible
these are the true inverses (`inv_mulVec_mulVec`). -/
theorem kronecker_inv_mulVec_totalized {κ μ : Type*} [Fintype κ] [DecidableEq κ] [Fintype μ]
    [DecidableEq μ] (PE : Matrix κ κ ℝ) (PD : Matrix μ μ ℝ) (Fs : κ × μ → ℝ) :
    (PE ⊗ₖ PD)⁻¹ *ᵥ Fs = (PE⁻¹ ⊗ₖ (1 : Matrix μ μ ℝ)) *ᵥ (((1 : Matrix κ κ ℝ) ⊗ₖ PD⁻¹) *ᵥ Fs) := by
  rw [mulVec_mulVec, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, inv_kronecker]

/-- The deterministic classification `x* = x xor b` of one binary variable when the other true
variable equals `b`: the identity for `b = false` and the swap for `b = true`. -/
def xorAxis (b : Bool) : Matrix Bool Bool ℝ := fun x' x ↦ if x' = xor x b then 1 else 0

/-- The joint classification `E* = D* = E xor D`: exposure is classified by `xorAxis D` and
disease by `xorAxis E`, independently given the true cell (both are deterministic). -/
def xorJoint : Matrix (Bool × Bool) (Bool × Bool) ℝ :=
  fun i j ↦ xorAxis j.2 i.1 j.1 * xorAxis j.1 i.2 j.2

/-- Independence of the errors given the true cell is not enough for sequential correction.
Under `xorJoint` the classified exposure and disease are independent given the true cell (the
joint kernel is the product of the two one-axis kernels), and every one-axis matrix is a
permutation, so each one-axis correction exists. Yet the joint matrix is singular: the true cells
`(1, 1)` and `(0, 0)` are both classified `(0, 0)`. Disease classification here depends on the
true exposure, which `jointMatrix` excludes. -/
theorem xorJoint_countermodel :
    IsClassificationMatrix xorJoint ∧
      (∀ e' d' e d, xorJoint (e', d') (e, d) = xorAxis d e' e * xorAxis e d' d) ∧
      (∀ b, IsClassificationMatrix (xorAxis b) ∧ xorAxis b * xorAxis b = 1 ∧
        (xorAxis b).det ≠ 0) ∧
      xorJoint.det = 0 := by
  have hsq : ∀ b, xorAxis b * xorAxis b = 1 := fun b ↦ by
    ext x' x
    rw [Matrix.mul_apply, Fintype.sum_bool]
    cases x' <;> cases x <;> cases b <;> simp [xorAxis]
  refine ⟨⟨fun i j ↦ ?_, fun ⟨e, d⟩ ↦ ?_⟩, fun _ _ _ _ ↦ rfl,
    fun b ↦ ⟨⟨fun x' x ↦ ?_, fun x ↦ ?_⟩, hsq b, det_ne_zero_of_right_inverse (hsq b)⟩, ?_⟩
  · simp only [xorJoint, xorAxis]
    split_ifs <;> norm_num
  · rw [Fintype.sum_prod_type]
    cases e <;> cases d <;> simp [xorJoint, xorAxis]
  · simp only [xorAxis]
    split_ifs <;> norm_num
  · cases x <;> cases b <;> simp [xorAxis]
  · apply exists_mulVec_eq_zero_iff.mp
    refine ⟨fun i ↦ if i = (true, true) then 1 else if i = (false, false) then -1 else 0,
      fun h ↦ ?_, ?_⟩
    · have := congrFun h (true, true)
      simp at this
    · funext ⟨e', d'⟩
      simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool]
      cases e' <;> cases d' <;> simp [xorJoint, xorAxis]

end Joint

section Polytomous

/-! ### Polytomous exposure (Tables 6.16 and 6.17) -/

/-- The observed diabetics of Table 6.16 by body mass index category. -/
def bmiDiabetics : Fin 3 → ℝ := ![3053, 5127, 6491]

/-- The observed nondiabetics of Table 6.16. -/
def bmiNondiabetics : Fin 3 → ℝ := ![81416, 65104, 33814]

/-- The classification matrix of body mass index (healthy `0`, overweight `1`, obese `2`) under
the assumptions as printed in the example of the section "Misclassification of Polytomous
Variables" (page 169): no overreporting, `9%` of the truly overweight classified healthy, `68.2%`
of the truly obese "incorrectly classified as overweight" (so `31.8%` classified obese), and no
obese person classified healthy. Rows are classified values, columns true values. -/
noncomputable def bmiMatrixStated : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0.09, 0; 0, 0.91, 0.682; 0, 0, 0.318]

/-- The printed assumptions are infeasible for Table 6.16. `bmiMatrixStated` is a valid
classification matrix, but no table of nonnegative true counts produces the observed diabetics,
nor the observed nondiabetics. For the diabetics the system forces `6491 / 0.318 ≈ 20411.95` true
obese and then `(5127 - 0.682 · 6491 / 0.318) / 0.91 ≈ -9663.68` true overweight. -/
theorem bmiStated_infeasible :
    IsClassificationMatrix bmiMatrixStated ∧
      (¬ ∃ F : Fin 3 → ℝ, 0 ≤ F ∧ bmiMatrixStated *ᵥ F = bmiDiabetics) ∧
      (¬ ∃ F : Fin 3 → ℝ, 0 ≤ F ∧ bmiMatrixStated *ᵥ F = bmiNondiabetics) ∧
      (5127 - 0.682 * (6491 / 0.318)) / 0.91 < (-9663.68 : ℝ) ∧
      (-9663.69 : ℝ) < (5127 - 0.682 * (6491 / 0.318)) / 0.91 := by
  refine ⟨⟨fun m t ↦ ?_, fun t ↦ ?_⟩, ?_, ?_, by norm_num, by norm_num⟩
  · fin_cases m <;> fin_cases t <;> norm_num [bmiMatrixStated]
  · fin_cases t <;> norm_num [bmiMatrixStated, Fin.sum_univ_three]
  all_goals
    rintro ⟨F, hF, h⟩
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h0 : 0 ≤ F 1 := hF 1
    simp [mulVec, dotProduct, Fin.sum_univ_three, bmiMatrixStated, bmiDiabetics,
      bmiNondiabetics] at h1 h2
    linarith

/-- The matrix correction under the printed assumptions: `bmiMatrixStated` is invertible, and its
inverse applied to the observed diabetics of Table 6.16 has a negative entry. -/
theorem bmiStated_inverse_not_nonneg :
    bmiMatrixStated.det ≠ 0 ∧ ¬ 0 ≤ bmiMatrixStated⁻¹ *ᵥ bmiDiabetics := by
  have hdet : bmiMatrixStated.det ≠ 0 := by
    rw [det_fin_three]
    norm_num [bmiMatrixStated]
  exact ⟨hdet, fun h ↦ bmiStated_infeasible.2.1
    ((exists_nonneg_preimage_iff _ hdet _).mpr h)⟩

/-- A repair of the printed assumptions: the matrix that keeps `68.2%` of the truly obese in the
obese category and moves `31.8%` to overweight, the reverse of the printed sentence, with `9%`
of the truly overweight classified healthy and no obese person classified healthy. The book's
obese cells (true obese = observed obese / 0.682) follow this matrix. Rows are classified values,
columns true values. -/
noncomputable def bmiMatrixRepaired : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0.09, 0; 0, 0.91, 0.318; 0, 0, 0.682]

theorem bmiMatrixRepaired_isClassificationMatrix : IsClassificationMatrix bmiMatrixRepaired := by
  refine ⟨fun m t ↦ ?_, fun t ↦ ?_⟩
  · fin_cases m <;> fin_cases t <;> norm_num [bmiMatrixRepaired]
  · fin_cases t <;> norm_num [bmiMatrixRepaired, Fin.sum_univ_three]

theorem bmiMatrixRepaired_det : bmiMatrixRepaired.det = 0.62062 := by
  rw [det_fin_three]
  norm_num [bmiMatrixRepaired]

/-- The back substitution that inverts `bmiMatrixRepaired`. -/
noncomputable def bmiCorrectRepaired (fs : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![fs 0 - 0.09 * ((fs 1 - 0.318 * (fs 2 / 0.682)) / 0.91),
    (fs 1 - 0.318 * (fs 2 / 0.682)) / 0.91, fs 2 / 0.682]

theorem bmiMatrixRepaired_inv_mulVec (fs : Fin 3 → ℝ) :
    bmiMatrixRepaired⁻¹ *ᵥ fs = bmiCorrectRepaired fs := by
  apply inv_mulVec_eq_of_mulVec_eq _ (by rw [bmiMatrixRepaired_det]; norm_num)
  funext i
  fin_cases i <;>
    simp [bmiMatrixRepaired, bmiCorrectRepaired, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The odds ratio of category `k` against the healthy category `0`, from the diabetic counts
`D` and nondiabetic counts `N`. -/
noncomputable def categoryOddsRatio (D N : Fin 3 → ℝ) (k : Fin 3) : ℝ := (D k / N k) / (D 0 / N 0)

/-- Polytomous misclassification can bias away from the null although it is nondifferential
(the same matrix for diabetics and nondiabetics). This is an additional scenario under the
repaired matrix `bmiMatrixRepaired` (the printed assumptions are infeasible:
`bmiStated_infeasible`). Correcting Table 6.16 with it gives the obese cells `9517.6` and
`49580.6` printed in Table 6.17, and odds ratios `≈ 1.145` (overweight) and `≈ 5.164` (obese).
The observed overweight odds ratio `≈ 2.100` is further from the null than the corrected one,
while the obese odds ratio `≈ 5.119` is closer. The printed odds ratios 1.4 and 5.7 come from a
different matrix (`bmiMatrixPrinted`). -/
theorem bmiRepaired_values :
    9517.59 < (bmiMatrixRepaired⁻¹ *ᵥ bmiDiabetics) 2 ∧
      (bmiMatrixRepaired⁻¹ *ᵥ bmiDiabetics) 2 < 9517.60 ∧
      49580.64 < (bmiMatrixRepaired⁻¹ *ᵥ bmiNondiabetics) 2 ∧
      (bmiMatrixRepaired⁻¹ *ᵥ bmiNondiabetics) 2 < 49580.65 ∧
      1.145 < categoryOddsRatio (bmiMatrixRepaired⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixRepaired⁻¹ *ᵥ bmiNondiabetics) 1 ∧
      categoryOddsRatio (bmiMatrixRepaired⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixRepaired⁻¹ *ᵥ bmiNondiabetics) 1 < 1.146 ∧
      5.163 < categoryOddsRatio (bmiMatrixRepaired⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixRepaired⁻¹ *ᵥ bmiNondiabetics) 2 ∧
      categoryOddsRatio (bmiMatrixRepaired⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixRepaired⁻¹ *ᵥ bmiNondiabetics) 2 < 5.164 ∧
      2.100 < categoryOddsRatio bmiDiabetics bmiNondiabetics 1 ∧
      categoryOddsRatio bmiDiabetics bmiNondiabetics 1 < 2.101 ∧
      5.119 < categoryOddsRatio bmiDiabetics bmiNondiabetics 2 ∧
      categoryOddsRatio bmiDiabetics bmiNondiabetics 2 < 5.120 := by
  simp only [bmiMatrixRepaired_inv_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [bmiCorrectRepaired, categoryOddsRatio, bmiDiabetics, bmiNondiabetics]

/-- The classification matrix behind the printed Table 6.17. Its healthy weight correction moves
`0.09/0.91` of the observed, not the true, overweight count; inverting that arithmetic gives
this matrix, under which `0.09 · 0.318 = 2.862%` of the truly obese are classified healthy and
`0.91 · 0.318 = 28.938%` overweight. It is a valid classification matrix but contradicts the
printed assumptions (page 169): no obese person classified healthy, and `68.2%` of the obese
classified overweight. -/
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

/-- The printed Table 6.17 is reproduced by `bmiMatrixPrinted` except in one digit: cells
`2545.9, 2607.5` (diabetics) and `74977.1` (nondiabetics, healthy), odds ratios `≈ 1.377`
(printed 1.4) and `≈ 5.653` (printed 5.7). The nondiabetic overweight cell is `≈ 55776.21`,
which rounds to `55,776.2`, while the book prints `55,776.3`. -/
theorem bmiPrinted_values :
    2545.93 < (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 0 ∧
      (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 0 < 2545.94 ∧
      2607.47 < (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 1 ∧
      (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics) 1 < 2607.48 ∧
      74977.14 < (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 0 ∧
      (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 0 < 74977.15 ∧
      55776.21 < (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 1 ∧
      (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 1 < 55776.22 ∧
      1.376 < categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 1 ∧
      categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 1 < 1.377 ∧
      5.653 < categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 2 ∧
      categoryOddsRatio (bmiMatrixPrinted⁻¹ *ᵥ bmiDiabetics)
        (bmiMatrixPrinted⁻¹ *ᵥ bmiNondiabetics) 2 < 5.654 := by
  simp only [bmiMatrixPrinted_inv_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
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

/-- Arithmetic on the printed Table 6.28 (neighborhood problems and functional decline,
page 184): the crude risk ratio of the observed table is `(20/172)/(28/667) ≈ 2.76993` (printed
2.8) and that of the hypothetical table is `(7.0/163.9)/(28.9/675.6) ≈ 0.99841` (printed 1.0).
The "2.2-fold" association of the text is the estimate reported by the cited study (Balfour and
Kaplan, 2002), an odds ratio of 2.23 adjusted for covariates: a different estimand from this
crude risk ratio, not an arithmetic discrepancy. -/
theorem table628_values :
    2.7699 < ((20 : ℝ) / 172) / (28 / 667) ∧ ((20 : ℝ) / 172) / (28 / 667) < 2.7700 ∧
      0.9984 < ((7.0 : ℝ) / 163.9) / (28.9 / 675.6) ∧
      ((7.0 : ℝ) / 163.9) / (28.9 / 675.6) < 0.9985 := by
  norm_num

/-- The observed cells of Table 6.28, indexed `(neighborhood problems, functional decline)`. -/
def cells628Observed (i : Bool × Bool) : ℝ :=
  if i.2 then (if i.1 then 20 else 28) else (if i.1 then 152 else 639)

/-- The hypothetical cells of Table 6.28, indexed as `cells628Observed`. -/
def cells628Hypothetical (i : Bool × Bool) : ℝ :=
  if i.2 then (if i.1 then 7.0 else 28.9) else (if i.1 then 156.9 else 646.7)

/-- The two tables of Table 6.28 do not have the same total (`839` and `839.5`), so neither is
the image of the other under any classification matrix (classification keeps the total,
`sum_mulVec`). The printed hypothetical table is therefore not an exact reclassification of
the observed one; `table628_values` is arithmetic on the printed tables. -/
theorem table628_totals :
    ∑ i, cells628Observed i = 839 ∧ ∑ i, cells628Hypothetical i = 839.5 ∧
      (¬ ∃ P, IsClassificationMatrix P ∧ P *ᵥ cells628Hypothetical = cells628Observed) ∧
      ¬ ∃ P, IsClassificationMatrix P ∧ P *ᵥ cells628Observed = cells628Hypothetical := by
  have hO : ∑ i, cells628Observed i = 839 := by
    norm_num [cells628Observed, Fintype.sum_prod_type, Fintype.sum_bool]
  have hH : ∑ i, cells628Hypothetical i = 839.5 := by
    norm_num [cells628Hypothetical, Fintype.sum_prod_type, Fintype.sum_bool]
  refine ⟨hO, hH, ?_, ?_⟩
  · rintro ⟨P, hP, h⟩
    have := sum_mulVec P hP cells628Hypothetical
    rw [h, hO, hH] at this
    norm_num at this
  · rintro ⟨P, hP, h⟩
    have := sum_mulVec P hP cells628Observed
    rw [h, hO, hH] at this
    norm_num at this

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
text (page 186) prints the first entry of the inverse as
`A = (a - D(1 - SP_{D1}))/(SE_{D1} + SP_{D1} - 1)` with an unindexed `D`; on that page `D` also
names the fourth true cell. By `exposure_inv_mulVec` the correct expression is that of Table 6.8,
with the case row total `D₁ Total = a + b` in place of `D`. -/
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
