/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedContrast
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Error contrasts with unequal variances

Let `K` be a full set of error contrasts for the mean (`Kᵀ 1 = 0`, `det(Kᵀ K) ≠ 0`, and every
`z` with `Kᵀ z = 0` constant) and let `V = diag(sᵢ)` with all `sᵢ > 0`, the covariance of the
study estimates in the random effects model given `τ² = t`, `sᵢ = vᵢ + t`. With
`W = ∑ 1/sᵢ` and `n` the number of studies:

* **Determinant identity** (`det_contrast_diagonal`):
  `n · det(Kᵀ V K) = det(Kᵀ K) · det V · W`. Proof: with `A = [K | 1]` and `B = [K | V⁻¹ 1]`,
  square after a relabeling of the columns, `AᵀA`, `AᵀB` and `BᵀVB` are block triangular, so
  `det(A)² = n det(KᵀK)`, `det A det B = det(KᵀK) W` and `det(B)² det V = det(KᵀVK) W`.
* **Quadratic form identity** (`contrast_quadForm_diagonal`):
  `(Kᵀ y)ᵀ (Kᵀ V K)⁻¹ (Kᵀ y) = Q`, Cochran's `Q` with the weights `1/sᵢ`. Proof:
  `q = V K (KᵀVK)⁻¹ Kᵀ y` has `Kᵀ (y - q) = 0`, so `y - q` is a constant `c`; `∑ (yᵢ - c)/sᵢ = 0`
  identifies `c` as the inverse variance weighted mean.
* **The restricted likelihood is the likelihood of error contrasts**
  (`contrastLogLik_diagonal_eq_restrictedLogLik`): if all `vᵢ + t > 0`,
  `contrastLogLik K (diag(vᵢ + t)) y = restrictedLogLik v y t + ½ log n - ½ log det(Kᵀ K)`.
  The constant depends on `K` and `n` only, not on `t` (Harville 1974). The equal variance case
  (`contrastLogLik_smul_one_eq_restrictedLogLik`) is a corollary.

## Main results

* `det_contrast_diagonal`, `contrast_quadForm_diagonal`,
  `contrastLogLik_diagonal_eq_restrictedLogLik`, `contrastLogLik_smul_one_eq_restrictedLogLik`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
* D. A. Harville, *Bayesian inference for variance components using only error contrasts*,
  Biometrika 61 (1974).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Matrix

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m]

/-- For `F, G` with `n` rows and columns indexed by `k ≃ n`, `det(Fᵀ G)` is the product of the
determinants of the square matrices obtained by relabeling the columns. -/
theorem det_transpose_mul_of_equiv [DecidableEq k] (e : n ≃ k) (F G : Matrix n k ℝ) :
    (Fᵀ * G).det = (F.submatrix id e).det * (G.submatrix id e).det := by
  rw [← det_transpose (F.submatrix id e), ← det_mul, ← det_submatrix_equiv_self e (Fᵀ * G),
    transpose_submatrix, submatrix_mul _ _ e id e Function.bijective_id]

/-- The three block determinants with one zero block: `det(fromBlocks A B 0 d) = det A · d` for a
`1 × 1` lower right block. -/
theorem det_fromBlocks_unit (A : Matrix m m ℝ) (B : Matrix m Unit ℝ) (D : Matrix Unit Unit ℝ) :
    (fromBlocks A B 0 D).det = A.det * D () () := by
  rw [det_fromBlocks_zero₂₁, det_unique D]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- `Kᵀ 1 = 0` as a product of matrices. -/
theorem transpose_mul_replicateCol_one {K : Matrix n m ℝ} (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) :
    Kᵀ * replicateCol Unit (fun _ : n => (1 : ℝ)) = 0 := by
  ext a u
  have := congrFun hK1 a
  simp only [mulVec, dotProduct, transpose_apply, mul_one, Pi.zero_apply] at this
  simp only [Matrix.mul_apply, replicateCol_apply, transpose_apply, mul_one]
  exact this

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- `1ᵀ K = 0` as a product of matrices. -/
theorem replicateCol_one_transpose_mul {K : Matrix n m ℝ} (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) :
    (replicateCol Unit (fun _ : n => (1 : ℝ)))ᵀ * K = 0 := by
  have h := congrArg transpose (transpose_mul_replicateCol_one hK1)
  rwa [transpose_mul, transpose_transpose, transpose_zero] at h

/-- **The determinant identity for error contrasts**: if `Kᵀ 1 = 0`, `det(Kᵀ K) ≠ 0`, every `z`
with `Kᵀ z = 0` is constant, and all `sᵢ > 0`, then
`n · det(Kᵀ diag(s) K) = det(Kᵀ K) · ∏ sᵢ · ∑ 1/sᵢ`. -/
theorem det_contrast_diagonal [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) {s : n → ℝ}
    (hs : ∀ i, 0 < s i) :
    (Fintype.card n : ℝ) * (Kᵀ * diagonal s * K).det =
      (Kᵀ * K).det * (∏ i, s i) * ∑ i, ivWeight s i := by
  classical
  have hcard : Fintype.card n = Fintype.card (m ⊕ Unit) := by
    rw [Fintype.card_sum, Fintype.card_unit, card_add_one_of_contrast hK1 hKK hker]
  set e : n ≃ m ⊕ Unit := Fintype.equivOfCardEq hcard
  set U : Matrix n Unit ℝ := replicateCol Unit fun _ => 1
  set R : Matrix n Unit ℝ := replicateCol Unit fun i => ivWeight s i
  set D : Matrix n n ℝ := diagonal s
  set W := ∑ i, ivWeight s i
  have hKU : Kᵀ * U = 0 := transpose_mul_replicateCol_one hK1
  have hUK : Uᵀ * K = 0 := replicateCol_one_transpose_mul hK1
  have hDR : D * R = U := by
    ext i u
    simp [D, R, U, diagonal_mul, ivWeight, (hs i).ne']
  have hUU : (Uᵀ * U) () () = Fintype.card n := by
    simp [U, dotProduct, Finset.card_univ]
  have hUR : (Uᵀ * R) () () = W := by
    simp [U, R, W, dotProduct]
  have hRDR : (Rᵀ * D * R) () () = W := by
    rw [Matrix.mul_assoc, hDR]
    simp [U, R, W, dotProduct]
  have hRDK : Rᵀ * D * K = 0 := by
    have hD : Dᵀ = D := diagonal_transpose s
    have : Rᵀ * D = Uᵀ := by
      rw [← hD, ← transpose_mul, hDR]
    rw [this, hUK]
  have hKDR : Kᵀ * D * R = 0 := by rw [Matrix.mul_assoc, hDR, hKU]
  set A : Matrix n (m ⊕ Unit) ℝ := fromCols K U
  set B : Matrix n (m ⊕ Unit) ℝ := fromCols K R
  have h1 : (A.submatrix id e).det * (A.submatrix id e).det =
      (Kᵀ * K).det * Fintype.card n := by
    rw [← det_transpose_mul_of_equiv e, transpose_fromCols, fromRows_mul_fromCols, hKU, hUK,
      det_fromBlocks_unit, hUU]
  have h2 : (A.submatrix id e).det * (B.submatrix id e).det = (Kᵀ * K).det * W := by
    rw [← det_transpose_mul_of_equiv e, transpose_fromCols, fromRows_mul_fromCols, hUK,
      det_fromBlocks_unit, hUR]
  have h3 : (B.submatrix id e).det * (D.det * (B.submatrix id e).det) =
      (Kᵀ * D * K).det * W := by
    have hDB : (D * B).submatrix id e = D * B.submatrix id e := by
      rw [submatrix_mul _ _ id id e Function.bijective_id, submatrix_id_id]
    rw [← det_mul, ← hDB, ← det_transpose_mul_of_equiv e, ← Matrix.mul_assoc,
      transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, hKDR, hRDK,
      det_fromBlocks_unit, hRDR]
  have hW : 0 < W := sum_ivWeight_pos hs
  have hDdet : D.det = ∏ i, s i := det_diagonal
  have hA : (A.submatrix id e).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact mul_ne_zero hKK hn h1.symm
  set a := (A.submatrix id e).det
  set b := (B.submatrix id e).det
  have key : (Kᵀ * D * K).det * W * ((Kᵀ * K).det * Fintype.card n) =
      ((Kᵀ * K).det * W) ^ 2 * D.det := by
    rw [← h1, ← h2, ← h3]
    ring
  have hc : (Kᵀ * K).det * W ≠ 0 := mul_ne_zero hKK hW.ne'
  rw [← hDdet]
  apply mul_left_cancel₀ hc
  linear_combination key

/-- **The quadratic form of the contrasts is Cochran's `Q`**: under the hypotheses of
`det_contrast_diagonal`, `(Kᵀ y)ᵀ (Kᵀ diag(s) K)⁻¹ (Kᵀ y) = Q`, Cochran's `Q` with the
weights `1/sᵢ`. -/
theorem contrast_quadForm_diagonal [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) {s : n → ℝ}
    (hs : ∀ i, 0 < s i) (y : n → ℝ) :
    (Kᵀ *ᵥ y) ⬝ᵥ ((Kᵀ * diagonal s * K)⁻¹ *ᵥ (Kᵀ *ᵥ y)) = cochranQ s y := by
  set M := Kᵀ * diagonal s * K
  have hMdet : M.det ≠ 0 := by
    have h := det_contrast_diagonal hK1 hKK hker hs
    have hW : 0 < ∑ i, ivWeight s i := sum_ivWeight_pos hs
    have hP : 0 < ∏ i, s i := Finset.prod_pos fun i _ => hs i
    intro h0
    rw [h0, mul_zero] at h
    exact mul_ne_zero (mul_ne_zero hKK hP.ne') hW.ne' h.symm
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hMdet
  set w := M⁻¹ *ᵥ (Kᵀ *ᵥ y) with hw
  set g := K *ᵥ w with hg
  set q := diagonal s *ᵥ g with hq
  have hKq : Kᵀ *ᵥ q = Kᵀ *ᵥ y := by
    rw [hq, hg, mulVec_mulVec, mulVec_mulVec]
    change M *ᵥ w = _
    rw [hw, mulVec_mulVec, mul_nonsing_inv _ hMu, one_mulVec]
  have hyq : Kᵀ *ᵥ (y - q) = 0 := by rw [mulVec_sub, hKq, sub_self]
  obtain ⟨c, hc⟩ := hker _ hyq
  have hsumg : ∑ i, g i = 0 := by
    have : (fun _ : n => (1 : ℝ)) ⬝ᵥ g = 0 := by
      rw [hg, dotProduct_mulVec, ← mulVec_transpose, hK1, zero_dotProduct]
    simpa [dotProduct] using this
  have hgi : ∀ i, g i = ivWeight s i * (y i - c) := by
    intro i
    have h := congrFun hc i
    simp only [Pi.sub_apply, hq, mulVec_diagonal] at h
    simp only [ivWeight]
    field_simp [(hs i).ne']
    linarith
  have hW : 0 < ∑ i, ivWeight s i := sum_ivWeight_pos hs
  have hc' : ivwEstimate s y = c := by
    have h0 : ∑ i, ivWeight s i * (y i - c) = 0 := by
      rw [← hsumg]; exact Finset.sum_congr rfl fun i _ => (hgi i).symm
    have h1 : ∑ i, ivWeight s i * y i = c * ∑ i, ivWeight s i := by
      simp only [mul_sub, Finset.sum_sub_distrib] at h0
      rw [Finset.mul_sum]
      linarith [show ∑ i, ivWeight s i * c = ∑ i, c * ivWeight s i from
        Finset.sum_congr rfl fun i _ => mul_comm _ _]
    rw [ivwEstimate, PopulationAdjustment.weightedMean, h1]
    field_simp
  have hlhs : (Kᵀ *ᵥ y) ⬝ᵥ w = y ⬝ᵥ g := by
    rw [hg, dotProduct_mulVec y K, ← mulVec_transpose]
  rw [hlhs, cochranQ, hc']
  have h0 : ∑ i, c * g i = 0 := by rw [← Finset.mul_sum, hsumg, mul_zero]
  have : ∀ i, ivWeight s i * (y i - c) ^ 2 = y i * g i - c * g i := fun i => by
    rw [hgi i]; ring
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, h0, sub_zero]
  rfl

/-- **The restricted likelihood is the likelihood of the error contrasts** (Harville 1974): for
contrasts as in `contrast_quadForm_diagonal` and all `vᵢ + t > 0`,
`contrastLogLik K (diag(vᵢ + t)) y = restrictedLogLik v y t + ½ log n - ½ log det(Kᵀ K)`.
The constant depends on `K` and `n` only, so both have the same maximizers in `t`. -/
theorem contrastLogLik_diagonal_eq_restrictedLogLik [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) {v : n → ℝ} {t : ℝ}
    (ht : ∀ i, 0 < v i + t) (y : n → ℝ) :
    contrastLogLik K (diagonal fun i => v i + t) y = restrictedLogLik v y t +
      1 / 2 * Real.log (Fintype.card n) - 1 / 2 * Real.log (Kᵀ * K).det := by
  set s : n → ℝ := fun i => v i + t
  have hdet := det_contrast_diagonal hK1 hKK hker ht
  have hquad := contrast_quadForm_diagonal hK1 hKK hker ht y
  have hW : 0 < ∑ i, ivWeight s i := sum_ivWeight_pos ht
  have hP : 0 < ∏ i, s i := Finset.prod_pos fun i _ => ht i
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hM : (Kᵀ * diagonal s * K).det =
      (Kᵀ * K).det * (∏ i, s i) * (∑ i, ivWeight s i) / Fintype.card n := by
    rw [eq_div_iff hn.ne', mul_comm]; exact hdet
  have hlog : Real.log (Kᵀ * diagonal s * K).det = Real.log (Kᵀ * K).det +
      ∑ i, Real.log (s i) + Real.log (∑ i, ivWeight s i) - Real.log (Fintype.card n) := by
    rw [hM, Real.log_div (by positivity) hn.ne', Real.log_mul (by positivity) hW.ne',
      Real.log_mul hKK hP.ne', Real.log_prod fun i _ => (ht i).ne']
  simp only [contrastLogLik, restrictedLogLik]
  rw [hquad, hlog]
  ring

/-- **The equal variance case as a corollary**: with `vᵢ = v` and `v + t > 0`,
`contrastLogLik K ((v + t) I) y = restrictedLogLik v y t + ½ log n - ½ log det(Kᵀ K)`. -/
theorem contrastLogLik_smul_one_eq_restrictedLogLik [Nonempty n] {K : Matrix n m ℝ}
    (hK1 : Kᵀ *ᵥ (fun _ => 1) = 0) (hKK : (Kᵀ * K).det ≠ 0)
    (hker : ∀ z : n → ℝ, Kᵀ *ᵥ z = 0 → ∃ c : ℝ, z = fun _ => c) {v t : ℝ} (hvt : 0 < v + t)
    (y : n → ℝ) :
    contrastLogLik K ((v + t) • 1) y = restrictedLogLik (fun _ : n => v) y t +
      1 / 2 * Real.log (Fintype.card n) - 1 / 2 * Real.log (Kᵀ * K).det := by
  rw [smul_one_eq_diagonal]
  exact contrastLogLik_diagonal_eq_restrictedLogLik hK1 hKK hker (v := fun _ => v)
    (fun _ => hvt) y

end MetaAnalysis

end CausalInference
