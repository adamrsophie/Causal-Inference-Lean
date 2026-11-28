/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Distance.Basic
public import CausalInference.BiasAnalysis.MeasurementError
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.LDL

/-!
# The Mahalanobis distance and whitening

For a positive definite matrix `Σ` (in the applications a covariance matrix of the covariates),
the **Mahalanobis distance** between summary vectors is `d_M(x, y; Σ) = √(δᵀ Σ⁻¹ δ)` with
`δ = y - x`. Whitening explains it: if `Σ = B Bᵀ` then `d_M(x, y; Σ) = ‖B⁻¹ δ‖₂`, the Euclidean
distance after the change of coordinates `v ↦ B⁻¹ v`, and a random vector with covariance
matrix `Σ` has identity covariance matrix in the new coordinates. Factors `B` exist: the
symmetric square root `Σ^{1/2}` and a lower triangular (Cholesky) factor.

Positive definiteness of `Σ` is a hypothesis of every result that inverts `Σ` or a factor of it.

## Main definitions

* `mahalanobis Σ x y`: the Mahalanobis distance.

## Main results

* `mahalanobis_eq_norm_whitened`: `d_M(x, y; Σ) = ‖B⁻¹ (y - x)‖₂` for every factor
  `Σ = B Bᵀ` of a positive definite `Σ`.
* `exists_sqrt_factor`, `exists_cholesky_factor`: a symmetric positive definite square root and
  a lower triangular factor exist.
* `mahalanobis_diagonal`: for `Σ = diag(s ℓ²)` the Mahalanobis distance is the standardized
  Euclidean distance.
* `mahalanobis_affine`: invariance under `x ↦ A x + c`, `Σ ↦ A Σ Aᵀ` for invertible `A`.
* `covMatrix_mulVec`, `covMatrix_whitened`: `Cov(M X) = M Cov(X) Mᵀ`, and the whitened vector
  `B⁻¹ X` has identity covariance matrix.
* `isMetric_mahalanobis`: the Mahalanobis distance is a metric.

## References

* P. C. Mahalanobis, *On the generalised distance in statistics*, Proceedings of the National
  Institute of Sciences of India 2 (1936).
-/

@[expose] public section

namespace CausalInference

namespace Transport

namespace Distance

open MeasureTheory ProbabilityTheory Matrix BiasAnalysis.MeasurementError

variable {p : ℕ}

/-- The **Mahalanobis distance** `d_M(x, y; Σ) = √((y - x)ᵀ Σ⁻¹ (y - x))` (Mahalanobis 1936).
It is meant for a positive definite `Σ`; every result below assumes it. -/
noncomputable def mahalanobis (Sig : Matrix (Fin p) (Fin p) ℝ) (x y : Fin p → ℝ) : ℝ :=
  √((y - x) ⬝ᵥ (Sig⁻¹ *ᵥ (y - x)))

/-- `(A u)ᵀ v = uᵀ (Aᵀ v)`. -/
theorem mulVec_dotProduct_eq (A : Matrix (Fin p) (Fin p) ℝ) (u v : Fin p → ℝ) :
    (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- `∑ v ℓ² = v ⬝ᵥ v`. -/
theorem sum_sq_eq_dotProduct (v : Fin p → ℝ) : ∑ l, v l ^ 2 = v ⬝ᵥ v := by
  simp only [dotProduct, sq]

/-- A factor `B` of a positive definite `Σ = B Bᵀ` is invertible: `det Σ = (det B)² > 0`. -/
theorem isUnit_det_of_eq_mul_transpose {Sig B : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef)
    (hB : Sig = B * Bᵀ) : IsUnit B.det := by
  refine isUnit_iff_ne_zero.2 fun h ↦ hSig.det_pos.ne' ?_
  rw [hB, det_mul, h, zero_mul]

/-- **Whitening.** For a positive definite `Σ` and any factor `Σ = B Bᵀ`,
`d_M(x, y; Σ) = ‖B⁻¹ (y - x)‖₂`: since `B` is invertible, `Σ⁻¹ = B⁻ᵀ B⁻¹`. -/
theorem mahalanobis_eq_norm_whitened {Sig B : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef)
    (hB : Sig = B * Bᵀ) (x y : Fin p → ℝ) :
    mahalanobis Sig x y = ‖(WithLp.toLp 2 (B⁻¹ *ᵥ (y - x)) : EuclideanSpace ℝ (Fin p))‖ := by
  have hdet := isUnit_det_of_eq_mul_transpose hSig hB
  have hinv : Sig⁻¹ = B⁻¹ᵀ * B⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [hB, Matrix.mul_assoc, ← Matrix.mul_assoc B⁻¹, nonsing_inv_mul _ hdet, Matrix.one_mul,
      ← transpose_mul, mul_nonsing_inv _ hdet, transpose_one]
  rw [norm_toLp_two, sum_sq_eq_dotProduct, mahalanobis, hinv, mulVec_dotProduct_eq,
    mulVec_mulVec]

/-- **The symmetric square root factor.** A positive definite `Σ` has a symmetric positive
definite square root `B`, `B B = Σ`, hence `Σ = B Bᵀ`: the square root `CFC.sqrt Σ` of the
continuous functional calculus, invertible because `det Σ > 0`. -/
theorem exists_sqrt_factor {Sig : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef) :
    ∃ B : Matrix (Fin p) (Fin p) ℝ, B.PosDef ∧ Bᵀ = B ∧ B * B = Sig ∧ Sig = B * Bᵀ := by
  open scoped MatrixOrder in
  set M := CFC.sqrt Sig with hMdef
  have hM : M.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sig)
  have hMM : M * M = Sig := by
    rw [← sq]; exact CFC.sq_sqrt Sig (Matrix.nonneg_iff_posSemidef.2 hSig.posSemidef)
  have hMt : M.transpose = M := by
    have := hM.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdetM : IsUnit M.det := by
    refine isUnit_iff_ne_zero.2 fun h ↦ hSig.det_pos.ne' ?_
    rw [← hMM, Matrix.det_mul, h, zero_mul]
  refine ⟨M, ?_, hMt, hMM, by rw [hMt, hMM]⟩
  exact (hM.posDef_iff_mulVec_injective).2
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det M).2 hdetM))

/-- **The Cholesky factor.** A positive definite `Σ` factors as `Σ = L Lᵀ` with `L` lower
triangular: from the `L D Lᵀ` decomposition of Mathlib, whose diagonal `D` is positive
definite (a congruence of `Σ`), take `L = L_LDL D^{1/2}`. -/
theorem exists_cholesky_factor {Sig : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef) :
    ∃ L : Matrix (Fin p) (Fin p) ℝ, L.BlockTriangular OrderDual.toDual ∧ Sig = L * Lᵀ := by
  have hD : (LDL.diag hSig).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hSig.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.2 (isUnit_of_invertible _))
  have hd : ∀ i, 0 < LDL.diagEntries hSig i := fun i ↦ by
    have := hD.diag_pos (i := i)
    simpa [LDL.diag] using this
  set r : Fin p → ℝ := fun i ↦ √(LDL.diagEntries hSig i)
  refine ⟨LDL.lower hSig * diagonal r,
    (LDL.isLowerTriangular_lower hSig).mul (blockTriangular_diagonal r), ?_⟩
  have hrr : diagonal r * diagonal r = LDL.diag hSig := by
    rw [diagonal_mul_diagonal, LDL.diag]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hd i).le
  conv_lhs => rw [← LDL.lower_conj_diag hSig]
  rw [Matrix.transpose_mul, diagonal_transpose, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← hrr]
  simp only [Matrix.mul_assoc]

/-- **A diagonal covariance gives the standardized Euclidean distance.** If
`Σ = diag(s₁², …, s_p²)` with every `s ℓ > 0`, then `d_M(x, y; Σ) = d_SE(x, y; s)`:
`Σ⁻¹ = diag(s ℓ⁻²)`. -/
theorem mahalanobis_diagonal {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) (x y : Fin p → ℝ) :
    mahalanobis (diagonal fun l ↦ s l ^ 2) x y = stdEuclidean s x y := by
  have hinv : (diagonal fun l ↦ s l ^ 2)⁻¹ = diagonal fun l ↦ (s l ^ 2)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext l
    exact inv_mul_cancel₀ (pow_ne_zero 2 (hs l).ne')
  rw [mahalanobis, stdEuclidean_eq_sqrt, hinv]
  congr 1
  simp only [dotProduct, mulVec_diagonal, Pi.sub_apply, div_pow]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  field_simp

/-- A congruence `A Σ Aᵀ` of a positive definite `Σ` by an invertible `A` is positive
definite. -/
theorem posDef_mul_mul_transpose {Sig A : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef)
    (hA : IsUnit A.det) : (A * Sig * Aᵀ).PosDef := by
  have := hSig.mul_mul_conjTranspose_same
    (vecMul_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det A).2 hA))
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- **Affine invariance of the Mahalanobis distance.** For a positive definite `Σ`, an
invertible `A` and any shift `c`, `d_M(A x + c, A y + c; A Σ Aᵀ) = d_M(x, y; Σ)`. Proof: if
`Σ = B Bᵀ` then `A Σ Aᵀ = (A B)(A B)ᵀ`, and `(A B)⁻¹ A (y - x) = B⁻¹ (y - x)`. -/
theorem mahalanobis_affine {Sig A : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef)
    (hA : IsUnit A.det) (c x y : Fin p → ℝ) :
    mahalanobis (A * Sig * Aᵀ) (A *ᵥ x + c) (A *ᵥ y + c) = mahalanobis Sig x y := by
  obtain ⟨B, -, -, -, hB⟩ := exists_sqrt_factor hSig
  have hdetB := isUnit_det_of_eq_mul_transpose hSig hB
  have hAB : A * Sig * Aᵀ = (A * B) * (A * B)ᵀ := by
    rw [hB, transpose_mul]; simp only [Matrix.mul_assoc]
  have hgap : A *ᵥ y + c - (A *ᵥ x + c) = A *ᵥ (y - x) := by
    rw [mulVec_sub]; abel
  rw [mahalanobis_eq_norm_whitened (posDef_mul_mul_transpose hSig hA) hAB,
    mahalanobis_eq_norm_whitened hSig hB, hgap, Matrix.mul_inv_rev, ← mulVec_mulVec,
    mulVec_mulVec _ A⁻¹ A, nonsing_inv_mul _ hA, one_mulVec]

/-- **The Mahalanobis distance is a metric** for a positive definite `Σ`: by whitening it is
the Euclidean distance after the injective map `v ↦ B⁻¹ v`. -/
theorem isMetric_mahalanobis {Sig : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef) :
    IsMetric (mahalanobis Sig) := by
  obtain ⟨B, -, -, -, hB⟩ := exists_sqrt_factor hSig
  have hdet := isUnit_det_of_eq_mul_transpose hSig hB
  have hinj : Function.Injective fun v ↦ (WithLp.toLp 2 (B⁻¹ *ᵥ v) : EuclideanSpace ℝ (Fin p)) :=
    (WithLp.toLp_injective 2).comp (mulVec_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det B hdet)))
  refine isMetric_of_dist hinj fun a b ↦ ?_
  rw [mahalanobis_eq_norm_whitened hSig hB, dist_comm, dist_eq_norm, ← WithLp.toLp_sub,
    mulVec_sub]

/-! ### Covariance matrices -/

section Covariance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The covariance matrix of a linear image.** For a random vector `X` with square integrable
coordinates and a matrix `M`, `Cov(M X) = M Cov(X) Mᵀ`, by bilinearity of the covariance. -/
theorem covMatrix_mulVec [IsFiniteMeasure μ] {X : Ω → Fin p → ℝ}
    (hX : ∀ j, MemLp (fun ω ↦ X ω j) 2 μ) (M : Matrix (Fin p) (Fin p) ℝ) :
    covMatrix μ (fun i ω ↦ (M *ᵥ X ω) i) = M * covMatrix μ (fun i ω ↦ X ω i) * Mᵀ := by
  ext i k
  have hc : ∀ (r : Fin p) (j : Fin p), MemLp (fun ω ↦ M r j * X ω j) 2 μ :=
    fun r j ↦ (hX j).const_mul (M r j)
  have h := covariance_fun_sum_fun_sum (μ := μ) (X := fun j ω ↦ M i j * X ω j)
    (Y := fun j ω ↦ M k j * X ω j) (hc i) (hc k)
  change cov[fun ω ↦ ∑ j, M i j * X ω j, fun ω ↦ ∑ j, M k j * X ω j; μ] = _
  rw [h]
  simp only [covariance_const_mul_left, covariance_const_mul_right, Matrix.mul_apply,
    transpose_apply, covMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

/-- **The whitened vector has identity covariance matrix.** If the covariance matrix `Σ` of a
random vector `X` with square integrable coordinates is positive definite and `Σ = B Bᵀ`, then
`Cov(B⁻¹ X) = B⁻¹ Σ B⁻ᵀ = I`. -/
theorem covMatrix_whitened [IsFiniteMeasure μ] {X : Ω → Fin p → ℝ}
    (hX : ∀ j, MemLp (fun ω ↦ X ω j) 2 μ) {B : Matrix (Fin p) (Fin p) ℝ}
    (hpos : (covMatrix μ (fun i ω ↦ X ω i)).PosDef)
    (hB : covMatrix μ (fun i ω ↦ X ω i) = B * Bᵀ) :
    covMatrix μ (fun i ω ↦ (B⁻¹ *ᵥ X ω) i) = 1 := by
  have hdet := isUnit_det_of_eq_mul_transpose hpos hB
  have hBt : IsUnit Bᵀ.det := by rwa [det_transpose]
  rw [covMatrix_mulVec hX, hB, ← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul,
    transpose_nonsing_inv, mul_nonsing_inv _ hBt]

end Covariance

/-! ### Examples -/

section Examples

/-- The lower triangular matrix `B₀ = [[1, 0], [1, 1]]`. -/
def exampleFactor : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- The covariance matrix `Σ₀ = B₀ B₀ᵀ = [[1, 1], [1, 2]]`. -/
def exampleCov : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 2]

theorem exampleCov_eq : exampleCov = exampleFactor * exampleFactorᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exampleCov, exampleFactor, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

theorem isUnit_det_exampleFactor : IsUnit exampleFactor.det := by
  simp [exampleFactor, det_fin_two]

/-- `Σ₀` is positive definite: a congruence of the identity by the invertible `B₀`. -/
theorem posDef_exampleCov : exampleCov.PosDef := by
  have := posDef_mul_mul_transpose PosDef.one isUnit_det_exampleFactor
  rwa [Matrix.mul_one, ← exampleCov_eq] at this

theorem inv_exampleFactor : exampleFactor⁻¹ = !![1, 0; -1, 1] := by
  refine inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exampleFactor, Matrix.mul_apply, Fin.sum_univ_two]

/-- **A whitening computation.** For `Σ₀ = [[1, 1], [1, 2]]`, the Mahalanobis distance from
`(0, 0)` to `(1, 1)` is `1`, while the Euclidean distance is `√2`: the whitened gap is
`B₀⁻¹ (1, 1) = (1, 0)`. -/
theorem mahalanobis_exampleCov :
    mahalanobis exampleCov 0 ![1, 1] = 1 ∧ euclidean (0 : Fin 2 → ℝ) ![1, 1] = √2 := by
  constructor
  · rw [mahalanobis_eq_norm_whitened posDef_exampleCov exampleCov_eq, inv_exampleFactor,
      norm_toLp_two]
    simp [Fin.sum_univ_two, mulVec, dotProduct]
  · rw [euclidean_eq_sqrt]
    norm_num [Fin.sum_univ_two]

/-- A lower triangular factor of `Σ₀` exists (it is `B₀`). -/
example : ∃ L : Matrix (Fin 2) (Fin 2) ℝ, L.BlockTriangular OrderDual.toDual ∧
    exampleCov = L * Lᵀ :=
  exists_cholesky_factor posDef_exampleCov

/-- With `s = (2, 1)` the diagonal Mahalanobis distance is the standardized one. -/
example (x y : Fin 2 → ℝ) :
    mahalanobis (diagonal fun l ↦ (![2, 1] : Fin 2 → ℝ) l ^ 2) x y =
      stdEuclidean ![2, 1] x y :=
  mahalanobis_diagonal (fun l ↦ by fin_cases l <;> norm_num) x y

/-- Affine invariance for `Σ₀` and `A = B₀`. -/
example (c x y : Fin 2 → ℝ) :
    mahalanobis (exampleFactor * exampleCov * exampleFactorᵀ) (exampleFactor *ᵥ x + c)
      (exampleFactor *ᵥ y + c) = mahalanobis exampleCov x y :=
  mahalanobis_affine posDef_exampleCov isUnit_det_exampleFactor c x y

/-- The Mahalanobis distance of `Σ₀` is a metric. -/
example : IsMetric (mahalanobis exampleCov) := isMetric_mahalanobis posDef_exampleCov

/-- The uniform law on four units. -/
noncomputable def fourLaw : Measure (Fin 4) := uniformOn Set.univ

instance : IsProbabilityMeasure fourLaw := by
  unfold fourLaw
  infer_instance

theorem fourLaw_real_singleton (ω : Fin 4) : fourLaw.real {ω} = 1 / 4 := by
  simp [fourLaw, measureReal_def, uniformOn_univ]

/-- Two independent signs on four units: `Z(ω) = (±1, ±1)` over the four sign patterns. -/
def signVec (ω : Fin 4) : Fin 2 → ℝ := ![![-1, -1, 1, 1] ω, ![-1, 1, -1, 1] ω]

/-- The two signs have identity covariance matrix. -/
theorem covMatrix_signVec : covMatrix fourLaw (fun i ω ↦ signVec ω i) = 1 := by
  have hmean : ∀ i, ∫ ω, signVec ω i ∂fourLaw = 0 := fun i ↦ by
    rw [integral_fintype Integrable.of_finite]
    fin_cases i <;> simp [Fin.sum_univ_four, fourLaw_real_singleton, signVec]
  ext i j
  simp only [covMatrix, Matrix.of_apply, covariance, hmean, sub_zero]
  rw [integral_fintype Integrable.of_finite]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, fourLaw_real_singleton, signVec] <;> norm_num

/-- **A whitening example.** The vector `X = B₀ Z` has covariance matrix `Σ₀`, and its whitened
version `B₀⁻¹ X` has identity covariance matrix. -/
theorem covMatrix_whitened_example :
    covMatrix fourLaw (fun i ω ↦ (exampleFactor *ᵥ signVec ω) i) = exampleCov ∧
      covMatrix fourLaw (fun i ω ↦ (exampleFactor⁻¹ *ᵥ (exampleFactor *ᵥ signVec ω)) i) =
        1 := by
  have hZ : ∀ j, MemLp (fun ω ↦ signVec ω j) 2 fourLaw := fun j ↦ MemLp.of_discrete
  have hX : ∀ j, MemLp (fun ω ↦ (exampleFactor *ᵥ signVec ω) j) 2 fourLaw :=
    fun j ↦ MemLp.of_discrete
  have hcov : covMatrix fourLaw (fun i ω ↦ (exampleFactor *ᵥ signVec ω) i) = exampleCov := by
    rw [covMatrix_mulVec hZ, covMatrix_signVec, Matrix.mul_one, exampleCov_eq]
  refine ⟨hcov, covMatrix_whitened hX (hcov ▸ posDef_exampleCov) (hcov.trans exampleCov_eq)⟩

end Examples

end Distance

end Transport

end CausalInference
