/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.Gram
public import CausalInference.BiasAnalysis.VarianceCovariance
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Generalized least squares and the Gauss-Markov theorem

Let `y` be a random vector with mean `X β` and covariance matrix `V` for every parameter `β`,
with `V` positive definite and `X` of full column rank (`IsLinearModel`). The **generalized least
squares estimator** is `β̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y = G y` (`glsMatrix`, `glsEstimate`; Aitken
1935). Both inverses exist: `V⁻¹` because `V` is positive definite, `(Xᵀ V⁻¹ X)⁻¹` because
`Xᵀ V⁻¹ X` is positive definite for `X` of full column rank (`isUnit_transpose_mul_mul_iff`).

* **Least squares.** `β̂` is the unique minimizer of `(y - X β)ᵀ V⁻¹ (y - X β)`
  (`glsObjective_eq_add`, `glsObjective_glsEstimate_le`); a unique minimizer for every `y` exists
  exactly when `X` has full column rank (`existsUnique_minimizer_iff`).
* **Unbiasedness.** A linear estimator `A y` is unbiased for `β` at every `β` exactly when
  `A X = 1` (`IsLinearModel.integral_mulVec_eq_iff`); `G X = 1` (`glsMatrix_mul_self`).
* **Covariance.** `Cov(A y) = A V Aᵀ` (`covMatrix_matrix_mulVec`) and
  `Cov(β̂) = (Xᵀ V⁻¹ X)⁻¹` (`IsLinearModel.covMatrix_glsEstimate`).
* **Gauss-Markov in the positive semidefinite order.** For `A X = 1`,
  `A V Aᵀ = (Xᵀ V⁻¹ X)⁻¹ + (A - G) V (A - G)ᵀ` (`mul_mul_transpose_eq_add`), so for every linear
  unbiased estimator `Cov(A y) - Cov(β̂)` is positive semidefinite, and the covariances are equal
  exactly when `A = G` (`IsLinearModel.gauss_markov`). For one contrast `cᵀ β`, every linear
  unbiased `aᵀ y` has variance at least `cᵀ (Xᵀ V⁻¹ X)⁻¹ c`, with equality exactly when
  `a = Gᵀ c` (`IsLinearModel.variance_dotProduct_ge`).

All hypotheses are met by independent Gaussian coordinates with means `X β` and positive
variances (`isLinearModel_pi_gaussian`).

## Main definitions

* `glsMatrix`, `glsEstimate`, `glsObjective`, `IsLinearModel`.

## Main results

* `glsMatrix_mul_self`, `glsMatrix_mul_mul_transpose`, `mul_mul_transpose_eq_add`,
  `posSemidef_mul_mul_transpose_sub`, `mul_mul_transpose_eq_iff`.
* `glsObjective_eq_add`, `glsObjective_glsEstimate_le`, `existsUnique_minimizer_iff`.
* `covMatrix_matrix_mulVec`, `IsLinearModel.integral_mulVec_eq_iff`,
  `IsLinearModel.integral_glsEstimate`, `IsLinearModel.covMatrix_glsEstimate`,
  `IsLinearModel.gauss_markov`, `IsLinearModel.variance_dotProduct_ge`.
* `isLinearModel_pi_gaussian`.

## References

* A. C. Aitken, *On least squares and linear combination of observations*, Proceedings of the
  Royal Society of Edinburgh 55 (1935).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory BiasAnalysis.MeasurementError

/-! ### The generalized least squares matrix -/

section Algebra

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- The **generalized least squares matrix** `G = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`. The results assume `V`
positive definite and `X` of full column rank, so that both inverses are genuine. -/
noncomputable def glsMatrix (X : Matrix n p ℝ) (V : Matrix n n ℝ) : Matrix p n ℝ :=
  (Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ * V⁻¹

/-- The **generalized least squares estimate** `β̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y`. -/
noncomputable def glsEstimate (X : Matrix n p ℝ) (V : Matrix n n ℝ) (y : n → ℝ) : p → ℝ :=
  glsMatrix X V *ᵥ y

/-- The **generalized least squares objective** `(y - X β)ᵀ V⁻¹ (y - X β)`. -/
noncomputable def glsObjective (X : Matrix n p ℝ) (V : Matrix n n ℝ) (y : n → ℝ) (β : p → ℝ) :
    ℝ :=
  (y - X *ᵥ β) ⬝ᵥ (V⁻¹ *ᵥ (y - X *ᵥ β))

omit [Fintype n] [DecidableEq n] in
/-- A positive definite real matrix is symmetric. -/
theorem transpose_eq_of_posDef {V : Matrix n n ℝ} (hV : V.PosDef) : Vᵀ = V := by
  have := hV.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

variable {X : Matrix n p ℝ} {V : Matrix n n ℝ}

/-- `Xᵀ V⁻¹ X` is invertible for `V` positive definite and `X` of full column rank. -/
theorem isUnit_gram_inv (hV : V.PosDef) (hX : Function.Injective X.mulVec) :
    IsUnit (Xᵀ * V⁻¹ * X) :=
  (isUnit_transpose_mul_mul_iff hV.inv).2 hX

omit [Fintype p] [DecidableEq p] in
/-- `Xᵀ V⁻¹ X` is symmetric for `V` positive definite. -/
theorem transpose_gram_inv (hV : V.PosDef) : (Xᵀ * V⁻¹ * X)ᵀ = Xᵀ * V⁻¹ * X := by
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_eq_of_posDef hV.inv,
    Matrix.mul_assoc]

/-- `(Xᵀ V⁻¹ X)⁻¹` is positive definite. -/
theorem posDef_inv_gram_inv (hV : V.PosDef) (hX : Function.Injective X.mulVec) :
    (Xᵀ * V⁻¹ * X)⁻¹.PosDef :=
  ((posDef_transpose_mul_mul_iff hV.inv).2 hX).inv

/-- **The generalized least squares matrix is a left inverse of the design**: `G X = 1`. -/
theorem glsMatrix_mul_self (hV : V.PosDef) (hX : Function.Injective X.mulVec) :
    glsMatrix X V * X = 1 := by
  rw [glsMatrix, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (isUnit_gram_inv hV hX))]

/-- `V Gᵀ = X (Xᵀ V⁻¹ X)⁻¹`. -/
theorem mul_transpose_glsMatrix (hV : V.PosDef) :
    V * (glsMatrix X V)ᵀ = X * (Xᵀ * V⁻¹ * X)⁻¹ := by
  rw [glsMatrix, transpose_mul, transpose_mul, transpose_eq_of_posDef hV.inv, transpose_transpose,
    transpose_nonsing_inv, transpose_gram_inv hV, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hV.isUnit), Matrix.one_mul]

/-- **The covariance of the generalized least squares estimate**: `G V Gᵀ = (Xᵀ V⁻¹ X)⁻¹`. -/
theorem glsMatrix_mul_mul_transpose (hV : V.PosDef) (hX : Function.Injective X.mulVec) :
    glsMatrix X V * V * (glsMatrix X V)ᵀ = (Xᵀ * V⁻¹ * X)⁻¹ := by
  rw [Matrix.mul_assoc, mul_transpose_glsMatrix hV, ← Matrix.mul_assoc, glsMatrix_mul_self hV hX,
    Matrix.one_mul]

/-- **The Gauss-Markov decomposition.** For every left inverse `A` of the design (`A X = 1`),
`A V Aᵀ = (Xᵀ V⁻¹ X)⁻¹ + (A - G) V (A - G)ᵀ`. -/
theorem mul_mul_transpose_eq_add (hV : V.PosDef) (hX : Function.Injective X.mulVec)
    {A : Matrix p n ℝ} (hA : A * X = 1) :
    A * V * Aᵀ = (Xᵀ * V⁻¹ * X)⁻¹ + (A - glsMatrix X V) * V * (A - glsMatrix X V)ᵀ := by
  set G := glsMatrix X V
  obtain ⟨D, rfl⟩ : ∃ D, A = G + D := ⟨A - G, by abel⟩
  rw [add_sub_cancel_left]
  have hDX : D * X = 0 := by
    rw [Matrix.add_mul, glsMatrix_mul_self hV hX] at hA
    exact left_eq_add.1 hA.symm
  have h1 : D * V * Gᵀ = 0 := by
    rw [Matrix.mul_assoc, mul_transpose_glsMatrix hV, ← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have h2 : G * V * Dᵀ = 0 := by
    have := congrArg Matrix.transpose h1
    rwa [transpose_mul, transpose_mul, transpose_transpose, transpose_eq_of_posDef hV,
      transpose_zero, ← Matrix.mul_assoc] at this
  rw [transpose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2,
    glsMatrix_mul_mul_transpose hV hX]
  abel

/-- **Gauss-Markov in the positive semidefinite order**: for `A X = 1`,
`A V Aᵀ - (Xᵀ V⁻¹ X)⁻¹` is positive semidefinite. -/
theorem posSemidef_mul_mul_transpose_sub (hV : V.PosDef) (hX : Function.Injective X.mulVec)
    {A : Matrix p n ℝ} (hA : A * X = 1) : (A * V * Aᵀ - (Xᵀ * V⁻¹ * X)⁻¹).PosSemidef := by
  rw [mul_mul_transpose_eq_add hV hX hA, add_sub_cancel_left]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    hV.posSemidef.mul_mul_conjTranspose_same (A - glsMatrix X V)

/-- **The equality case**: for `A X = 1`, `A V Aᵀ = (Xᵀ V⁻¹ X)⁻¹` exactly when `A = G`. -/
theorem mul_mul_transpose_eq_iff (hV : V.PosDef) (hX : Function.Injective X.mulVec)
    {A : Matrix p n ℝ} (hA : A * X = 1) :
    A * V * Aᵀ = (Xᵀ * V⁻¹ * X)⁻¹ ↔ A = glsMatrix X V := by
  rw [mul_mul_transpose_eq_add hV hX hA, add_eq_left]
  constructor
  · intro h
    rw [← sub_eq_zero]
    ext k i
    set D := A - glsMatrix X V
    have hk : Dᵀ *ᵥ Pi.single k 1 = 0 := by
      by_contra hne
      have hpos := hV.dotProduct_mulVec_pos hne
      rw [star_trivial, ← dotProduct_transpose_mul_mul_mulVec, transpose_transpose, h,
        zero_mulVec, dotProduct_zero] at hpos
      exact lt_irrefl _ hpos
    have := congrFun hk i
    simpa [mulVec_single_one] using this
  · intro h
    rw [h, sub_self, Matrix.zero_mul, Matrix.zero_mul]

/-- **The scalar Gauss-Markov decomposition.** If `Xᵀ a = c`, then
`aᵀ V a = cᵀ (Xᵀ V⁻¹ X)⁻¹ c + (a - Gᵀ c)ᵀ V (a - Gᵀ c)`. -/
theorem dotProduct_mulVec_eq_add (hV : V.PosDef) (hX : Function.Injective X.mulVec)
    {a : n → ℝ} {c : p → ℝ} (ha : Xᵀ *ᵥ a = c) :
    a ⬝ᵥ (V *ᵥ a) = c ⬝ᵥ ((Xᵀ * V⁻¹ * X)⁻¹ *ᵥ c) +
      (a - (glsMatrix X V)ᵀ *ᵥ c) ⬝ᵥ (V *ᵥ (a - (glsMatrix X V)ᵀ *ᵥ c)) := by
  set G := glsMatrix X V
  set s := Gᵀ *ᵥ c
  have hVs : V *ᵥ s = X *ᵥ ((Xᵀ * V⁻¹ * X)⁻¹ *ᵥ c) := by
    rw [mulVec_mulVec, mul_transpose_glsMatrix hV, ← mulVec_mulVec]
  have hXs : Xᵀ *ᵥ s = c := by
    rw [mulVec_mulVec, ← transpose_mul, glsMatrix_mul_self hV hX, transpose_one, one_mulVec]
  have hcross : (a - s) ⬝ᵥ (V *ᵥ s) = 0 := by
    rw [hVs, dotProduct_comm, mulVec_dotProduct_eq, mulVec_sub, ha, hXs, sub_self,
      dotProduct_zero]
  have hss : s ⬝ᵥ (V *ᵥ s) = c ⬝ᵥ ((Xᵀ * V⁻¹ * X)⁻¹ *ᵥ c) := by
    rw [hVs, dotProduct_comm, mulVec_dotProduct_eq, hXs, dotProduct_comm]
  have hsym : s ⬝ᵥ (V *ᵥ (a - s)) = (a - s) ⬝ᵥ (V *ᵥ s) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_eq_of_posDef hV, dotProduct_comm]
  have hexp : a = s + (a - s) := by abel
  conv_lhs => rw [hexp]
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym, hcross, hss]
  ring

end Algebra

/-! ### Least squares -/

section LeastSquares

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  {X : Matrix n p ℝ} {V : Matrix n n ℝ}

/-- **Completing the square**: the objective at `β` is its value at `β̂` plus
`(β - β̂)ᵀ (Xᵀ V⁻¹ X) (β - β̂)`. -/
theorem glsObjective_eq_add (hV : V.PosDef) (hX : Function.Injective X.mulVec) (y : n → ℝ)
    (β : p → ℝ) :
    glsObjective X V y β = glsObjective X V y (glsEstimate X V y) +
      (β - glsEstimate X V y) ⬝ᵥ ((Xᵀ * V⁻¹ * X) *ᵥ (β - glsEstimate X V y)) := by
  set b := glsEstimate X V y
  have hW : (V⁻¹)ᵀ = V⁻¹ := transpose_eq_of_posDef hV.inv
  have hMb : (Xᵀ * V⁻¹ * X) *ᵥ b = Xᵀ *ᵥ (V⁻¹ *ᵥ y) := by
    have h := isUnit_gram_inv hV hX
    simp only [b, glsEstimate, glsMatrix, mulVec_mulVec, ← Matrix.mul_assoc,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 h), Matrix.one_mul]
  have hnorm : Xᵀ *ᵥ (V⁻¹ *ᵥ (y - X *ᵥ b)) = 0 := by
    rw [mulVec_sub, mulVec_sub, ← hMb]
    simp only [mulVec_mulVec, Matrix.mul_assoc, sub_self]
  have hy : y - X *ᵥ β = (y - X *ᵥ b) - X *ᵥ (β - b) := by rw [mulVec_sub]; abel
  have h1 : (X *ᵥ (β - b)) ⬝ᵥ (V⁻¹ *ᵥ (y - X *ᵥ b)) = 0 := by
    rw [mulVec_dotProduct_eq, hnorm, dotProduct_zero]
  have h2 : (y - X *ᵥ b) ⬝ᵥ (V⁻¹ *ᵥ (X *ᵥ (β - b))) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm, h1]
  have h3 : (X *ᵥ (β - b)) ⬝ᵥ (V⁻¹ *ᵥ (X *ᵥ (β - b))) =
      (β - b) ⬝ᵥ ((Xᵀ * V⁻¹ * X) *ᵥ (β - b)) :=
    (dotProduct_transpose_mul_mul_mulVec X V⁻¹ (β - b)).symm
  rw [glsObjective, glsObjective, hy]
  generalize X *ᵥ (β - b) = u at h1 h2 h3 ⊢
  generalize y - X *ᵥ b = e at h1 h2 ⊢
  rw [mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, h1, h2, h3]
  ring

/-- **The generalized least squares estimate is the unique minimizer** of the objective, for
`V` positive definite and `X` of full column rank. -/
theorem glsObjective_glsEstimate_le (hV : V.PosDef) (hX : Function.Injective X.mulVec)
    (y : n → ℝ) (β : p → ℝ) :
    glsObjective X V y (glsEstimate X V y) ≤ glsObjective X V y β ∧
      (glsObjective X V y β = glsObjective X V y (glsEstimate X V y) ↔
        β = glsEstimate X V y) := by
  have hM := (posDef_transpose_mul_mul_iff hV.inv).2 hX
  rw [glsObjective_eq_add hV hX y β]
  have h0 := hM.posSemidef.dotProduct_mulVec_nonneg (β - glsEstimate X V y)
  rw [star_trivial] at h0
  refine ⟨by linarith, ⟨fun h => ?_, fun h => by rw [h, sub_self]; simp⟩⟩
  by_contra hne
  have := hM.dotProduct_mulVec_pos (sub_ne_zero.2 hne)
  rw [star_trivial] at this
  linarith

omit [DecidableEq p] in
/-- **Unique least squares solutions exist exactly for full column rank**: for `V` positive
definite, the objective has a unique minimizer for every data vector if and only if `X` has
full column rank. -/
theorem existsUnique_minimizer_iff (hV : V.PosDef) :
    (∀ y, ∃! β, ∀ β', glsObjective X V y β ≤ glsObjective X V y β') ↔
      Function.Injective X.mulVec := by
  classical
  refine ⟨fun h β₀ β₁ hβ => ?_, fun hX y => ⟨glsEstimate X V y,
    fun β' => (glsObjective_glsEstimate_le hV hX y β').1, fun β hβ' => ?_⟩⟩
  · obtain ⟨m, hm, huniq⟩ := h 0
    have hshift : X *ᵥ (m + (β₁ - β₀)) = X *ᵥ m := by
      rw [mulVec_add, mulVec_sub, hβ, sub_self, add_zero]
    have hm' : ∀ β', glsObjective X V 0 (m + (β₁ - β₀)) ≤ glsObjective X V 0 β' := by
      intro β'; simp only [glsObjective, hshift]; exact hm β'
    have h0 : β₁ - β₀ = 0 := by
      have := congrArg (· - m) (huniq _ hm'); simpa using this
    exact (sub_eq_zero.1 h0).symm
  · have h := glsObjective_glsEstimate_le hV hX y β
    exact h.2.1 (le_antisymm (hβ' _) h.1)

end LeastSquares

/-! ### Linear estimators of a random vector -/

section Moments

variable {n m : Type*} [Fintype n] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {Y : n → Ω → ℝ}

/-- The mean of a linear image: `E[(A y)_k] = (A E[y])_k`. -/
theorem integral_matrix_mulVec (hY : ∀ i, Integrable (Y i) μ) (A : Matrix m n ℝ) (k : m) :
    ∫ ω, (A *ᵥ fun i => Y i ω) k ∂μ = (A *ᵥ fun i => ∫ ω, Y i ω ∂μ) k := by
  simp only [mulVec, dotProduct]
  rw [integral_finsetSum _ fun i _ => (hY i).const_mul _]
  simp only [integral_const_mul]

/-- The coordinates of a linear image of a square integrable vector are square integrable. -/
theorem memLp_matrix_mulVec (hY : ∀ i, MemLp (Y i) 2 μ) (A : Matrix m n ℝ) (k : m) :
    MemLp (fun ω => (A *ᵥ fun i => Y i ω) k) 2 μ := by
  simp only [mulVec, dotProduct]
  exact memLp_finsetSum _ fun i _ => (hY i).const_mul _

/-- **The covariance matrix of a linear image**: `Cov(A y) = A Cov(y) Aᵀ`, for square integrable
coordinates and a rectangular matrix `A`. -/
theorem covMatrix_matrix_mulVec [IsFiniteMeasure μ] (hY : ∀ i, MemLp (Y i) 2 μ)
    (A : Matrix m n ℝ) :
    covMatrix μ (fun k ω => (A *ᵥ fun i => Y i ω) k) = A * covMatrix μ Y * Aᵀ := by
  ext k l
  have hc : ∀ (r : m) (j : n), MemLp (fun ω => A r j * Y j ω) 2 μ :=
    fun r j => (hY j).const_mul (A r j)
  have h := covariance_fun_sum_fun_sum (μ := μ) (X := fun j ω => A k j * Y j ω)
    (Y := fun j ω => A l j * Y j ω) (hc k) (hc l)
  change cov[fun ω => ∑ j, A k j * Y j ω, fun ω => ∑ j, A l j * Y j ω; μ] = _
  rw [h]
  simp only [covariance_const_mul_left, covariance_const_mul_right, Matrix.mul_apply,
    transpose_apply, covMatrix, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Moments

/-! ### The linear model and the Gauss-Markov theorem -/

section Model

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
  {Ω : Type*} [MeasurableSpace Ω]

variable (n) in
/-- A **linear model** for a random vector `y = (Y i)`: under the law `P β`, for every parameter
`β`, the coordinates are square integrable with mean `X β` and covariance matrix `V`. -/
structure IsLinearModel (P : (p → ℝ) → Measure Ω) (Y : n → Ω → ℝ) (X : Matrix n p ℝ)
    (V : Matrix n n ℝ) : Prop where
  /-- Each `P β` is a probability measure. -/
  isProbabilityMeasure : ∀ β, IsProbabilityMeasure (P β)
  /-- Finite second moments. -/
  memLp : ∀ β i, MemLp (Y i) 2 (P β)
  /-- `E_β[y] = X β`. -/
  integral_eq : ∀ β i, ∫ ω, Y i ω ∂P β = (X *ᵥ β) i
  /-- `Cov_β(y) = V`. -/
  covMatrix_eq : ∀ β, covMatrix (P β) Y = V

namespace IsLinearModel

variable {P : (p → ℝ) → Measure Ω} {Y : n → Ω → ℝ} {X : Matrix n p ℝ} {V : Matrix n n ℝ}

omit [DecidableEq n] [DecidableEq p] in
theorem integral_mulVec (h : IsLinearModel n P Y X V) {m : Type*} (A : Matrix m n ℝ) (β : p → ℝ)
    (k : m) : ∫ ω, (A *ᵥ fun i => Y i ω) k ∂P β = ((A * X) *ᵥ β) k := by
  have := h.isProbabilityMeasure β
  rw [integral_matrix_mulVec (fun i => (h.memLp β i).integrable one_le_two),
    show (fun i => ∫ ω, Y i ω ∂P β) = X *ᵥ β from funext (h.integral_eq β), mulVec_mulVec]

omit [DecidableEq n] in
/-- **Unbiased linear estimators**: `A y` is unbiased for `β` at every `β` exactly when
`A X = 1`. -/
theorem integral_mulVec_eq_iff (h : IsLinearModel n P Y X V) (A : Matrix p n ℝ) :
    (∀ β k, ∫ ω, (A *ᵥ fun i => Y i ω) k ∂P β = β k) ↔ A * X = 1 := by
  simp only [h.integral_mulVec]
  constructor
  · intro hA
    ext k l
    have := hA (Pi.single l 1) k
    rw [mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  · intro hA β k
    rw [hA, one_mulVec]

/-- **The generalized least squares estimate is unbiased**, for `V` positive definite and `X` of
full column rank. -/
theorem integral_glsEstimate (h : IsLinearModel n P Y X V) (hV : V.PosDef)
    (hX : Function.Injective X.mulVec) (β : p → ℝ) (k : p) :
    ∫ ω, glsEstimate X V (fun i => Y i ω) k ∂P β = β k :=
  (h.integral_mulVec_eq_iff _).2 (glsMatrix_mul_self hV hX) β k

omit [DecidableEq n] [DecidableEq p] in
theorem covMatrix_mulVec (h : IsLinearModel n P Y X V) {m : Type*} (A : Matrix m n ℝ)
    (β : p → ℝ) : covMatrix (P β) (fun k ω => (A *ᵥ fun i => Y i ω) k) = A * V * Aᵀ := by
  have := h.isProbabilityMeasure β
  rw [covMatrix_matrix_mulVec (h.memLp β), h.covMatrix_eq]

/-- **The covariance of the generalized least squares estimate** is `(Xᵀ V⁻¹ X)⁻¹`. -/
theorem covMatrix_glsEstimate (h : IsLinearModel n P Y X V) (hV : V.PosDef)
    (hX : Function.Injective X.mulVec) (β : p → ℝ) :
    covMatrix (P β) (fun k ω => glsEstimate X V (fun i => Y i ω) k) = (Xᵀ * V⁻¹ * X)⁻¹ := by
  rw [show (fun k ω => glsEstimate X V (fun i => Y i ω) k) =
    fun k ω => (glsMatrix X V *ᵥ fun i => Y i ω) k from rfl, h.covMatrix_mulVec,
    glsMatrix_mul_mul_transpose hV hX]

/-- **The Gauss-Markov theorem** (Aitken 1935). In a linear model with positive definite
covariance `V` and a design `X` of full column rank, let `A y` be a linear estimator unbiased
for `β` at every `β`. Then `Cov(A y) - Cov(β̂)` is positive semidefinite, and
`Cov(A y) = Cov(β̂)` exactly when `A` is the generalized least squares matrix. -/
theorem gauss_markov (h : IsLinearModel n P Y X V) (hV : V.PosDef)
    (hX : Function.Injective X.mulVec) {A : Matrix p n ℝ}
    (hA : ∀ β k, ∫ ω, (A *ᵥ fun i => Y i ω) k ∂P β = β k) (β : p → ℝ) :
    (covMatrix (P β) (fun k ω => (A *ᵥ fun i => Y i ω) k) -
        covMatrix (P β) (fun k ω => glsEstimate X V (fun i => Y i ω) k)).PosSemidef ∧
      (covMatrix (P β) (fun k ω => (A *ᵥ fun i => Y i ω) k) =
          covMatrix (P β) (fun k ω => glsEstimate X V (fun i => Y i ω) k) ↔
        A = glsMatrix X V) := by
  have hAX := (h.integral_mulVec_eq_iff A).1 hA
  rw [h.covMatrix_mulVec, h.covMatrix_glsEstimate hV hX]
  exact ⟨posSemidef_mul_mul_transpose_sub hV hX hAX, mul_mul_transpose_eq_iff hV hX hAX⟩

/-- **The Gauss-Markov theorem for one contrast.** For a target `cᵀ β`, the estimate `cᵀ β̂`
is unbiased with variance `cᵀ (Xᵀ V⁻¹ X)⁻¹ c`, and every linear estimator `aᵀ y` unbiased for
`cᵀ β` at every `β` has at least this variance, with equality exactly when `a = Gᵀ c`. -/
theorem variance_dotProduct_ge (h : IsLinearModel n P Y X V) (hV : V.PosDef)
    (hX : Function.Injective X.mulVec) (c : p → ℝ) {a : n → ℝ}
    (ha : ∀ β, ∫ ω, a ⬝ᵥ (fun i => Y i ω) ∂P β = c ⬝ᵥ β) (β : p → ℝ) :
    ∫ ω, c ⬝ᵥ glsEstimate X V (fun i => Y i ω) ∂P β = c ⬝ᵥ β ∧
      Var[fun ω => c ⬝ᵥ glsEstimate X V (fun i => Y i ω); P β] =
        c ⬝ᵥ ((Xᵀ * V⁻¹ * X)⁻¹ *ᵥ c) ∧
      c ⬝ᵥ ((Xᵀ * V⁻¹ * X)⁻¹ *ᵥ c) ≤ Var[fun ω => a ⬝ᵥ (fun i => Y i ω); P β] ∧
      (Var[fun ω => a ⬝ᵥ (fun i => Y i ω); P β] = c ⬝ᵥ ((Xᵀ * V⁻¹ * X)⁻¹ *ᵥ c) ↔
        a = (glsMatrix X V)ᵀ *ᵥ c) := by
  have := h.isProbabilityMeasure β
  have hint : ∀ β' (b : n → ℝ), ∫ ω, b ⬝ᵥ (fun i => Y i ω) ∂P β' = (Xᵀ *ᵥ b) ⬝ᵥ β' := by
    intro β' b
    have e := h.integral_mulVec (Matrix.of fun (_ : Unit) i => b i) β' ()
    simp only [mulVec, dotProduct, Matrix.of_apply, Matrix.mul_apply, transpose_apply] at e ⊢
    rw [e]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hvar : ∀ b : n → ℝ, Var[fun ω => b ⬝ᵥ (fun i => Y i ω); P β] = b ⬝ᵥ (V *ᵥ b) := by
    intro b
    have e := BiasAnalysis.VarianceCovariance.variance_linearization_cov Y (h.memLp β) b
    rw [BiasAnalysis.VarianceCovariance.quadraticVariance_eq_dotProduct, h.covMatrix_eq] at e
    exact e
  have hXa : Xᵀ *ᵥ a = c := by
    funext k
    have := ha (Pi.single k 1)
    rwa [hint, dotProduct_single, dotProduct_single, mul_one, mul_one] at this
  have hG : ∀ z : n → ℝ, c ⬝ᵥ glsEstimate X V z = ((glsMatrix X V)ᵀ *ᵥ c) ⬝ᵥ z := by
    intro z
    rw [glsEstimate, dotProduct_mulVec, ← mulVec_transpose]
  have hfun : (fun ω => c ⬝ᵥ glsEstimate X V (fun i => Y i ω)) =
      fun ω => ((glsMatrix X V)ᵀ *ᵥ c) ⬝ᵥ (fun i => Y i ω) := funext fun ω => hG _
  have hXs : Xᵀ *ᵥ ((glsMatrix X V)ᵀ *ᵥ c) = c := by
    rw [mulVec_mulVec, ← transpose_mul, glsMatrix_mul_self hV hX, transpose_one, one_mulVec]
  have hs := dotProduct_mulVec_eq_add hV hX hXs
  simp only [sub_self, mulVec_zero, dotProduct_zero, add_zero] at hs
  have hdec := dotProduct_mulVec_eq_add hV hX hXa
  have hpsd := hV.posSemidef.dotProduct_mulVec_nonneg (a - (glsMatrix X V)ᵀ *ᵥ c)
  rw [star_trivial] at hpsd
  refine ⟨by rw [hfun, hint, hXs], by rw [hfun, hvar, hs], by rw [hvar, hdec]; linarith,
    ⟨fun he => ?_, fun he => by rw [hvar, he, hs]⟩⟩
  rw [hvar, hdec, add_eq_left] at he
  by_contra hne
  have := hV.dotProduct_mulVec_pos (sub_ne_zero.2 hne)
  rw [star_trivial, he] at this
  exact lt_irrefl _ this

end IsLinearModel

omit [DecidableEq p] in
/-- **A concrete linear model**: under independent Gaussian coordinates `y_i ~ N((X β)_i, v_i)`
with `v_i > 0`, the coordinates form a linear model with design `X` and covariance
`diag(v)`. -/
theorem isLinearModel_pi_gaussian (X : Matrix n p ℝ) {v : n → ℝ} (hv : ∀ i, 0 < v i) :
    IsLinearModel n (fun β => Measure.pi fun i => gaussianReal ((X *ᵥ β) i) (v i).toNNReal)
      (fun i x => x i) X (diagonal v) := by
  have hlaw : ∀ (β : p → ℝ) i, HasLaw (fun x : n → ℝ => x i)
      (gaussianReal ((X *ᵥ β) i) (v i).toNNReal)
      (Measure.pi fun i => gaussianReal ((X *ᵥ β) i) (v i).toNNReal) := fun β i =>
    (measurePreserving_eval (fun i => gaussianReal ((X *ᵥ β) i) (v i).toNNReal) i).hasLaw
  have hmem : ∀ (β : p → ℝ) i, MemLp (fun x : n → ℝ => x i) 2
      (Measure.pi fun i => gaussianReal ((X *ᵥ β) i) (v i).toNNReal) := fun β i =>
    (hlaw β i).memLp (memLp_id_gaussianReal 2)
  refine ⟨fun β => inferInstance, hmem, fun β i => ?_, fun β => ?_⟩
  · rw [(hlaw β i).integral_eq, integral_id_gaussianReal]
  · ext i j
    simp only [covMatrix, Matrix.of_apply, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      rw [covariance_self (hmem β i).aestronglyMeasurable.aemeasurable,
        (hlaw β i).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (hv i).le]
    · simp only [hij, ↓reduceIte]
      have hind := iIndepFun_pi (μ := fun i => gaussianReal ((X *ᵥ β) i) (v i).toNNReal)
        (X := fun _ => id) fun _ => aemeasurable_id
      exact (hind.indepFun hij).covariance_eq_zero (hmem β i) (hmem β j)

end Model

end NetworkMetaAnalysis

end CausalInference
