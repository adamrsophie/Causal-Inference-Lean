/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LikelihoodTests
public import CausalInference.Estimation.GaussianLinearImage

/-!
# The chi-square law with `k` degrees of freedom

The chi-square law `χ²ₖ` is the law of `‖G‖² = G₁² + ⋯ + Gₖ²` for a standard Gaussian vector
`G ~ N(0, Iₖ)` in `ℝᵏ` (`EuclideanSpace ℝ (Fin k)`). Mathlib has the gamma law but not the
identification of the law of `‖G‖²` with the gamma law of shape `k / 2` and rate `1 / 2`, so the
chi-square law is defined here directly as the image of `N(0, Iₖ)` under the squared norm; this
is the form in which it arises in the limit theory of quadratic test statistics.

## Main definitions

* `CausalInference.chiSquared k`: the chi-square law with `k` degrees of freedom.
* `CausalInference.quadForm A z`: the quadratic form `zᵀ A z` on `ℝ^ι`.

## Main results

* `CausalInference.chiSquared_one`: for `k = 1` it is `CausalInference.chiSquaredOne`, the law
  of the square of a standard Gaussian.
* `CausalInference.continuous_quadForm`: the quadratic form is continuous.
* `CausalInference.multivariateGaussian_map_quadForm_inv`: **the law of a Gaussian quadratic
  form**: if `Z ~ N(0, Σ)` with `Σ` positive definite, then `Zᵀ Σ⁻¹ Z ~ χ²ₖ`, and
  `ProbabilityTheory.HasLaw.quadForm_inv_chiSquared` for random variables.

References: T. W. Anderson (2003), *An Introduction to Multivariate Statistical Analysis*, third
edition, chapter 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

/-- The chi-square law with `k` degrees of freedom: the law of `‖G‖²` for a standard Gaussian
vector `G ~ N(0, Iₖ)` in `ℝᵏ`. -/
noncomputable def chiSquared (k : ℕ) : Measure ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1).map fun x ↦ ‖x‖ ^ 2

instance (k : ℕ) : IsProbabilityMeasure (chiSquared k) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

/-- **One degree of freedom.** `χ²₁` is the law of the square of a standard Gaussian: for
`G ~ N(0, 1)` in `ℝ¹`, `‖G‖² = ⟪G, e₀⟫²` and `⟪G, e₀⟫ ~ N(0, 1)`. -/
theorem chiSquared_one : chiSquared 1 = chiSquaredOne := by
  set t : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with ht
  have hlaw := multivariateGaussian_map_inner (S := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    PosSemidef.one t
  have hv : (WithLp.ofLp t ⬝ᵥ (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ WithLp.ofLp t).toNNReal = 1 := by
    simp [ht, dotProduct]
  rw [hv] at hlaw
  have hfun : (fun x : EuclideanSpace ℝ (Fin 1) ↦ ‖x‖ ^ 2) =
      (fun y : ℝ ↦ y ^ 2) ∘ fun x ↦ ⟪x, t⟫ := by
    funext x
    simp [ht, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_single_right]
  rw [chiSquared, hfun, ← Measure.map_map (g := fun y : ℝ ↦ y ^ 2) (by fun_prop) (by fun_prop),
    hlaw, chiSquaredOne]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form `zᵀ A z` of a square matrix `A` on `ℝ^ι`. -/
noncomputable def quadForm (A : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  WithLp.ofLp z ⬝ᵥ A *ᵥ WithLp.ofLp z

omit [DecidableEq ι] in
/-- The quadratic form `z ↦ zᵀ A z` is continuous. -/
theorem continuous_quadForm (A : Matrix ι ι ℝ) : Continuous (quadForm A) := by
  have hc := PiLp.continuous_ofLp 2 (fun _ : ι ↦ ℝ)
  exact hc.dotProduct (continuous_const.matrix_mulVec hc)

omit [DecidableEq ι] in
/-- Scaling the argument of a quadratic form. -/
theorem quadForm_smul (A : Matrix ι ι ℝ) (c : ℝ) (z : EuclideanSpace ℝ ι) :
    quadForm A (c • z) = c ^ 2 * quadForm A z := by
  simp only [quadForm, WithLp.ofLp_smul, mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

/-- The squared norm in `ℝᵏ` is the quadratic form of the identity. -/
theorem quadForm_one (z : EuclideanSpace ℝ ι) : quadForm 1 z = ‖z‖ ^ 2 := by
  rw [quadForm, one_mulVec, EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

open scoped MatrixOrder in
/-- **The law of a Gaussian quadratic form.** If `Σ` is positive definite, the image of
`N(0, Σ)` under `z ↦ zᵀ Σ⁻¹ z` is `χ²ₖ`. With the symmetric square root `M = Σ^{1/2}`, `N(0, Σ)`
is the image of `N(0, Iₖ)` under `g ↦ M g`, and `(M g)ᵀ Σ⁻¹ (M g) = gᵀ (M Σ⁻¹ M) g = ‖g‖²`. -/
theorem multivariateGaussian_map_quadForm_inv {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ}
    (hS : S.PosDef) :
    (multivariateGaussian 0 S).map (quadForm S⁻¹) = chiSquared k := by
  set M := CFC.sqrt S with hMdef
  have hM : M.PosSemidef := nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)
  have hMM : M * M = S := by
    rw [← sq]; exact CFC.sq_sqrt S (nonneg_iff_posSemidef.2 hS.posSemidef)
  have hMt : Mᵀ = M := by
    have := hM.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hdetM : IsUnit M.det := by
    refine isUnit_iff_ne_zero.2 fun h ↦ hS.det_pos.ne' ?_
    rw [← hMM, det_mul, h, zero_mul]
  have hkey : M * S⁻¹ * M = 1 := by
    rw [← hMM, Matrix.mul_inv_rev]
    calc M * (M⁻¹ * M⁻¹) * M = (M * M⁻¹) * (M⁻¹ * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv _ hdetM, nonsing_inv_mul _ hdetM, Matrix.one_mul]
  have hmap := multivariateGaussian_map_matrixCLM (PosSemidef.one (n := Fin k) (R := ℝ)) 0 M
  rw [Matrix.mul_one, hMt, hMM, map_zero] at hmap
  rw [← hmap, Measure.map_map (continuous_quadForm S⁻¹).measurable
    (matrixCLM M).continuous.measurable, chiSquared]
  congr 1
  funext g
  simp only [Function.comp_apply, quadForm, matrixCLM_apply]
  rw [← quadForm_one, quadForm]
  have hsym : ∀ y, (M *ᵥ WithLp.ofLp g) ⬝ᵥ y = WithLp.ofLp g ⬝ᵥ (M *ᵥ y) := fun y ↦ by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hMt, dotProduct_comm]
  rw [hsym, mulVec_mulVec, mulVec_mulVec, hkey]

/-- **The law of a Gaussian quadratic form, for random variables.** If `Z ~ N(0, Σ)` with `Σ`
positive definite, then `Zᵀ Σ⁻¹ Z ~ χ²ₖ`. -/
theorem _root_.ProbabilityTheory.HasLaw.quadForm_inv_chiSquared {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ}
    (hS : S.PosDef)
    {Z : Ω' → EuclideanSpace ℝ (Fin k)} (hZ : HasLaw Z (multivariateGaussian 0 S) P') :
    HasLaw (fun ω ↦ quadForm S⁻¹ (Z ω)) (chiSquared k) P' := by
  rw [← multivariateGaussian_map_quadForm_inv hS]
  exact (hasLaw_map (continuous_quadForm S⁻¹).measurable.aemeasurable).fun_comp hZ

/-- **The quadratic form of the inverse covariance.** If `Y ~ N(0, Σ⁻¹)` with `Σ` positive
definite, then `Yᵀ Σ Y ~ χ²ₖ`; this is the limit law of a Wald statistic. -/
theorem _root_.ProbabilityTheory.HasLaw.quadForm_chiSquared_of_inv {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ}
    (hS : S.PosDef)
    {Y : Ω' → EuclideanSpace ℝ (Fin k)} (hY : HasLaw Y (multivariateGaussian 0 S⁻¹) P') :
    HasLaw (fun ω ↦ quadForm S (Y ω)) (chiSquared k) P' := by
  have h := hY.quadForm_inv_chiSquared hS.inv
  rwa [nonsing_inv_nonsing_inv S (isUnit_iff_ne_zero.2 hS.det_pos.ne')] at h

end CausalInference
