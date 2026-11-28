/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HierarchicalPosterior
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Multivariate normal conjugacy with known covariance

**The density.** For a positive definite `S`, Mathlib's multivariate normal law
`multivariateGaussian μ S` on `ℝ^p` (as `EuclideanSpace ℝ ι`) has the Lebesgue density
`(2π)^{-p/2} det(S)^{-1/2} exp(-(x - μ)ᵀ S⁻¹ (x - μ) / 2)` (`multivariateGaussian_eq_withDensity`,
`multivariateGaussianPDF`). Proof: the law is the image of the standard normal product under
`y ↦ μ + √S y`; change of variables with Jacobian `det √S = √det S`.

**Conjugacy.** Let `y₁, …, yₙ` (`n ≥ 1`) be i.i.d. `N_p(θ, Σ)` given `θ`, with `Σ` positive
definite and known, and let the prior be `θ ~ N_p(m₀, Σ₀)`, `Σ₀` positive definite. With the
precisions `P₀ = Σ₀⁻¹` and `P = Σ⁻¹`, the **posterior precision** is `P₁ = P₀ + n P`, positive
definite, and the posterior (`multivariateNormal_posterior`) is
`N_p(P₁⁻¹ (P₀ m₀ + P ∑ yᵢ), P₁⁻¹)`; the marginal likelihood is positive and finite. Only
positive definite matrices are inverted. The posterior mean is a matrix weighted average of the
prior mean and the sample mean, `P₁⁻¹ P₀ m₀ + P₁⁻¹ (n P) ȳ`, with weights summing to the identity
(`posteriorMeanVec_eq_shrinkage`).

## Main definitions

* `multivariateGaussianPDF`, `posteriorPrecisionMat`, `posteriorMeanVec`.

## Main results

* `multivariateGaussian_eq_withDensity`, `quadForm_sub_eq_complete`,
  `multivariateNormal_posterior`, `posteriorMeanVec_eq_shrinkage`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **density of `N_p(μ, S)`** at `x`:
`(2π)^{-p/2} det(S)^{-1/2} exp(-(x - μ)ᵀ S⁻¹ (x - μ) / 2)`. It is the density of
`multivariateGaussian μ S` when `S` is positive definite (`multivariateGaussian_eq_withDensity`). -/
noncomputable def multivariateGaussianPDF (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√S.det)⁻¹ *
    Real.exp (-(1 / 2) * ((WithLp.ofLp x - WithLp.ofLp μ) ⬝ᵥ
      S⁻¹ *ᵥ (WithLp.ofLp x - WithLp.ofLp μ)))

omit [DecidableEq ι] in
private lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (ν.withDensity g).map e = (ν.map e).withDensity (g ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs (hg.comp e.symm.measurable) e.measurable]
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]

omit [DecidableEq ι] in
/-- The standard normal product on `ℝ^ι` has the Lebesgue density `∏ᵢ φ(yᵢ)`. -/
theorem pi_gaussianReal_zero_one_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      volume.withDensity (fun y : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) := by
  have h := commonEffectKernel_apply (ι := ι) (s := fun _ => 1) (fun _ => one_pos) 0
  rw [commonEffectKernel_eq_likelihoodKernel,
    likelihoodKernel_apply (measurable_commonEffectLikelihood _)] at h
  simp only [Real.toNNReal_one] at h
  rw [← h, volume_pi]
  congr 1
  funext y
  simp [commonEffectLikelihood]

private lemma map_affine_volume' (m : ι → ℝ) {B : Matrix ι ι ℝ} (hB : B.det ≠ 0) :
    (volume : Measure (ι → ℝ)).map (fun y => m + B *ᵥ y) =
      ENNReal.ofReal |(B.det)⁻¹| • volume := by
  have hfun : (fun y => m + B *ᵥ y) = (fun z => m + z) ∘ ⇑(Matrix.toLin' B) := by
    funext y
    simp only [Function.comp_apply, Matrix.toLin'_apply]
  have hc : Continuous ⇑(Matrix.toLin' B) := (Matrix.toLin' B).continuous_of_finiteDimensional
  rw [hfun, ← Measure.map_map (measurable_const_add m) hc.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (f := Matrix.toLin' B)
      (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin', Measure.map_smul,
    Measure.IsAddLeftInvariant.map_add_left_eq_self m]
  exact (measurable_const_add m).aemeasurable

/-- **The density of a nonsingular multivariate normal law**: for `S` positive definite,
`multivariateGaussian μ S = volume.withDensity (multivariateGaussianPDF μ S)`. -/
theorem multivariateGaussian_eq_withDensity {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hS : S.PosDef) :
    multivariateGaussian μ S =
      volume.withDensity fun x => ENNReal.ofReal (multivariateGaussianPDF μ S x) := by
  set B := CFC.sqrt S with hBdef
  set m := WithLp.ofLp μ with hm
  have hB0 : 0 ≤ B := CFC.sqrt_nonneg S
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hBt : Bᵀ = B := by
    have := hB0.isSelfAdjoint
    rwa [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hBdet : 0 < B.det := by
    have h1 : 0 ≤ B.det := (nonneg_iff_posSemidef.mp hB0).det_nonneg
    have h2 : B.det * B.det = S.det := by rw [← det_mul, hBB]
    refine h1.lt_of_ne fun h => ?_
    rw [← h, zero_mul] at h2
    exact hS.det_pos.ne' h2.symm
  have hdetS : √S.det = B.det := by rw [← hBB, det_mul, Real.sqrt_mul_self hBdet.le]
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet.ne'
  have hc1 : Continuous fun y : ι → ℝ => B *ᵥ y :=
    (Matrix.mulVecLin B).continuous_of_finiteDimensional
  have hc2 : Continuous fun y : ι → ℝ => B⁻¹ *ᵥ y :=
    (Matrix.mulVecLin B⁻¹).continuous_of_finiteDimensional
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
    { toFun := fun y => m + B *ᵥ y
      invFun := fun z => B⁻¹ *ᵥ (z - m)
      left_inv := fun y => by
        simp only [add_sub_cancel_left, mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
      right_inv := fun z => by
        simp only [mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec, add_sub_cancel]
      measurable_toFun := (continuous_const.add hc1).measurable
      measurable_invFun := (hc2.comp (continuous_id.sub continuous_const)).measurable }
  have hΦ : Measurable fun y : ι → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  set E := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hmvn : multivariateGaussian μ S =
      ((Measure.pi fun _ : ι => gaussianReal 0 1).map e).map E := by
    rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop)
      (by fun_prop), Measure.map_map E.measurable e.measurable]
    congr 1
  have hvol : (volume : Measure (EuclideanSpace ℝ ι)) = (volume : Measure (ι → ℝ)).map E :=
    (PiLp.volume_preserving_toLp ι).map_eq.symm
  have hq : ∀ v : ι → ℝ, (B⁻¹ *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ v) = v ⬝ᵥ (S⁻¹ *ᵥ v) := fun v => by
    rw [show (B⁻¹ *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ v) = v ⬝ᵥ (B⁻¹ᵀ *ᵥ (B⁻¹ *ᵥ v)) by
      rw [dotProduct_mulVec v B⁻¹ᵀ, vecMul_transpose], mulVec_mulVec, transpose_nonsing_inv, hBt,
      ← Matrix.mul_inv_rev, hBB]
  have hprod : ∀ u : ι → ℝ, ∏ i, gaussianPDFReal 0 1 (u i) =
      ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * Real.exp (-(u ⬝ᵥ u) / 2) := fun u => by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, inv_pow]
    congr 2
    simp only [dotProduct, sq, neg_div, Finset.sum_neg_distrib, Finset.sum_div]
  have hg : Measurable fun z : ι → ℝ => ENNReal.ofReal |(B.det)⁻¹| *
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 ((B⁻¹ *ᵥ (z - m)) i)) :=
    (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 1).comp ((measurable_pi_apply i).comp
        (hc2.comp (continuous_id.sub continuous_const)).measurable))).const_mul _
  have hdens : (Measure.pi fun _ : ι => gaussianReal 0 1).map e =
      volume.withDensity (fun z : ι → ℝ => ENNReal.ofReal |(B.det)⁻¹| *
        ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 ((B⁻¹ *ᵥ (z - m)) i))) := by
    rw [pi_gaussianReal_zero_one_eq_withDensity, map_withDensity_equiv _ e hΦ,
      show (⇑e : (ι → ℝ) → ι → ℝ) = fun y => m + B *ᵥ y from rfl,
      map_affine_volume' m hBdet.ne', withDensity_smul_measure,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    rfl
  rw [hmvn, hdens, map_withDensity_equiv _ E hg, hvol]
  congr 1
  funext x
  change ENNReal.ofReal |(B.det)⁻¹| *
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 ((B⁻¹ *ᵥ (WithLp.ofLp x - m)) i)) = _
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have h12 : ∀ q : ℝ, -(1 / 2) * q = -q / 2 := fun q => by ring
  rw [hprod, hq, abs_inv, abs_of_pos hBdet, multivariateGaussianPDF, hdetS, h12]
  ring

theorem measurable_multivariateGaussianPDF_mean (S : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    Measurable fun μ => ENNReal.ofReal (multivariateGaussianPDF μ S x) := by
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  unfold multivariateGaussianPDF
  fun_prop

theorem measurable_multivariateGaussianPDF (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable fun x => ENNReal.ofReal (multivariateGaussianPDF μ S x) := by
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  unfold multivariateGaussianPDF
  fun_prop

omit [DecidableEq ι] in
private lemma dotProduct_mulVec_comm_of_symm' {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (u v : ι → ℝ) :
    u ⬝ᵥ P *ᵥ v = v ⬝ᵥ P *ᵥ u := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]

omit [DecidableEq ι] in
private lemma quad_sub_of_symm' {P : Matrix ι ι ℝ} (hP : Pᵀ = P) (u v : ι → ℝ) :
    (u - v) ⬝ᵥ P *ᵥ (u - v) = u ⬝ᵥ P *ᵥ u - 2 * (u ⬝ᵥ P *ᵥ v) + v ⬝ᵥ P *ᵥ v := by
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [dotProduct_mulVec_comm_of_symm' hP v u]
  ring

/-- **Completing the square**: for symmetric `P₁` with invertible determinant and `m₁ = P₁⁻¹ b`,
`θᵀ P₁ θ - 2 θᵀ b = (θ - m₁)ᵀ P₁ (θ - m₁) - m₁ᵀ P₁ m₁`. -/
theorem quadForm_sub_eq_complete {P1 : Matrix ι ι ℝ} (h1 : P1ᵀ = P1) (hu : IsUnit P1.det)
    (t b : ι → ℝ) :
    t ⬝ᵥ P1 *ᵥ t - 2 * (t ⬝ᵥ b) =
      (t - P1⁻¹ *ᵥ b) ⬝ᵥ P1 *ᵥ (t - P1⁻¹ *ᵥ b) - (P1⁻¹ *ᵥ b) ⬝ᵥ P1 *ᵥ (P1⁻¹ *ᵥ b) := by
  have hb : P1 *ᵥ (P1⁻¹ *ᵥ b) = b := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  rw [quad_sub_of_symm' h1, hb]
  ring

omit [Fintype ι] [DecidableEq ι] in
private lemma symm_of_posDef {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) : Qᵀ = Q := by
  have := hQ.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

/-- The **posterior precision** `Σ₀⁻¹ + n Σ⁻¹` for `n` observations with covariance `Σ` and the
prior covariance `Σ₀`. -/
noncomputable def posteriorPrecisionMat (S0 Sg : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  S0⁻¹ + (n : ℝ) • Sg⁻¹

/-- The **posterior mean** `P₁⁻¹ (Σ₀⁻¹ m₀ + Σ⁻¹ ∑ⱼ yⱼ)`, `P₁ = posteriorPrecisionMat`. -/
noncomputable def posteriorMeanVec {J : Type*} [Fintype J] (m0 : EuclideanSpace ℝ ι)
    (S0 Sg : Matrix ι ι ℝ) (y : J → EuclideanSpace ℝ ι) : ι → ℝ :=
  (posteriorPrecisionMat S0 Sg (Fintype.card J))⁻¹ *ᵥ
    (S0⁻¹ *ᵥ WithLp.ofLp m0 + Sg⁻¹ *ᵥ ∑ j, WithLp.ofLp (y j))

/-- The posterior precision is positive definite for positive definite `Σ₀`, `Σ` (any `n`). -/
theorem posDef_posteriorPrecisionMat {S0 Sg : Matrix ι ι ℝ} (hS0 : S0.PosDef) (hSg : Sg.PosDef)
    (n : ℕ) : (posteriorPrecisionMat S0 Sg n).PosDef := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [posteriorPrecisionMat] using hS0.inv
  · exact hS0.inv.add (hSg.inv.smul (by exact_mod_cast hn))

/-- **The posterior mean is a matrix weighted average** of the prior mean and the sample mean
`ȳ = n⁻¹ ∑ yⱼ`: `m₁ = W₀ m₀ + W ȳ` with `W₀ = P₁⁻¹ Σ₀⁻¹`, `W = P₁⁻¹ (n Σ⁻¹)` and
`W₀ + W = I`. -/
theorem posteriorMeanVec_eq_shrinkage {J : Type*} [Fintype J] [Nonempty J]
    {S0 Sg : Matrix ι ι ℝ} (hS0 : S0.PosDef) (hSg : Sg.PosDef) (m0 : EuclideanSpace ℝ ι)
    (y : J → EuclideanSpace ℝ ι) :
    posteriorMeanVec m0 S0 Sg y =
        ((posteriorPrecisionMat S0 Sg (Fintype.card J))⁻¹ * S0⁻¹) *ᵥ WithLp.ofLp m0 +
          ((posteriorPrecisionMat S0 Sg (Fintype.card J))⁻¹ * ((Fintype.card J : ℝ) • Sg⁻¹)) *ᵥ
            ((Fintype.card J : ℝ)⁻¹ • ∑ j, WithLp.ofLp (y j)) ∧
      (posteriorPrecisionMat S0 Sg (Fintype.card J))⁻¹ * S0⁻¹ +
          (posteriorPrecisionMat S0 Sg (Fintype.card J))⁻¹ * ((Fintype.card J : ℝ) • Sg⁻¹) =
        1 := by
  have hn : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hu : IsUnit (posteriorPrecisionMat S0 Sg (Fintype.card J)).det :=
    (isUnit_iff_isUnit_det _).1 (posDef_posteriorPrecisionMat hS0 hSg _).isUnit
  refine ⟨?_, ?_⟩
  · rw [posteriorMeanVec, mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [smul_mulVec, mulVec_smul, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · rw [← Matrix.mul_add, ← posteriorPrecisionMat, nonsing_inv_mul _ hu]

/-- **Multivariate normal conjugacy.** Let `y₁, …, yₙ`, `n ≥ 1`, be i.i.d. `N_p(θ, Σ)` given `θ`
and `θ ~ N_p(m₀, Σ₀)`, with `Σ` and `Σ₀` positive definite. The marginal likelihood
`∫ ∏ⱼ φ(yⱼ; θ, Σ) dN(m₀, Σ₀)(θ)` is positive and finite, and the normalized posterior is
`N_p(P₁⁻¹ (Σ₀⁻¹ m₀ + Σ⁻¹ ∑ yⱼ), P₁⁻¹)` with the posterior precision `P₁ = Σ₀⁻¹ + n Σ⁻¹`. Proof:
both densities are explicit (`multivariateGaussian_eq_withDensity`); the exponent of prior times
likelihood is a quadratic in `θ` with leading matrix `P₁` and linear term `Σ₀⁻¹ m₀ + Σ⁻¹ ∑ yⱼ`,
and completing the square (`quadForm_sub_eq_complete`) shows that prior times likelihood is a
constant multiple of the posterior density. -/
theorem multivariateNormal_posterior {J : Type*} [Fintype J] {S0 Sg : Matrix ι ι ℝ}
    (hS0 : S0.PosDef) (hSg : Sg.PosDef) (m0 : EuclideanSpace ℝ ι) (y : J → EuclideanSpace ℝ ι) :
    0 < ∫⁻ θ, ENNReal.ofReal (∏ j, multivariateGaussianPDF θ Sg (y j))
        ∂multivariateGaussian m0 S0 ∧
      ∫⁻ θ, ENNReal.ofReal (∏ j, multivariateGaussianPDF θ Sg (y j))
        ∂multivariateGaussian m0 S0 ≠ ∞ ∧
      normalizedPosterior (multivariateGaussian m0 S0)
          (fun θ => ENNReal.ofReal (∏ j, multivariateGaussianPDF θ Sg (y j))) =
        multivariateGaussian (WithLp.toLp 2 (posteriorMeanVec m0 S0 Sg y))
          (posteriorPrecisionMat S0 Sg (Fintype.card J))⁻¹ := by
  set P0 := S0⁻¹
  set Ps := Sg⁻¹
  set P1 := posteriorPrecisionMat S0 Sg (Fintype.card J) with hP1def
  have hP0 : P0.PosDef := hS0.inv
  have hPs : Ps.PosDef := hSg.inv
  have hP1 : P1.PosDef := posDef_posteriorPrecisionMat hS0 hSg _
  have hu1 : IsUnit P1.det := (isUnit_iff_isUnit_det _).1 hP1.isUnit
  have hinv1 : P1⁻¹⁻¹ = P1 := nonsing_inv_nonsing_inv _ hu1
  have hP1s : P1ᵀ = P1 := symm_of_posDef hP1
  have hP0s : P0ᵀ = P0 := symm_of_posDef hP0
  have hPss : Psᵀ = Ps := symm_of_posDef hPs
  set b : ι → ℝ := P0 *ᵥ WithLp.ofLp m0 + Ps *ᵥ ∑ j, WithLp.ofLp (y j) with hb
  set m1 := WithLp.toLp 2 (posteriorMeanVec m0 S0 Sg y)
  have hm1 : WithLp.ofLp m1 = P1⁻¹ *ᵥ b := rfl
  set Ω1 := P1⁻¹
  have hΩ1 : Ω1.PosDef := hP1.inv
  set a := ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹
  have ha : 0 < a := by positivity
  have hdet : ∀ {Q : Matrix ι ι ℝ}, Q.PosDef → 0 < (√Q.det)⁻¹ := fun hQ =>
    inv_pos.2 (Real.sqrt_pos.2 hQ.det_pos)
  have h0 := hdet hS0
  have hs := hdet hSg
  have h1 := hdet hΩ1
  set c0 : ℝ := WithLp.ofLp m0 ⬝ᵥ P0 *ᵥ WithLp.ofLp m0 +
    ∑ j, WithLp.ofLp (y j) ⬝ᵥ Ps *ᵥ WithLp.ofLp (y j)
  set R : ℝ := c0 - WithLp.ofLp m1 ⬝ᵥ P1 *ᵥ WithLp.ofLp m1
  set C : ℝ := a * (√S0.det)⁻¹ * (a * (√Sg.det)⁻¹) ^ Fintype.card J *
    Real.exp (-(1 / 2) * R) / (a * (√Ω1.det)⁻¹)
  have hC : 0 < C := by positivity
  have hexp : ∀ t : ι → ℝ, (t - WithLp.ofLp m0) ⬝ᵥ P0 *ᵥ (t - WithLp.ofLp m0) +
      ∑ j, (WithLp.ofLp (y j) - t) ⬝ᵥ Ps *ᵥ (WithLp.ofLp (y j) - t) =
      (t - WithLp.ofLp m1) ⬝ᵥ P1 *ᵥ (t - WithLp.ofLp m1) + R := by
    intro t
    have hc := quadForm_sub_eq_complete hP1s hu1 t b
    rw [← hm1] at hc
    simp only [quad_sub_of_symm' hP0s, quad_sub_of_symm' hPss, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hlin : ∑ j, 2 * (WithLp.ofLp (y j) ⬝ᵥ Ps *ᵥ t) =
        2 * (t ⬝ᵥ (Ps *ᵥ ∑ j, WithLp.ofLp (y j))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [← dotProduct_mulVec_comm_of_symm' hPss, ← sum_dotProduct]
    have hquad : t ⬝ᵥ P1 *ᵥ t = t ⬝ᵥ P0 *ᵥ t + (Fintype.card J : ℝ) * (t ⬝ᵥ Ps *ᵥ t) := by
      rw [hP1def, posteriorPrecisionMat, add_mulVec, dotProduct_add, smul_mulVec,
        dotProduct_smul, smul_eq_mul]
    have hlin0 : t ⬝ᵥ b = t ⬝ᵥ P0 *ᵥ WithLp.ofLp m0 + t ⬝ᵥ (Ps *ᵥ ∑ j, WithLp.ofLp (y j)) := by
      rw [hb, dotProduct_add]
    rw [hlin]
    simp only [R, c0]
    linarith [hc, hquad, hlin0]
  have hLm : Measurable fun θ : EuclideanSpace ℝ ι =>
      ENNReal.ofReal (∏ j, multivariateGaussianPDF θ Sg (y j)) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    unfold multivariateGaussianPDF
    fun_prop
  have key := normalizedPosterior_eq_of_mul_eq (κ := volume)
    (measurable_multivariateGaussianPDF m0 S0) hLm (c := ENNReal.ofReal C)
    (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top
    (g := fun x => ENNReal.ofReal (multivariateGaussianPDF m1 Ω1 x)) ?_ ?_
  · rw [← multivariateGaussian_eq_withDensity hS0, ← multivariateGaussian_eq_withDensity hΩ1]
      at key
    refine ⟨?_, ?_, key.2⟩
    · rw [key.1]; exact ENNReal.ofReal_pos.2 hC
    · rw [key.1]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall fun θ => ?_
    rw [← ENNReal.ofReal_mul (by unfold multivariateGaussianPDF; positivity),
      ← ENNReal.ofReal_mul hC.le]
    congr 1
    have hE := hexp (WithLp.ofLp θ)
    simp only [multivariateGaussianPDF, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, ← Real.exp_sum, hinv1]
    have hsym : ∀ j, (WithLp.ofLp (y j) - WithLp.ofLp θ) ⬝ᵥ Sg⁻¹ *ᵥ
        (WithLp.ofLp (y j) - WithLp.ofLp θ) = (WithLp.ofLp (y j) - WithLp.ofLp θ) ⬝ᵥ Ps *ᵥ
        (WithLp.ofLp (y j) - WithLp.ofLp θ) := fun j => rfl
    have hne : a * (√Ω1.det)⁻¹ ≠ 0 := by positivity
    have he : Real.exp (-(1 / 2) * ((WithLp.ofLp θ - WithLp.ofLp m0) ⬝ᵥ
          P0 *ᵥ (WithLp.ofLp θ - WithLp.ofLp m0))) *
        Real.exp (∑ j, -(1 / 2) * ((WithLp.ofLp (y j) - WithLp.ofLp θ) ⬝ᵥ
          Ps *ᵥ (WithLp.ofLp (y j) - WithLp.ofLp θ))) =
        Real.exp (-(1 / 2) * R) * Real.exp (-(1 / 2) *
          ((WithLp.ofLp θ - WithLp.ofLp m1) ⬝ᵥ P1 *ᵥ (WithLp.ofLp θ - WithLp.ofLp m1))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Finset.mul_sum]
      congr 1
      linarith
    simp only [C, Ω1]
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination (a * (√S0.det)⁻¹ * (a * (√Sg.det)⁻¹) ^ Fintype.card J *
      (a * (√P1⁻¹.det)⁻¹)) * he
  · have h := measure_univ (μ := multivariateGaussian m1 Ω1)
    rw [multivariateGaussian_eq_withDensity hΩ1, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at h
    exact h

end MetaAnalysis

end CausalInference
