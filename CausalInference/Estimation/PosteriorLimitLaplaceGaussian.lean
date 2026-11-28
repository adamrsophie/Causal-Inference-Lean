/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ChiSquared
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The density of a nonsingular multivariate normal law and Gaussian mass integrals

For a positive definite covariance `S` on `ℝ^ι`, Mathlib's `multivariateGaussian m S` (the image
of the standard Gaussian under `x ↦ m + √S x`) has Lebesgue density

  `φ_{m,S}(x) = (2π)^{-p/2} det(S)^{-1/2} exp(-(x - m)ᵀ S⁻¹ (x - m) / 2)`, `p = card ι`

(`multivariateGaussian_eq_withDensity_mvGaussianPDF`). The proof writes the standard Gaussian as
the product of `p` standard normal laws, with density `∏ φ(yᵢ)`, and changes variables along the
affine map `y ↦ m + √S y`, whose Jacobian is `det √S = √det S`.

The normal approximation of a posterior is `N(m, n⁻¹ M⁻¹)`, the image of `N(0, M⁻¹)` under
`u ↦ m + n^{-1/2} u` (`multivariateGaussian_map_affine`). Its density is
`(√n)^p (2π)^{-p/2} √det M · exp(-(n/2) (θ - m)ᵀ M (θ - m))`
(`map_affine_multivariateGaussian_inv_eq_withDensity`).

The Gaussian mass `G_p(b) = ∫ exp(-b ‖v‖²) dv = (π/b)^{p/2}` (`gaussianMass`) controls the
Laplace estimates of the posterior; `sqrt_pow_mul_gaussianMass` is its scaling law
`(√n)^p G_p(n b) = G_p(b)`.

## Main definitions

* `PosteriorLimit.mvGaussianPDF`, `PosteriorLimit.gaussianNormConst`,
  `PosteriorLimit.gaussianMass`.

## Main results

* `pi_gaussianReal_eq_withDensity_prod`, `map_mulVec_add_volume`,
  `multivariateGaussian_eq_withDensity_mvGaussianPDF`, `multivariateGaussian_map_affine`,
  `map_affine_multivariateGaussian_inv_eq_withDensity`.
* `integrable_exp_neg_mul_sq_norm_sub`, `integral_exp_neg_mul_sq_norm_sub`,
  `sqrt_pow_mul_gaussianMass`.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd edition, Wiley
  (2003), chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal MatrixOrder

namespace CausalInference

namespace PosteriorLimit

/-! ### Change of variables helpers -/

/-- The image of a measure with density under a measurable equivalence `e` is the image measure
with density `g ∘ e⁻¹`. -/
lemma map_withDensity_of_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (ν.withDensity g).map e = (ν.map e).withDensity (g ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs (hg.comp e.symm.measurable) e.measurable]
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]

variable {ι : Type*} [Fintype ι]

/-- The product of `p` standard normal laws on `ℝ^p` has Lebesgue density `∏ φ(yᵢ)`: the two
measures agree on boxes by Fubini for a product of functions of separate coordinates. -/
lemma pi_gaussianReal_eq_withDensity_prod :
    Measure.pi (fun _ : ι ↦ gaussianReal 0 1) =
      volume.withDensity (fun y : ι → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  have hint : Integrable (fun y : ι → ℝ ↦ ∏ i, (s i).indicator (gaussianPDFReal 0 1) (y i))
      (volume : Measure (ι → ℝ)) :=
    Integrable.fintype_prod fun i ↦ (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have hind : (univ.pi s).indicator
      (fun y : ι → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) =
      fun y ↦ ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (y i)) := by
    funext y
    by_cases hy : y ∈ univ.pi s
    · rw [indicator_of_mem hy]
      congr 1
      exact Finset.prod_congr rfl fun i _ ↦ (indicator_of_mem (hy i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hy]
      simp only [Set.mem_univ_pi, not_forall] at hy
      obtain ⟨i, hi⟩ := hy
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _),
        ENNReal.ofReal_zero]
  have hnn : ∀ i x, 0 ≤ (s i).indicator (gaussianPDFReal 0 1) x := fun i x ↦
    indicator_nonneg (fun x _ ↦ gaussianPDFReal_nonneg 0 1 x) x
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs), hind,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun y ↦ Finset.prod_nonneg fun i _ ↦ hnn i (y i)),
    integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg fun i _ ↦ integral_nonneg (hnn i)]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

variable [DecidableEq ι]

/-- An invertible affine map `y ↦ m + B y` of `ℝ^p` scales Lebesgue measure by `|det B|⁻¹`. -/
lemma map_mulVec_add_volume (m : ι → ℝ) {B : Matrix ι ι ℝ} (hB : B.det ≠ 0) :
    (volume : Measure (ι → ℝ)).map (fun y ↦ m + B *ᵥ y) =
      ENNReal.ofReal |(B.det)⁻¹| • volume := by
  have hfun : (fun y ↦ m + B *ᵥ y) = (fun z ↦ m + z) ∘ ⇑(Matrix.toLin' B) := by
    funext y
    simp only [Function.comp_apply, Matrix.toLin'_apply]
  have hc : Continuous ⇑(Matrix.toLin' B) := (Matrix.toLin' B).continuous_of_finiteDimensional
  rw [hfun, ← Measure.map_map (measurable_const_add m) hc.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (f := Matrix.toLin' B)
      (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin', Measure.map_smul,
    Measure.IsAddLeftInvariant.map_add_left_eq_self m]
  exact (measurable_const_add m).aemeasurable

/-! ### The density -/

/-- The **density of `N(m, S)`**:
`(2π)^{-p/2} det(S)^{-1/2} exp(-(x - m)ᵀ S⁻¹ (x - m) / 2)`, written with `(√(2π))^p` and
`√det S`. It is the Lebesgue density of `multivariateGaussian m S` for positive definite `S`. -/
noncomputable def mvGaussianPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√S.det)⁻¹ *
    Real.exp (-(1 / 2) * quadForm S⁻¹ (x - m))

/-- **The density of a nonsingular multivariate normal law.** For `S` positive definite,
`N(m, S) = φ_{m,S} · Lebesgue`. The standard Gaussian is the product of `p` standard normal laws
(density `∏ φ`), and `N(m, S)` is its image under `y ↦ m + √S y`; the change of variables has
Jacobian `det √S = √det S`, and `‖(√S)⁻¹ v‖² = vᵀ S⁻¹ v`. -/
theorem multivariateGaussian_eq_withDensity_mvGaussianPDF {m : EuclideanSpace ℝ ι}
    {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    multivariateGaussian m S =
      volume.withDensity (fun x ↦ ENNReal.ofReal (mvGaussianPDF m S x)) := by
  set B := CFC.sqrt S with hBdef
  set m' := WithLp.ofLp m with hm
  have hB0 : 0 ≤ B := CFC.sqrt_nonneg S
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hBt : Bᵀ = B := by
    have := hB0.isSelfAdjoint
    rwa [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hBdet : 0 < B.det := by
    have h1 : 0 ≤ B.det := (nonneg_iff_posSemidef.mp hB0).det_nonneg
    have h2 : B.det * B.det = S.det := by rw [← det_mul, hBB]
    refine h1.lt_of_ne fun h ↦ ?_
    rw [← h, zero_mul] at h2
    exact hS.det_pos.ne' h2.symm
  have hdetS : √S.det = B.det := by rw [← hBB, det_mul, Real.sqrt_mul_self hBdet.le]
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet.ne'
  have hc1 : Continuous fun y : ι → ℝ ↦ B *ᵥ y :=
    (Matrix.mulVecLin B).continuous_of_finiteDimensional
  have hc2 : Continuous fun y : ι → ℝ ↦ B⁻¹ *ᵥ y :=
    (Matrix.mulVecLin B⁻¹).continuous_of_finiteDimensional
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
    { toFun := fun y ↦ m' + B *ᵥ y
      invFun := fun z ↦ B⁻¹ *ᵥ (z - m')
      left_inv := fun y ↦ by
        simp only [add_sub_cancel_left, mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
      right_inv := fun z ↦ by
        simp only [mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec, add_sub_cancel]
      measurable_toFun := (continuous_const.add hc1).measurable
      measurable_invFun := (hc2.comp (continuous_id.sub continuous_const)).measurable }
  have hΦ : Measurable fun y : ι → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i)) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i))
  set E := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hmvn : multivariateGaussian m S =
      ((Measure.pi fun _ : ι ↦ gaussianReal 0 1).map e).map E := by
    rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop)
      (by fun_prop), Measure.map_map E.measurable e.measurable]
    congr 1
  have hvol : (volume : Measure (EuclideanSpace ℝ ι)) = (volume : Measure (ι → ℝ)).map E :=
    (PiLp.volume_preserving_toLp ι).map_eq.symm
  have hq : ∀ v : ι → ℝ, (B⁻¹ *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ v) = v ⬝ᵥ (S⁻¹ *ᵥ v) := fun v ↦ by
    rw [show (B⁻¹ *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ v) = v ⬝ᵥ (B⁻¹ᵀ *ᵥ (B⁻¹ *ᵥ v)) by
      rw [dotProduct_mulVec v B⁻¹ᵀ, vecMul_transpose], mulVec_mulVec, transpose_nonsing_inv, hBt,
      ← Matrix.mul_inv_rev, hBB]
  have hprod : ∀ u : ι → ℝ, ∏ i, gaussianPDFReal 0 1 (u i) =
      ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * Real.exp (-(u ⬝ᵥ u) / 2) := fun u ↦ by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum, inv_pow]
    congr 2
    simp only [dotProduct, sq, neg_div, Finset.sum_neg_distrib, Finset.sum_div]
  have hg : Measurable fun z : ι → ℝ ↦ ENNReal.ofReal |(B.det)⁻¹| *
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 ((B⁻¹ *ᵥ (z - m')) i)) :=
    (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ ↦
      (measurable_gaussianPDFReal 0 1).comp ((measurable_pi_apply i).comp
        (hc2.comp (continuous_id.sub continuous_const)).measurable))).const_mul _
  have hdens : (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map e =
      volume.withDensity (fun z : ι → ℝ ↦ ENNReal.ofReal |(B.det)⁻¹| *
        ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 ((B⁻¹ *ᵥ (z - m')) i))) := by
    rw [pi_gaussianReal_eq_withDensity_prod, map_withDensity_of_measurableEquiv _ e hΦ,
      show (⇑e : (ι → ℝ) → ι → ℝ) = fun y ↦ m' + B *ᵥ y from rfl,
      map_mulVec_add_volume m' hBdet.ne', withDensity_smul_measure,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    rfl
  rw [hmvn, hdens, map_withDensity_of_measurableEquiv _ E hg, hvol]
  congr 1
  funext x
  change ENNReal.ofReal |(B.det)⁻¹| *
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 ((B⁻¹ *ᵥ (WithLp.ofLp x - m')) i)) = _
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  have h12 : ∀ q : ℝ, -(1 / 2) * q = -q / 2 := fun q ↦ by ring
  rw [hprod, hq, abs_inv, abs_of_pos hBdet, mvGaussianPDF, quadForm, WithLp.ofLp_sub, hdetS, h12]
  ring

/-! ### Affine images and the normal approximation -/

/-- **Affine images of a centered normal law**: the image of `N(0, S)` under `u ↦ m + c u` with
`c ≥ 0` is `N(m, c² S)`; the matrix square root of `c² S` is `c √S`. -/
lemma multivariateGaussian_map_affine {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (m : EuclideanSpace ℝ ι) {c : ℝ} (hc : 0 ≤ c) :
    (multivariateGaussian 0 S).map (fun u ↦ m + c • u) = multivariateGaussian m (c ^ 2 • S) := by
  have hsq : CFC.sqrt (c ^ 2 • S) = c • CFC.sqrt S := by
    refine CFC.sqrt_unique ?_ (smul_nonneg hc (CFC.sqrt_nonneg S))
    rw [smul_mul_smul_comm, CFC.sqrt_mul_sqrt_self S (nonneg_iff_posSemidef.2 hS), sq]
  unfold multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop), hsq]
  congr 1
  funext x
  simp [map_smul]

/-- The normalizing constant `(2π)^{-p/2} √det M` of `N(0, M⁻¹)`. -/
noncomputable def gaussianNormConst (M : Matrix ι ι ℝ) : ℝ :=
  ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * √M.det

lemma gaussianNormConst_pos {M : Matrix ι ι ℝ} (hM : M.PosDef) : 0 < gaussianNormConst M := by
  have := hM.det_pos
  unfold gaussianNormConst
  positivity

/-- **The density of the normal approximation.** For `M` positive definite and `n > 0`, the image
of `N(0, M⁻¹)` under `u ↦ m + n^{-1/2} u`, that is `N(m, n⁻¹ M⁻¹)`, has Lebesgue density
`(√n)^p (2π)^{-p/2} √det M · exp(-(n/2) (θ - m)ᵀ M (θ - m))`. -/
theorem map_affine_multivariateGaussian_inv_eq_withDensity {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (m : EuclideanSpace ℝ ι) {n : ℝ} (hn : 0 < n) :
    (multivariateGaussian 0 M⁻¹).map (fun u ↦ m + (√n)⁻¹ • u) =
      volume.withDensity fun θ ↦ ENNReal.ofReal ((√n) ^ Fintype.card ι * gaussianNormConst M *
        Real.exp (-(n / 2) * quadForm M (θ - m))) := by
  have hMi : M⁻¹.PosDef := hM.inv
  have hc2 : ((√n)⁻¹) ^ 2 = n⁻¹ := by rw [inv_pow, Real.sq_sqrt hn.le]
  rw [multivariateGaussian_map_affine hMi.posSemidef m (inv_nonneg.2 (Real.sqrt_nonneg n)), hc2,
    multivariateGaussian_eq_withDensity_mvGaussianPDF (hMi.smul (inv_pos.2 hn))]
  congr 1
  funext θ
  congr 1
  have hdS := hM.det_pos
  have hdet : (n⁻¹ • M⁻¹).det = (n⁻¹) ^ Fintype.card ι * M.det⁻¹ := by
    rw [Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hinv : (n⁻¹ • M⁻¹)⁻¹ = n • M := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, Matrix.mul_nonsing_inv M hdS.ne'.isUnit, mul_inv_cancel₀ hn.ne',
      one_smul]
  have hsq : √((n⁻¹) ^ Fintype.card ι * M.det⁻¹) = ((√n) ^ Fintype.card ι)⁻¹ * (√M.det)⁻¹ := by
    have hp : n ^ Fintype.card ι = ((√n) ^ Fintype.card ι) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hn.le]
    rw [Real.sqrt_mul (pow_nonneg (inv_nonneg.2 hn.le) _), Real.sqrt_inv, inv_pow,
      Real.sqrt_inv, hp, Real.sqrt_sq (by positivity)]
  have hq : quadForm (n • M) (θ - m) = n * quadForm M (θ - m) := by
    simp [quadForm, smul_mulVec, dotProduct_smul]
  rw [mvGaussianPDF, hdet, hinv, hsq, hq, gaussianNormConst]
  have hs : 0 < √n := Real.sqrt_pos.2 hn
  field_simp

/-! ### Gaussian mass integrals -/

/-- The **Gaussian mass** `G_p(b) = (π/b)^{p/2}`, the value of `∫ exp(-b ‖v‖²) dv` on `ℝ^p` for
`b > 0` (`integral_exp_neg_mul_sq_norm_sub`). -/
noncomputable def gaussianMass (ι : Type*) [Fintype ι] (b : ℝ) : ℝ :=
  (Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2)

omit [DecidableEq ι] in
lemma gaussianMass_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ gaussianMass ι b := by
  unfold gaussianMass
  have := Real.pi_pos
  positivity

omit [DecidableEq ι] in
/-- The Gaussian kernel `θ ↦ exp(-b ‖θ - m‖²)` is integrable for `b > 0`. -/
lemma integrable_exp_neg_mul_sq_norm_sub {b : ℝ} (hb : 0 < b) (m : EuclideanSpace ℝ ι) :
    Integrable fun θ : EuclideanSpace ℝ ι ↦ Real.exp (-b * ‖θ - m‖ ^ 2) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ ι)
    (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  have h2 : Integrable fun v : EuclideanSpace ℝ ι ↦ Real.exp (-b * ‖v‖ ^ 2) := by
    refine h.congr (ae_of_all _ fun v ↦ ?_)
    have e : -(b : ℂ) * (‖v‖ : ℂ) ^ 2 + 0 * inner ℝ (0 : EuclideanSpace ℝ ι) v =
        ((-b * ‖v‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    simp only [e, Complex.norm_exp_ofReal]
  exact h2.comp_sub_right m

omit [DecidableEq ι] in
/-- **The Gaussian mass integral**: `∫ exp(-b ‖θ - m‖²) dθ = (π/b)^{p/2}` for `b > 0`. -/
lemma integral_exp_neg_mul_sq_norm_sub {b : ℝ} (hb : 0 < b) (m : EuclideanSpace ℝ ι) :
    ∫ θ : EuclideanSpace ℝ ι, Real.exp (-b * ‖θ - m‖ ^ 2) = gaussianMass ι b := by
  rw [integral_sub_right_eq_self (fun v : EuclideanSpace ℝ ι ↦ Real.exp (-b * ‖v‖ ^ 2)) m,
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace, gaussianMass]

omit [DecidableEq ι] in
/-- **Scaling of the Gaussian mass**: `(√n)^p G_p(n b) = G_p(b)` for `n, b > 0`. -/
lemma sqrt_pow_mul_gaussianMass {n b : ℝ} (hn : 0 < n) (hb : 0 < b) :
    (√n) ^ Fintype.card ι * gaussianMass ι (n * b) = gaussianMass ι b := by
  unfold gaussianMass
  have h1 : (√n) ^ Fintype.card ι = n ^ ((Fintype.card ι : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    ring_nf
  rw [h1, show Real.pi / (n * b) = n⁻¹ * (Real.pi / b) by field_simp,
    Real.mul_rpow (inv_nonneg.2 hn.le) (by positivity), Real.inv_rpow hn.le, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

end PosteriorLimit

end CausalInference
