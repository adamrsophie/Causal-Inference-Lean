/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolution
public import CausalInference.Estimation.VectorCLT
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Regular asymptotically linear estimators

Let `T` be asymptotically linear at `θ₀` under `P_θ₀` with influence function `φ` (square
integrable, mean zero) in a family regular at `θ₀` with positive information `I = I(θ₀)` and score
`s = s(θ₀; ·)`. Under the local alternative `θ₀ + h/√n`, the law of `√n (T_n - θ₀ - h/√n)`
converges weakly to `N((E[φ s] - 1) h, E[φ²])`. Hence `T` is regular in Hájek's sense exactly
when `E[φ s] = 1`, and then its limit is `N(0, E[φ²])`. For such an estimator
`φ = I⁻¹ s + (φ - I⁻¹ s)` with the second term orthogonal to the score, so
`E[φ²] = I⁻¹ + E[(φ - I⁻¹ s)²] ≥ I⁻¹` with equality exactly when `φ = I⁻¹ s` almost everywhere:
the convolution theorem for linear estimators.

The proof: by the multivariate central limit theorem `(√n (T_n - θ₀), S_n)`, with
`S_n = n^{-1/2} ∑_{i < n} s(O_i)`, converges to a centered bivariate Gaussian law with
covariance `E[φ s]`; local asymptotic normality replaces `h S_n - h² I / 2` by the log likelihood
ratio; Le Cam's third lemma gives the limit under the alternative as an exponential tilt, which a
Gaussian computation identifies as a shift by `h E[φ s]`.

## Main results

* `CausalInference.integral_mul_exp_multivariateGaussian`: the exponential tilt of a centered
  bivariate Gaussian law, `E[f(X) e^{h Z - h² Var Z / 2}] = E[f(X + h Cov(X, Z))]`.
* `CausalInference.ParametricFamily.tendsto_integral_pi_law_of_isAsymptoticallyLinear`: the limit
  law `N((E[φ s] - 1) h, E[φ²])` under local alternatives.
* `CausalInference.ParametricFamily.exists_isHajekRegular_iff_integral_mul_score_eq_one`: regular
  if and only if `E[φ s] = 1`; `isHajekRegular_of_integral_mul_score_eq_one` gives the limit.
* `CausalInference.ParametricFamily.isHajekRegular_of_isAsymptoticallyLinear_inv_fisherInfo`:
  the efficient case `φ = I⁻¹ s`, which is `isHajekRegular_of_isAsymptoticallyLinear`.
* `CausalInference.ParametricFamily.integral_sq_eq_inv_fisherInfo_add_of_isHajekRegular`,
  `inv_fisherInfo_le_integral_sq_of_isHajekRegular`,
  `integral_sq_eq_inv_fisherInfo_iff_of_isHajekRegular`: the decomposition, the bound and its
  equality case.

The instances are in `CausalInference.Estimation.HajekRegularLinearExamples`.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; L. Le Cam (1960),
*Locally asymptotically normal families of distributions*, University of California Publications
in Statistics; A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 6 to 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

/-! ### The exponential tilt of a bivariate Gaussian law -/

section BivariateTilt

/-- **The exponential tilt of a centered bivariate Gaussian law.** Let `(X, Z)` have the law
`N(0, Σ)` on `ℝ²` with `Σ₁₁ = I > 0`. Tilting by the likelihood ratio `e^{h Z - h² I / 2}` shifts
`X` by `h Σ₀₁ = h Cov(X, Z)`: `E[f(X) e^{h Z - h² I / 2}] = E[f(X + h Σ₀₁)]`. The residual
`W = X - (Σ₀₁ / I) Z` is uncorrelated with `Z`, hence independent of it (the pair is Gaussian),
and the shift identity of `N(0, I)` applies to `Z` for each fixed `W`. -/
theorem integral_mul_exp_multivariateGaussian {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef)
    (hI : 0 < S 1 1) (h : ℝ) (f : ℝ →ᵇ ℝ) :
    ∫ v, f (v 0) * Real.exp (h * v 1 - h ^ 2 * S 1 1 / 2) ∂multivariateGaussian 0 S =
      ∫ v, f (v 0 + h * S 0 1) ∂multivariateGaussian 0 S := by
  set ρ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S with hρ
  set I := S 1 1 with hIdef
  set a := S 0 1 / I with ha
  have hm0 : MemLp (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) 2 ρ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp_memLp' IsGaussian.memLp_two_id
  have hm1 : MemLp (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) 2 ρ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).comp_memLp' IsGaussian.memLp_two_id
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
    ContinuousLinearMap.prod
      ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) -
        a • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ))
      (EuclideanSpace.proj (1 : Fin 2))
  have hL : ∀ v, L v = (v 0 - a * v 1, v 1) := fun v ↦ rfl
  have hG : HasGaussianLaw (fun v ↦ (v 0 - a * v 1, v 1)) ρ := by
    have e : (fun v : EuclideanSpace ℝ (Fin 2) ↦ (v 0 - a * v 1, v 1)) = ⇑L :=
      funext fun v ↦ (hL v).symm
    rw [e]
    exact (IsGaussian.hasGaussianLaw_id (μ := ρ)).map L
  have hcov : cov[fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0 - a * v 1, fun v ↦ v 1; ρ] = 0 := by
    rw [covariance_fun_sub_left hm0 (hm1.const_mul a) hm1, covariance_const_mul_left,
      covariance_eval_multivariateGaussian hS, covariance_eval_multivariateGaussian hS, ha]
    field_simp
    ring
  have hind := hG.indepFun_of_covariance_eq_zero hcov
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1 hind
  have hZ : ρ.map (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) = gaussianReal 0 I.toNNReal :=
    (measurePreserving_eval_multivariateGaussian hS (i := 1)).map_eq
  have hWZm : Measurable fun v : EuclideanSpace ℝ (Fin 2) ↦ (v 0 - a * v 1, v 1) := by fun_prop
  rw [hZ] at hprod
  set νW := ρ.map fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0 - a * v 1 with hνW
  have : IsProbabilityMeasure νW :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  have hv : I.toNNReal ≠ 0 := by simpa using hI
  have hIc : ((I.toNNReal : ℝ≥0) : ℝ) = I := Real.coe_toNNReal I hI.le
  have hint : Integrable (fun p : ℝ × ℝ ↦ f (p.1 + a * p.2) *
      Real.exp (h * p.2 - h ^ 2 * I / 2)) (νW.prod (gaussianReal 0 I.toNNReal)) := by
    have hE : Integrable (fun p : ℝ × ℝ ↦ (1 : ℝ) * Real.exp (h * p.2 - h ^ 2 * I / 2))
        (νW.prod (gaussianReal 0 I.toNNReal)) := by
      refine (integrable_const (1 : ℝ)).mul_prod
        (g := fun z ↦ Real.exp (h * z - h ^ 2 * I / 2)) ?_
      have := (integrable_exp_mul_gaussianReal (μ := 0) (v := I.toNNReal) h).mul_const
        (Real.exp (-(h ^ 2 * I / 2)))
      refine this.congr (Eventually.of_forall fun z ↦ ?_)
      simp only [← Real.exp_add]
      ring_nf
    refine (hE.const_mul ‖f‖).mono' (by fun_prop) (Eventually.of_forall fun p ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), one_mul]
    exact mul_le_mul_of_nonneg_right
      (by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _) (Real.exp_pos _).le
  have hint2 : Integrable (fun p : ℝ × ℝ ↦ f (p.1 + a * (p.2 + h * I)))
      (νW.prod (gaussianReal 0 I.toNNReal)) :=
    Integrable.of_bound (by fun_prop) ‖f‖ (Eventually.of_forall fun p ↦ f.norm_coe_le_norm _)
  have e1 : ∫ v, f (v 0) * Real.exp (h * v 1 - h ^ 2 * I / 2) ∂ρ =
      ∫ p, f (p.1 + a * p.2) * Real.exp (h * p.2 - h ^ 2 * I / 2)
        ∂(ρ.map fun v : EuclideanSpace ℝ (Fin 2) ↦ (v 0 - a * v 1, v 1)) := by
    rw [integral_map hWZm.aemeasurable (by fun_prop)]
    simp only [sub_add_cancel]
  have e2 : ∫ v, f (v 0 + h * S 0 1) ∂ρ = ∫ p, f (p.1 + a * (p.2 + h * I))
        ∂(ρ.map fun v : EuclideanSpace ℝ (Fin 2) ↦ (v 0 - a * v 1, v 1)) := by
    rw [integral_map hWZm.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    simp only
    congr 1
    rw [ha]
    field_simp
    ring
  rw [e1, e2, hprod, integral_prod _ hint, integral_prod _ hint2]
  refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
  have := integral_mul_exp_gaussianReal hv h (f := fun z ↦ f (w + a * z)) (by fun_prop)
  simp only [hIc] at this
  exact this

end BivariateTilt

open BiasAnalysis.MeasurementError (covMatrix)

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {F : ParametricFamily ℝ S} [SigmaFinite F.ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → S} {θ₀ : ℝ}

omit [SigmaFinite F.ν] [IsProbabilityMeasure μ] in
/-- A function of the observation has its integral under `P_θ₀`. -/
lemma integral_comp_eq_integral_law (hO : IsIIDSample O μ) (hlaw : μ.map (O 0) = F.law θ₀)
    {g : S → ℝ} (hg : Measurable g) : μ[fun ω ↦ g (O 0 ω)] = ∫ x, g x ∂F.law θ₀ := by
  rw [← integral_map (hO.aemeasurable 0) hg.aestronglyMeasurable, hlaw]

/-- **The limit law of an asymptotically linear estimator under local alternatives.** Let `O` be
an i.i.d. sample with law `P_θ₀`, the family regular at `θ₀` with positive information and the
smoothness of `logLikRatio_sub_tendstoInMeasure`, and `T` asymptotically linear at `θ₀` with
influence function `φ` (square integrable with mean zero). Then under the sample family at
`θ₀ + h/√n`, the law of `√n (T_n - θ₀ - h/√n)` converges weakly to `N((E[φ s] - 1) h, E[φ²])`,
where `s = s(θ₀; ·)` and the expectations are under `P_θ₀`. By the multivariate central limit
theorem `(√n (T_n - θ₀), S_n)` converges to a centered Gaussian law with covariance `E[φ s]`; by
local asymptotic normality and Le Cam's third lemma the law under the alternative is the
exponential tilt of that limit, which `integral_mul_exp_multivariateGaussian` computes. -/
theorem tendsto_integral_pi_law_of_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    {φ : S → ℝ} (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀ φ O μ)
    (h : ℝ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ x, f (√(n : ℝ) * (T n x - (θ₀ + h / √(n : ℝ))))
      ∂(F.pi n).law (θ₀ + h / √(n : ℝ))) atTop
      (𝓝 (∫ y, f y ∂gaussianReal ((∫ x, φ x * F.score θ₀ x ∂F.law θ₀ - 1) * h)
        (∫ x, φ x ^ 2 ∂F.law θ₀).toNNReal)) := by
  set I := F.fisherInfo θ₀ with hIdef
  have hX0 := hO.aemeasurable 0
  have hsm := hs.measurable_score
  have hmem : MemLp (fun ω ↦ F.score θ₀ (O 0 ω)) 2 μ :=
    (memLp_map_measure_iff hsm.aestronglyMeasurable hX0).1 (by rw [hlaw]; exact hreg.memLp_score)
  have hs0 : μ[fun ω ↦ F.score θ₀ (O 0 ω)] = 0 := by
    rw [integral_comp_eq_integral_law hO hlaw hsm, hreg.integral_score_eq_zero]
  /- The score mean is asymptotically linear with influence function the score. -/
  have hALs : IsAsymptoticallyLinear (sampleMean (F.score θ₀) O) 0 (F.score θ₀) O μ := by
    have := sampleMean_isAsymptoticallyLinear hsm hmem
    simp only [hs0, sub_zero] at this
    exact this
  set ψ : Fin 2 → S → ℝ := ![φ, F.score θ₀] with hψ
  set C := covMatrix μ fun i ω ↦ ψ i (O 0 ω) with hC
  have hALv : ∀ i, IsAsymptoticallyLinear (![fun n ω ↦ T n fun i ↦ O i ω,
      sampleMean (F.score θ₀) O] i) (![θ₀, 0] i) (ψ i) O μ := fun i ↦ by
    fin_cases i
    · exact hlin
    · exact hALs
  have hR : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ O i ω) μ := fun n ↦
    AEMeasurable.of_eval fun i ↦ hO.aemeasurable i
  have hmeasv : ∀ i n, AEMeasurable (![fun n ω ↦ T n fun i ↦ O i ω,
      sampleMean (F.score θ₀) O] i n) μ := fun i n ↦ by
    fin_cases i
    · exact (hTm n).comp_aemeasurable (hR n)
    · exact (Finset.aemeasurable_fun_sum _ fun k _ ↦
        hsm.comp_aemeasurable (hO.aemeasurable k)).const_mul _
  have hvec := IsAsymptoticallyLinear.tendstoInDistribution_multivariateGaussian hO hALv
    hmeasv (Y := id) HasLaw.id
  have hCpos : C.PosSemidef := posSemidef_covMatrix fun i ↦ (hALv i).memLp
  have hφm := hlin.measurable
  have hC00 : C 0 0 = ∫ x, φ x ^ 2 ∂F.law θ₀ := by
    simp only [hC, covMatrix, Matrix.of_apply, hψ, Matrix.cons_val_zero]
    rw [covariance_self hlin.memLp.aemeasurable,
      variance_of_integral_eq_zero hlin.memLp.aemeasurable hlin.integral_eq_zero,
      integral_comp_eq_integral_law hO hlaw (hφm.pow_const 2)]
  have hC01 : C 0 1 = ∫ x, φ x * F.score θ₀ x ∂F.law θ₀ := by
    simp only [hC, covMatrix, Matrix.of_apply, hψ, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [covariance_eq_sub hlin.memLp hmem, hs0, mul_zero, sub_zero]
    exact integral_comp_eq_integral_law hO hlaw (hφm.mul hsm)
  have hC11 : C 1 1 = I := by
    simp only [hC, covMatrix, Matrix.of_apply, hψ, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [covariance_self hmem.aemeasurable, variance_of_integral_eq_zero hmem.aemeasurable hs0,
      integral_score_sq_eq_fisherInfo hX0 hlaw hsm]
  set G : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun v ↦ (v 0, h * v 1 - h ^ 2 * I / 2) with hG
  have hGc : Continuous G := by fun_prop
  set ρ := (multivariateGaussian 0 C).map G with hρ
  have hj2 := (hvec.continuous_comp hGc).of_hasLaw ⟨hGc.aemeasurable, rfl⟩ HasLaw.id
  have hlan := logLikRatio_sub_tendstoInMeasure hO hlaw hreg hs hdl h
  have hXm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) * (T n (fun i ↦ O i ω) - θ₀)) μ :=
    fun n ↦ (measurable_const.mul ((hTm n).sub measurable_const)).comp_aemeasurable (hR n)
  have hj3 : TendstoInDistribution (fun (k : ℕ) ω ↦
      (√(k : ℝ) * (T k (fun i ↦ O i ω) - θ₀), F.logLikRatio O θ₀ (θ₀ + h / √(k : ℝ)) k ω))
      atTop id (fun _ ↦ μ) ρ := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hj2 ?_
      fun k ↦ (hXm k).prodMk (aemeasurable_logLikRatio hO _ k)
    have hp := (tendstoInMeasure_const (μ := μ) (0 : ℝ)).prodMk hlan
    refine hp.congr' (Eventually.of_forall fun k ↦ Eventually.of_forall fun ω ↦ ?_)
      (Eventually.of_forall fun _ ↦ rfl)
    simp only [Pi.sub_apply]
    simp only [hG, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val',
      Matrix.cons_val_fin_one, sampleMean, Function.comp_apply, PiLp.smul_apply, PiLp.sub_apply,
      Matrix.cons_val_zero, smul_eq_mul, Matrix.cons_val_one, sub_zero, Prod.mk_sub_mk, sub_self,
      Prod.mk.injEq, sub_right_inj, true_and]
    rw [← mul_assoc (√(k : ℝ)), sqrt_mul_inv_self]
  have hI' : 0 < C 1 1 := hC11 ▸ hI
  have hmass : ∫ p, Real.exp p.2 ∂ρ = 1 := by
    rw [hρ, integral_map hGc.aemeasurable (by fun_prop)]
    have e := integral_mul_exp_multivariateGaussian hCpos hI' h
      (BoundedContinuousFunction.const _ 1)
    simp only [BoundedContinuousFunction.const_apply, one_mul, integral_const, smul_eq_mul,
      mul_one, probReal_univ, hC11] at e
    exact e
  let f' : ℝ →ᵇ ℝ := f.compContinuous ⟨fun y ↦ y - h, by fun_prop⟩
  have hf' : ∀ y, f' y = f (y - h) := fun y ↦ rfl
  have h3 := tendsto_integral_pi_law_of_tendstoInDistribution hO hlaw hreg.mem_nhds
    hreg.support hTm (m := fun k ↦ k) tendsto_id h hj3 hmass f'
  have hmap : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) C).map (fun v ↦ v 0) =
      gaussianReal 0 (C 0 0).toNNReal := by
    simpa using (measurePreserving_eval_multivariateGaussian hCpos (μ := 0) (i := 0)).map_eq
  have hlim : ∫ p, f' p.1 * Real.exp p.2 ∂ρ =
      ∫ y, f y ∂gaussianReal ((∫ x, φ x * F.score θ₀ x ∂F.law θ₀ - 1) * h)
        (∫ x, φ x ^ 2 ∂F.law θ₀).toNNReal := by
    rw [← hC00, ← hC01, hρ, integral_map hGc.aemeasurable (by fun_prop)]
    have e := integral_mul_exp_multivariateGaussian hCpos hI' h f'
    rw [hC11] at e
    simp only [hG]
    rw [e, show (C 0 1 - 1) * h = 0 + (C 0 1 - 1) * h by ring, ← gaussianReal_map_add_const,
      integral_map (by fun_prop) f.continuous.aestronglyMeasurable, ← hmap,
      integral_map (by fun_prop) (by fun_prop)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hf']
    congr 1
    ring
  rw [hlim] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs0 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [hf']
  congr 1
  field_simp
  ring

/-- **An asymptotically linear estimator with `E[φ s] = 1` is regular.** Under the hypotheses of
`tendsto_integral_pi_law_of_isAsymptoticallyLinear`, if the influence function has unit
covariance with the score, `E_θ₀[φ s(θ₀; ·)] = 1`, then `T` is regular at `θ₀` in Hájek's sense
with limit `N(0, E_θ₀[φ²])`. -/
theorem isHajekRegular_of_integral_mul_score_eq_one (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    {φ : S → ℝ} (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀ φ O μ)
    (hc : ∫ x, φ x * F.score θ₀ x ∂F.law θ₀ = 1) :
    F.IsHajekRegular T θ₀ (gaussianReal 0 (∫ x, φ x ^ 2 ∂F.law θ₀).toNNReal) := by
  refine ⟨hTm, fun h f ↦ ?_⟩
  have := tendsto_integral_pi_law_of_isAsymptoticallyLinear hO hlaw hreg hs hdl hI hTm hlin h f
  rwa [hc, sub_self, zero_mul] at this

/-- **Regularity of an asymptotically linear estimator is unit covariance with the score.** Under
the hypotheses of `tendsto_integral_pi_law_of_isAsymptoticallyLinear`, `T` is regular at `θ₀` in
Hájek's sense with some limit law if and only if `E_θ₀[φ s(θ₀; ·)] = 1`; the limit is then
`N(0, E_θ₀[φ²])` (`isHajekRegular_of_integral_mul_score_eq_one`). For the converse, the limits
under `h = 0` and `h = 1` are `N(0, E[φ²])` and `N(E[φ s] - 1, E[φ²])`, and both equal the limit
law of regularity, so their means agree. -/
theorem exists_isHajekRegular_iff_integral_mul_score_eq_one (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    {φ : S → ℝ} (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀ φ O μ) :
    (∃ L : Measure ℝ, F.IsHajekRegular T θ₀ L) ↔ ∫ x, φ x * F.score θ₀ x ∂F.law θ₀ = 1 := by
  refine ⟨fun ⟨L, hL⟩ ↦ ?_, fun hc ↦
    ⟨_, isHajekRegular_of_integral_mul_score_eq_one hO hlaw hreg hs hdl hI hTm hlin hc⟩⟩
  set c := ∫ x, φ x * F.score θ₀ x ∂F.law θ₀
  set V := (∫ x, φ x ^ 2 ∂F.law θ₀).toNNReal
  have key : ∀ f : ℝ →ᵇ ℝ, ∫ y, f y ∂gaussianReal 0 V = ∫ y, f y ∂gaussianReal (c - 1) V := by
    intro f
    have h0 := tendsto_integral_pi_law_of_isAsymptoticallyLinear hO hlaw hreg hs hdl hI hTm
      hlin 0 f
    have h1 := tendsto_integral_pi_law_of_isAsymptoticallyLinear hO hlaw hreg hs hdl hI hTm
      hlin 1 f
    rw [mul_zero] at h0
    rw [mul_one] at h1
    exact (tendsto_nhds_unique h0 (hL.tendsto 0 f)).trans
      (tendsto_nhds_unique (hL.tendsto 1 f) h1)
  have e := (gaussianReal_ext_iff.1 (ext_of_forall_integral_eq_of_IsFiniteMeasure key)).1
  linarith

omit [SigmaFinite F.ν] [IsProbabilityMeasure μ] in
/-- The efficient influence function `I(θ₀)⁻¹ s(θ₀; ·)` has unit covariance with the score:
`E_θ₀[I⁻¹ s · s] = I⁻¹ I = 1`, for `I(θ₀) > 0`. -/
lemma integral_inv_fisherInfo_mul_score_mul_score (hI : 0 < F.fisherInfo θ₀) :
    ∫ x, (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x * F.score θ₀ x ∂F.law θ₀ = 1 := by
  simp_rw [mul_assoc, ← sq]
  rw [integral_const_mul, ← fisherInfo, inv_mul_cancel₀ hI.ne']

/-- **The efficient case.** Under the hypotheses of
`tendsto_integral_pi_law_of_isAsymptoticallyLinear`, an estimator asymptotically linear with the
efficient influence function `I(θ₀)⁻¹ s(θ₀; ·)` is regular with limit `N(0, I(θ₀)⁻¹)`. This is
`CausalInference.ParametricFamily.isHajekRegular_of_isAsymptoticallyLinear`, recovered from
`isHajekRegular_of_integral_mul_score_eq_one`: the covariance with the score is `1` and the
variance is `I⁻² E[s²] = I⁻¹`. -/
theorem isHajekRegular_of_isAsymptoticallyLinear_inv_fisherInfo (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀
      (fun x ↦ (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) O μ) :
    F.IsHajekRegular T θ₀ (gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal) := by
  have h := isHajekRegular_of_integral_mul_score_eq_one hO hlaw hreg hs hdl hI hTm hlin
    (integral_inv_fisherInfo_mul_score_mul_score hI)
  have hv : ∫ x, ((F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) ^ 2 ∂F.law θ₀ = (F.fisherInfo θ₀)⁻¹ := by
    simp_rw [mul_pow]
    rw [integral_const_mul, ← fisherInfo]
    field_simp
  rwa [hv] at h

/-! ### The convolution structure of a regular linear estimator -/

omit [SigmaFinite F.ν] [IsProbabilityMeasure μ] in
/-- **Orthogonal decomposition of an influence function with unit covariance.** At a regular point
with `I(θ₀) > 0`, let `φ` be square integrable under `P_θ₀` with `E_θ₀[φ s] = 1`, `s = s(θ₀; ·)`.
Then `φ - I⁻¹ s` is orthogonal to the score, `E[(φ - I⁻¹ s) s] = 0`, and
`E[(φ - I⁻¹ s)²] = E[φ²] - I⁻¹`. -/
theorem integral_sub_inv_fisherInfo_mul_score (hreg : F.IsRegularAt θ₀)
    (hI : 0 < F.fisherInfo θ₀) {φ : S → ℝ}
    (hφ : MemLp φ 2 (F.law θ₀)) (hc : ∫ x, φ x * F.score θ₀ x ∂F.law θ₀ = 1) :
    ∫ x, (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) * F.score θ₀ x ∂F.law θ₀ = 0 ∧
      ∫ x, (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) ^ 2 ∂F.law θ₀ =
        ∫ x, φ x ^ 2 ∂F.law θ₀ - (F.fisherInfo θ₀)⁻¹ := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  set I := F.fisherInfo θ₀ with hIdef
  have hs2 := hreg.memLp_score
  have hφs : Integrable (fun x ↦ φ x * F.score θ₀ x) (F.law θ₀) := hφ.integrable_mul hs2
  have hss : Integrable (fun x ↦ F.score θ₀ x ^ 2) (F.law θ₀) := hs2.integrable_sq
  have hφφ : Integrable (fun x ↦ φ x ^ 2) (F.law θ₀) := hφ.integrable_sq
  have hIs : ∫ x, F.score θ₀ x ^ 2 ∂F.law θ₀ = I := rfl
  constructor
  · have e : (fun x ↦ (φ x - I⁻¹ * F.score θ₀ x) * F.score θ₀ x) =
        fun x ↦ φ x * F.score θ₀ x - I⁻¹ * F.score θ₀ x ^ 2 := funext fun x ↦ by ring
    rw [e, integral_sub hφs (hss.const_mul _), integral_const_mul, hc, hIs,
      inv_mul_cancel₀ hI.ne', sub_self]
  · have e : (fun x ↦ (φ x - I⁻¹ * F.score θ₀ x) ^ 2) =
        fun x ↦ φ x ^ 2 - 2 * I⁻¹ * (φ x * F.score θ₀ x) + I⁻¹ ^ 2 * F.score θ₀ x ^ 2 :=
      funext fun x ↦ by ring
    have i1 : Integrable (fun x ↦ 2 * I⁻¹ * (φ x * F.score θ₀ x)) (F.law θ₀) :=
      hφs.const_mul _
    have i2 : Integrable (fun x ↦ φ x ^ 2 - 2 * I⁻¹ * (φ x * F.score θ₀ x)) (F.law θ₀) :=
      hφφ.sub i1
    have i3 : Integrable (fun x ↦ I⁻¹ ^ 2 * F.score θ₀ x ^ 2) (F.law θ₀) := hss.const_mul _
    rw [e, integral_add i2 i3, integral_sub hφφ i1, integral_const_mul, integral_const_mul, hc, hIs]
    field_simp
    ring

omit [SigmaFinite F.ν] in
/-- The influence function of an asymptotically linear estimator is square integrable under
`P_θ₀` when the observations have law `P_θ₀`. -/
lemma _root_.CausalInference.IsAsymptoticallyLinear.memLp_law (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) {θhat : ℕ → Ω → ℝ} {φ : S → ℝ}
    (hlin : IsAsymptoticallyLinear θhat θ₀ φ O μ) : MemLp φ 2 (F.law θ₀) := by
  rw [← hlaw]
  exact (memLp_map_measure_iff hlin.measurable.aestronglyMeasurable (hO.aemeasurable 0)).2
    hlin.memLp

/-- **The convolution structure of a regular asymptotically linear estimator.** Under the
hypotheses of `tendsto_integral_pi_law_of_isAsymptoticallyLinear`, if `T` is regular at `θ₀`
with some limit law, its influence function decomposes as `φ = I⁻¹ s + (φ - I⁻¹ s)` with the
second term orthogonal to the score, and the asymptotic variance splits as
`E[φ²] = I⁻¹ + E[(φ - I⁻¹ s)²]`: the limit `N(0, E[φ²])` is the efficient limit `N(0, I⁻¹)`
convolved with an independent `N(0, E[(φ - I⁻¹ s)²])`. -/
theorem integral_sq_eq_inv_fisherInfo_add_of_isHajekRegular (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    {φ : S → ℝ} (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀ φ O μ)
    (hT : ∃ L : Measure ℝ, F.IsHajekRegular T θ₀ L) :
    ∫ x, (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) * F.score θ₀ x ∂F.law θ₀ = 0 ∧
      ∫ x, φ x ^ 2 ∂F.law θ₀ =
        (F.fisherInfo θ₀)⁻¹ + ∫ x, (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) ^ 2 ∂F.law θ₀ := by
  have hc := (exists_isHajekRegular_iff_integral_mul_score_eq_one hO hlaw hreg hs hdl hI hTm
    hlin).1 hT
  obtain ⟨h1, h2⟩ := integral_sub_inv_fisherInfo_mul_score hreg hI
    (hlin.memLp_law hO hlaw) hc
  exact ⟨h1, by rw [h2]; ring⟩

/-- **The variance bound for regular asymptotically linear estimators.** Under the hypotheses of
`integral_sq_eq_inv_fisherInfo_add_of_isHajekRegular`, `I(θ₀)⁻¹ ≤ E_θ₀[φ²]`, which is the Hájek
bound `CausalInference.ParametricFamily.hajek_convolution_bound` for the limit `N(0, E[φ²])`,
obtained here from `E[φ s] = 1` by the Cauchy-Schwarz decomposition. -/
theorem inv_fisherInfo_le_integral_sq_of_isHajekRegular (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    {φ : S → ℝ} (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀ φ O μ)
    (hT : ∃ L : Measure ℝ, F.IsHajekRegular T θ₀ L) :
    (F.fisherInfo θ₀)⁻¹ ≤ ∫ x, φ x ^ 2 ∂F.law θ₀ := by
  rw [(integral_sq_eq_inv_fisherInfo_add_of_isHajekRegular hO hlaw hreg hs hdl hI hTm hlin
    hT).2]
  exact le_add_of_nonneg_right (integral_nonneg fun x ↦ sq_nonneg _)

/-- **Equality in the bound.** Under the hypotheses of
`integral_sq_eq_inv_fisherInfo_add_of_isHajekRegular`, `E_θ₀[φ²] = I(θ₀)⁻¹` if and only if
`φ = I(θ₀)⁻¹ s(θ₀; ·)` `P_θ₀`-almost everywhere. -/
theorem integral_sq_eq_inv_fisherInfo_iff_of_isHajekRegular (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    (hI : 0 < F.fisherInfo θ₀) {T : ∀ n, (Fin n → S) → ℝ} (hTm : ∀ n, Measurable (T n))
    {φ : S → ℝ} (hlin : IsAsymptoticallyLinear (fun n ω ↦ T n fun i ↦ O i ω) θ₀ φ O μ)
    (hT : ∃ L : Measure ℝ, F.IsHajekRegular T θ₀ L) :
    ∫ x, φ x ^ 2 ∂F.law θ₀ = (F.fisherInfo θ₀)⁻¹ ↔
      φ =ᵐ[F.law θ₀] fun x ↦ (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hreg.mem_nhds)
  have hd := (integral_sq_eq_inv_fisherInfo_add_of_isHajekRegular hO hlaw hreg hs hdl hI hTm hlin
    hT).2
  have hint : Integrable (fun x ↦ (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) ^ 2)
      (F.law θ₀) :=
    ((hlin.memLp_law hO hlaw).sub (hreg.memLp_score.const_mul _)).integrable_sq
  have h0 := integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg
    (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x)) hint
  constructor
  · intro he
    have : ∫ x, (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) ^ 2 ∂F.law θ₀ = 0 := by linarith
    filter_upwards [h0.1 this] with x hx
    have : (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) ^ 2 = 0 := hx
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro hae
    have : ∫ x, (φ x - (F.fisherInfo θ₀)⁻¹ * F.score θ₀ x) ^ 2 ∂F.law θ₀ = 0 :=
      h0.2 (hae.mono fun x hx ↦ by simp [hx])
    rw [hd, this, add_zero]

end ParametricFamily

end CausalInference
