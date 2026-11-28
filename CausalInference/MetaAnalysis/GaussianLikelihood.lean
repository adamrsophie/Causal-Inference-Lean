/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CochranQ
public import CausalInference.Estimation.CramerRao

/-!
# Meta-analysis: the Gaussian likelihood of the common effect model

In the Gaussian common effect model the study estimates are independent with `Yᵢ ~ N(θ, vᵢ)`.
Their joint density, the likelihood `L(θ; y) = ∏ᵢ φ(yᵢ; θ, vᵢ)` (`commonEffectLikelihood`), is
`∏ᵢ (2π vᵢ)^{-1/2} exp(-½ ∑ wᵢ (yᵢ - θ)²)`, so that by the weighted sum of squares decomposition
`∑ wᵢ (yᵢ - θ)² = Q + (∑ wᵢ)(θ̂ - θ)²` the likelihood is uniquely maximized at the pooled
estimate (`commonEffectLikelihood_lt`): **the pooled estimate is the maximum likelihood
estimate**. The log-likelihood has derivative `∑ wᵢ (yᵢ - θ) = (∑ wᵢ)(θ̂ - θ)`
(`hasDerivAt_log_commonEffectLikelihood`).

The model is a dominated parametric family on `ℝ^ι` (`commonEffectFamily`), whose law is
`⊗ᵢ N(θ, vᵢ)` (`commonEffectFamily_law`). The library's `ParametricFamily.pi` is the family of an
i.i.d. sample and does not fit here, since the variances differ across studies; the family is
defined directly. Its score is `∑ wᵢ (yᵢ - θ)` (`commonEffectFamily_score`), the Fisher
information is `∑ wᵢ` (`commonEffectFamily_fisherInfo`), and:

* **the pooled estimate attains the Cramér-Rao bound**: it is efficient
  (`isEfficient_ivwEstimate`, with `ParametricFamily.IsEfficient`), with variance
  `1 / I(θ) = 1 / ∑ wᵢ`;
* **every unbiased estimator has variance at least `1 / ∑ wᵢ`**, when its mean can be
  differentiated under the integral sign (`variance_ivwEstimate_le`), the regularity of the
  Cramér-Rao bound (`ParametricFamily.cramer_rao_unbiased`); the first order interchange of the
  family holds at every `θ` (`commonEffectFamily_derivInterchange`), and the interchange for the
  mean of `θ̂` itself holds (`meanDerivInterchange_ivwEstimate`), so the bound applies to `θ̂`.

## Main definitions

* `commonEffectLikelihood`, `commonEffectFamily`.

## Main results

* `commonEffectLikelihood_eq`, `hasDerivAt_log_commonEffectLikelihood`,
  `commonEffectLikelihood_lt`.
* `commonEffectFamily_law`, `commonEffectFamily_score`, `commonEffectFamily_fisherInfo`,
  `commonEffectFamily_derivInterchange`, `meanDerivInterchange_ivwEstimate`,
  `isEfficient_ivwEstimate`, `variance_ivwEstimate_le`.

## References

* L. V. Hedges and I. Olkin, *Statistical Methods for Meta-Analysis*, Academic Press, 1985.
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset Filter Topology

/-! ### The likelihood and its maximum -/

section Likelihood

variable {ι : Type*} [Fintype ι] {v : ι → ℝ}

/-- The **Gaussian common effect likelihood** `θ ↦ ∏ᵢ φ(yᵢ; θ, vᵢ)`: the joint density of
independent `Yᵢ ~ N(θ, vᵢ)` at the data `y`. -/
noncomputable def commonEffectLikelihood (v : ι → ℝ) (θ : ℝ) (y : ι → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal θ (v i).toNNReal (y i)

/-- The likelihood is `∏ᵢ (2π vᵢ)^{-1/2}` times `exp(-½ ∑ wᵢ (yᵢ - θ)²)`. -/
theorem commonEffectLikelihood_eq (hv : ∀ i, 0 < v i) (θ : ℝ) (y : ι → ℝ) :
    commonEffectLikelihood v θ y = (∏ i, (√(2 * Real.pi * v i))⁻¹) *
      Real.exp (-(1 / 2) * ∑ i, ivWeight v i * (y i - θ) ^ 2) := by
  simp only [commonEffectLikelihood, gaussianPDFReal, Real.coe_toNNReal _ (hv _).le,
    Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ivWeight]
  ring

theorem commonEffectLikelihood_pos (hv : ∀ i, 0 < v i) (θ : ℝ) (y : ι → ℝ) :
    0 < commonEffectLikelihood v θ y :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos _ _ _
    (by rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv i)

/-- The derivative of `u ↦ -½ ∑ wᵢ (yᵢ - u)²` at `θ` is `∑ wᵢ (yᵢ - θ)`. -/
theorem hasDerivAt_neg_half_sum_sq (v y : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun u => -(1 / 2) * ∑ i, ivWeight v i * (y i - u) ^ 2)
      (∑ i, ivWeight v i * (y i - θ)) θ := by
  have hi : ∀ i, HasDerivAt (fun u => ivWeight v i * (y i - u) ^ 2)
      (ivWeight v i * (↑(2 : ℕ) * (y i - θ) ^ (2 - 1) * -1)) θ := fun i =>
    (((hasDerivAt_id' θ).const_sub (y i)).pow 2).const_mul (ivWeight v i)
  convert (HasDerivAt.fun_sum fun i _ => hi i).const_mul (-(1 / 2)) using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The derivative of the likelihood: `∂_θ L(θ) = L(θ) ∑ wᵢ (yᵢ - θ)`. -/
theorem hasDerivAt_commonEffectLikelihood (hv : ∀ i, 0 < v i) (y : ι → ℝ) (θ : ℝ) :
    HasDerivAt (fun u => commonEffectLikelihood v u y)
      (commonEffectLikelihood v θ y * ∑ i, ivWeight v i * (y i - θ)) θ := by
  have he : (fun u => commonEffectLikelihood v u y) = fun u =>
      (∏ i, (√(2 * Real.pi * v i))⁻¹) *
        Real.exp (-(1 / 2) * ∑ i, ivWeight v i * (y i - u) ^ 2) :=
    funext fun u => commonEffectLikelihood_eq hv u y
  rw [he]
  convert ((hasDerivAt_neg_half_sum_sq v y θ).exp).const_mul
    (∏ i, (√(2 * Real.pi * v i))⁻¹) using 1
  rw [commonEffectLikelihood_eq hv]
  ring

/-- **The score equation.** The log-likelihood has derivative
`∑ wᵢ (yᵢ - θ) = (∑ wᵢ)(θ̂ - θ)` at every `θ`; it vanishes exactly at `θ = θ̂`. -/
theorem hasDerivAt_log_commonEffectLikelihood [Nonempty ι] (hv : ∀ i, 0 < v i) (y : ι → ℝ)
    (θ : ℝ) :
    HasDerivAt (fun u => Real.log (commonEffectLikelihood v u y))
      ((∑ i, ivWeight v i) * (ivwEstimate v y - θ)) θ := by
  rw [← sum_ivWeight_mul_sub hv]
  have hC : 0 < ∏ i, (√(2 * Real.pi * v i))⁻¹ := Finset.prod_pos fun i _ =>
    inv_pos.2 (Real.sqrt_pos.2 (by have := hv i; positivity))
  have he : (fun u => Real.log (commonEffectLikelihood v u y)) = fun u =>
      Real.log (∏ i, (√(2 * Real.pi * v i))⁻¹) +
        -(1 / 2) * ∑ i, ivWeight v i * (y i - u) ^ 2 := by
    funext u
    rw [commonEffectLikelihood_eq hv, Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [he]
  exact (hasDerivAt_neg_half_sum_sq v y θ).const_add _

/-- **The pooled estimate is the maximum likelihood estimate**: for positive variances and at
least one study, `L(θ; y) < L(θ̂; y)` for every `θ ≠ θ̂`. Proof: the exponent is
`-½ (Q + (∑ wᵢ)(θ̂ - θ)²)`. -/
theorem commonEffectLikelihood_lt [Nonempty ι] (hv : ∀ i, 0 < v i) (y : ι → ℝ) {θ : ℝ}
    (hθ : θ ≠ ivwEstimate v y) :
    commonEffectLikelihood v θ y < commonEffectLikelihood v (ivwEstimate v y) y := by
  have hW := sum_ivWeight_pos hv
  have hC : 0 < ∏ i, (√(2 * Real.pi * v i))⁻¹ := Finset.prod_pos fun i _ =>
    inv_pos.2 (Real.sqrt_pos.2 (by have := hv i; positivity))
  have h1 := cochranQ_eq_sub hv y θ
  have h2 := cochranQ_eq_sub hv y (ivwEstimate v y)
  have hd : 0 < (∑ i, ivWeight v i) * (ivwEstimate v y - θ) ^ 2 :=
    mul_pos hW (lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 (Ne.symm hθ)))))
  rw [commonEffectLikelihood_eq hv, commonEffectLikelihood_eq hv]
  refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hC
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sub_zero] at h2
  linarith

end Likelihood

/-! ### The common effect model as a parametric family -/

section Family

variable {ι : Type*} [Fintype ι] {v : ι → ℝ}

/-- The **Gaussian common effect model as a dominated parametric family**: sample space `ℝ^ι`
with Lebesgue measure, parameter set `ℝ`, and density the likelihood `∏ᵢ φ(yᵢ; θ, vᵢ)`. -/
noncomputable def commonEffectFamily (hv : ∀ i, 0 < v i) : ParametricFamily ℝ (ι → ℝ) where
  ν := Measure.pi fun _ => volume
  Θ := Set.univ
  density θ y := commonEffectLikelihood v θ y
  measurable_density θ := Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal θ _).comp (measurable_pi_apply i)
  density_nonneg θ _ y := Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _
  integrable_density θ _ := Integrable.fintype_prod
    (f := fun i => gaussianPDFReal θ (v i).toNNReal) fun i => integrable_gaussianPDFReal θ _
  integral_density θ _ := by
    simp only [commonEffectLikelihood]
    rw [integral_fintype_prod_eq_prod (f := fun i => gaussianPDFReal θ (v i).toNNReal)]
    exact Finset.prod_eq_one fun i _ => integral_gaussianPDFReal_eq_one θ (by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv i)

variable (hv : ∀ i, 0 < v i)
include hv

/-- **The law of the family is `⊗ᵢ N(θ, vᵢ)`**: both measures agree on boxes, by Fubini for a
product of indicators. -/
theorem commonEffectFamily_law (θ : ℝ) :
    (commonEffectFamily hv).law θ = Measure.pi fun i => gaussianReal θ (v i).toNNReal := by
  set F := commonEffectFamily hv
  have hv' : ∀ i, (v i).toNNReal ≠ 0 := fun i => by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hv i
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hlaw_i : ∀ i, gaussianReal θ (v i).toNNReal (s i) =
      ENNReal.ofReal (∫ x, (s i).indicator (gaussianPDFReal θ (v i).toNNReal) x) := fun i => by
    rw [gaussianReal_of_var_ne_zero θ (hv' i), withDensity_apply _ (hs i),
      integral_indicator (hs i),
      ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal θ _).integrableOn
        (ae_of_all _ (gaussianPDFReal_nonneg _ _))]
    rfl
  have hprod : (Set.univ.pi s).indicator (fun x : ι → ℝ => F.density θ x) =
      fun x => ∏ i, (s i).indicator (gaussianPDFReal θ (v i).toNNReal) (x i) := by
    ext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_univ_pi] using hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  have hint := (F.integrable_density θ (Set.mem_univ θ)).integrableOn (s := Set.univ.pi s)
  rw [ParametricFamily.law, withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ (F.density_nonneg θ (Set.mem_univ θ))),
    ← integral_indicator (MeasurableSet.univ_pi hs)]
  change ENNReal.ofReal (∫ x, (Set.univ.pi s).indicator
    (fun x : ι → ℝ => F.density θ x) x ∂Measure.pi fun _ => volume) = _
  rw [hprod, integral_fintype_prod_eq_prod
      (f := fun i => (s i).indicator (gaussianPDFReal θ (v i).toNNReal)),
    ENNReal.ofReal_prod_of_nonneg fun i _ => integral_nonneg fun x =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg _ _ y) x]
  exact Finset.prod_congr rfl fun i _ => (hlaw_i i).symm

/-- The derivative of the density in the parameter is the density times `∑ wᵢ (yᵢ - θ)`. -/
theorem commonEffectFamily_densityDeriv (θ : ℝ) (y : ι → ℝ) :
    (commonEffectFamily hv).densityDeriv θ y =
      (commonEffectFamily hv).density θ y * ∑ i, ivWeight v i * (y i - θ) :=
  (hasDerivAt_commonEffectLikelihood hv y θ).deriv

/-- **The score of the family** is `s(θ; y) = ∑ wᵢ (yᵢ - θ)`. -/
theorem commonEffectFamily_score (θ : ℝ) (y : ι → ℝ) :
    (commonEffectFamily hv).score θ y = ∑ i, ivWeight v i * (y i - θ) := by
  rw [ParametricFamily.score, commonEffectFamily_densityDeriv hv]
  exact mul_div_cancel_left₀ _ (commonEffectLikelihood_pos hv θ y).ne'

/-- The pooled estimate is an unbiased estimator of `θ` in the family. -/
theorem isUnbiased_ivwEstimate [Nonempty ι] :
    (commonEffectFamily hv).IsUnbiased (ivwEstimate v) id := by
  intro θ _
  have h := (isGaussianCommonEffectModel_pi hv θ).isCommonEffectModel
  have := h.isProbabilityMeasure
  refine ⟨?_, ?_⟩
  · rw [commonEffectFamily_law hv]
    exact h.memLp_ivwEstimate.integrable one_le_two
  · rw [ParametricFamily.mean, commonEffectFamily_law hv]
    exact h.integral_variance_ivwEstimate.1

/-- Moments of the pooled estimate under `P_θ`: square integrable with `E_θ[θ̂ - θ] = 0` and
`E_θ[(θ̂ - θ)²] = 1 / ∑ wᵢ`. -/
theorem commonEffectFamily_moments [Nonempty ι] (θ : ℝ) :
    MemLp (ivwEstimate v) 2 ((commonEffectFamily hv).law θ) ∧
      ∫ y, (ivwEstimate v y - θ) ∂(commonEffectFamily hv).law θ = 0 ∧
      ∫ y, (ivwEstimate v y - θ) ^ 2 ∂(commonEffectFamily hv).law θ =
        1 / ∑ i, ivWeight v i := by
  have h := (isGaussianCommonEffectModel_pi hv θ).isCommonEffectModel
  have := h.isProbabilityMeasure
  obtain ⟨hmean, hvar⟩ := h.integral_variance_ivwEstimate
  have hmean' : ∫ y, ivwEstimate v y ∂(Measure.pi fun i => gaussianReal θ (v i).toNNReal) = θ :=
    hmean
  have hvar' : Var[ivwEstimate v; Measure.pi fun i => gaussianReal θ (v i).toNNReal] =
      1 / ∑ i, ivWeight v i := hvar
  have he : ivwEstimate v = fun y : ι → ℝ => ∑ i, ivWeight v i / (∑ j, ivWeight v j) * y i :=
    funext (ivwEstimate_eq_sum v)
  have hm : MemLp (ivwEstimate v) 2 (Measure.pi fun i => gaussianReal θ (v i).toNNReal) := by
    rw [he]
    exact memLp_finsetSum _ fun i _ => (h.memLp i).const_mul _
  rw [commonEffectFamily_law hv]
  refine ⟨hm, ?_, ?_⟩
  · rw [integral_sub (hm.integrable one_le_two) (integrable_const θ), hmean', integral_const,
      smul_eq_mul, probReal_univ, one_mul, sub_self]
  · rw [← hvar', variance_eq_integral hm.aemeasurable, hmean']

/-- **The Fisher information of the family is `∑ wᵢ`.** -/
theorem commonEffectFamily_fisherInfo [Nonempty ι] (θ : ℝ) :
    (commonEffectFamily hv).fisherInfo θ = ∑ i, ivWeight v i := by
  obtain ⟨-, -, h2⟩ := commonEffectFamily_moments hv θ
  have hW := sum_ivWeight_pos hv
  rw [ParametricFamily.fisherInfo]
  simp only [commonEffectFamily_score hv, sum_ivWeight_mul_sub hv, mul_pow]
  rw [integral_const_mul, h2, sq, mul_assoc, mul_one_div_cancel hW.ne', mul_one]

/-- The score is square integrable under `P_θ`. -/
theorem memLp_commonEffectFamily_score [Nonempty ι] (θ : ℝ) :
    MemLp ((commonEffectFamily hv).score θ) 2 ((commonEffectFamily hv).law θ) := by
  obtain ⟨hm, -, -⟩ := commonEffectFamily_moments hv θ
  have := ParametricFamily.isProbabilityMeasure_law (F := commonEffectFamily hv) (Set.mem_univ θ)
  have : (commonEffectFamily hv).score θ =
      fun y => (∑ i, ivWeight v i) * (ivwEstimate v y - θ) := by
    funext y
    rw [commonEffectFamily_score hv, sum_ivWeight_mul_sub hv]
  rw [this]
  exact (hm.sub (memLp_const θ)).const_mul _

/-- **First order interchange** at every `θ`: the density integrates to one for every parameter
and `∫ ∂_θ f dν = E_θ[s] = 0`. -/
theorem commonEffectFamily_derivInterchange [Nonempty ι] (θ : ℝ) :
    (commonEffectFamily hv).DerivInterchange θ := by
  set F := commonEffectFamily hv
  obtain ⟨hm, h0, -⟩ := commonEffectFamily_moments hv θ
  have := ParametricFamily.isProbabilityMeasure_law (F := F) (Set.mem_univ θ)
  have hd : F.densityDeriv θ = fun y => F.density θ y * F.score θ y := by
    funext y
    rw [commonEffectFamily_score hv, commonEffectFamily_densityDeriv hv]
  have hsint : Integrable (F.score θ) (F.law θ) :=
    (memLp_commonEffectFamily_score hv θ).integrable one_le_two
  have hs0 : ∫ y, F.score θ y ∂F.law θ = 0 := by
    simp only [F, commonEffectFamily_score hv, sum_ivWeight_mul_sub hv]
    rw [integral_const_mul, h0, mul_zero]
  have hc : (fun u => ∫ x, F.density u x ∂F.ν) = fun _ => 1 :=
    funext fun u => F.integral_density u (Set.mem_univ u)
  refine ⟨?_, ?_⟩
  · rw [hd]
    exact (ParametricFamily.integrable_law_iff (Set.mem_univ θ)).1 hsint
  · rw [hc, hd, ← ParametricFamily.integral_law (Set.mem_univ θ), hs0]
    exact hasDerivAt_const θ 1

/-- **Interchange for the mean of the pooled estimate**: `u ↦ E_u[θ̂] = u` is differentiated
under the integral sign, `∫ θ̂ ∂_θ f dν = E_θ[θ̂ s] = 1`. -/
theorem meanDerivInterchange_ivwEstimate [Nonempty ι] (θ : ℝ) :
    (commonEffectFamily hv).MeanDerivInterchange (ivwEstimate v) θ := by
  set F := commonEffectFamily hv
  obtain ⟨hm, h0, h2⟩ := commonEffectFamily_moments hv θ
  have := ParametricFamily.isProbabilityMeasure_law (F := F) (Set.mem_univ θ)
  have hW := sum_ivWeight_pos hv
  have hd : (fun y => ivwEstimate v y * F.densityDeriv θ y) =
      fun y => F.density θ y * (ivwEstimate v y * F.score θ y) := by
    funext y
    rw [commonEffectFamily_densityDeriv hv, commonEffectFamily_score hv]
    ring
  have hTs : (fun y => ivwEstimate v y * F.score θ y) = fun y =>
      (∑ i, ivWeight v i) * (ivwEstimate v y - θ) ^ 2 +
        (∑ i, ivWeight v i) * θ * (ivwEstimate v y - θ) := by
    funext y
    rw [commonEffectFamily_score hv, sum_ivWeight_mul_sub hv]
    ring
  have hi1 : Integrable (fun y => (∑ i, ivWeight v i) * (ivwEstimate v y - θ) ^ 2)
      (F.law θ) := ((hm.sub (memLp_const θ)).integrable_sq).const_mul _
  have hi2 : Integrable (fun y => (∑ i, ivWeight v i) * θ * (ivwEstimate v y - θ))
      (F.law θ) := ((hm.integrable one_le_two).sub (integrable_const θ)).const_mul _
  have hint : Integrable (fun y => ivwEstimate v y * F.score θ y) (F.law θ) := by
    rw [hTs]; exact hi1.add hi2
  have hval : ∫ y, ivwEstimate v y * F.densityDeriv θ y ∂F.ν = 1 := by
    rw [hd, ← ParametricFamily.integral_law (Set.mem_univ θ), hTs, integral_add hi1 hi2,
      integral_const_mul, integral_const_mul, h2, h0, mul_zero, add_zero,
      mul_one_div_cancel hW.ne']
  have hmean : (fun u => ∫ x, ivwEstimate v x * F.density u x ∂F.ν) = id := by
    funext u
    rw [show (fun x => ivwEstimate v x * F.density u x) =
      fun x => F.density u x * ivwEstimate v x from funext fun x => mul_comm _ _,
      ← ParametricFamily.integral_law (Set.mem_univ u)]
    exact ((isUnbiased_ivwEstimate hv) u (Set.mem_univ u)).2
  refine ⟨?_, ?_⟩
  · rw [hd]
    exact (ParametricFamily.integrable_law_iff (Set.mem_univ θ)).1 hint
  · rw [hmean, hval]
    exact hasDerivAt_id θ

/-- **The pooled estimate is efficient** (Hedges and Olkin 1985): it is unbiased, square
integrable, and its variance `1 / ∑ wᵢ` equals the Cramér-Rao bound `1 / I(θ)` at every `θ`. -/
theorem isEfficient_ivwEstimate [Nonempty ι] :
    (commonEffectFamily hv).IsEfficient (ivwEstimate v) id := by
  refine ⟨isUnbiased_ivwEstimate hv, fun θ _ => ?_⟩
  obtain ⟨hm, -, -⟩ := commonEffectFamily_moments hv θ
  have h := (isGaussianCommonEffectModel_pi hv θ).isCommonEffectModel
  have hvar : Var[ivwEstimate v; (commonEffectFamily hv).law θ] = 1 / ∑ i, ivWeight v i := by
    rw [commonEffectFamily_law hv]
    exact h.integral_variance_ivwEstimate.2
  refine ⟨hm, ?_, ?_⟩
  · rw [commonEffectFamily_fisherInfo hv]; exact sum_ivWeight_pos hv
  · rw [hvar, commonEffectFamily_fisherInfo hv, deriv_id, one_pow]

/-- **No unbiased estimator beats the pooled estimate** (Cramér-Rao). In the Gaussian common
effect model with at least one study, every estimator `T` of `θ` that is unbiased, square
integrable under `P_θ`, and whose mean can be differentiated under the integral sign at `θ` has
`Var_θ(T) ≥ 1 / I(θ) = 1 / ∑ wᵢ = Var_θ(θ̂)`. The pooled estimate itself meets every hypothesis
(`isUnbiased_ivwEstimate`, `meanDerivInterchange_ivwEstimate`, `commonEffectFamily_moments`). -/
theorem variance_ivwEstimate_le [Nonempty ι] {T : (ι → ℝ) → ℝ} {θ : ℝ}
    (hu : (commonEffectFamily hv).IsUnbiased T id)
    (hT : (commonEffectFamily hv).MeanDerivInterchange T θ)
    (hT2 : MemLp T 2 ((commonEffectFamily hv).law θ)) :
    Var[ivwEstimate v; (commonEffectFamily hv).law θ] ≤
      Var[T; (commonEffectFamily hv).law θ] := by
  have hI : 0 < (commonEffectFamily hv).fisherInfo θ := by
    rw [commonEffectFamily_fisherInfo hv]; exact sum_ivWeight_pos hv
  rw [((isEfficient_ivwEstimate hv).2 θ (Set.mem_univ θ)).2.2, deriv_id, one_pow]
  exact ParametricFamily.cramer_rao_unbiased Filter.univ_mem hu
    (commonEffectFamily_derivInterchange hv θ) hT hT2 (memLp_commonEffectFamily_score hv θ) hI

end Family

end MetaAnalysis

end CausalInference
