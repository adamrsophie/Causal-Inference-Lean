/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitCoverage
public import CausalInference.Estimation.EmpiricalLawMonteCarlo
public import CausalInference.PopulationAdjustment.StandardizationConsistencyLogistic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Bayesian outcome model standardization

The outcome model is logistic: the mean outcome at covariates `x` under arm `t` is
`σ(z(x, t) ⬝ ξ)` with design `z` and coefficient `ξ ∈ ℝ^κ`. The target of a population adjusted
comparison is the marginal effect on the scale `g` in the target covariate law `ν`,

  `Ψ(ξ) = linkMarginal g ν (σ(z(·, t₀) ⬝ ξ)) (σ(z(·, t₁) ⬝ ξ))`,

that is `Ψ(ξ) = g(∫ σ(z(x, t₁) ⬝ ξ) dν) - g(∫ σ(z(x, t₀) ⬝ ξ) dν)`

(`logisticTarget`). Bayesian standardization pushes the posterior `Π_n` of `ξ` forward through
`Ψ`; the posterior of the target is `Ψ_# Π_n`.

* `hasStrictFDerivAt_logisticMean`: the standardized mean `ξ ↦ ∫ σ(z(x,t) ⬝ ξ) dν` is strictly
  differentiable everywhere, with derivative `∫ σ'(z(x,t) ⬝ ξ) z(x,t) ⬝ (·) dν`, when the design
  coordinates are integrable under `ν`. The proof differentiates under the integral sign with the
  bound `|σ'| ≤ 1` and then upgrades to a strict derivative through continuity of the derivative.
* `hasStrictFDerivAt_logisticTarget`: the chain rule for `Ψ` when `g` is strictly differentiable
  at the two standardized means; `measurable_logisticTarget`: `Ψ` is measurable for measurable `g`.
* `isBernsteinVonMisesWeak_logisticTarget`, `tendstoInMeasure_tvDist_logisticTarget`: the
  posterior of the target satisfies the weak Bernstein and von Mises conclusion with centering
  `Ψ(ξ̂_n)` and limit `D_# N`, and is close in total variation to the image of the normal
  approximation.
* `tendsto_credibleInterval_coverage_logisticTarget`: unanchored coverage of the equal tailed
  credible interval of the target.
* `tendsto_credibleInterval_coverage_logisticTarget_anchored`: anchored coverage, for the joint
  posterior of `(ξ, d)` with `d` the comparator effect and the target `Ψ(ξ) - d`.
* `monteCarlo_logisticTarget`: Monte Carlo draws from a fixed posterior of the coefficient give
  i.i.d. draws of the target, with almost sure weak convergence of their empirical law and almost
  sure convergence of their empirical quantiles under strict crossing. For a posterior depending
  on the data, `EmpiricalLaw.ae_data_tendsto_ae_empiricalMeasure` and the other statements of
  that section apply to the transformed draws for almost every data value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

namespace BayesStandardization

open EffectMeasure PosteriorLimit BiasAnalysis.Distributions

variable {𝒳 κ : Type*} [MeasurableSpace 𝒳] [Fintype κ]

/-! ### The design as a continuous linear functional -/

/-- The functional `ξ ↦ v ⬝ ξ` as a continuous linear map. -/
noncomputable def designCLM (v : κ → ℝ) : (κ → ℝ) →L[ℝ] ℝ :=
  ∑ j, v j • ContinuousLinearMap.proj j

@[simp]
lemma designCLM_apply (v ξ : κ → ℝ) : designCLM v ξ = v ⬝ᵥ ξ := by
  simp [designCLM, dotProduct]

lemma continuous_designCLM : Continuous (designCLM : (κ → ℝ) → (κ → ℝ) →L[ℝ] ℝ) :=
  continuous_finsetSum _ fun j _ ↦ (continuous_apply j).smul continuous_const

lemma norm_designCLM_le (v : κ → ℝ) : ‖designCLM v‖ ≤ ∑ j, |v j| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)
    fun ξ ↦ ?_
  rw [designCLM_apply, Real.norm_eq_abs, dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm ξ j) (abs_nonneg _)

/-! ### The standardized mean and its derivative -/

/-- The standardized mean of arm `t` in the covariate law `ν`: `∫ σ(z(x, t) ⬝ ξ) dν`. -/
noncomputable def logisticMean (ν : Measure 𝒳) (z : 𝒳 × Bool → κ → ℝ) (t : Bool)
    (ξ : κ → ℝ) : ℝ :=
  ∫ x, Real.sigmoid (z (x, t) ⬝ᵥ ξ) ∂ν

/-- The integrand of the derivative: `σ'(z(x, t) ⬝ ξ) • (z(x, t) ⬝ ·)`. -/
noncomputable def logisticMeanDerivIntegrand (z : 𝒳 × Bool → κ → ℝ) (t : Bool) (ξ : κ → ℝ)
    (x : 𝒳) : (κ → ℝ) →L[ℝ] ℝ :=
  (Real.sigmoid (z (x, t) ⬝ᵥ ξ) * (1 - Real.sigmoid (z (x, t) ⬝ᵥ ξ))) • designCLM (z (x, t))

/-- The derivative of the standardized mean. -/
noncomputable def logisticMeanDeriv (ν : Measure 𝒳) (z : 𝒳 × Bool → κ → ℝ) (t : Bool)
    (ξ : κ → ℝ) : (κ → ℝ) →L[ℝ] ℝ :=
  ∫ x, logisticMeanDerivIntegrand z t ξ x ∂ν

section Derivative

variable {ν : Measure 𝒳} {z : 𝒳 × Bool → κ → ℝ} {t : Bool}

lemma abs_sigmoid_mul_one_sub_le (s : ℝ) : |Real.sigmoid s * (1 - Real.sigmoid s)| ≤ 1 := by
  have h0 := Real.sigmoid_pos s
  have h1 := Real.sigmoid_lt_one s
  rw [abs_of_pos (mul_pos h0 (by linarith))]
  nlinarith

omit [MeasurableSpace 𝒳] in
lemma norm_logisticMeanDerivIntegrand_le (ξ : κ → ℝ) (x : 𝒳) :
    ‖logisticMeanDerivIntegrand z t ξ x‖ ≤ ∑ j, |z (x, t) j| := by
  rw [logisticMeanDerivIntegrand, norm_smul, Real.norm_eq_abs]
  calc _ ≤ 1 * ‖designCLM (z (x, t))‖ :=
        mul_le_mul_of_nonneg_right (abs_sigmoid_mul_one_sub_le _) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact norm_designCLM_le _

lemma hasFDerivAt_sigmoid_dotProduct (v ξ : κ → ℝ) :
    HasFDerivAt (fun ξ ↦ Real.sigmoid (v ⬝ᵥ ξ))
      ((Real.sigmoid (v ⬝ᵥ ξ) * (1 - Real.sigmoid (v ⬝ᵥ ξ))) • designCLM v) ξ := by
  have hL : HasFDerivAt (fun ξ ↦ v ⬝ᵥ ξ) (designCLM v) ξ := by
    have hf : (fun ξ ↦ v ⬝ᵥ ξ) = ⇑(designCLM v) := funext fun ξ ↦ (designCLM_apply v ξ).symm
    rw [hf]
    exact (designCLM v).hasFDerivAt
  exact (Real.hasDerivAt_sigmoid _).comp_hasFDerivAt ξ hL

omit [MeasurableSpace 𝒳] in
lemma continuous_logisticMeanDerivIntegrand (x : 𝒳) :
    Continuous fun ξ ↦ logisticMeanDerivIntegrand z t ξ x := by
  have hs : Continuous fun ξ : κ → ℝ ↦ Real.sigmoid (z (x, t) ⬝ᵥ ξ) :=
    continuous_sigmoid.comp (continuous_const.dotProduct continuous_id)
  exact (hs.mul (continuous_const.sub hs)).smul continuous_const

variable (hz : ∀ j, Measurable fun c ↦ z c j)
include hz

lemma aestronglyMeasurable_logisticMeanDerivIntegrand (ξ : κ → ℝ) :
    AEStronglyMeasurable (logisticMeanDerivIntegrand z t ξ) ν := by
  have hzt : Measurable fun x : 𝒳 ↦ z (x, t) :=
    measurable_pi_iff.2 fun j ↦ (hz j).comp (measurable_id.prodMk measurable_const)
  have hs : Measurable fun x : 𝒳 ↦ z (x, t) ⬝ᵥ ξ :=
    (measurable_dotProduct_design hz ξ).comp (measurable_id.prodMk measurable_const)
  have hpair : Measurable fun x : 𝒳 ↦ (z (x, t) ⬝ᵥ ξ, z (x, t)) := hs.prodMk hzt
  have hcont : Continuous fun p : ℝ × (κ → ℝ) ↦
      (Real.sigmoid p.1 * (1 - Real.sigmoid p.1)) • designCLM p.2 :=
    ((continuous_sigmoid.comp continuous_fst).mul
      (continuous_const.sub (continuous_sigmoid.comp continuous_fst))).smul
      (continuous_designCLM.comp continuous_snd)
  exact hcont.comp_aestronglyMeasurable hpair.aestronglyMeasurable

variable [IsProbabilityMeasure ν] (hzi : ∀ j, Integrable (fun x ↦ z (x, t) j) ν)
include hzi

omit hz [IsProbabilityMeasure ν] in
lemma integrable_sum_abs_design : Integrable (fun x ↦ ∑ j, |z (x, t) j|) ν :=
  integrable_finsetSum _ fun j _ ↦ (hzi j).abs

/-- **Differentiation under the integral sign.** The standardized mean has the derivative
`∫ σ'(z(x, t) ⬝ ξ) z(x, t) ⬝ (·) dν` at every `ξ`. -/
theorem hasFDerivAt_logisticMean (ξ : κ → ℝ) :
    HasFDerivAt (logisticMean ν z t) (logisticMeanDeriv ν z t ξ) ξ := by
  have hreg := logisticSurface_regular hz t ν
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun x ↦ ∑ j, |z (x, t) j|)
    (F := fun ξ x ↦ Real.sigmoid (z (x, t) ⬝ᵥ ξ)) univ_mem
    (Eventually.of_forall fun ξ ↦ (hreg.1 ξ).aestronglyMeasurable) ?_
    (aestronglyMeasurable_logisticMeanDerivIntegrand hz ξ)
    (ae_of_all _ fun x ξ _ ↦ norm_logisticMeanDerivIntegrand_le ξ x)
    (integrable_sum_abs_design hzi)
    (ae_of_all _ fun x ξ _ ↦ hasFDerivAt_sigmoid_dotProduct _ _)
  exact (integrable_const (1 : ℝ)).mono' (hreg.1 ξ).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hreg.2.2.1 ξ x)

omit [IsProbabilityMeasure ν] in
lemma continuous_logisticMeanDeriv : Continuous (logisticMeanDeriv ν z t) :=
  continuous_of_dominated (aestronglyMeasurable_logisticMeanDerivIntegrand hz)
    (fun ξ ↦ ae_of_all _ fun x ↦ norm_logisticMeanDerivIntegrand_le ξ x)
    (integrable_sum_abs_design hzi) (ae_of_all _ fun x ↦ continuous_logisticMeanDerivIntegrand x)

/-- **The standardized mean is strictly differentiable** at every coefficient. -/
theorem hasStrictFDerivAt_logisticMean (ξ : κ → ℝ) :
    HasStrictFDerivAt (logisticMean ν z t) (logisticMeanDeriv ν z t ξ) ξ :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Eventually.of_forall fun ξ' ↦ hasFDerivAt_logisticMean hz hzi ξ')
    (continuous_logisticMeanDeriv hz hzi).continuousAt

end Derivative

/-! ### The target -/

/-- The **target** of the population adjusted comparison: the marginal effect on the scale `g`
of arm `t₁` against arm `t₀` in the covariate law `ν`, as a function of the outcome model
coefficient. -/
noncomputable def logisticTarget (g : ℝ → ℝ) (ν : Measure 𝒳) (z : 𝒳 × Bool → κ → ℝ)
    (t₀ t₁ : Bool) (ξ : κ → ℝ) : ℝ :=
  linkMarginal g ν (fun x ↦ Real.sigmoid (z (x, t₀) ⬝ᵥ ξ))
    (fun x ↦ Real.sigmoid (z (x, t₁) ⬝ᵥ ξ))

lemma logisticTarget_eq (g : ℝ → ℝ) (ν : Measure 𝒳) (z : 𝒳 × Bool → κ → ℝ) (t₀ t₁ : Bool) :
    logisticTarget g ν z t₀ t₁ =
      fun ξ ↦ g (logisticMean ν z t₁ ξ) - g (logisticMean ν z t₀ ξ) := rfl

/-- The derivative of the target. -/
noncomputable def logisticTargetDeriv (ν : Measure 𝒳) (z : 𝒳 × Bool → κ → ℝ) (t₀ t₁ : Bool)
    (g₀' g₁' : ℝ) (ξ : κ → ℝ) : (κ → ℝ) →L[ℝ] ℝ :=
  g₁' • logisticMeanDeriv ν z t₁ ξ - g₀' • logisticMeanDeriv ν z t₀ ξ

variable {ν : Measure 𝒳} [IsProbabilityMeasure ν] {z : 𝒳 × Bool → κ → ℝ}
  {t₀ t₁ : Bool} {g : ℝ → ℝ}

/-- **The chain rule for the target.** With integrable design coordinates in both arms and `g`
strictly differentiable at the two standardized means, the target is strictly differentiable. -/
theorem hasStrictFDerivAt_logisticTarget (hz : ∀ j, Measurable fun c ↦ z c j)
    (hzi₀ : ∀ j, Integrable (fun x ↦ z (x, t₀) j) ν)
    (hzi₁ : ∀ j, Integrable (fun x ↦ z (x, t₁) j) ν) {ξ₀ : κ → ℝ} {g₀' g₁' : ℝ}
    (hg₀ : HasStrictDerivAt g g₀' (logisticMean ν z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean ν z t₁ ξ₀)) :
    HasStrictFDerivAt (logisticTarget g ν z t₀ t₁) (logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀)
      ξ₀ := by
  rw [logisticTarget_eq]
  exact (hg₁.comp_hasStrictFDerivAt ξ₀ (hasStrictFDerivAt_logisticMean hz hzi₁ ξ₀)).sub
    (hg₀.comp_hasStrictFDerivAt ξ₀ (hasStrictFDerivAt_logisticMean hz hzi₀ ξ₀))

/-- The standardized mean is continuous in the coefficient. -/
lemma continuous_logisticMean (hz : ∀ j, Measurable fun c ↦ z c j) (t : Bool) :
    Continuous (logisticMean ν z t) := by
  have hreg := logisticSurface_regular hz t ν
  exact continuous_of_dominated (fun ξ ↦ (hreg.1 ξ).aestronglyMeasurable)
    (fun ξ ↦ ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hreg.2.2.1 ξ x)
    (integrable_const 1) (ae_of_all _ fun x ↦ hreg.2.2.2 x)

/-- The target is measurable in the coefficient for a measurable link. -/
lemma measurable_logisticTarget (hz : ∀ j, Measurable fun c ↦ z c j) (hg : Measurable g) :
    Measurable (logisticTarget g ν z t₀ t₁) := by
  rw [logisticTarget_eq]
  exact (hg.comp (continuous_logisticMean hz t₁).measurable).sub
    (hg.comp (continuous_logisticMean hz t₀).measurable)

/-! ### The posterior of the target -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The posterior of the target.** If the posteriors `Π_n` of the coefficient satisfy the weak
Bernstein and von Mises conclusion (implied by the total variation form,
`IsBernsteinVonMises.isBernsteinVonMisesWeak`) with a consistent centering `ξ̂_n → ξ₀`, then the
posteriors `Ψ_# Π_n` of the target satisfy the weak conclusion with centering `Ψ(ξ̂_n)` and limit
`D_# N`. -/
theorem isBernsteinVonMisesWeak_logisticTarget {Pn : ℕ → Ω → Measure (κ → ℝ)}
    {ξh : ℕ → Ω → κ → ℝ} {N : Measure (κ → ℝ)} (h : IsBernsteinVonMisesWeak P Pn ξh N) {ξ₀ : κ → ℝ}
    (hcons : TendstoInMeasure P ξh atTop (fun _ ↦ ξ₀)) (hz : ∀ j, Measurable fun c ↦ z c j)
    (hzi₀ : ∀ j, Integrable (fun x ↦ z (x, t₀) j) ν)
    (hzi₁ : ∀ j, Integrable (fun x ↦ z (x, t₁) j) ν) (hg : Measurable g) {g₀' g₁' : ℝ}
    (hg₀ : HasStrictDerivAt g g₀' (logisticMean ν z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean ν z t₁ ξ₀)) :
    IsBernsteinVonMisesWeak P (fun n ω ↦ (Pn n ω).map (logisticTarget g ν z t₀ t₁))
      (fun n ω ↦ logisticTarget g ν z t₀ t₁ (ξh n ω))
      (N.map (logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀)) :=
  h.map hcons (measurable_logisticTarget hz hg)
    (hasStrictFDerivAt_logisticTarget hz hzi₀ hzi₁ hg₀ hg₁)

/-- **The posterior of the target, total variation form.** Under the total variation conclusion
for the coefficient, the posterior of the target is close in total variation to the image under
`Ψ` of the normal approximation `N(ξ̂_n, n⁻¹ ·)`. -/
theorem tendstoInMeasure_tvDist_logisticTarget {Pn : ℕ → Ω → Measure (κ → ℝ)}
    {ξh : ℕ → Ω → κ → ℝ} {N : Measure (κ → ℝ)} (h : IsBernsteinVonMises P Pn ξh N)
    (hz : ∀ j, Measurable fun c ↦ z c j) (hg : Measurable g) :
    TendstoInMeasure P (fun n ω ↦ tvDist ((Pn n ω).map (logisticTarget g ν z t₀ t₁))
      ((N.map fun u ↦ ξh n ω + (√(n : ℝ))⁻¹ • u).map (logisticTarget g ν z t₀ t₁))) atTop
      (fun _ ↦ 0) :=
  h.tendstoInMeasure_tvDist_map (measurable_logisticTarget hz hg)

/-- **Unanchored coverage.** Let the posteriors of the coefficient satisfy the weak Bernstein and
von Mises conclusion with a centered Gaussian limit `N` and centering `ξ̂_n` with
`√n (ξ̂_n - ξ₀) → N` in distribution; let `g` be measurable and strictly differentiable at the two
standardized means, with positive limiting variance `Var(D Z) > 0`, `Z ∼ N`. Then the equal tailed
credible interval of the posterior of the target covers `Ψ(ξ₀)` with probability tending to
`1 - α`. -/
theorem tendsto_credibleInterval_coverage_logisticTarget [IsProbabilityMeasure P]
    {Pn : ℕ → Ω → Measure (κ → ℝ)} {ξh : ℕ → Ω → κ → ℝ} {N : Measure (κ → ℝ)} [IsGaussian N]
    (h : IsBernsteinVonMisesWeak P Pn ξh N) (hN0 : ∫ u, u ∂N = 0) {ξ₀ : κ → ℝ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ} (hY : HasLaw Y N P')
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (ξh n ω - ξ₀)) atTop Y
      (fun _ ↦ P) P')
    (hz : ∀ j, Measurable fun c ↦ z c j) (hzi₀ : ∀ j, Integrable (fun x ↦ z (x, t₀) j) ν)
    (hzi₁ : ∀ j, Integrable (fun x ↦ z (x, t₁) j) ν) (hg : Measurable g) {g₀' g₁' : ℝ}
    (hg₀ : HasStrictDerivAt g g₀' (logisticMean ν z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean ν z t₁ ξ₀))
    (hσ : 0 < Var[logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀; N]) {α c : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hc : cdf (gaussianReal 0 1) c = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | logisticTarget g ν z t₀ t₁ ξ₀ ∈
      credibleInterval ((Pn n ω).map (logisticTarget g ν z t₀ t₁)) α}) atTop (𝓝 (1 - α)) :=
  h.tendsto_credibleInterval_coverage_map hN0 hY hT (measurable_logisticTarget hz hg)
    (hasStrictFDerivAt_logisticTarget hz hzi₀ hzi₁ hg₀ hg₁) hσ hα hc

/-- The **anchored target** `Ψ(ξ) - d` of the coefficient and the comparator effect `d`. -/
noncomputable def anchoredTarget (g : ℝ → ℝ) (ν : Measure 𝒳) (z : 𝒳 × Bool → κ → ℝ)
    (t₀ t₁ : Bool) (p : (κ → ℝ) × ℝ) : ℝ :=
  logisticTarget g ν z t₀ t₁ p.1 - p.2

/-- **Anchored coverage.** The parameter is the pair `(ξ, d)` of the outcome model coefficient
and the comparator effect, with a joint posterior. Under the weak Bernstein and von Mises
conclusion for the joint posterior with a centered Gaussian limit `N`, `√n` normality of the
joint centering with limit `N`, the conditions of `hasStrictFDerivAt_logisticTarget`, and
positive limiting variance of the derivative `(u, e) ↦ D u - e`, the equal tailed credible
interval of the posterior of `Ψ(ξ) - d` covers `Ψ(ξ₀) - d₀` with probability tending to
`1 - α`. -/
theorem tendsto_credibleInterval_coverage_logisticTarget_anchored [IsProbabilityMeasure P]
    {Pn : ℕ → Ω → Measure ((κ → ℝ) × ℝ)} {θh : ℕ → Ω → (κ → ℝ) × ℝ}
    {N : Measure ((κ → ℝ) × ℝ)} [IsGaussian N] (h : IsBernsteinVonMisesWeak P Pn θh N)
    (hN0 : ∫ u, u ∂N = 0) {ξ₀ : κ → ℝ} {d₀ : ℝ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → (κ → ℝ) × ℝ} (hY : HasLaw Y N P')
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - (ξ₀, d₀))) atTop Y
      (fun _ ↦ P) P')
    (hz : ∀ j, Measurable fun c ↦ z c j) (hzi₀ : ∀ j, Integrable (fun x ↦ z (x, t₀) j) ν)
    (hzi₁ : ∀ j, Integrable (fun x ↦ z (x, t₁) j) ν) (hg : Measurable g) {g₀' g₁' : ℝ}
    (hg₀ : HasStrictDerivAt g g₀' (logisticMean ν z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean ν z t₁ ξ₀))
    (hσ : 0 < Var[(logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀).comp (ContinuousLinearMap.fst ℝ _ ℝ) -
      ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ; N]) {α c : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hc : cdf (gaussianReal 0 1) c = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | anchoredTarget g ν z t₀ t₁ (ξ₀, d₀) ∈
      credibleInterval ((Pn n ω).map (anchoredTarget g ν z t₀ t₁)) α}) atTop (𝓝 (1 - α)) := by
  have hm : Measurable (anchoredTarget g ν z t₀ t₁) :=
    ((measurable_logisticTarget hz hg).comp measurable_fst).sub measurable_snd
  have hd : HasStrictFDerivAt (anchoredTarget g ν z t₀ t₁)
      ((logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀).comp (ContinuousLinearMap.fst ℝ _ ℝ) -
        ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ) (ξ₀, d₀) :=
    ((hasStrictFDerivAt_logisticTarget hz hzi₀ hzi₁ hg₀ hg₁).comp (ξ₀, d₀)
      hasStrictFDerivAt_fst).sub hasStrictFDerivAt_snd
  exact h.tendsto_credibleInterval_coverage_map hN0 hY hT hm hd hσ hα hc

/-! ### Monte Carlo approximation of the posterior of the target -/

section MonteCarlo

variable {Ωs : Type*} {mΩs : MeasurableSpace Ωs} {S : Measure Ωs} [IsProbabilityMeasure S]

/-- **Monte Carlo draws of the target.** Let `ξ₀, ξ₁, ...` be i.i.d. draws under `S` from a fixed
posterior `Q` of the coefficient, and `g` measurable. The transformed draws `Ψ(ξ_m)` are i.i.d.
with law `Ψ_# Q`; almost surely their empirical laws converge weakly to `Ψ_# Q`, and if the
distribution function of `Ψ_# Q` crosses `p` strictly at `c`, almost surely their empirical `p`
quantile converges to `c`. -/
theorem monteCarlo_logisticTarget {D : ℕ → Ωs → κ → ℝ} (hD : IsIIDSample D S)
    {Q : Measure (κ → ℝ)} (hQ : S.map (D 0) = Q) (hz : ∀ j, Measurable fun c ↦ z c j)
    (hg : Measurable g) :
    IsIIDSample (fun m ω ↦ logisticTarget g ν z t₀ t₁ (D m ω)) S ∧
      S.map (fun ω ↦ logisticTarget g ν z t₀ t₁ (D 0 ω)) = Q.map (logisticTarget g ν z t₀ t₁) ∧
      (∀ᵐ ω ∂S, Tendsto (β := ProbabilityMeasure ℝ) (fun n : ℕ ↦
        (⟨empiricalMeasure (fun m ω ↦ logisticTarget g ν z t₀ t₁ (D m ω)) (n + 1) ω,
          inferInstance⟩ : ProbabilityMeasure ℝ)) atTop
        (𝓝 (⟨S.map (fun ω ↦ logisticTarget g ν z t₀ t₁ (D 0 ω)),
          (Measure.isProbabilityMeasure_map_iff ((hD.comp (measurable_logisticTarget hz hg)).ident
            0).aemeasurable_fst).2 inferInstance⟩ : ProbabilityMeasure ℝ))) ∧
      ∀ {p c : ℝ}, (∀ ε, 0 < ε → cdf (Q.map (logisticTarget g ν z t₀ t₁)) (c - ε) < p) →
        (∀ ε, 0 < ε → p < cdf (Q.map (logisticTarget g ν z t₀ t₁)) (c + ε)) →
        ∀ᵐ ω ∂S, Tendsto (fun n ↦ quantile (empiricalMeasure
          (fun m ω ↦ logisticTarget g ν z t₀ t₁ (D m ω)) n ω) p) atTop (𝓝 c) := by
  have hm := measurable_logisticTarget (ν := ν) (t₀ := t₀) (t₁ := t₁) hz hg
  have hD' := hD.comp hm
  have hlaw : S.map (fun ω ↦ logisticTarget g ν z t₀ t₁ (D 0 ω)) =
      Q.map (logisticTarget g ν z t₀ t₁) := by
    rw [← hQ, AEMeasurable.map_map_of_aemeasurable hm.aemeasurable (hD.ident 0).aemeasurable_fst]
    rfl
  refine ⟨hD', hlaw, EmpiricalLaw.tendsto_ae_empiricalMeasure hD', fun hlo hhi ↦ ?_⟩
  rw [← hlaw] at hlo hhi
  exact EmpiricalLaw.tendsto_ae_quantile_empiricalMeasure hD' hlo hhi

end MonteCarlo

end BayesStandardization

end PopulationAdjustment

end CausalInference
