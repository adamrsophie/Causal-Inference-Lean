/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LogisticFitNormality
public import CausalInference.PopulationAdjustment.StandardizationInstancesLogisticModel

/-!
# Coverage of Bayesian standardization with the logistic fit

The coverage theorems of `BayesStandardizationLogistic` assume the asymptotic normality of the
maximum likelihood fit, a positive limiting variance of the derivative of the target, and
integrable design coordinates under the target law. This file derives all three.

* **Normality.** `Trial.LogisticOutcomeModel.tendstoInDistribution_glmMLE` gives
  `√n (ξ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)` once the fit is almost everywhere measurable.
* **Variance.** For `Z ∼ N(0, S)` with `S` positive definite and a nonzero linear functional
  `D`, `Var(D Z) = dᵀ S d > 0` with `d` the Riesz vector of `D`
  (`variance_multivariateGaussian_pos`, `variance_logisticLimit_pos`). Since `I(ξ₀)` is positive
  definite, so is `I(ξ₀)⁻¹`, and the variance premise follows from `D Ψ(ξ₀) ≠ 0`.
* **Integrability.** In a randomized trial the assignment is independent of the covariates and
  each arm has positive probability, so an almost sure bound `|z(X, A)| ≤ B` gives
  `|z(x, t)| ≤ B` for `T_X`-almost every `x` and both arms `t`
  (`Trial.IsRandomizedTwoArm.ae_covLaw_abs_design_le`). The bound reaches a target law `ν` only
  where `ν ≪ T_X`, the common support; under that overlap the design coordinates are
  `ν`-integrable (`integrable_design_of_absolutelyContinuous`).
* **Nonzero derivative.** If one design coordinate is the indicator of arm `t₁`, zero in arm
  `t₀` and one in arm `t₁`, and `g'` is nonzero at the mean of arm `t₁`, then `D Ψ(ξ₀) ≠ 0`
  (`logisticTargetDeriv_ne_zero_of_indicator`).
* **Vanishing derivative.** For `t₀ = t₁` the target is the constant `0`, the push forward of
  every posterior is `δ₀`, its credible interval is `{0}`, and coverage is identically `1`
  (`credibleInterval_map_logisticTarget_self`, `measureReal_coverage_logisticTarget_self`). So
  coverage tends to `1`, not to `1 - α`: the hypothesis `D Ψ(ξ₀) ≠ 0` cannot be dropped.

The results are `tendsto_credibleInterval_coverage_logisticFit` and
`tendsto_credibleInterval_coverage_marginalEffect_logisticFit`; in the latter the integrability
of the trial potential outcomes also follows from the logistic outcome model.

## Main results

* `variance_multivariateGaussian_pos`, `variance_logisticLimit_pos`.
* `Trial.IsRandomizedTwoArm.ae_covLaw_abs_design_le`,
  `integrable_design_of_absolutelyContinuous`.
* `hasStrictDerivAt_logit_of_mem_Ioo`, `logisticMean_mem_Ioo`,
  `cdf_gaussianReal_quantile_one_sub_half`.
* `logisticTargetDeriv_ne_zero_of_indicator`, `quantile_dirac_of_mem_Ioo`,
  `credibleInterval_map_logisticTarget_self`, `measureReal_coverage_logisticTarget_self`.
* `tendsto_credibleInterval_coverage_logisticFit`,
  `tendsto_credibleInterval_coverage_marginalEffect_logisticFit`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Theorem 10.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace CausalInference

namespace PopulationAdjustment

open PosteriorLimit IndirectComparison EffectMeasure BayesStandardization PointTreatment
  Transport BiasAnalysis.Distributions

/-! ### Positive variance of a nonzero linear functional -/

section Variance

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **A nonzero linear functional has positive variance under a nondegenerate Gaussian**:
`Var(L Z) = dᵀ S d > 0` for `Z ∼ N(0, S)`, `S` positive definite, `L = ⟪d, ·⟫ ≠ 0`. -/
theorem variance_multivariateGaussian_pos {S : Matrix κ κ ℝ} (hS : S.PosDef)
    {L : EuclideanSpace ℝ κ →L[ℝ] ℝ} (hL : L ≠ 0) :
    0 < Var[L; multivariateGaussian 0 S] := by
  set d := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ κ)).symm L
  have hLd : ⇑L = fun u ↦ ⟪d, u⟫ := by
    funext u
    simp [d, InnerProductSpace.toDual_symm_apply]
  rw [hLd, ← covarianceBilin_self IsGaussian.memLp_two_id,
    covarianceBilin_multivariateGaussian hS.posSemidef]
  have hd : d ≠ 0 := by simpa [d] using hL
  have hd' : WithLp.ofLp d ≠ 0 := by simpa using hd
  exact (Matrix.posDef_iff_dotProduct_mulVec.1 hS).2 hd'

/-- **Positive variance on `κ → ℝ`.** For `S` positive definite and `D ≠ 0`, the variance of
`D` under the law `N(0, S)` carried to `κ → ℝ` is positive. -/
theorem variance_map_multivariateGaussian_pos {S : Matrix κ κ ℝ} (hS : S.PosDef)
    {D : (κ → ℝ) →L[ℝ] ℝ} (hD : D ≠ 0) :
    0 < Var[D; (multivariateGaussian 0 S).map (PiLp.continuousLinearEquiv 2 ℝ
      fun _ : κ ↦ ℝ)] := by
  have hcomp : (⇑D ∘ ⇑(PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)) =
      ⇑(D.comp ((PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ) :
        EuclideanSpace ℝ κ →L[ℝ] (κ → ℝ))) := rfl
  rw [variance_map D.continuous.aemeasurable
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ).continuous.aemeasurable, hcomp]
  refine variance_multivariateGaussian_pos hS fun h ↦ hD (ContinuousLinearMap.ext fun v ↦ ?_)
  have := congrArg (fun L : EuclideanSpace ℝ κ →L[ℝ] ℝ ↦ L (WithLp.toLp 2 v)) h
  exact this

/-- **Positive limiting variance of the target.** For `I(ξ₀)` positive definite and a nonzero
derivative `D`, `Var[D; N(0, I(ξ₀)⁻¹)] > 0`. -/
theorem variance_logisticLimit_pos {𝒳 : Type*} [MeasurableSpace 𝒳] {R : Measure (𝒳 × Bool)}
    {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ} (hI : (logisticInfo R z ξ₀).PosDef)
    {D : (κ → ℝ) →L[ℝ] ℝ} (hD : D ≠ 0) : 0 < Var[D; logisticLimit R z ξ₀] :=
  variance_map_multivariateGaussian_pos hI.inv hD

end Variance

/-! ### The design bound under the target law -/

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ] {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ]
  {z : 𝒳 × Bool → κ → ℝ}

/-- In a randomized trial both arms have positive probability. -/
lemma _root_.CausalInference.IndirectComparison.Trial.IsRandomizedTwoArm.measure_A_ne_zero
    (hT : T.IsRandomizedTwoArm) (t : Bool) : T.μ (T.A ⁻¹' {t}) ≠ 0 := by
  have hA : 0 < T.μ.real (T.A ⁻¹' {t}) := by
    cases t
    · have hs : MeasurableSet (T.A ⁻¹' {true}) := hT.measurable_A (measurableSet_singleton _)
      have e : T.A ⁻¹' {false} = (T.A ⁻¹' {true})ᶜ := by ext ω; simp
      have h := probReal_add_probReal_compl (μ := T.μ) hs
      rw [e]
      linarith [hT.prob_lt_one]
    · exact hT.prob_pos
  intro h
  rw [measureReal_def, h, ENNReal.toReal_zero] at hA
  exact lt_irrefl _ hA

omit [Fintype κ] in
/-- **The design bound holds in each arm on the covariate law.** In a randomized trial, an
almost sure bound `|z(X, A)_j| ≤ B` gives `|z(x, t)_j| ≤ B` for `T_X`-almost every `x` and every
arm `t`: the assignment is independent of the covariates and `P(A = t) > 0`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.IsRandomizedTwoArm.ae_covLaw_abs_design_le
    (hT : T.IsRandomizedTwoArm) (hz : ∀ j, Measurable fun c ↦ z c j) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) (t : Bool)
    [Finite κ] : ∀ᵐ x ∂T.covLaw, ∀ j, |z (x, t) j| ≤ B := by
  set S : Set 𝒳 := {x | ¬ ∀ j, |z (x, t) j| ≤ B}
  have hS : MeasurableSet S := by
    change MeasurableSet {x : 𝒳 | ∀ j, |z (x, t) j| ≤ B}ᶜ
    refine MeasurableSet.compl ?_
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦ measurableSet_le
      (continuous_abs.measurable.comp ((hz j).comp (measurable_id.prodMk measurable_const)))
      measurable_const
  have hind : IndepFun T.A T.X T.μ := hT.indepFun.comp measurable_id measurable_fst
  rw [ae_iff] at hB
  have hinter : T.μ (T.A ⁻¹' {t} ∩ T.X ⁻¹' S) = 0 := by
    refine measure_mono_null (fun ω hω ↦ ?_) hB
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1
    simp only [Set.mem_ofPred_eq, h1]
    exact h2
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind
  rw [hind _ _ (measurableSet_singleton t) hS, mul_eq_zero] at hinter
  rw [ae_iff, Population.covLaw, Measure.map_apply hT.measurable_X hS]
  exact hinter.resolve_left (hT.measure_A_ne_zero t)

omit [Fintype κ] in
/-- **Integrable design under an overlapping target law.** In a randomized trial with an almost
surely bounded design, the design coordinates of each arm are integrable under every
probability law `ν ≪ T_X`. -/
theorem integrable_design_of_absolutelyContinuous (hT : T.IsRandomizedTwoArm)
    (hz : ∀ j, Measurable fun c ↦ z c j) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {ν : Measure 𝒳} [IsFiniteMeasure ν]
    (hν : ν ≪ T.covLaw) (t : Bool) [Finite κ] (j : κ) : Integrable (fun x ↦ z (x, t) j) ν := by
  have h : ∀ᵐ x ∂ν, ∀ j, |z (x, t) j| ≤ B := hν.ae_le (hT.ae_covLaw_abs_design_le hz hB t)
  exact Integrable.of_bound
    ((hz j).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    B (h.mono fun x hx ↦ by rw [Real.norm_eq_abs]; exact hx j)

/-! ### A sufficient condition for a nonzero derivative -/

/-- The derivative of the standardized mean evaluated at a direction. -/
lemma logisticMeanDeriv_apply {ν : Measure 𝒳} [IsProbabilityMeasure ν]
    (hz : ∀ j, Measurable fun c ↦ z c j) {t : Bool}
    (hzi : ∀ j, Integrable (fun x ↦ z (x, t) j) ν) (ξ v : κ → ℝ) :
    logisticMeanDeriv ν z t ξ v = ∫ x, Real.sigmoid (z (x, t) ⬝ᵥ ξ) *
      (1 - Real.sigmoid (z (x, t) ⬝ᵥ ξ)) * (z (x, t) ⬝ᵥ v) ∂ν := by
  have hint : Integrable (logisticMeanDerivIntegrand z t ξ) ν :=
    (integrable_sum_abs_design hzi).mono' (aestronglyMeasurable_logisticMeanDerivIntegrand hz ξ)
      (ae_of_all _ fun x ↦ norm_logisticMeanDerivIntegrand_le ξ x)
  rw [logisticMeanDeriv, ContinuousLinearMap.integral_apply hint]
  simp [logisticMeanDerivIntegrand]

/-- **A sufficient condition for a nonzero derivative of the target.** If the design has a
coordinate `j` equal to `0` in arm `t₀` and to `1` in arm `t₁` (the indicator of arm `t₁`), and
`g'` is nonzero at the standardized mean of arm `t₁`, then
`D Ψ(ξ₀) e_j = g₁' ∫ σ(1 - σ)(z(x, t₁) ⬝ ξ₀) dν ≠ 0`. -/
theorem logisticTargetDeriv_ne_zero_of_indicator {ν : Measure 𝒳} [IsProbabilityMeasure ν]
    (hz : ∀ j, Measurable fun c ↦ z c j) {t₀ t₁ : Bool}
    (hzi₀ : ∀ j, Integrable (fun x ↦ z (x, t₀) j) ν)
    (hzi₁ : ∀ j, Integrable (fun x ↦ z (x, t₁) j) ν) {j : κ}
    (h₀ : ∀ x, z (x, t₀) j = 0) (h₁ : ∀ x, z (x, t₁) j = 1) {g₀' g₁' : ℝ} (hg₁' : g₁' ≠ 0)
    (ξ₀ : κ → ℝ) : logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀ ≠ 0 := by
  classical
  intro h
  have h2 := congrArg (fun L : (κ → ℝ) →L[ℝ] ℝ ↦ L (Pi.single j 1)) h
  simp only [logisticTargetDeriv, sub_apply, smul_apply,
    smul_eq_mul, zero_apply] at h2
  rw [logisticMeanDeriv_apply hz hzi₁, logisticMeanDeriv_apply hz hzi₀] at h2
  simp only [dotProduct_single, mul_one, h₀, h₁, mul_zero, integral_zero, sub_zero] at h2
  have hpos : 0 < ∫ x, Real.sigmoid (z (x, t₁) ⬝ᵥ ξ₀) * (1 - Real.sigmoid (z (x, t₁) ⬝ᵥ ξ₀))
      ∂ν := by
    have hm : Measurable fun x : 𝒳 ↦ z (x, t₁) ⬝ᵥ ξ₀ :=
      (measurable_dotProduct_design hz ξ₀).comp (measurable_id.prodMk measurable_const)
    have hpos : ∀ x, 0 < Real.sigmoid (z (x, t₁) ⬝ᵥ ξ₀) *
        (1 - Real.sigmoid (z (x, t₁) ⬝ᵥ ξ₀)) := fun x ↦
      mul_pos (Real.sigmoid_pos _) (sub_pos.2 (Real.sigmoid_lt_one _))
    refine (integral_pos_iff_support_of_nonneg (fun x ↦ (hpos x).le) ?_).2 ?_
    · refine Integrable.of_bound ((continuous_sigmoid.measurable.comp hm).mul
        (measurable_const.sub (continuous_sigmoid.measurable.comp hm))).aestronglyMeasurable 1
        (ae_of_all _ fun x ↦ ?_)
      rw [Real.norm_eq_abs]; exact abs_sigmoid_mul_one_sub_le _
    · rw [Function.support_eq_univ fun x ↦ (hpos x).ne', measure_univ]
      exact one_pos
  exact hg₁' ((mul_eq_zero.1 h2).resolve_right hpos.ne')

/-! ### The derivative may not vanish -/

/-- The quantile of a point mass at a level in `(0, 1)` is the point. -/
theorem quantile_dirac_of_mem_Ioo (a : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    quantile (Measure.dirac a) u = a := by
  unfold quantile
  simp only [hu, ↓reduceIte]
  have hset : {x | u ≤ cdf (Measure.dirac a) x} = Ici a := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_Ici, cdf_eq_real]
    by_cases hx : a ≤ x
    · simp [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic, hx, hu.2.le]
    · simp [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic, hx, hu.1]
  rw [hset, csInf_Ici]

/-- **With equal arms the credible interval is a point.** For `t₀ = t₁` the target is the
constant `0`, so the push forward of every probability law is `δ₀` and its credible interval
is `{0}`. -/
theorem credibleInterval_map_logisticTarget_self (g : ℝ → ℝ) (ν : Measure 𝒳) (t : Bool)
    (M : Measure (κ → ℝ)) [IsProbabilityMeasure M] {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    credibleInterval (M.map (logisticTarget g ν z t t)) α = {0} := by
  have h0 : logisticTarget g ν z t t = fun _ ↦ 0 := by
    funext ξ; simp [logisticTarget, linkMarginal]
  rw [h0, Measure.map_const, measure_univ, one_smul, credibleInterval,
    quantile_dirac_of_mem_Ioo _ ⟨by linarith [hα.1], by linarith [hα.2]⟩,
    quantile_dirac_of_mem_Ioo _ ⟨by linarith [hα.1, hα.2], by linarith [hα.1]⟩, Icc_self]

/-- **With equal arms coverage is identically one.** For `t₀ = t₁` and posteriors that are
probability laws, the credible interval of the target contains the true target for every
sample, so the coverage probability is `1` for every `n` and does not tend to `1 - α`. -/
theorem measureReal_coverage_logisticTarget_self {P : Measure Ξ} [IsProbabilityMeasure P]
    (g : ℝ → ℝ) (ν : Measure 𝒳) (t : Bool) {Pn : ℕ → Ξ → Measure (κ → ℝ)}
    (hPn : ∀ n ω, IsProbabilityMeasure (Pn n ω)) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (ξ₀ : κ → ℝ) (n : ℕ) :
    P.real {ω | logisticTarget g ν z t t ξ₀ ∈
      credibleInterval ((Pn n ω).map (logisticTarget g ν z t t)) α} = 1 := by
  have h : {ω | logisticTarget g ν z t t ξ₀ ∈
      credibleInterval ((Pn n ω).map (logisticTarget g ν z t t)) α} = univ := by
    ext ω
    have := hPn n ω
    rw [Set.mem_ofPred_eq, credibleInterval_map_logisticTarget_self (z := z) g ν t (Pn n ω) hα]
    simp [logisticTarget, linkMarginal]
  rw [h, probReal_univ]

/-! ### The logit link -/

/-- **The logit link is strictly differentiable on `(0, 1)`**, with derivative
`1 / (q (1 - q))`. -/
theorem hasStrictDerivAt_logit_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    HasStrictDerivAt logit (1 / (q * (1 - q))) q := by
  have h1 : (1 : ℝ) - q ≠ 0 := by linarith [hq.2]
  have hd := (hasStrictDerivAt_id q).div ((hasStrictDerivAt_id q).const_sub 1) h1
  have hl := hd.log (div_ne_zero hq.1.ne' h1)
  have e : logit = fun p ↦ Real.log (p / (1 - p)) := funext logit_eq_log_div
  rw [e]
  convert hl using 1
  · funext p; simp [Pi.div_apply]
  · simp only [Pi.div_apply, id]
    have h0 : q ≠ 0 := hq.1.ne'
    field_simp
    ring

/-- The standardized mean of a logistic surface under a probability law lies in `(0, 1)`. -/
theorem logisticMean_mem_Ioo {ν : Measure 𝒳} [IsProbabilityMeasure ν]
    (hz : ∀ j, Measurable fun c ↦ z c j) (t : Bool) (ξ : κ → ℝ) :
    logisticMean ν z t ξ ∈ Ioo (0 : ℝ) 1 := by
  have hm : Measurable fun x : 𝒳 ↦ Real.sigmoid (z (x, t) ⬝ᵥ ξ) :=
    continuous_sigmoid.measurable.comp
      ((measurable_dotProduct_design hz ξ).comp (measurable_id.prodMk measurable_const))
  refine integral_mem_Ioo_zero_one (Integrable.of_bound hm.aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ ?_)) (ae_of_all _ fun x ↦ ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩)
  rw [Real.norm_eq_abs, abs_of_pos (Real.sigmoid_pos _)]
  exact (Real.sigmoid_lt_one _).le

/-- The standard normal quantile of level `1 - α / 2` solves `Φ(c) = 1 - α / 2`. -/
theorem cdf_gaussianReal_quantile_one_sub_half {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    cdf (gaussianReal 0 1) (quantile (gaussianReal 0 1) (1 - α / 2)) = 1 - α / 2 :=
  cdf_quantile ⟨by linarith [hα.2], by linarith [hα.1]⟩ continuous_cdf_gaussianReal_zero_one

/-! ### Coverage with every hypothesis on the fit discharged -/

variable {ξ₀ : κ → ℝ}

/-- **Coverage of the credible intervals for the standardized logistic target.** Let the
records `((X, A), Y)` of a randomized trial follow the logistic outcome model at `ξ₀` with a
design bounded almost surely, `O` an i.i.d. sample of the records, `K` a compact neighborhood
of `ξ₀`, the fit over `K` almost everywhere measurable, and `π` a prior density that is
measurable, nonnegative, integrable, continuous and positive at `ξ₀`. Let the target law `ν`
overlap the trial, `ν ≪ T_X`, let `g` be measurable and strictly differentiable at the two
standardized means, and let the derivative `D Ψ(ξ₀)` be nonzero. Then the equal tailed credible
interval of level `1 - α` for `Ψ` under the logistic posterior contains `Ψ(ξ₀)` with
probability tending to `1 - α`. -/
theorem tendsto_credibleInterval_coverage_logisticFit (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    (hξm : ∀ n, AEMeasurable (glmMLE logisticDens z K O n) P)
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀)
    {ν : Measure 𝒳} [IsProbabilityMeasure ν] (hν : ν ≪ T.covLaw) {t₀ t₁ : Bool}
    {g : ℝ → ℝ} (hg : Measurable g) {g₀' g₁' : ℝ}
    (hg₀ : HasStrictDerivAt g g₀' (logisticMean ν z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean ν z t₁ ξ₀))
    (hD : logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀ ≠ 0) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ P.real {ω | logisticTarget g ν z t₀ t₁ ξ₀ ∈
      credibleInterval ((logisticPosterior p z fun i : Fin n ↦ O i ω).map
        (logisticTarget g ν z t₀ t₁)) α}) atTop (𝓝 (1 - α)) := by
  classical
  set N := logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀
  have hY : HasLaw (id : (κ → ℝ) → κ → ℝ) N N := ⟨aemeasurable_id, Measure.map_id⟩
  exact tendsto_credibleInterval_coverage_logisticOutcomeModel hT hM hB hK hKξ₀ hO hlaw hpm hp0
    hpi hpc hpξ₀ hY (hM.tendstoInDistribution_glmMLE hT hB hK hKξ₀ hO hlaw hξm hY)
    (integrable_design_of_absolutelyContinuous hT hM.measurable_z hB hν t₀)
    (integrable_design_of_absolutelyContinuous hT hM.measurable_z hB hν t₁) hg hg₀ hg₁
    (variance_logisticLimit_pos (hM.posDef_logisticInfo hT hB) hD) hα
    (cdf_gaussianReal_quantile_one_sub_half hα)

/-- **Coverage of the target marginal effect.** Under the hypotheses of
`tendsto_credibleInterval_coverage_logisticFit` for the target law `Q_X`, with the overlap
`Q_X ≪ T_X`, integrable target potential outcomes of the arms `s₀, s₁`, and each arm used
absolutely constant from the trial to the target, the equal tailed credible interval of level
`1 - α` for `Ψ` under the logistic posterior contains the target marginal effect
`g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])` with probability tending to `1 - α`. -/
theorem tendsto_credibleInterval_coverage_marginalEffect_logisticFit
    {Q : Population Ω₂ 𝒳 ι} [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    (hξm : ∀ n, AEMeasurable (glmMLE logisticDens z K O n) P)
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀)
    (hX₂ : Measurable Q.X) {t₀ t₁ : Bool} {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y t₀) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y t₁) Q.μ Q.X (Q.Y s₁)) (hov : Q.covLaw ≪ T.covLaw)
    {g : ℝ → ℝ} (hg : Measurable g) {g₀' g₁' : ℝ}
    (hg₀ : HasStrictDerivAt g g₀' (logisticMean Q.covLaw z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean Q.covLaw z t₁ ξ₀))
    (hD : logisticTargetDeriv Q.covLaw z t₀ t₁ g₀' g₁' ξ₀ ≠ 0) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ P.real {ω | Q.marginalEffect g s₀ s₁ ∈
      credibleInterval ((logisticPosterior p z fun i : Fin n ↦ O i ω).map
        (logisticTarget g Q.covLaw z t₀ t₁)) α}) atTop (𝓝 (1 - α)) := by
  classical
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  rw [← logisticTarget_eq_marginalEffect hT (hM.integrable_potentialOutcome hT) hM hX₂ hYQ₀
    hYQ₁ hsi₀ hsi₁ hov g]
  exact tendsto_credibleInterval_coverage_logisticFit hT hM hB hK hKξ₀ hO hlaw hξm hpm hp0 hpi
    hpc hpξ₀ hov hg hg₀ hg₁ hD hα

end PopulationAdjustment

end CausalInference
