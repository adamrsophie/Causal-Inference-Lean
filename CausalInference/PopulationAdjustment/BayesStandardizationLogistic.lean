/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLogistic
public import CausalInference.PopulationAdjustment.BayesStandardization

/-!
# Bayesian standardization with a logistic outcome model

A trial with a logistic outcome model `σ(z(x, a) ⬝ ξ₀)` (`Trial.LogisticOutcomeModel`) and an
i.i.d. sample of its records give the logistic posterior `Π_n` of the coefficient (the
normalized product of a prior density and the likelihood, `PosteriorLimit.logisticPosterior`).
The standardized target of a coefficient `ξ` in a target population with covariate law `ν` is
`Ψ(ξ) = g(∫ σ(z(x, t₁) ⬝ ξ) dν) - g(∫ σ(z(x, t₀) ⬝ ξ) dν)` (`logisticTarget`).

* **The posterior concentrates** (`isBernsteinVonMises_logisticOutcomeModel`): when the design is
  bounded almost surely in the trial, `‖Π_n - N(ξ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability for a
  prior density integrable, continuous and positive at `ξ₀`, with the maximum likelihood fit
  `ξ̂_n` over a compact neighborhood of `ξ₀`. Full rank and consistency come from the model.
* **The target at the true coefficient is the target marginal effect**
  (`logisticTarget_eq_marginalEffect`): `Ψ(ξ₀) = g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])` under
  randomization, absolute constancy of the arms and overlap.
* **Credible intervals cover** (`tendsto_credibleInterval_coverage_logisticOutcomeModel`,
  `tendsto_credibleInterval_coverage_marginalEffect`): the equal tailed credible interval of
  level `1 - α` for `Ψ` under `Π_n` contains `Ψ(ξ₀)`, the target marginal effect, with
  probability tending to `1 - α`, given asymptotic normality of the maximum likelihood fit,
  `√n (ξ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)`, and a nondegenerate derivative of `Ψ`.

## Main results

* `isBernsteinVonMises_logisticOutcomeModel`, `integral_id_logisticLimit`.
* `logisticTarget_eq_marginalEffect`.
* `tendsto_credibleInterval_coverage_logisticOutcomeModel`,
  `tendsto_credibleInterval_coverage_marginalEffect`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Theorem 10.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open IndirectComparison PosteriorLimit BayesStandardization EffectMeasure PointTreatment Transport

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ]

/-! ### The link between the target and the marginal effect -/

/-- **The standardized logistic target at the true coefficient is the target marginal effect.**
For a randomized trial with integrable potential outcomes and a logistic outcome model at `ξ₀`,
and a target population whose arms `s₀, s₁` are absolutely constant with the trial arms
`t₀, t₁` with overlap `Q_X ≪ T_X`, `Ψ(ξ₀) = g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])`. -/
theorem logisticTarget_eq_marginalEffect {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 ι}
    [IsProbabilityMeasure T.μ] [IsProbabilityMeasure Q.μ] {z : 𝒳 × Bool → κ → ℝ}
    {ξ₀ : κ → ℝ} (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hM : T.LogisticOutcomeModel z ξ₀) (hX₂ : Measurable Q.X) {t₀ t₁ : Bool} {s₀ s₁ : ι}
    (hYQ₀ : Integrable (Q.Y s₀) Q.μ) (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y t₀) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y t₁) Q.μ Q.X (Q.Y s₁)) (hov : Q.covLaw ≪ T.covLaw)
    (g : ℝ → ℝ) : logisticTarget g Q.covLaw z t₀ t₁ ξ₀ = Q.marginalEffect g s₀ s₁ := by
  have hreg := hM.isOutcomeRegression hT hYi
  have h₀ := (integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ₀
    (hT.isCondMean hYi hreg t₀) hsi₀ hov).2
  have h₁ := (integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ₁
    (hT.isCondMean hYi hreg t₁) hsi₁ hov).2
  rw [logisticTarget, linkMarginal, Population.marginalEffect, h₀, h₁]

/-! ### The Bernstein and von Mises theorem for a trial -/

variable [DecidableEq κ]

/-- The limit law of the standardized logistic posterior: `N(0, I(ξ₀)⁻¹)` on `κ → ℝ`, with the
information matrix of the regressor law `R`. -/
noncomputable abbrev logisticLimit (R : Measure (𝒳 × Bool)) (z : 𝒳 × Bool → κ → ℝ)
    (ξ₀ : κ → ℝ) : Measure (κ → ℝ) :=
  (multivariateGaussian 0 (logisticInfo R z ξ₀)⁻¹).map
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)

/-- The limit law `N(0, I(ξ₀)⁻¹)` is centered. -/
theorem integral_id_logisticLimit (R : Measure (𝒳 × Bool)) (z : 𝒳 × Bool → κ → ℝ)
    (ξ₀ : κ → ℝ) : ∫ u, u ∂logisticLimit R z ξ₀ = 0 := by
  rw [logisticLimit, integral_map (by fun_prop) (by fun_prop),
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]

/-- **The Bernstein and von Mises theorem for a trial with a logistic outcome model.** Let the
records `((X, A), Y)` of a randomized trial follow the logistic model at `ξ₀`, with a design
bounded by `B` almost surely in the trial; let `O` be an i.i.d. sample of the records, `K` a
compact neighborhood of `ξ₀`, and `π` a prior density that is measurable, nonnegative,
integrable, continuous at `ξ₀` and positive there. Then the logistic posteriors satisfy
`‖Π_n - N(ξ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability, with `ξ̂_n` the maximum likelihood fit over
`K` and `I(ξ₀)` the information matrix of the regressor law `law(X, A)`. -/
theorem isBernsteinVonMises_logisticOutcomeModel {T : Trial Ω₁ 𝒳 Bool}
    [IsProbabilityMeasure T.μ] {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀) :
    IsBernsteinVonMises P (fun n ω ↦ logisticPosterior p z fun i : Fin n ↦ O i ω)
      (glmMLE logisticDens z K O)
      (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) := by
  have hXA : Measurable fun ω ↦ (T.X ω, T.A ω) := hT.measurable_X.prodMk hT.measurable_A
  have hF : Measurable fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω) :=
    hXA.prodMk (measurable_obsOutcome hT.measurable_A hT.measurable_Y)
  have hR : P.map (fun ω ↦ (O 0 ω).1) = T.μ.map fun ω ↦ (T.X ω, T.A ω) := by
    rw [show (fun ω ↦ (O 0 ω).1) = Prod.fst ∘ O 0 from rfl,
      ← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hO.aemeasurable 0),
      hlaw, Measure.map_map measurable_fst hF]
    rfl
  have hset : MeasurableSet {c : 𝒳 × Bool | ∀ j, |z c j| ≤ B} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_le (continuous_abs.measurable.comp (hM.measurable_z j)) measurable_const
  have hBR : ∀ᵐ c ∂(T.μ.map fun ω ↦ (T.X ω, T.A ω)), ∀ j, |z c j| ≤ B :=
    (ae_map_iff hXA.aemeasurable hset).2 hB
  have hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂(T.μ.map fun ω ↦ (T.X ω, T.A ω)), z c ⬝ᵥ v = 0) → v = 0 :=
    fun v hv ↦ hM.full_rank v (ae_of_ae_map hXA.aemeasurable hv)
  exact isBernsteinVonMises_logistic hO hR hM.measurable_z hBR hfull hK hKξ₀
    (hM.tendstoInMeasure hT hK (mem_of_mem_nhds hKξ₀) hO hlaw) hpm hp0 hpi hpc hpξ₀

/-! ### Coverage of the credible intervals -/

/-- **Coverage of the credible intervals for the standardized logistic target.** Under the
hypotheses of `isBernsteinVonMises_logisticOutcomeModel`, let the maximum likelihood fit be
asymptotically normal, `√n (ξ̂_n - ξ₀) ⇒ Y` with `Y ∼ N(0, I(ξ₀)⁻¹)`, let the target law `ν` have
integrable design coordinates, let `g` be strictly differentiable at the two standardized means,
and let the derivative of `Ψ` at `ξ₀` have positive variance under `N(0, I(ξ₀)⁻¹)`. Then the
equal tailed credible interval of level `1 - α` for `Ψ` under the logistic posterior contains
`Ψ(ξ₀)` with probability tending to `1 - α`. -/
theorem tendsto_credibleInterval_coverage_logisticOutcomeModel {T : Trial Ω₁ 𝒳 Bool}
    [IsProbabilityMeasure T.μ] {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ} (hY : HasLaw Y (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) P')
    (hAN : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • (glmMLE logisticDens z K O n ω - ξ₀)) atTop Y (fun _ ↦ P) P')
    {ν : Measure 𝒳} [IsProbabilityMeasure ν] {t₀ t₁ : Bool}
    (hzi₀ : ∀ j, Integrable (fun x ↦ z (x, t₀) j) ν)
    (hzi₁ : ∀ j, Integrable (fun x ↦ z (x, t₁) j) ν) {g : ℝ → ℝ} (hg : Measurable g)
    {g₀' g₁' : ℝ} (hg₀ : HasStrictDerivAt g g₀' (logisticMean ν z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean ν z t₁ ξ₀))
    (hσ : 0 < Var[logisticTargetDeriv ν z t₀ t₁ g₀' g₁' ξ₀;
      logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀]) {α c : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hc : cdf (gaussianReal 0 1) c = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | logisticTarget g ν z t₀ t₁ ξ₀ ∈
      credibleInterval ((logisticPosterior p z fun i : Fin n ↦ O i ω).map
        (logisticTarget g ν z t₀ t₁)) α}) atTop (𝓝 (1 - α)) :=
  tendsto_credibleInterval_coverage_logisticTarget
    (isBernsteinVonMises_logisticOutcomeModel hT hM hB hK hKξ₀ hO hlaw hpm hp0 hpi hpc
      hpξ₀).isBernsteinVonMisesWeak
    (integral_id_logisticLimit _ z ξ₀) hY hAN hM.measurable_z hzi₀ hzi₁ hg hg₀ hg₁ hσ hα hc

/-- **Coverage of the target marginal effect.** Under the hypotheses of
`tendsto_credibleInterval_coverage_logisticOutcomeModel` for the target law `Q_X`, and those of
`logisticTarget_eq_marginalEffect` for the target arms `s₀, s₁`, the equal tailed credible
interval of level `1 - α` for `Ψ` under the logistic posterior contains the target marginal
effect `g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])` with probability tending to `1 - α`. -/
theorem tendsto_credibleInterval_coverage_marginalEffect {T : Trial Ω₁ 𝒳 Bool}
    {Q : Population Ω₂ 𝒳 ι} [IsProbabilityMeasure T.μ] [IsProbabilityMeasure Q.μ]
    {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ} (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ} (hY : HasLaw Y (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) P')
    (hAN : TendstoInDistribution
      (fun (n : ℕ) ω ↦ √(n : ℝ) • (glmMLE logisticDens z K O n ω - ξ₀)) atTop Y (fun _ ↦ P) P')
    (hX₂ : Measurable Q.X) {t₀ t₁ : Bool} {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y t₀) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y t₁) Q.μ Q.X (Q.Y s₁)) (hov : Q.covLaw ≪ T.covLaw)
    (hzi₀ : ∀ j, Integrable (fun x ↦ z (x, t₀) j) Q.covLaw)
    (hzi₁ : ∀ j, Integrable (fun x ↦ z (x, t₁) j) Q.covLaw) {g : ℝ → ℝ} (hg : Measurable g)
    {g₀' g₁' : ℝ} (hg₀ : HasStrictDerivAt g g₀' (logisticMean Q.covLaw z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean Q.covLaw z t₁ ξ₀))
    (hσ : 0 < Var[logisticTargetDeriv Q.covLaw z t₀ t₁ g₀' g₁' ξ₀;
      logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀]) {α c : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) (hc : cdf (gaussianReal 0 1) c = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | Q.marginalEffect g s₀ s₁ ∈
      credibleInterval ((logisticPosterior p z fun i : Fin n ↦ O i ω).map
        (logisticTarget g Q.covLaw z t₀ t₁)) α}) atTop (𝓝 (1 - α)) := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  rw [← logisticTarget_eq_marginalEffect hT hYi hM hX₂ hYQ₀ hYQ₁ hsi₀ hsi₁ hov g]
  exact tendsto_credibleInterval_coverage_logisticOutcomeModel hT hM hB hK hKξ₀ hO hlaw hpm hp0
    hpi hpc hpξ₀ hY hAN hzi₀ hzi₁ hg hg₀ hg₁ hσ hα hc

end PopulationAdjustment

end CausalInference
