/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.BayesStandardizationCoverageAnchored
public import CausalInference.Estimation.LogisticFitNormalitySelection

/-!
# Coverage of Bayesian standardization with no hypothesis on the fit

The logistic posterior `Π_n` and its equal tailed credible interval for the standardized target
`Ψ` are functions of the data alone; the maximum likelihood fit enters the coverage proofs only
as the centering of the Bernstein and von Mises approximation and of the normal limit of the
fit. Centering at the measurable fit `measurableLogisticFit`, which maximizes the likelihood for
every sample and is almost everywhere measurable, both are proved without any hypothesis on a
fit (`isBernsteinVonMises_logisticOutcomeModel_measurableLogisticFit`,
`Trial.LogisticOutcomeModel.tendstoInDistribution_measurableLogisticFit`).

Hence the three coverage theorems for the logistic fit hold with the measurability hypothesis
on `glmMLE` removed and their conclusions unchanged:

* `tendsto_credibleInterval_coverage_logisticPosterior`: the credible interval for `Ψ` contains
  `Ψ(ξ₀)` with probability tending to `1 - α`;
* `tendsto_credibleInterval_coverage_marginalEffect_logisticPosterior`: it contains the target
  marginal effect `g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])`;
* `tendsto_credibleInterval_coverage_anchored_logisticPosterior`: the credible interval of the
  product posterior for `Ψ(ξ) - d` contains `Ψ(ξ₀) - d₀`.

## Main results

* `tendsto_credibleInterval_coverage_logisticPosterior`,
  `tendsto_credibleInterval_coverage_marginalEffect_logisticPosterior`,
  `tendsto_credibleInterval_coverage_anchored_logisticPosterior`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Theorem 10.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open PosteriorLimit IndirectComparison EffectMeasure BayesStandardization PointTreatment
  Transport

variable {Ω₁ Ω₂ Ξ Ξ₂ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MeasurableSpace Ξ] [MeasurableSpace Ξ₂] [MeasurableSpace 𝒳] [Fintype κ]
  {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ] {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

/-- **Coverage of the credible intervals for the standardized logistic target, with no
hypothesis on the fit.** Let the records `((X, A), Y)` of a randomized trial follow the logistic
outcome model at `ξ₀` with a design bounded almost surely, `O` an i.i.d. sample of the records,
`K` a compact neighborhood of `ξ₀`, and `π` a prior density that is measurable, nonnegative,
integrable, continuous and positive at `ξ₀`. Let the target law `ν` overlap the trial,
`ν ≪ T_X`, let `g` be measurable and strictly differentiable at the two standardized means, and
let the derivative `D Ψ(ξ₀)` be nonzero. Then the equal tailed credible interval of level
`1 - α` for `Ψ` under the logistic posterior contains `Ψ(ξ₀)` with probability tending to
`1 - α`. -/
theorem tendsto_credibleInterval_coverage_logisticPosterior (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
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
  exact tendsto_credibleInterval_coverage_logisticTarget
    (isBernsteinVonMises_logisticOutcomeModel_measurableLogisticFit hT hM hB hK hKξ₀ hO hlaw hpm
      hp0 hpi hpc hpξ₀).isBernsteinVonMisesWeak
    (integral_id_logisticLimit _ z ξ₀) hY
    (hM.tendstoInDistribution_measurableLogisticFit hT hB hK hKξ₀ hO hlaw hY) hM.measurable_z
    (integrable_design_of_absolutelyContinuous hT hM.measurable_z hB hν t₀)
    (integrable_design_of_absolutelyContinuous hT hM.measurable_z hB hν t₁) hg hg₀ hg₁
    (variance_logisticLimit_pos (hM.posDef_logisticInfo hT hB) hD) hα
    (cdf_gaussianReal_quantile_one_sub_half hα)

/-- **Coverage of the target marginal effect, with no hypothesis on the fit.** Under the
hypotheses of `tendsto_credibleInterval_coverage_logisticPosterior` for the target law `Q_X`,
with the overlap `Q_X ≪ T_X`, integrable target potential outcomes of the arms `s₀, s₁`, and
each arm used absolutely constant from the trial to the target, the equal tailed credible
interval of level `1 - α` for `Ψ` under the logistic posterior contains the target marginal
effect `g(E_Q[Y(s₁)]) - g(E_Q[Y(s₀)])` with probability tending to `1 - α`. -/
theorem tendsto_credibleInterval_coverage_marginalEffect_logisticPosterior
    {Q : Population Ω₂ 𝒳 ι} [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
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
  exact tendsto_credibleInterval_coverage_logisticPosterior hT hM hB hK hKξ₀ hO hlaw hpm hp0 hpi
    hpc hpξ₀ hov hg hg₀ hg₁ hD hα

/-- **Anchored coverage of Bayesian standardization, with no hypothesis on the fit.** Let the
index trial satisfy the hypotheses of `tendsto_credibleInterval_coverage_logisticPosterior` with
sampling law `P₁`, and let the comparator be an independent i.i.d. sample `Y` under `P₂`, square
integrable with variance `σ² > 0`, analyzed with the normal location posterior with known
variance `σ²` and a normal prior of variance `τ² > 0`. Under `P₁ ⊗ P₂` the equal tailed credible
interval of level `1 - α` of the product posterior for `Ψ(ξ) - d` contains `Ψ(ξ₀) - E[Y₀]` with
probability tending to `1 - α`. -/
theorem tendsto_credibleInterval_coverage_anchored_logisticPosterior (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P₁ : Measure Ξ} [IsProbabilityMeasure P₁]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P₁)
    (hlaw : P₁.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀)
    {P₂ : Measure Ξ₂} [IsProbabilityMeasure P₂] {Y : ℕ → Ξ₂ → ℝ} (hY : IsIIDSample Y P₂)
    {σ2 : ℝ} (hσ : 0 < σ2) (hvar : Var[Y 0; P₂] = σ2)
    {θp τ2 : ℝ} (hτ : 0 < τ2)
    {ν : Measure 𝒳} [IsProbabilityMeasure ν] (hν : ν ≪ T.covLaw) {t₀ t₁ : Bool}
    {g : ℝ → ℝ} (hg : Measurable g) {g₀' g₁' : ℝ}
    (hg₀ : HasStrictDerivAt g g₀' (logisticMean ν z t₀ ξ₀))
    (hg₁ : HasStrictDerivAt g g₁' (logisticMean ν z t₁ ξ₀)) {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ (P₁.prod P₂).real {ω | anchoredTarget g ν z t₀ t₁ (ξ₀, P₂[Y 0]) ∈
      credibleInterval (((logisticPosterior p z fun i : Fin n ↦ O i ω.1).prod
        (normalLocationPosterior θp τ2 σ2 Y n ω.2)).map (anchoredTarget g ν z t₀ t₁)) α})
      atTop (𝓝 (1 - α)) := by
  classical
  have hY2 : MemLp (Y 0) 2 P₂ := by
    refine (evariance_lt_top_iff_memLp (hY.aemeasurable 0).aestronglyMeasurable).1
      (lt_top_iff_ne_top.2 fun h ↦ ?_)
    rw [variance, h, ENNReal.toReal_top] at hvar
    linarith
  set R := T.μ.map fun ω ↦ (T.X ω, T.A ω)
  set N := (logisticLimit R z ξ₀).prod (gaussianReal 0 σ2.toNNReal)
  have h₁ := isBernsteinVonMises_logisticOutcomeModel_measurableLogisticFit hT hM hB hK hKξ₀ hO
    hlaw hpm hp0 hpi hpc hpξ₀
  have h₂ := normalLocation_isBernsteinVonMises_of_iid (θp := θp) hτ hσ hY
    (hY2.integrable one_le_two)
  have hW := (h₁.prod h₂).isBernsteinVonMisesWeak
  have hA := hM.tendstoInDistribution_measurableLogisticFit hT hB hK hKξ₀ hO hlaw
    (HasLaw.id (μ := logisticLimit R z ξ₀))
  have hmean : P₂[fun ω ↦ (id (Y 0 ω) - P₂[fun ω ↦ id (Y 0 ω)]) ^ 2] = σ2 := by
    rw [← hvar, variance_eq_integral hY2.aemeasurable]
    rfl
  have hC := (sampleMean_isAsymptoticallyLinear (O := Y) measurable_id hY2).tendstoInDistribution
    hY ((isSampleMeasurable_sampleMean measurable_id Y).aemeasurable hY)
    (Y := id) (by rw [hmean]; exact HasLaw.id)
  have hJ := hA.prodMk_of_prod hC
  have hN0 : ∫ u, u ∂N = 0 := integral_id_prod_eq_zero (integral_id_logisticLimit R z ξ₀) _
  exact tendsto_credibleInterval_coverage_logisticTarget_anchored hW hN0 (HasLaw.id (μ := N)) hJ
    hM.measurable_z (integrable_design_of_absolutelyContinuous hT hM.measurable_z hB hν t₀)
    (integrable_design_of_absolutelyContinuous hT hM.measurable_z hB hν t₁) hg hg₀ hg₁
    (variance_comp_fst_sub_snd_pos _ hσ) hα (cdf_gaussianReal_quantile_one_sub_half hα)

end PopulationAdjustment

end CausalInference
