/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.BayesStandardizationCoverage
public import CausalInference.Estimation.PosteriorLimitProduct
public import CausalInference.Estimation.PosteriorLimitNormalLocation

/-!
# Anchored coverage of Bayesian standardization

The anchored comparison subtracts from the standardized logistic target `Ψ(ξ)` of an index
trial the effect `d` of a comparator. The two experiments are independent: the index trial is
an i.i.d. sample of records of a randomized trial with a logistic outcome model, the comparator
an i.i.d. sample `Y_i` with mean `d₀` and variance `σ² > 0`, analyzed with the normal location
model with known variance `σ²` and a normal prior. The joint posterior is the product of the
logistic posterior and the normal location posterior, and the target is `Ψ(ξ) - d`.

Every hypothesis of the anchored coverage theorem is proved:

* the product posteriors satisfy the Bernstein and von Mises conclusion with the limit
  `N(0, I(ξ₀)⁻¹) ⊗ N(0, σ²)` (`IsBernsteinVonMises.prod`);
* the pair of the logistic fit and the comparator sample mean is jointly asymptotically normal
  with the same limit (`TendstoInDistribution.prodMk_of_prod` with the asymptotic normality of
  the fit and the central limit theorem);
* the limiting variance of the derivative `(u, e) ↦ D u - e` is
  `Var(D Z) + σ² ≥ σ² > 0` by independence of the two coordinates of the limit
  (`variance_comp_fst_sub_snd_pos`), so no condition on `D` is needed.

The result is `tendsto_credibleInterval_coverage_anchored_logisticFit`. The variance hypothesis
`Var[Y₀] = σ²` states that the comparator model is correct: it makes the limit of the posterior
spread equal to the limit of the sampling spread of the comparator mean.

## Main results

* `variance_comp_fst_sub_snd_pos`, `integral_id_prod_eq_zero`.
* `tendsto_credibleInterval_coverage_anchored_logisticFit`.

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

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
/-- **The limiting variance of an anchored derivative is positive.** Under
`N₁ ⊗ N(0, σ²)` with `N₁` Gaussian, `Var(D u - e) = Var(D u) + σ² ≥ σ² > 0`. -/
theorem variance_comp_fst_sub_snd_pos [Finite κ] {N₁ : Measure (κ → ℝ)} [IsGaussian N₁]
    (D : (κ → ℝ) →L[ℝ] ℝ) {σ2 : ℝ} (hσ : 0 < σ2) :
    0 < Var[D.comp (ContinuousLinearMap.fst ℝ _ ℝ) - ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ;
      N₁.prod (gaussianReal 0 σ2.toNNReal)] := by
  have := Fintype.ofFinite κ
  set G := gaussianReal 0 σ2.toNNReal
  have hfun : ⇑(D.comp (ContinuousLinearMap.fst ℝ _ ℝ) - ContinuousLinearMap.snd ℝ (κ → ℝ) ℝ) =
      (fun x : (κ → ℝ) × ℝ ↦ D x.1) + fun x ↦ (fun e : ℝ ↦ -e) x.2 := by
    funext x; simp [sub_eq_add_neg]
  have hD2 : MemLp (fun x : (κ → ℝ) × ℝ ↦ D x.1) 2 (N₁.prod G) :=
    (IsGaussian.memLp_dual N₁ D 2 (by simp)).comp_measurePreserving measurePreserving_fst
  have hG2 : MemLp (fun e : ℝ ↦ -e) 2 G := (IsGaussian.memLp_two_id (μ := G)).neg
  have hN2 : MemLp (fun x : (κ → ℝ) × ℝ ↦ (fun e : ℝ ↦ -e) x.2) 2 (N₁.prod G) :=
    hG2.comp_measurePreserving measurePreserving_snd
  have hind := indepFun_prod (μ := N₁) (ν := G) D.continuous.measurable measurable_neg
  rw [hfun, IndepFun.variance_add hD2 hN2 hind]
  have hsnd : Var[fun x : (κ → ℝ) × ℝ ↦ (fun e : ℝ ↦ -e) x.2; N₁.prod G] = σ2 := by
    have h := variance_map (X := fun e : ℝ ↦ -e) (μ := N₁.prod G) (Y := Prod.snd)
      measurable_neg.aemeasurable measurable_snd.aemeasurable
    rw [Measure.map_snd_prod, measure_univ, one_smul] at h
    rw [← Function.comp_def, ← h, variance_fun_neg, variance_fun_id_gaussianReal,
      Real.coe_toNNReal _ hσ.le]
  rw [hsnd]
  linarith [variance_nonneg (fun x : (κ → ℝ) × ℝ ↦ D x.1) (N₁.prod G)]

/-- A product of centered Gaussian laws is centered. -/
theorem integral_id_prod_eq_zero {N₁ : Measure (κ → ℝ)} [IsGaussian N₁]
    (h₁ : ∫ u, u ∂N₁ = 0) (v : ℝ≥0) :
    ∫ u, u ∂(N₁.prod (gaussianReal 0 v)) = 0 := by
  have hi : Integrable (fun u : (κ → ℝ) × ℝ ↦ u) (N₁.prod (gaussianReal 0 v)) :=
    IsGaussian.memLp_two_id.integrable one_le_two
  have e : (fun u : (κ → ℝ) × ℝ ↦ u) = fun u ↦ (u.1, u.2) := rfl
  rw [e, integral_pair hi.fst hi.snd, integral_fun_fst (f := fun u : κ → ℝ ↦ u),
    integral_fun_snd (f := fun u : ℝ ↦ u), h₁, integral_id_gaussianReal]
  simp

variable {Ω₁ Ξ₁ Ξ₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ₁] [MeasurableSpace Ξ₂]
  [MeasurableSpace 𝒳] {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ]
  {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

/-- **Anchored coverage of Bayesian standardization.** Let the index trial satisfy the
hypotheses of `tendsto_credibleInterval_coverage_logisticFit` with sampling law `P₁`, and let
the comparator be an independent i.i.d. sample `Y` under `P₂`, square integrable with variance
`σ² > 0`, analyzed with the normal location posterior with known variance `σ²` and a normal
prior of variance `τ² > 0`. Under `P₁ ⊗ P₂` the equal tailed credible interval of level `1 - α`
of the product posterior for `Ψ(ξ) - d` contains `Ψ(ξ₀) - E[Y₀]` with probability tending to
`1 - α`. -/
theorem tendsto_credibleInterval_coverage_anchored_logisticFit (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P₁ : Measure Ξ₁} [IsProbabilityMeasure P₁]
    {O : ℕ → Ξ₁ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P₁)
    (hlaw : P₁.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    (hξm : ∀ n, AEMeasurable (glmMLE logisticDens z K O n) P₁)
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
  have h₁ := isBernsteinVonMises_logisticOutcomeModel hT hM hB hK hKξ₀ hO hlaw hpm hp0 hpi hpc
    hpξ₀
  have h₂ := normalLocation_isBernsteinVonMises_of_iid (θp := θp) hτ hσ hY
    (hY2.integrable one_le_two)
  have hW := (h₁.prod h₂).isBernsteinVonMisesWeak
  have hA := hM.tendstoInDistribution_glmMLE hT hB hK hKξ₀ hO hlaw hξm
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
