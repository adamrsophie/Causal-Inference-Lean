/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LogisticFitNormalitySelectionAgreement
public import CausalInference.Estimation.MeasurableMaximizerGLM

/-!
# Asymptotic normality of every logistic maximum likelihood fit

Let `O` be an i.i.d. sample of records with law `P_{ξ₀}` of the logistic family, with a design
bounded and of full rank under the regressor law `R`, and let `K` be a compact neighborhood of
`ξ₀`. Let `θ̂` be **any** sequence that, for every `n`, almost surely lies in `K` and maximizes
the likelihood of the first `n` records over `K`.

* **Normality** (`tendstoInDistribution_sqrt_smul_logistic_of_isMaxOn`): if each `θ̂_n` is
  almost everywhere measurable, `√n (θ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)`. The proof is the vector
  Z-estimator theorem for the logistic score; consistency and the score equations hold for every
  maximizer sequence (`tendstoInMeasure_logisticFamily_of_isMaxOn`,
  `withProbTendingToOne_logisticScoreSum_eq_zero_of_isMaxOn`).
* **The measurable fit** (`tendstoInDistribution_sqrt_smul_measurableLogisticFit`): the fit
  `measurableLogisticFit` is a maximizer for every sample and is almost everywhere measurable,
  so normality holds for it with no hypothesis beyond the model.
* **The posterior** (`isBernsteinVonMises_logistic_of_isMaxOn`): for a prior density integrable,
  continuous and positive at `ξ₀`, `‖Π_n - N(θ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability, for every
  maximizer sequence `θ̂`, measurable or not: it agrees with `glmMLE` with probability tending
  to one (`withProbTendingToOne_glmMLE_eq_of_isMaxOn`).

The trial forms are `Trial.LogisticOutcomeModel.tendstoInDistribution_of_isMaxOn`,
`Trial.LogisticOutcomeModel.tendstoInDistribution_measurableLogisticFit` and
`isBernsteinVonMises_logisticOutcomeModel_of_isMaxOn`.

For `glmMLE` itself the measurability hypothesis of
`tendstoInDistribution_sqrt_smul_glmMLE_logistic` stays: convergence in distribution includes
almost everywhere measurability of the sequence, and `glmMLE` is a choice among maximizers made
without regard to it.

## Main results

* `tendstoInDistribution_sqrt_smul_logistic_of_isMaxOn`,
  `tendstoInDistribution_sqrt_smul_measurableLogisticFit`,
  `isBernsteinVonMises_logistic_of_isMaxOn`.
* `Trial.LogisticOutcomeModel.tendstoInDistribution_of_isMaxOn`,
  `Trial.LogisticOutcomeModel.tendstoInDistribution_measurableLogisticFit`,
  `isBernsteinVonMises_logisticOutcomeModel_of_isMaxOn`,
  `isBernsteinVonMises_logisticOutcomeModel_measurableLogisticFit`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 5 and
  Theorem 10.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open PopulationAdjustment PopulationAdjustment.BayesStandardization

variable {C κ : Type*} [Fintype κ] [MeasurableSpace C] {R : Measure C} [IsProbabilityMeasure R]
  {z : C → κ → ℝ} {hz : ∀ j, Measurable fun c ↦ z c j}
  {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
  {O : ℕ → Ξ → C × ℝ} {K : Set (κ → ℝ)} {ξ₀ : κ → ℝ} {B : ℝ}

omit [MeasurableSpace C] [IsProbabilityMeasure P] in
/-- A maximizer sequence in Euclidean coordinates is a root of the score equations with
probability tending to one. -/
lemma withProbTendingToOne_sum_logisticEstFun_of_isMaxOn (hKξ₀ : K ∈ 𝓝 ξ₀)
    {θh : ℕ → Ξ → κ → ℝ}
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω))
    (hcons : TendstoInMeasure P θh atTop (fun _ ↦ ξ₀)) :
    WithProbTendingToOne P fun n ↦ {ω | ∑ i ∈ range n,
      logisticEstFun z (O i ω) (WithLp.toLp 2 (θh n ω)) = 0} := by
  refine (withProbTendingToOne_logisticScoreSum_eq_zero_of_isMaxOn hKξ₀ hmax hcons).mono
    fun n ω h ↦ ?_
  simp only [Set.mem_ofPred_eq] at h ⊢
  have e : ∑ i ∈ range n, logisticEstFun z (O i ω) (WithLp.toLp 2 (θh n ω)) =
      WithLp.toLp 2 (logisticScoreSum z (fun i : Fin n ↦ O i ω) (θh n ω)) := by
    rw [logisticScoreSum, WithLp.toLp_sum, ← Fin.sum_univ_eq_sum_range
      (fun i ↦ logisticEstFun z (O i ω) (WithLp.toLp 2 (θh n ω)))]
    rfl
  rw [e, h]
  rfl

variable [DecidableEq κ]

/-- **Asymptotic normality of every logistic maximum likelihood fit.** Let `O` be an i.i.d.
sample with law `P_{ξ₀}` of the logistic family with regressor law `R`, the design bounded by `B`
and of full rank `R`-almost surely, `K` a compact neighborhood of `ξ₀`, and `θ̂` any sequence of
almost everywhere measurable maps such that for every `n`, almost surely, `θ̂_n ∈ K` maximizes
the likelihood of the first `n` records over `K`. Then `√n (θ̂_n - ξ₀)` converges in
distribution to every random vector with law `N(0, I(ξ₀)⁻¹)` on `κ → ℝ`. -/
theorem tendstoInDistribution_sqrt_smul_logistic_of_isMaxOn (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hKξ₀ : K ∈ 𝓝 ξ₀) {θh : ℕ → Ξ → κ → ℝ}
    (hθm : ∀ n, AEMeasurable (θh n) P)
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ}
    (hY : HasLaw Y ((multivariateGaussian 0 (logisticInfo R z ξ₀)⁻¹).map
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - ξ₀)) atTop Y (fun _ ↦ P) P' := by
  have hzm : Measurable z := measurable_pi_iff.2 hz
  have hI := posDef_logisticInfo hzm hB hfull ξ₀
  have hcons := tendstoInMeasure_logisticFamily_of_isMaxOn hO hlaw hB hfull hK
    (mem_of_mem_nhds hKξ₀) hmax
  have hψm : Measurable fun q : C × ℝ ↦ logisticEstFun z q (WithLp.toLp 2 ξ₀) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun k ↦
      (measurable_logisticDensScore_design hz ξ₀).mul ((hz k).comp measurable_fst))
  have hJm : ∀ θ ∈ Metric.closedBall (WithLp.toLp 2 ξ₀ : EuclideanSpace ℝ κ) 1, ∀ i j,
      Measurable fun q : C × ℝ ↦ logisticEstJac z q θ i j := fun θ _ i j ↦
    ((((measurable_sigmoidWeight_dotProduct hzm (WithLp.ofLp θ)).mul (hz i)).mul
      (hz j)).comp measurable_fst).neg
  have hcont : ∀ q : C × ℝ, ∀ i j, Continuous fun θ : EuclideanSpace ℝ κ ↦
      logisticEstJac z q θ i j := fun q i j ↦
    (((continuous_sigmoidWeight.comp
      (continuous_const.dotProduct (PiLp.continuous_ofLp 2 _))).mul continuous_const).mul
      continuous_const).neg
  have hdom : ∀ᵐ q ∂(P.map (O 0)), ∀ θ ∈ Metric.closedBall
      (WithLp.toLp 2 ξ₀ : EuclideanSpace ℝ κ) 1, ∀ i j,
      |logisticEstJac z q θ i j| ≤ (fun _ ↦ (max B 0) ^ 2) q := by
    rw [hlaw]
    refine (ae_abs_design_le hB).mono fun q hq θ _ i j ↦ ?_
    simp only [logisticEstJac, Matrix.of_apply, abs_neg]
    have h1 : |sigmoidWeight (z q.1 ⬝ᵥ WithLp.ofLp θ)| ≤ 1 := by
      rw [abs_of_pos (sigmoidWeight_pos _)]; exact sigmoidWeight_le_one _
    simpa using abs_mul_le_of_abs_le (le_max_right B 0) h1 abs_one.le (hq i) (hq j)
  have hzero : P[fun ω ↦ logisticEstFun z (O 0 ω) (WithLp.toLp 2 ξ₀)] = 0 := by
    rw [← integral_map (hO.aemeasurable 0) hψm.aestronglyMeasurable, hlaw,
      integral_logisticEstFun_eq_zero hB]
  have hA : (breadMatrix (P.map (O 0)) (logisticEstJac z) (WithLp.toLp 2 ξ₀)).det ≠ 0 := by
    rw [hlaw, breadMatrix_logisticEstJac hB]; exact hI.det_pos.ne'
  have hYE := hasLaw_toLp_of_hasLaw hY
  rw [← sandwich_logisticInfo (hz := hz) hB hI, ← hlaw] at hYE
  have h := vectorZEstimator_tendstoInDistribution_of_root hO one_pos hψm hJm
    (ae_of_all _ fun q θ _ ↦ hasFDerivAt_logisticEstFun z q θ)
    (ae_of_all _ fun q i j ↦ (hcont q i j).continuousOn) (integrable_const _) hdom hzero
    (memLp_logisticEstFun hO hlaw hB) hA
    (θh := fun n ω ↦ WithLp.toLp 2 (θh n ω))
    (fun n ↦ (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable (hθm n))
    (hcons.comp_continuousAt (PiLp.continuous_toLp 2 _).continuousAt)
    (withProbTendingToOne_sum_logisticEstFun_of_isMaxOn hKξ₀ hmax hcons) hYE
  exact h.continuous_comp (PiLp.continuous_ofLp 2 _)

/-- **Asymptotic normality of the measurable logistic fit, with no measurability hypothesis.**
Under the model hypotheses of `tendstoInDistribution_sqrt_smul_logistic_of_isMaxOn`, the
measurable fit over `K` (`measurableLogisticFit`) satisfies `√n (θ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)`. -/
theorem tendstoInDistribution_sqrt_smul_measurableLogisticFit (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hKξ₀ : K ∈ 𝓝 ξ₀)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ}
    (hY : HasLaw Y ((multivariateGaussian 0 (logisticInfo R z ξ₀)⁻¹).map
      (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (measurableLogisticFit z K O n ω - ξ₀))
      atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_sqrt_smul_logistic_of_isMaxOn hO hlaw hB hfull hK hKξ₀
    (aemeasurable_measurableLogisticFit hz hK ⟨ξ₀, mem_of_mem_nhds hKξ₀⟩ hO.aemeasurable)
    (fun n ↦ ae_of_all _ fun ω ↦
      measurableLogisticFit_mem_isMaxOn hz hK ⟨ξ₀, mem_of_mem_nhds hKξ₀⟩ O n ω) hY

/-- **The Bernstein and von Mises theorem for every logistic maximizer sequence.** Let `O` be an
i.i.d. sample with law `P_{ξ₀}` of the logistic family with regressor law `R`, the design bounded
and of full rank under `R`, `K` a compact neighborhood of `ξ₀`, `θ̂` any sequence such that for
every `n`, almost surely, `θ̂_n ∈ K` maximizes the likelihood of the first `n` records over `K`,
and `π` a prior density measurable, nonnegative, integrable, continuous at `ξ₀` and positive
there. Then `‖Π_n - N(θ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability. No measurability of `θ̂` is
needed. -/
theorem isBernsteinVonMises_logistic_of_isMaxOn (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = (glmFamily logisticKernel R z hz).law ξ₀)
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (hK : IsCompact K) (hKξ₀ : K ∈ 𝓝 ξ₀) {θh : ℕ → Ξ → κ → ℝ}
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀) :
    IsBernsteinVonMises P (fun n ω ↦ logisticPosterior p z fun i : Fin n ↦ O i ω) θh
      ((multivariateGaussian 0 (logisticInfo R z ξ₀)⁻¹).map
        (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ ↦ ℝ)) :=
  (isBernsteinVonMises_logistic hO (map_fst_eq_of_map_eq_logisticFamily hO hlaw) hz hB hfull hK
    hKξ₀ (tendstoInMeasure_glmMLE_logisticFamily hO hlaw hB hfull hK (mem_of_mem_nhds hKξ₀))
    hpm hp0 hpi hpc hpξ₀).congr_withProbTendingToOne
    (withProbTendingToOne_glmMLE_eq_of_isMaxOn hO hlaw hB hfull hK hKξ₀ hmax)

end PosteriorLimit

/-! ### The trial form -/

namespace IndirectComparison

open PosteriorLimit PopulationAdjustment

variable {Ω₁ Ξ 𝒳 κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [Fintype κ] [DecidableEq κ] {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ]
  {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

omit [DecidableEq κ] in
/-- The design bound and full rank of a trial with a logistic outcome model, on the law of the
covariates and the arm. -/
lemma Trial.LogisticOutcomeModel.bound_fullRank (hT : T.IsRandomizedTwoArm)
    (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) :
    (∀ᵐ c ∂(T.μ.map fun ω ↦ (T.X ω, T.A ω)), ∀ j, |z c j| ≤ B) ∧
      ∀ v : κ → ℝ, (∀ᵐ c ∂(T.μ.map fun ω ↦ (T.X ω, T.A ω)), z c ⬝ᵥ v = 0) → v = 0 := by
  have hXA : Measurable fun ω ↦ (T.X ω, T.A ω) := hT.measurable_X.prodMk hT.measurable_A
  have hset : MeasurableSet {c : 𝒳 × Bool | ∀ j, |z c j| ≤ B} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_le (continuous_abs.measurable.comp (hM.measurable_z j)) measurable_const
  exact ⟨(ae_map_iff hXA.aemeasurable hset).2 hB,
    fun v hv ↦ hM.full_rank v (ae_of_ae_map hXA.aemeasurable hv)⟩

/-- **Asymptotic normality of every logistic fit in a randomized trial.** Let the records
`((X, A), Y)` of a randomized trial follow the logistic outcome model at `ξ₀` with a design
bounded by `B` almost surely, `O` an i.i.d. sample of the records, `K` a compact neighborhood of
`ξ₀`, and `θ̂` a sequence of almost everywhere measurable maps such that for every `n`, almost
surely, `θ̂_n ∈ K` maximizes the likelihood of the first `n` records over `K`. Then
`√n (θ̂_n - ξ₀)` converges in distribution to every random vector with law `N(0, I(ξ₀)⁻¹)`. -/
theorem Trial.LogisticOutcomeModel.tendstoInDistribution_of_isMaxOn
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {θh : ℕ → Ξ → κ → ℝ} (hθm : ∀ n, AEMeasurable (θh n) P)
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ} (hY : HasLaw Y (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - ξ₀)) atTop Y (fun _ ↦ P) P' :=
  have h := hM.bound_fullRank hT hB
  tendstoInDistribution_sqrt_smul_logistic_of_isMaxOn hO (hlaw.trans hM.law_eq) h.1 h.2 hK hKξ₀
    hθm hmax hY

/-- **Asymptotic normality of the measurable logistic fit in a randomized trial, with no
measurability hypothesis.** Under the hypotheses of
`Trial.LogisticOutcomeModel.tendstoInDistribution_glmMLE` without its measurability hypothesis,
the measurable fit over `K` satisfies `√n (θ̂_n - ξ₀) ⇒ N(0, I(ξ₀)⁻¹)`. -/
theorem Trial.LogisticOutcomeModel.tendstoInDistribution_measurableLogisticFit
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → κ → ℝ} (hY : HasLaw Y (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (measurableLogisticFit z K O n ω - ξ₀))
      atTop Y (fun _ ↦ P) P' :=
  hM.tendstoInDistribution_of_isMaxOn hT hB hK hKξ₀ hO hlaw
    (aemeasurable_measurableLogisticFit hM.measurable_z hK ⟨ξ₀, mem_of_mem_nhds hKξ₀⟩
      hO.aemeasurable)
    (fun n ↦ ae_of_all _ fun ω ↦ measurableLogisticFit_mem_isMaxOn hM.measurable_z hK
      ⟨ξ₀, mem_of_mem_nhds hKξ₀⟩ O n ω) hY

end IndirectComparison

namespace PopulationAdjustment

open PosteriorLimit IndirectComparison

variable {Ω₁ Ξ 𝒳 κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [Fintype κ] [DecidableEq κ] {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ]
  {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

/-- **The Bernstein and von Mises theorem for a trial, centered at any maximizer sequence.**
Under the hypotheses of `isBernsteinVonMises_logisticOutcomeModel`, for every sequence `θ̂` such
that for every `n`, almost surely, `θ̂_n ∈ K` maximizes the likelihood of the first `n` records
over `K`, `‖Π_n - N(θ̂_n, n⁻¹ I(ξ₀)⁻¹)‖_TV → 0` in probability. -/
theorem isBernsteinVonMises_logisticOutcomeModel_of_isMaxOn
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {θh : ℕ → Ξ → κ → ℝ}
    (hmax : ∀ n, ∀ᵐ ω ∂P, θh n ω ∈ K ∧
      IsMaxOn (glmLikelihood logisticDens z fun i : Fin n ↦ O i ω) K (θh n ω))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀) :
    IsBernsteinVonMises P (fun n ω ↦ logisticPosterior p z fun i : Fin n ↦ O i ω) θh
      (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) :=
  have h := hM.bound_fullRank hT hB
  isBernsteinVonMises_logistic_of_isMaxOn hO (hlaw.trans hM.law_eq) h.1 h.2 hK hKξ₀ hmax hpm hp0
    hpi hpc hpξ₀

/-- **The Bernstein and von Mises theorem for a trial, centered at the measurable fit.** -/
theorem isBernsteinVonMises_logisticOutcomeModel_measurableLogisticFit
    (hT : T.IsRandomizedTwoArm) (hM : T.LogisticOutcomeModel z ξ₀) {B : ℝ}
    (hB : ∀ᵐ ω ∂T.μ, ∀ j, |z (T.X ω, T.A ω) j| ≤ B) {K : Set (κ → ℝ)} (hK : IsCompact K)
    (hKξ₀ : K ∈ 𝓝 ξ₀) {P : Measure Ξ} [IsProbabilityMeasure P]
    {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω ↦ ((T.X ω, T.A ω), T.obsOutcome ω))
    {p : (κ → ℝ) → ℝ} (hpm : Measurable p) (hp0 : ∀ ξ, 0 ≤ p ξ) (hpi : Integrable p)
    (hpc : ContinuousAt p ξ₀) (hpξ₀ : 0 < p ξ₀) :
    IsBernsteinVonMises P (fun n ω ↦ logisticPosterior p z fun i : Fin n ↦ O i ω)
      (measurableLogisticFit z K O) (logisticLimit (T.μ.map fun ω ↦ (T.X ω, T.A ω)) z ξ₀) :=
  isBernsteinVonMises_logisticOutcomeModel_of_isMaxOn hT hM hB hK hKξ₀ hO hlaw
    (fun n ↦ ae_of_all _ fun ω ↦ measurableLogisticFit_mem_isMaxOn hM.measurable_z hK
      ⟨ξ₀, mem_of_mem_nhds hKξ₀⟩ O n ω) hpm hp0 hpi hpc hpξ₀

end PopulationAdjustment

end CausalInference
