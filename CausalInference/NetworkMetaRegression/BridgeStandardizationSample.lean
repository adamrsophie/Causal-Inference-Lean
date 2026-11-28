/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.BridgeStandardization
public import CausalInference.PopulationAdjustment.WeightedConsistencySharpCommonLimit
public import CausalInference.PopulationAdjustment.WeightedNormalityWaldTwoSample
public import CausalInference.PopulationAdjustment.StandardizationConsistencyConditional

/-!
# The common limit of weighting and standardization at estimated target moments

`MultilevelModel.commonLimit_anchored_identity` balances the trial on the exact target feature
means `t`. In practice the target reports estimated moments `t̂_n`, for instance the sample means
of the features in a target sample independent of the trial. This file replaces `t` by random
reported moments `t̂_n = G_n(W)` that converge in probability to the target feature mean `t` and
are independent of the trial sample.

* **The general statement** (`MultilevelModel.commonLimit_anchored_identity_reportedMoments`):
  in a randomized trial whose regression is the multilevel predictor `η_k(φ(x))` at the trial
  baseline `μ_T` with the identity link, and a target whose conditional means of `Y(a), Y(b),
  Y(c)` are `η_k(φ(x))` at a target baseline `α_Q`, the least squares fit converges to
  `ipdCoef M μ_T a c`; the anchored entropy balancing comparison at `t̂_n` is consistent for the
  target effect of `b` against `a`; the anchored standardized comparison, the fitted arms
  evaluated at `t̂_n`, converges to the same limit; their difference converges to `0`; and the
  limit is the multilevel target effect `linkMarginal id (Q_X ∘ φ⁻¹) (η_a) (η_b)
  = (γ_b - γ_a) + tᵀ(β₂,b - β₂,a)`.
* **Sample means of an independent target sample**
  (`MultilevelModel.commonLimit_anchored_identity_targetSample`): on the product of the trial
  sample space and the target sample space, the sample means of the features of an i.i.d.
  sample from the target covariate law satisfy every condition on `t̂_n`.
* **An instance** (`commonLimitExample_anchored_targetSample`): the binary covariate example of
  `commonLimit_anchored_identity_example` with the reported moments estimated from an i.i.d.
  target sample; every hypothesis holds and the limit is `-5/4`.

The features may be unbounded: only a finite exponential moment in the trial and integrability
in the target are used.

## Main definitions

* `commonLimitExampleTargetSampleLaw`: the law of an i.i.d. target sample in the instance.

## Main results

* `MultilevelModel.commonLimit_anchored_identity_reportedMoments`
* `MultilevelModel.commonLimit_anchored_identity_targetSample`
* `commonLimitExample_anchored_targetSample`

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport PopulationAdjustment

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

variable {Ω₁ Ω₂ Ξ 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 K}
  {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {W : Ξ → 𝒲} {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **The multilevel model in the two study network at estimated target moments: weighting and
standardization share the multilevel limit.** Let the trial of `a` (arm `true`) against `c`
(arm `false`) be a randomized two arm trial with square integrable outcomes, whose regression of
the outcome on the covariates and the arm is the multilevel predictor `η_k(φ(x))` at the baseline
`μ_T` with the identity link, with a bounded conditional variance of the residual in each arm.
Let the features be measurable with a finite exponential moment around `t` in the trial and `t`
in the interior of the closed convex hull of the support of the trial feature law. Let the
conditional means of `Y(a), Y(b), Y(c)` in the target be `η_k(φ(x))` at a target baseline `α_Q`,
with integrable potential outcomes and features, and `t` the target feature mean. Let the
reported moments `t̂_n = G_n(W)` be measurable, independent of the trial sample, and converge in
probability to `t`, and the reported contrast `d̂_bc` converge in probability to the target effect
of `c` against `b`. Then for an i.i.d. sample of the trial:

* the least squares fit converges in probability to `ipdCoef M μ_T a c`;
* the anchored entropy balancing comparison at `t̂_n` is consistent for the target effect of `b`
  against `a` on the mean scale;
* the anchored standardized comparison, the fitted arms evaluated at `t̂_n`, converges in
  probability to the same limit;
* their difference converges in probability to `0`;
* the limit is `linkMarginal id (Q_X ∘ φ⁻¹) m_a m_b` with `m_k(u) = η_k(u)` at `α_Q`, and it
  equals `(γ_b - γ_a) + tᵀ(β₂,b - β₂,a)`.

The relative constancy of the conditional contrast between the trial and the target, the linear
outcome model of the trial and the convergence of the fit are derived. -/
theorem commonLimit_anchored_identity_reportedMoments [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (M : MultilevelModel J K p)
    {μT αQ : ℝ} {a b c : K} (hT : T.IsRandomizedTwoArm) (hY2 : ∀ e, MemLp (T.Y e) 2 T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun e x => M.eta μT (if e then a else c) (φ x))
    (hφ : Measurable φ) (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) {σ2 : ℝ}
    (hvar : ∀ e : Bool, T.μ[fun ω => (T.Y e ω - M.eta μT (if e then a else c) (φ (T.X ω))) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (hYa : Integrable (Q.Y a) Q.μ) (hYb : Integrable (Q.Y b) Q.μ) (hYc : Integrable (Q.Y c) Q.μ)
    (ha : Q.IsCondMean a fun x => M.eta αQ a (φ x))
    (hb : Q.IsCondMean b fun x => M.eta αQ b (φ x))
    (hc : Q.IsCondMean c fun x => M.eta αQ c (φ x))
    {dbc : ℕ → Ξ → ℝ} (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect id b c) :
    TendstoInMeasure P (leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse
      O) atTop (fun _ => M.ipdCoef μT a c) ∧
    IsConsistent (fun n ω => (sampleBalancedArmMean φ (G n (W ω)) O false n ω -
        sampleBalancedArmMean φ (G n (W ω)) O true n ω) - dbc n ω)
        (Q.marginalEffect id a b) P ∧
    TendstoInMeasure P (fun n ω => (reportedMomentsArmFit φ O (G n (W ω)) false n ω -
        reportedMomentsArmFit φ O (G n (W ω)) true n ω) - dbc n ω) atTop
        (fun _ => Q.marginalEffect id a b) ∧
    TendstoInMeasure P (fun n ω => ((reportedMomentsArmFit φ O (G n (W ω)) false n ω -
        reportedMomentsArmFit φ O (G n (W ω)) true n ω) - dbc n ω) -
          ((sampleBalancedArmMean φ (G n (W ω)) O false n ω -
            sampleBalancedArmMean φ (G n (W ω)) O true n ω) - dbc n ω)) atTop
        (fun _ => 0) ∧
    Q.marginalEffect id a b =
      linkMarginal id (Q.covLaw.map φ) (M.surface id αQ a) (M.surface id αQ b) ∧
    Q.marginalEffect id a b = (M.γ b - M.γ a) + t ⬝ᵥ (M.β₂ b - M.β₂ a) := by
  have hz := M.featureInteractionDesign_dotProduct_ipdCoef μT a c φ
  have hreg' : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun e x => featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μT a c := by
    simpa only [hz] using hreg
  have hM := T.linearOutcomeModel_of_interior hT hY2 hφ hint (hexp 1) hreg'
  have hvar' : ∀ e : Bool, T.μ[fun ω => (T.Y e ω -
      featureInteractionDesign φ e (T.X ω) ⬝ᵥ M.ipdCoef μT a c) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2 := fun e => by
    simpa only [hz] using hvar e
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  have hrel : (fun ω => featureInteractionDesign φ false (Q.X ω) ⬝ᵥ M.ipdCoef μT a c -
      featureInteractionDesign φ true (Q.X ω) ⬝ᵥ M.ipdCoef μT a c) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance] := by
    filter_upwards [condExp_sub hYc hYa (MeasurableSpace.comap Q.X inferInstance), ha.2, hc.2]
      with ω h1 h2 h3
    change _ = Q.μ[Q.Y c - Q.Y a | MeasurableSpace.comap Q.X inferInstance] ω
    rw [h1, Pi.sub_apply, ← h2, ← h3, hz, hz]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    linarith [M.eta_sub_eta μT αQ c (φ (Q.X ω)), M.eta_sub_eta μT αQ a (φ (Q.X ω))]
  obtain ⟨h1, h2, h3⟩ := commonLimit_reportedMoments_anchored_identity hT hY2 hφ hint hexp hreg'
    hO hOm hlaw hW hWO hG htm hvar' hX₂ hQφ ht hYa hYc hrel hdbc
  have hme := Population.marginalEffect_eq_linkMarginal id hX₂ hYa hYb ha hb
  have hmap : linkMarginal id Q.covLaw (fun x => M.eta αQ a (φ x)) (fun x => M.eta αQ b (φ x)) =
      linkMarginal id (Q.covLaw.map φ) (M.surface id αQ a) (M.surface id αQ b) := by
    simp only [linkMarginal, surface, id]
    rw [integral_map hφ.aemeasurable (M.continuous_eta αQ b).aestronglyMeasurable,
      integral_map hφ.aemeasurable (M.continuous_eta αQ a).aestronglyMeasurable]
  refine ⟨hM.tendstoInMeasure hT hO hlaw, h1, h2, h3, hme.trans hmap, ?_⟩
  rw [hme]
  simp only [linkMarginal, id]
  rw [M.integral_eta_comp αQ b hQφ, M.integral_eta_comp αQ a hQφ]
  have htv : (fun i => ∫ x, φ x i ∂Q.covLaw) = t := funext ht
  rw [htv]
  simp only [dotProduct_add, dotProduct_sub]
  ring

/-! ### Reported moments from an independent target sample -/

variable {Ξ₁ Ξ₂ : Type*} [MeasurableSpace Ξ₁] [MeasurableSpace Ξ₂] {P₁ : Measure Ξ₁}
  {P₂ : Measure Ξ₂}

/-- **The multilevel limit at the sample means of an independent target sample.** Under the
hypotheses of `commonLimit_anchored_identity_reportedMoments` on the trial and the target, let
`O` be a measurable i.i.d. sample of the trial on `Ξ₁` and `X*` a measurable i.i.d. sample of the
target covariates on `Ξ₂`, with law `Q_X`. On the product `Ξ₁ × Ξ₂` of the two sample spaces,
with the reported moments the feature means `t̂_n = n⁻¹ Σ_{i<n} φ(X*_i)` of the target sample,
the anchored entropy balancing comparison and the anchored standardized comparison at `t̂_n`
both converge in probability to the target effect of `b` against `a`, their difference
converges in probability to `0`, and the limit is `(γ_b - γ_a) + tᵀ(β₂,b - β₂,a)`. The
independence of the two samples, the i.i.d. structure of each on the product and the
convergence of `t̂_n` to `t` are derived. -/
theorem commonLimit_anchored_identity_targetSample [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] [IsProbabilityMeasure Q.μ]
    (M : MultilevelModel J K p) {μT αQ : ℝ} {a b c : K} (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ e, MemLp (T.Y e) 2 T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun e x => M.eta μT (if e then a else c) (φ x))
    (hφ : Measurable φ) (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {O : ℕ → Ξ₁ → 𝒳 × Bool × ℝ} (hO : IsIIDSample O P₁) (hOm : ∀ i, Measurable (O i))
    (hlaw : P₁.map (O 0) = T.ipdLaw) {Xs : ℕ → Ξ₂ → 𝒳} (hXs : IsIIDSample Xs P₂)
    (hXsm : ∀ i, Measurable (Xs i)) (hXlaw : P₂.map (Xs 0) = Q.covLaw) {σ2 : ℝ}
    (hvar : ∀ e : Bool, T.μ[fun ω => (T.Y e ω - M.eta μT (if e then a else c) (φ (T.X ω))) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (hYa : Integrable (Q.Y a) Q.μ) (hYb : Integrable (Q.Y b) Q.μ) (hYc : Integrable (Q.Y c) Q.μ)
    (ha : Q.IsCondMean a fun x => M.eta αQ a (φ x))
    (hb : Q.IsCondMean b fun x => M.eta αQ b (φ x))
    (hc : Q.IsCondMean c fun x => M.eta αQ c (φ x))
    {dbc : ℕ → Ξ₁ × Ξ₂ → ℝ}
    (hdbc : TendstoInMeasure (P₁.prod P₂) dbc atTop fun _ => Q.marginalEffect id b c) :
    IsConsistent (fun n ω =>
        (sampleBalancedArmMean φ (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω)
          (fun i ω => O i ω.1) false n ω -
        sampleBalancedArmMean φ (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω)
          (fun i ω => O i ω.1) true n ω) - dbc n ω)
        (Q.marginalEffect id a b) (P₁.prod P₂) ∧
    TendstoInMeasure (P₁.prod P₂) (fun n ω =>
        (reportedMomentsArmFit φ (fun i ω => O i ω.1)
          (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω) false n ω -
        reportedMomentsArmFit φ (fun i ω => O i ω.1)
          (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω) true n ω) - dbc n ω)
      atTop (fun _ => Q.marginalEffect id a b) ∧
    TendstoInMeasure (P₁.prod P₂) (fun n ω =>
        ((reportedMomentsArmFit φ (fun i ω => O i ω.1)
          (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω) false n ω -
        reportedMomentsArmFit φ (fun i ω => O i ω.1)
          (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω) true n ω) - dbc n ω) -
        ((sampleBalancedArmMean φ
          (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω)
          (fun i ω => O i ω.1) false n ω -
        sampleBalancedArmMean φ (fun k => sampleMean (fun x => φ x k) (fun i ω => Xs i ω.2) n ω)
          (fun i ω => O i ω.1) true n ω) - dbc n ω))
      atTop (fun _ => 0) ∧
    Q.marginalEffect id a b = (M.γ b - M.γ a) + t ⬝ᵥ (M.β₂ b - M.β₂ a) := by
  set Φ : ℕ → Ξ₁ × Ξ₂ → Fin p → ℝ := fun i ω => φ (Xs i ω.2) with hΦ
  set Wt : Ξ₁ × Ξ₂ → ℕ → Fin p → ℝ := fun ω i => Φ i ω with hWt
  set Gt : ℕ → (ℕ → Fin p → ℝ) → Fin p → ℝ :=
    fun n w k => sampleMean (fun u : Fin p → ℝ => u k) (fun i w => w i) n w with hGt
  have hΦm : ∀ i, Measurable (Φ i) := fun i => hφ.comp ((hXsm i).comp measurable_snd)
  have hΦs : IsIIDSample Φ (P₁.prod P₂) :=
    (isIIDSample_comp_snd_prod (P₁ := P₁) hXsm hXs).comp hφ
  have hWm : Measurable Wt := measurable_pi_iff.2 hΦm
  have hGm : ∀ n, Measurable (Gt n) := fun n => measurable_pi_iff.2 fun k =>
    measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply k).comp (measurable_pi_apply i))
  have hΦlaw : (P₁.prod P₂).map (Φ 0) = Q.covLaw.map φ := by
    change (P₁.prod P₂).map (φ ∘ Xs 0 ∘ Prod.snd) = _
    rw [← Measure.map_map hφ ((hXsm 0).comp measurable_snd),
      ← Measure.map_map (hXsm 0) measurable_snd, Measure.map_snd_prod, measure_univ, one_smul,
      hXlaw]
  have htm : TendstoInMeasure (P₁.prod P₂) (fun n ω => Gt n (Wt ω)) atTop (fun _ => t) := by
    have h := tendstoInMeasure_sampleMean_coord hΦs fun k => by
      rw [hΦlaw]
      exact (integrable_map_measure (measurable_pi_apply k).aestronglyMeasurable
        hφ.aemeasurable).2 (hQφ k)
    have hlim : (fun k => ∫ x, x k ∂((P₁.prod P₂).map (Φ 0))) = t := by
      funext k
      rw [hΦlaw, integral_map hφ.aemeasurable (measurable_pi_apply k).aestronglyMeasurable, ht]
    rw [hlim] at h
    exact h
  have hOs : IsIIDSample (fun i (ω : Ξ₁ × Ξ₂) => O i ω.1) (P₁.prod P₂) :=
    isIIDSample_comp_fst_prod hOm hO
  have hOm' : ∀ i, Measurable fun ω : Ξ₁ × Ξ₂ => O i ω.1 := fun i => (hOm i).comp measurable_fst
  have hlaw' : (P₁.prod P₂).map (fun ω => O 0 ω.1) = T.ipdLaw := by
    rw [show (fun ω : Ξ₁ × Ξ₂ => O 0 ω.1) = O 0 ∘ Prod.fst from rfl,
      ← Measure.map_map (hOm 0) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul, hlaw]
  have hWO : IndepFun Wt (fun ω k => O k ω.1) (P₁.prod P₂) :=
    (indepFun_comp_fst_comp_snd (P₁ := P₁) (P₂ := P₂) (F := fun ω₁ k => O k ω₁)
      (G := fun ω₂ i => φ (Xs i ω₂)) (measurable_pi_iff.2 hOm)
      (measurable_pi_iff.2 fun i => hφ.comp (hXsm i))).symm
  obtain ⟨-, h1, h2, h3, -, h5⟩ := M.commonLimit_anchored_identity_reportedMoments hT hY2 hreg hφ
    hint hexp hOs hOm' hlaw' hWm hWO hGm htm hvar hX₂ hQφ ht hYa hYb hYc ha hb hc hdbc
  exact ⟨h1, h2, h3, h5⟩

end MultilevelModel

/-! ### An instance -/

section Example

/-- The law of the target sample of the binary covariate example: infinitely many independent
copies of the target covariate. -/
noncomputable def commonLimitExampleTargetSampleLaw : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => lsExampleTarget.covLaw

instance : IsProbabilityMeasure commonLimitExampleTargetSampleLaw := by
  unfold commonLimitExampleTargetSampleLaw; infer_instance

theorem map_commonLimitExampleTargetSampleLaw (i : ℕ) :
    commonLimitExampleTargetSampleLaw.map (fun w : ℕ → Bool => w i) = lsExampleTarget.covLaw :=
  Measure.infinitePi_map_eval _ i

/-- **The target sample is i.i.d.** with the target covariate law. -/
theorem isIIDSample_commonLimitExampleTargetSample :
    IsIIDSample (fun i (w : ℕ → Bool) => w i) commonLimitExampleTargetSampleLaw where
  indep := iIndepFun_infinitePi (P := fun _ => lsExampleTarget.covLaw) (X := fun _ => id)
    fun _ => measurable_id
  ident i := ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    (map_commonLimitExampleTargetSampleLaw i).trans (map_commonLimitExampleTargetSampleLaw 0).symm⟩

/-- **The common limit in the binary covariate example at the target sample means.** For the
example trial of `true` against `false` with feature `1{x}` and the multilevel model
`commonLimitExampleModel`, an i.i.d. sample of the trial and an independent i.i.d. sample of the
target covariates, on the product of the two sample spaces, with the reported moments the target
sample means of the feature and a zero reported contrast (`b = c = false`): every hypothesis of
`MultilevelModel.commonLimit_anchored_identity_targetSample` holds, the anchored entropy
balancing comparison at the sample means is consistent for `-5/4`, the anchored standardized
comparison converges in probability to `-5/4`, their difference converges in probability to `0`,
and `-5/4 = (γ_false - γ_true) + (1/4)(β₂,false - β₂,true)`. -/
theorem commonLimitExample_anchored_targetSample :
    IsConsistent (fun n ω =>
        (sampleBalancedArmMean commonLimitExampleFeature
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          (fun i ω => lsExampleSample i ω.1) false n ω -
        sampleBalancedArmMean commonLimitExampleFeature
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          (fun i ω => lsExampleSample i ω.1) true n ω) - 0)
        (-5 / 4) (lsExampleSampleLaw.prod commonLimitExampleTargetSampleLaw) ∧
    TendstoInMeasure (lsExampleSampleLaw.prod commonLimitExampleTargetSampleLaw) (fun n ω =>
        (reportedMomentsArmFit commonLimitExampleFeature (fun i ω => lsExampleSample i ω.1)
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          false n ω -
        reportedMomentsArmFit commonLimitExampleFeature (fun i ω => lsExampleSample i ω.1)
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          true n ω) - 0)
      atTop (fun _ => -5 / 4) ∧
    TendstoInMeasure (lsExampleSampleLaw.prod commonLimitExampleTargetSampleLaw) (fun n ω =>
        ((reportedMomentsArmFit commonLimitExampleFeature (fun i ω => lsExampleSample i ω.1)
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          false n ω -
        reportedMomentsArmFit commonLimitExampleFeature (fun i ω => lsExampleSample i ω.1)
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          true n ω) - 0) -
        ((sampleBalancedArmMean commonLimitExampleFeature
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          (fun i ω => lsExampleSample i ω.1) false n ω -
        sampleBalancedArmMean commonLimitExampleFeature
          (fun k => sampleMean (fun x => commonLimitExampleFeature x k) (fun i ω => ω.2 i) n ω)
          (fun i ω => lsExampleSample i ω.1) true n ω) - 0))
      atTop (fun _ => 0) ∧
    (commonLimitExampleModel.γ false - commonLimitExampleModel.γ true) +
      commonLimitExampleMean ⬝ᵥ
        (commonLimitExampleModel.β₂ false - commonLimitExampleModel.β₂ true) = -5 / 4 := by
  have h0 : lsExampleTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have hdbc : TendstoInMeasure (lsExampleSampleLaw.prod commonLimitExampleTargetSampleLaw)
      (fun (_ : ℕ) (_ : (ℕ → Bool × Bool) × (ℕ → Bool)) => (0 : ℝ)) atTop
        fun _ => lsExampleTarget.marginalEffect id false false := by
    rw [h0]; exact tendstoInMeasure_const 0
  have hreg : IsOutcomeRegression lsExampleTrial.μ lsExampleTrial.A lsExampleTrial.X
      lsExampleTrial.obsOutcome fun e x => commonLimitExampleModel.eta 0
        (if e then true else false) (commonLimitExampleFeature x) := by
    simpa only [commonLimitExampleModel_eta_ite] using commonLimitExample_regression
  have hvar : ∀ e : Bool, lsExampleTrial.μ[fun ω => (lsExampleTrial.Y e ω -
      commonLimitExampleModel.eta 0 (if e then true else false)
        (commonLimitExampleFeature (lsExampleTrial.X ω))) ^ 2 |
      MeasurableSpace.comap lsExampleTrial.X inferInstance]
        ≤ᵐ[lsExampleTrial.μ] fun _ => (0 : ℝ) := fun e => by
    have hz : (fun ω => (lsExampleTrial.Y e ω - commonLimitExampleModel.eta 0
        (if e then true else false) (commonLimitExampleFeature (lsExampleTrial.X ω))) ^ 2) =
        0 := funext fun ω => by
      rw [commonLimitExampleModel_eta_ite, commonLimitExample_dotProduct]; simp [lsExampleTrial]
    rw [hz, condExp_zero]
    rfl
  have : IsProbabilityMeasure lsExampleTrial.covLaw := by
    rw [lsExampleTrial_covLaw]; infer_instance
  have hint := mem_interior_map_of_margin (measurable_of_finite commonLimitExampleFeature)
    (by norm_num : (0 : ℝ) < 1 / 4) commonLimitExample_margin
  obtain ⟨h1, h2, h3, h4⟩ := commonLimitExampleModel.commonLimit_anchored_identity_targetSample
    (Q := lsExampleTarget) (a := true) (b := false) (c := false)
    lsExampleTrial_isRandomizedTwoArm lsExample_linearOutcomeModel.memLp_Y hreg
    (measurable_of_finite _) hint (fun _ => Integrable.of_finite) isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) isIIDSample_commonLimitExampleTargetSample
    (fun i => measurable_pi_apply i) (map_commonLimitExampleTargetSampleLaw 0) hvar
    (measurable_of_finite _) (fun _ => Integrable.of_finite) commonLimitExample_featureMean
    Integrable.of_finite Integrable.of_finite Integrable.of_finite
    (isCondMean_commonLimitExampleModel true) (isCondMean_commonLimitExampleModel false)
    (isCondMean_commonLimitExampleModel false) hdbc
  rw [commonLimitExample_marginalEffect] at h1 h2 h4
  exact ⟨h1, h2, h3, h4.symm⟩

end Example

end NetworkMetaRegression

end CausalInference
