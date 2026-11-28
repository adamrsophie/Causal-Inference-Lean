/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.Estimands
public import CausalInference.PopulationAdjustment.CommonLimitExamples

/-!
# The multilevel model in the two study network and the common limit of the estimators

In the smallest anchored network, a trial of `a` against `c` with individual data and a target
population with the reported contrast of `b` against `c`, let the individual level model of the
multilevel network meta-regression hold with the identity link: the conditional mean of the
outcome of the trial on treatment `k` given the covariates `x` is `η_k(φ(x))` at the trial
baseline `μ_T`, and in the target it is `η_k(φ(x))` at a target baseline `α_Q`, for the
treatments `a, b, c`.

* **The coefficients of the trial regression** (`MultilevelModel.ipdCoef`): the trial
  regression is the interaction regression of `PopulationAdjustment.featureInteractionDesign`
  with intercept `μ_T + γ_c`, main effects `β₁ + β₂,c`, treatment effect `γ_a - γ_c` and
  interactions `β₂,a - β₂,c` (`MultilevelModel.featureInteractionDesign_dotProduct_ipdCoef`).
* **The common limit** (`MultilevelModel.commonLimit_anchored_identity`): from the individual
  level model in the trial and in the target and the conditions on the trial and the sample
  (randomization, square integrable outcomes, bounded measurable features with the margin
  condition at `t`, a bounded conditional variance, `t` the target feature mean), with a reported
  contrast converging in probability to the target effect of `c` against `b`:
  * the least squares fit converges in probability to `ipdCoef` (derived, not assumed);
  * the anchored entropy balancing comparison is consistent for the target effect of `b` against
    `a`, the anchored standardized comparison converges to it, and their difference converges
    in probability to `0`;
  * this limit is the population average marginal effect of the multilevel model in the target,
    `linkMarginal id (P*_X ∘ φ⁻¹) m_a m_b` with `m_k = η_k` at `α_Q`, and equals
    `(γ_b - γ_a) + tᵀ(β₂,b - β₂,a)`.
* **An instance** (`commonLimit_anchored_identity_example`): the binary covariate example of
  `PopulationAdjustment.commonLimitExample_anchored`, written as a multilevel model with
  `γ = (0, 1)`, `β₁ = 1` and `β₂ = (0, 1)`, has the common limit `-5/4`, which is
  `(γ_false - γ_true) + (1/4)(β₂,false - β₂,true)`.

## Main definitions

* `MultilevelModel.ipdCoef`, `commonLimitExampleModel`.

## Main results

* `MultilevelModel.featureInteractionDesign_dotProduct_ipdCoef`,
  `MultilevelModel.integral_eta_comp`, `MultilevelModel.commonLimit_anchored_identity`,
  `commonLimit_anchored_identity_example`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport PopulationAdjustment

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-- The coefficients of the trial regression of `a` against `c` at the trial baseline `μ` in the
interaction design: intercept `μ + γ_c`, main effects `β₁ + β₂,c`, treatment effect `γ_a - γ_c`
and interactions `β₂,a - β₂,c`. -/
def ipdCoef (M : MultilevelModel J K p) (μ : ℝ) (a c : K) : Option (Fin p) ⊕ Option (Fin p) → ℝ :=
  Sum.elim (fun o => o.elim (μ + M.γ c) fun i => (M.β₁ + M.β₂ c) i)
    fun o => o.elim (M.γ a - M.γ c) fun i => (M.β₂ a - M.β₂ c) i

/-- **The trial regression is the multilevel predictor**: the interaction design at
`ipdCoef M μ a c` is `η_a(φ(x))` on the arm `true` and `η_c(φ(x))` on the arm `false`, at the
baseline `μ`. -/
theorem featureInteractionDesign_dotProduct_ipdCoef {𝒳 : Type*} (M : MultilevelModel J K p)
    (μ : ℝ) (a c : K) (φ : 𝒳 → Fin p → ℝ) (e : Bool) (x : 𝒳) :
    featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μ a c = M.eta μ (if e then a else c) (φ x) := by
  rw [featureInteractionDesign_dotProduct, eta_eq_affine]
  have h1 : interactionMain (M.ipdCoef μ a c) = M.β₁ + M.β₂ c := rfl
  have h2 : interactionModifier (M.ipdCoef μ a c) = M.β₂ a - M.β₂ c := rfl
  rw [h1, h2]
  cases e
  · simp only [Bool.false_eq_true, ite_false, add_zero, dotProduct_comm]
    rfl
  · simp only [ite_true, dotProduct_comm (φ x)]
    simp only [interactionIntercept, interactionEffect, ipdCoef, Sum.elim_inl, Sum.elim_inr,
      Option.elim_none, add_add_sub_cancel]

/-- **The mean of the predictor under a covariate law**: if the features have integrable
coordinates under the probability law `ν`, then
`∫ η_k(φ(x)) ν(dx) = (α + γ_k) + φ̄ᵀ(β₁ + β₂,k)` with `φ̄ = ∫ φ dν`. -/
theorem integral_eta_comp {𝒳 : Type*} [MeasurableSpace 𝒳] (M : MultilevelModel J K p) (α : ℝ)
    (k : K) {φ : 𝒳 → Fin p → ℝ} {ν : Measure 𝒳} [IsProbabilityMeasure ν]
    (hφ : ∀ i, Integrable (fun x => φ x i) ν) :
    ∫ x, M.eta α k (φ x) ∂ν = (α + M.γ k) + (fun i => ∫ x, φ x i ∂ν) ⬝ᵥ (M.β₁ + M.β₂ k) := by
  simp only [eta_eq_affine, dotProduct]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun i _ => (hφ i).mul_const _),
    integral_const, probReal_univ, one_smul, integral_finsetSum _ fun i _ => (hφ i).mul_const _]
  simp only [integral_mul_const]

variable {Ω₁ Ω₂ Ξ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 K} {P : Measure Ξ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

/-- **The multilevel model in the two study network: weighting and standardization share the
multilevel limit.** Let the trial of `a` (arm `true`) against `c` (arm `false`) be a randomized
two arm trial with square integrable outcomes, whose regression of the outcome on the covariates
and the arm is the multilevel predictor `η_k(φ(x))` at the baseline `μ_T` with the identity link,
and let the conditional means of `Y(a), Y(b), Y(c)` in the target be `η_k(φ(x))` at a baseline
`α_Q`, with integrable potential outcomes. Let the features be measurable and bounded around `t`
with the margin condition at `t` in the trial, `t` be the target feature mean, the conditional
variance of the trial residual be bounded, and the reported contrast `d̂_bc` converge in
probability to the target effect of `c` against `b`. Then for an i.i.d. sample of the trial:

* the least squares fit converges in probability to `ipdCoef M μ_T a c`;
* the anchored entropy balancing comparison is consistent for the target effect of `b` against
  `a` on the mean scale;
* the anchored standardized comparison converges in probability to the same limit;
* their difference converges in probability to `0`;
* the limit is the population average marginal effect of the multilevel model in the target,
  `linkMarginal id (P*_X ∘ φ⁻¹) m_a m_b` with `m_k(u) = η_k(u)` at `α_Q`, and it equals
  `(γ_b - γ_a) + tᵀ(β₂,b - β₂,a)`.

No shared effect modifier assumption is used: on the identity link the baseline cancels in the
contrast. The convergence of the fit follows from the conditions on the trial. -/
theorem commonLimit_anchored_identity [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (M : MultilevelModel J K p) {μT αQ : ℝ} {a b c : K}
    (hT : T.IsRandomizedTwoArm) (hY2 : ∀ e, MemLp (T.Y e) 2 T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun e x => M.eta μT (if e then a else c) (φ x))
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - M.eta μT (if o.2.1 then a else c) (φ o.1)) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (hYa : Integrable (Q.Y a) Q.μ) (hYb : Integrable (Q.Y b) Q.μ) (hYc : Integrable (Q.Y c) Q.μ)
    (ha : Q.IsCondMean a fun x => M.eta αQ a (φ x))
    (hb : Q.IsCondMean b fun x => M.eta αQ b (φ x))
    (hc : Q.IsCondMean c fun x => M.eta αQ c (φ x))
    {dbc : ℕ → Ξ → ℝ} (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect id b c) :
    TendstoInMeasure P (leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse
      O) atTop (fun _ => M.ipdCoef μT a c) ∧
    IsConsistent (anchoredBalancedEstimate id φ t O dbc) (Q.marginalEffect id a b) P ∧
      TendstoInMeasure P (fun n ω => linkMarginal id Q.covLaw
        (fun x => featureInteractionDesign φ true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω)
        (fun x => featureInteractionDesign φ false x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω) -
          dbc n ω) atTop (fun _ => Q.marginalEffect id a b) ∧
      TendstoInMeasure P (fun n ω => (linkMarginal id Q.covLaw
        (fun x => featureInteractionDesign φ true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω)
        (fun x => featureInteractionDesign φ false x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω) -
          dbc n ω) - anchoredBalancedEstimate id φ t O dbc n ω) atTop (fun _ => 0) ∧
      Q.marginalEffect id a b =
        linkMarginal id (Q.covLaw.map φ) (M.surface id αQ a) (M.surface id αQ b) ∧
      Q.marginalEffect id a b = (M.γ b - M.γ a) + t ⬝ᵥ (M.β₂ b - M.β₂ a) := by
  have hz := M.featureInteractionDesign_dotProduct_ipdCoef μT a c φ
  have hreg' : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun e x => featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μT a c := by
    simpa only [hz] using hreg
  have hM := T.linearOutcomeModel_featureInteraction hT hY2 hφ hB hδ hmargin hreg'
  have hvar' : T.ipdLaw[fun o => (o.2.2 -
      featureInteractionDesign φ o.2.1 o.1 ⬝ᵥ M.ipdCoef μT a c) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2 := by
    simpa only [hz] using hvar
  have : IsProbabilityMeasure Q.covLaw :=
    (Measure.isProbabilityMeasure_map_iff hX₂.aemeasurable).2 inferInstance
  have hzQ : ∀ e j, Integrable (fun x => featureInteractionDesign φ e x j) Q.covLaw :=
    fun e j => integrable_featureInteractionDesign hφ hB e j
  have haff : ∀ e x, featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μT a c =
      (μT + M.γ (if e then a else c)) + (M.β₁ + M.β₂ (if e then a else c)) ⬝ᵥ φ x :=
    fun e x => by rw [hz, eta_eq_affine, dotProduct_comm]
  have hrel : (fun ω => featureInteractionDesign φ false (Q.X ω) ⬝ᵥ M.ipdCoef μT a c -
      featureInteractionDesign φ true (Q.X ω) ⬝ᵥ M.ipdCoef μT a c) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance] := by
    filter_upwards [condExp_sub hYc hYa (MeasurableSpace.comap Q.X inferInstance), ha.2, hc.2]
      with ω h1 h2 h3
    change _ = Q.μ[Q.Y c - Q.Y a | MeasurableSpace.comap Q.X inferInstance] ω
    rw [h1, Pi.sub_apply, ← h2, ← h3, hz, hz]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    linarith [M.eta_sub_eta μT αQ c (φ (Q.X ω)), M.eta_sub_eta μT αQ a (φ (Q.X ω))]
  obtain ⟨h1, h2, h3⟩ := commonLimit_leastSquares_anchored_identity hT hM hO hOm hlaw hφ hB hδ
    hmargin hvar' haff hX₂ ht hzQ hYa hYc hrel hdbc
  have hφi : ∀ i, Integrable (fun x => φ x i) Q.covLaw := fun i =>
    (integrable_const (B + ‖t‖)).mono' ((measurable_pi_apply i).comp hφ).aestronglyMeasurable
      (ae_of_all _ fun x => by
        calc ‖φ x i‖ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) i
          _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
          _ ≤ B + ‖t‖ := (norm_add_le _ _).trans (by linarith [hB x]))
  have hme := Population.marginalEffect_eq_linkMarginal id hX₂ hYa hYb ha hb
  have hmap : linkMarginal id Q.covLaw (fun x => M.eta αQ a (φ x)) (fun x => M.eta αQ b (φ x)) =
      linkMarginal id (Q.covLaw.map φ) (M.surface id αQ a) (M.surface id αQ b) := by
    simp only [linkMarginal, surface, id]
    rw [integral_map hφ.aemeasurable (M.continuous_eta αQ b).aestronglyMeasurable,
      integral_map hφ.aemeasurable (M.continuous_eta αQ a).aestronglyMeasurable]
  refine ⟨hM.tendstoInMeasure hT hO hlaw, h1, h2, h3, hme.trans hmap, ?_⟩
  rw [hme]
  simp only [linkMarginal, id]
  rw [M.integral_eta_comp αQ b hφi, M.integral_eta_comp αQ a hφi]
  have htv : (fun i => ∫ x, φ x i ∂Q.covLaw) = t := funext ht
  rw [htv]
  simp only [dotProduct_add, dotProduct_sub]
  ring

end MultilevelModel

/-! ### An instance -/

section Example

/-- The multilevel model of the binary covariate example: one study, treatments `false` and
`true`, the feature `1{x}`, baseline `0`, `β₁ = 1`, `γ = (γ_false, γ_true) = (0, 1)` and
`β₂ = (0, 1)`, anchored at `false`. -/
noncomputable def commonLimitExampleModel : MultilevelModel Unit Bool 1 :=
  ⟨fun _ => 0, fun _ => 1, fun k => if k then 1 else 0, fun k _ => if k then 1 else 0⟩

theorem commonLimitExampleModel_eta (k x : Bool) :
    commonLimitExampleModel.eta 0 k (commonLimitExampleFeature x) = lsExampleOutcome k x := by
  cases k <;> cases x <;> norm_num [MultilevelModel.eta_eq_affine, commonLimitExampleModel,
    commonLimitExampleFeature, lsExampleOutcome, dotProduct]

theorem commonLimitExampleModel_eta_ite (e x : Bool) :
    commonLimitExampleModel.eta 0 (if e then true else false) (commonLimitExampleFeature x) =
      featureInteractionDesign commonLimitExampleFeature e x ⬝ᵥ commonLimitExampleCoef := by
  rw [commonLimitExample_dotProduct, ← commonLimitExampleModel_eta]
  cases e <;> rfl

/-- The coefficients of the trial regression of the example are `(0, 1, 1, 1)`. -/
theorem ipdCoef_commonLimitExampleModel :
    commonLimitExampleModel.ipdCoef 0 true false = commonLimitExampleCoef := by
  funext k
  rcases k with (_ | i) | (_ | i) <;>
    simp [MultilevelModel.ipdCoef, commonLimitExampleModel, commonLimitExampleCoef]

theorem isCondMean_commonLimitExampleModel (k : Bool) :
    lsExampleTarget.IsCondMean k
      fun x => commonLimitExampleModel.eta 0 k (commonLimitExampleFeature x) := by
  simp only [commonLimitExampleModel_eta]
  have hsm : StronglyMeasurable[MeasurableSpace.comap lsExampleTarget.X inferInstance]
      (lsExampleTarget.Y k) :=
    ((measurable_of_finite (lsExampleOutcome k)).comp
      (comap_measurable (id : Bool → Bool))).stronglyMeasurable
  have h := condExp_of_stronglyMeasurable (μ := lsExampleTarget.μ)
    (measurable_of_finite lsExampleTarget.X).comap_le hsm Integrable.of_finite
  refine ⟨measurable_of_finite _, ?_⟩
  rw [h]
  rfl

/-- **The common limit in the binary covariate example of the multilevel model.** For the
example trial of `true` against `false` with feature `1{x}` and target feature mean `1/4`, with
the multilevel model `commonLimitExampleModel` and a zero reported contrast (`b = c = false`):

* the least squares fit converges in probability to `ipdCoef = (0, 1, 1, 1)`;
* the anchored entropy balancing comparison is consistent for `-5/4`;
* `-5/4 = (γ_false - γ_true) + (1/4)(β₂,false - β₂,true)`, the multilevel estimand. -/
theorem commonLimit_anchored_identity_example :
    TendstoInMeasure lsExampleSampleLaw (leastSquaresFit (recordDesign
      (featureInteractionDesign commonLimitExampleFeature)) recordResponse lsExampleSample) atTop
        (fun _ => commonLimitExampleCoef) ∧
      IsConsistent (anchoredBalancedEstimate id commonLimitExampleFeature commonLimitExampleMean
        lsExampleSample fun _ _ => 0) (-5 / 4) lsExampleSampleLaw ∧
      (commonLimitExampleModel.γ false - commonLimitExampleModel.γ true) +
        commonLimitExampleMean ⬝ᵥ
          (commonLimitExampleModel.β₂ false - commonLimitExampleModel.β₂ true) = -5 / 4 := by
  have h0 : lsExampleTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have hdbc : TendstoInMeasure lsExampleSampleLaw
      (fun (_ : ℕ) (_ : ℕ → Bool × Bool) => (0 : ℝ)) atTop
        fun _ => lsExampleTarget.marginalEffect id false false := by
    rw [h0]; exact tendstoInMeasure_const 0
  have hreg : IsOutcomeRegression lsExampleTrial.μ lsExampleTrial.A lsExampleTrial.X
      lsExampleTrial.obsOutcome fun e x => commonLimitExampleModel.eta 0
        (if e then true else false) (commonLimitExampleFeature x) := by
    simpa only [commonLimitExampleModel_eta_ite] using commonLimitExample_regression
  have hvar : lsExampleTrial.ipdLaw[fun o => (o.2.2 - commonLimitExampleModel.eta 0
      (if o.2.1 then true else false) (commonLimitExampleFeature o.1)) ^ 2 |
        MeasurableSpace.comap (fun o : Bool × Bool × ℝ => (o.1, o.2.1)) inferInstance]
          ≤ᵐ[lsExampleTrial.ipdLaw] fun _ => (0 : ℝ) := by
    simpa only [commonLimitExampleModel_eta_ite] using commonLimitExample_variance
  obtain ⟨h1, h2, -, -, -, h6⟩ := commonLimitExampleModel.commonLimit_anchored_identity
    (Q := lsExampleTarget) (a := true) (b := false) (c := false)
    lsExampleTrial_isRandomizedTwoArm lsExample_linearOutcomeModel.memLp_Y hreg
    isIIDSample_lsExampleSample
    (fun i => (measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i))
    (map_lsExampleSample 0) (measurable_of_finite _) commonLimitExample_bound
    (by norm_num) commonLimitExample_margin hvar measurable_id commonLimitExample_featureMean
    Integrable.of_finite Integrable.of_finite Integrable.of_finite
    (isCondMean_commonLimitExampleModel true) (isCondMean_commonLimitExampleModel false)
    (isCondMean_commonLimitExampleModel false) hdbc
  rw [ipdCoef_commonLimitExampleModel] at h1
  rw [commonLimitExample_marginalEffect] at h2 h6
  exact ⟨h1, h2, h6.symm⟩

end Example

end NetworkMetaRegression

end CausalInference
