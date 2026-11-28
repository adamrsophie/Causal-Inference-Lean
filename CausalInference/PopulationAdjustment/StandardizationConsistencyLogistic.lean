/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyConditional
public import CausalInference.PopulationAdjustment.OutcomeModelFitLikelihood
public import CausalInference.Measures.OddsRatioLink

/-!
# Standardization of a logistic outcome model fitted by maximum likelihood

A logistic outcome model `P(Y = 1 | X = x, A = t) = σ(z(x, t) ⬝ ξ₀)` is fitted by maximum
likelihood to the individual data of a randomized trial (`glmMLE`, consistent by
`tendstoInMeasure_logisticMLE`) and standardized to the covariate law of a target.

**What is assumed about the data generating law** (`Trial.LogisticOutcomeModel`): the law of the
records `((X, A), Y)` of the trial is the logistic family at `ξ₀`, with the regressor law of
`(X, A)` in the dominating measure; the design is measurable, has integrable coordinates and full
rank. With randomization (`Trial.IsRandomizedTwoArm`) and integrable potential outcomes, the
regression `E[Y | X, A] = σ(z(X, A) ⬝ ξ₀)` is derived from the likelihood model
(`Trial.LogisticOutcomeModel.isOutcomeRegression`). The surface `σ(z(x, t) ⬝ ξ)` is bounded by
one and continuous in `ξ`, so every regularity condition of the standardized fit holds under any
target covariate law (`logisticSurface_regular`). The parameter set `K` of the fit is a compact
set containing `ξ₀`, chosen by the analyst.

**Results.**

* `tendstoInMeasure_logistic_linkMarginal`, `tendstoInMeasure_logistic_anchored`: the
  standardized marginal estimand and the anchored comparison are consistent for the target
  marginal effect.
* `tendstoInMeasure_logistic_sampleMean_armMean`: the average of the fitted surface over target
  draws is consistent for the target arm mean.
* `tendstoInMeasure_logistic_conditionalPlugIn`: the conditional plug-in on the logit scale
  converges to the target marginal log odds ratio plus the difference of the averaging gaps of the
  two true surfaces; it is not consistent for the marginal log odds ratio in general.

## Main definitions

* `Trial.LogisticOutcomeModel`.

## Main results

* `logit_sigmoid`, `logisticSurface_regular`, `Trial.LogisticOutcomeModel.isOutcomeRegression`,
  `Trial.LogisticOutcomeModel.tendstoInMeasure`.
* `tendstoInMeasure_logistic_linkMarginal`, `tendstoInMeasure_logistic_anchored`,
  `tendstoInMeasure_logistic_sampleMean_armMean`,
  `tendstoInMeasure_logistic_conditionalPlugIn`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- **The logit inverts the logistic function**: `logit (σ s) = s`. -/
theorem logit_sigmoid (s : ℝ) : logit (Real.sigmoid s) = s := by
  rw [logit_eq_log_div, ← Real.sigmoid_neg, ← Real.sigmoid_mul_rexp_neg,
    div_mul_cancel_left₀ (Real.sigmoid_pos s).ne', Real.exp_neg, inv_inv, Real.log_exp]

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ]

/-- **The logistic surface is regular in the coefficient** under any probability law `ν`: it is
measurable, bounded by one and continuous in `ξ`. -/
theorem logisticSurface_regular {z : 𝒳 × Bool → κ → ℝ} (hz : ∀ j, Measurable fun c => z c j)
    (t : Bool) (ν : Measure 𝒳) [IsProbabilityMeasure ν] :
    (∀ ξ : κ → ℝ, Measurable fun x => Real.sigmoid (z (x, t) ⬝ᵥ ξ)) ∧
      Integrable (fun _ : 𝒳 => (1 : ℝ)) ν ∧
      (∀ ξ : κ → ℝ, ∀ x, |Real.sigmoid (z (x, t) ⬝ᵥ ξ)| ≤ 1) ∧
      ∀ x, Continuous fun ξ : κ → ℝ => Real.sigmoid (z (x, t) ⬝ᵥ ξ) :=
  ⟨fun ξ => continuous_sigmoid.measurable.comp
      ((measurable_dotProduct_design hz ξ).comp (measurable_id.prodMk measurable_const)),
    integrable_const _,
    fun ξ x => by
      rw [abs_of_pos (Real.sigmoid_pos _)]; exact Real.sigmoid_le_one _,
    fun x => continuous_sigmoid.comp (continuous_const.dotProduct continuous_id)⟩

/-- The **assumptions on a trial with a logistic outcome model**: a measurable design `z(x, t)`
with integrable coordinates and full rank in the trial, and records `((X, A), Y)` whose law is
the logistic family at `ξ₀` with the regressor law `law(X, A)` in the dominating measure. -/
structure _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel
    (T : Trial Ω₁ 𝒳 Bool) [IsProbabilityMeasure T.μ] (z : 𝒳 × Bool → κ → ℝ) (ξ₀ : κ → ℝ) :
    Prop where
  /-- The design coordinates are measurable. -/
  measurable_z : ∀ j, Measurable fun c => z c j
  /-- The design coordinates are integrable in the trial. -/
  integrable_z : ∀ j, Integrable (fun ω => z (T.X ω, T.A ω) j) T.μ
  /-- The design has full rank in the trial. -/
  full_rank : ∀ v : κ → ℝ, (∀ᵐ ω ∂T.μ, z (T.X ω, T.A ω) ⬝ᵥ v = 0) → v = 0
  /-- The records follow the logistic model at `ξ₀`. -/
  law_eq : T.μ.map (fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) =
    (glmFamily logisticKernel (T.μ.map fun ω => (T.X ω, T.A ω)) z measurable_z).law ξ₀

variable {T : Trial Ω₁ 𝒳 Bool} {z : 𝒳 × Bool → κ → ℝ} {ξ₀ : κ → ℝ}

/-- The observed outcome of a trial with integrable potential outcomes is integrable. -/
theorem integrable_obsOutcome (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ) :
    Integrable T.obsOutcome T.μ := by
  refine ((hYi true).norm.add (hYi false).norm).mono'
    (measurable_obsOutcome hT.measurable_A hT.measurable_Y).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  simp only [Trial.obsOutcome, Pi.add_apply]
  cases T.A ω
  · exact le_add_of_nonneg_left (norm_nonneg _)
  · exact le_add_of_nonneg_right (norm_nonneg _)

/-- **The observed regression of a logistic outcome model** is `σ(z(x, a) ⬝ ξ₀)`, derived from
the law of the records, for a randomized trial with integrable potential outcomes. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.isOutcomeRegression
    [IsProbabilityMeasure T.μ] (hM : T.LogisticOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) :
    IsOutcomeRegression T.μ T.A T.X T.obsOutcome fun a x => Real.sigmoid (z (x, a) ⬝ᵥ ξ₀) := by
  have h := isOutcomeRegression_of_glm hT.measurable_X hT.measurable_A
    (measurable_obsOutcome hT.measurable_A hT.measurable_Y) (integrable_obsOutcome hT hYi) rfl
    hM.law_eq
  simp only [logisticKernel_mean] at h
  exact h

/-- **The logistic maximum likelihood fit of a trial is consistent**: for an i.i.d. sample of the
records `((X, A), Y)` of a trial with a logistic outcome model, the fit over a compact `K ∋ ξ₀`
converges in probability to `ξ₀`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.LogisticOutcomeModel.tendstoInMeasure
    [IsProbabilityMeasure T.μ] {P : Measure Ξ} [IsProbabilityMeasure P]
    (hM : T.LogisticOutcomeModel z ξ₀) (hT : T.IsRandomizedTwoArm) {K : Set (κ → ℝ)}
    (hK : IsCompact K) (hξ₀ : ξ₀ ∈ K) {O : ℕ → Ξ → (𝒳 × Bool) × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω)) :
    TendstoInMeasure P (glmMLE logisticDens z K O) atTop (fun _ => ξ₀) :=
  tendstoInMeasure_logisticMLE (Cv := fun ω => (T.X ω, T.A ω))
    (hT.measurable_X.prodMk hT.measurable_A)
    (measurable_obsOutcome hT.measurable_A hT.measurable_Y) rfl hM.law_eq hM.full_rank
    hM.integrable_z hK hξ₀ hO hlaw

variable {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {K : Set (κ → ℝ)}
  {O : ℕ → Ξ → (𝒳 × Bool) × ℝ}

/-- **The standardized logistic marginal estimand is consistent.** In a randomized trial with
integrable potential outcomes and a logistic outcome model (`Trial.LogisticOutcomeModel`), with
an i.i.d. sample of its records and the fit over a compact `K ∋ ξ₀`, with the arms `t₀ ↦ s₀`,
`t₁ ↦ s₁` transported to a target with integrable outcomes and overlap, and a link `g`
continuous at the two target arm means, the marginal estimand of the standardized fitted
surfaces `σ(z(·, t) ⬝ ξ̂)` under `Q_X` converges in probability to the target marginal effect. -/
theorem tendstoInMeasure_logistic_linkMarginal [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) (hM : T.LogisticOutcomeModel z ξ₀) (hK : IsCompact K)
    (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {t₀ t₁ : Bool} {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y t₀) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y t₁) Q.μ Q.X (Q.Y s₁)) (hov : Q.covLaw ≪ T.covLaw)
    {g : ℝ → ℝ} (hg₀ : ContinuousAt g (Q.armMean s₀)) (hg₁ : ContinuousAt g (Q.armMean s₁)) :
    TendstoInMeasure P
      (fun n ω => linkMarginal g Q.covLaw
        (fun x => Real.sigmoid (z (x, t₀) ⬝ᵥ glmMLE logisticDens z K O n ω))
        (fun x => Real.sigmoid (z (x, t₁) ⬝ᵥ glmMLE logisticDens z K O n ω)))
      atTop (fun _ => Q.marginalEffect g s₀ s₁) := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  have hr := fun t => logisticSurface_regular hM.measurable_z t Q.covLaw
  exact tendstoInMeasure_linkMarginal_fit (h := fun ξ t x => Real.sigmoid (z (x, t) ⬝ᵥ ξ)) hT
    hYi (hM.isOutcomeRegression hT hYi) hX₂ hYQ₀ hYQ₁ hsi₀ hsi₁ hov
    (fun t => Eventually.of_forall fun ξ => ((hr t).1 ξ).aestronglyMeasurable)
    (fun t => (hr t).2.1) (fun t => Eventually.of_forall fun ξ => ae_of_all _ ((hr t).2.2.1 ξ))
    (fun t => ae_of_all _ fun x => ((hr t).2.2.2 x).continuousAt)
    (hM.tendstoInMeasure hT hK hξ₀ hO hlaw) hg₀ hg₁

/-- **The anchored comparison with the standardized logistic fit is consistent.** Under the
hypotheses of `tendstoInMeasure_logistic_linkMarginal` for the arms `t_a ↦ a` and `t_c ↦ c`,
with a reported contrast `d̂_bc` converging in probability to the target marginal effect of `c`
relative to `b`, the anchored estimator converges in probability to the target marginal effect of
`b` relative to `a`. -/
theorem tendstoInMeasure_logistic_anchored [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) (hM : T.LogisticOutcomeModel z ξ₀) (hK : IsCompact K)
    (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {ta tc : Bool} {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y ta) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y tc) Q.μ Q.X (Q.Y c)) (hov : Q.covLaw ≪ T.covLaw)
    {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    TendstoInMeasure P
      (fun n ω => linkMarginal g Q.covLaw
        (fun x => Real.sigmoid (z (x, ta) ⬝ᵥ glmMLE logisticDens z K O n ω))
        (fun x => Real.sigmoid (z (x, tc) ⬝ᵥ glmMLE logisticDens z K O n ω)) - dbc n ω)
      atTop (fun _ => Q.marginalEffect g a b) := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  have hr := fun t => logisticSurface_regular hM.measurable_z t Q.covLaw
  exact tendstoInMeasure_anchored_fit (h := fun ξ t x => Real.sigmoid (z (x, t) ⬝ᵥ ξ)) hT
    hYi (hM.isOutcomeRegression hT hYi) hX₂ hYQa hYQc hsia hsic hov
    (fun t => Eventually.of_forall fun ξ => ((hr t).1 ξ).aestronglyMeasurable)
    (fun t => (hr t).2.1) (fun t => Eventually.of_forall fun ξ => ae_of_all _ ((hr t).2.2.1 ξ))
    (fun t => ae_of_all _ fun x => ((hr t).2.2.2 x).continuousAt)
    (hM.tendstoInMeasure hT hK hξ₀ hO hlaw) hdbc hga hgc

/-- **The average of the logistic fit over target draws is consistent for the target arm
mean.** Under the hypotheses of `tendstoInMeasure_logistic_linkMarginal` for the arm `t ↦ s`,
with `m n → ∞` i.i.d. draws `X'` from `Q_X` on the probability space of the trial sample (no
independence between the two is needed), `(m n)⁻¹ ∑_{i < m n} σ(z(X'_i, t) ⬝ ξ̂_n)` converges in
probability to `E_Q[Y(s)]`. -/
theorem tendstoInMeasure_logistic_sampleMean_armMean [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ) (hM : T.LogisticOutcomeModel z ξ₀) (hK : IsCompact K)
    (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {t : Bool} {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    {Xs : ℕ → Ξ → 𝒳} (hXs : IsIIDSample Xs P) (hν : P.map (Xs 0) = Q.covLaw) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) :
    TendstoInMeasure P
      (fun n ω => sampleMean (fun x => Real.sigmoid (z (x, t) ⬝ᵥ glmMLE logisticDens z K O n ω))
        Xs (m n) ω) atTop (fun _ => Q.armMean s) := by
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  obtain ⟨hm', hH, hd, hc⟩ := logisticSurface_regular hM.measurable_z t Q.covLaw
  exact tendstoInMeasure_sampleMean_fit_armMean
    (hθf := fun ξ t x => Real.sigmoid (z (x, t) ⬝ᵥ ξ)) hT hYi (hM.isOutcomeRegression hT hYi)
    hX₂ hYQ hsi hov univ_mem (fun ξ _ => hm' ξ) (ae_of_all _ fun x => (hc x).continuousOn) hH
    (ae_of_all _ fun x ξ _ => hd ξ x) (hM.tendstoInMeasure hT hK hξ₀ hO hlaw) hXs hν hm

/-- **The conditional plug-in of the logistic fit on the logit scale misses the marginal log
odds ratio by the averaging gap.** For covariates in `ℝ^p` and the interaction design
`z(x, t) = (1, x, 1[t], 1[t] x)`, under the hypotheses of
`tendstoInMeasure_logistic_linkMarginal` with `false ↦ s₀`, `true ↦ s₁`, target covariates with
integrable coordinates and a reported target covariate mean converging in probability to `x̄`,
the conditional plug-in `γ̂ + x̂ᵀβ̂₂` (the fitted log odds ratio at `x̂`) converges in
probability to the target marginal log odds ratio plus `J(m₀) - J(m₁)`, the difference of the
averaging gaps on the logit scale of the two true surfaces. -/
theorem tendstoInMeasure_logistic_conditionalPlugIn {p : ℕ}
    {T : Trial Ω₁ (Fin p → ℝ) Bool} {Q : Population Ω₂ (Fin p → ℝ) ι}
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {K : Set (Option (Fin p) ⊕ Option (Fin p) → ℝ)}
    {O : ℕ → Ξ → ((Fin p → ℝ) × Bool) × ℝ} [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hM : T.LogisticOutcomeModel (fun c => interactionDesign c.2 c.1) ξ₀) (hK : IsCompact K)
    (hξ₀ : ξ₀ ∈ K) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.μ.map fun ω => ((T.X ω, T.A ω), T.obsOutcome ω))
    (hX₂ : Measurable Q.X) {s₀ s₁ : ι} (hYQ₀ : Integrable (Q.Y s₀) Q.μ)
    (hYQ₁ : Integrable (Q.Y s₁) Q.μ)
    (hsi₀ : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y s₀))
    (hsi₁ : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y s₁))
    (hov : Q.covLaw ≪ T.covLaw) (hν : ∀ k, Integrable (fun x : Fin p → ℝ => x k) Q.covLaw)
    {xh : ℕ → Ξ → Fin p → ℝ} (hx : TendstoInMeasure P xh atTop fun _ => covMean Q.covLaw) :
    TendstoInMeasure P
      (fun n ω => linkContrast logit
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ
          glmMLE logisticDens (fun c => interactionDesign c.2 c.1) K O n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ
          glmMLE logisticDens (fun c => interactionDesign c.2 c.1) K O n ω)) (xh n ω)) atTop
      (fun _ => Q.marginalEffect logit s₀ s₁ +
        (averagingGap logit Q.covLaw (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ ξ₀)) -
          averagingGap logit Q.covLaw (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ ξ₀)))) :=
  tendstoInMeasure_conditionalPlugIn hT hYi logit_sigmoid (hM.isOutcomeRegression hT hYi) hX₂
    hYQ₀ hYQ₁ hsi₀ hsi₁ hov hν (hM.tendstoInMeasure hT hK hξ₀ hO hlaw) hx

end PopulationAdjustment

end CausalInference
