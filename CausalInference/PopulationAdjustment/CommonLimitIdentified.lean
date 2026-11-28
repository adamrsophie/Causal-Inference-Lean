/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitLinear

/-!
# Estimation composed with identification

Identification shows that a target effect equals an estimand computed from the trial surfaces
(`UnanchoredSetting.IdentificationAssumptions.identification`,
`AnchoredSetting.IdentificationAssumptions.identification`); the consistency theorems of
the weighted estimator and of standardization show that an estimator converges to a functional
of the trial law. This file composes the two: for an index trial, an i.i.d. sample of its
individual data and a target population satisfying the identification assumptions, both
estimators converge in probability to the identified estimand, which is the target causal effect.

The index trial `T` randomizes the arms `true` and `false`, with a regression linear in the
interaction design of the features (`featureInteractionDesign`); every design condition of the
two consistency theorems is derived from the primitive conditions of `CommonLimitLinear`. In a
comparison with treatments in `ι` the arms are the treatments `a` and `c` (`Trial.relabelArms`).

**Which constancy and which scale.**

* **Unanchored** (`unanchored_identified`): absolute constancy of `a` from the trial and of `b`
  from a second source, overlap, any link `g` continuous at the two target means. Both
  estimators of `g(m_b) - g(m_a)` converge to the unanchored estimand `linkMarginal g Q_X m_a m_b`,
  which is the target marginal effect.
* **Anchored, identity scale, relative constancy** (`anchored_identity_identified`): the effect of
  `c` against `a` on the identity scale is conditionally constant from the trial to the target;
  the arm means need not carry over. The identified conditional estimand
  `linkConditional id Q_X m_a m_c` is the target effect of `c` relative to `a`, and both
  estimators converge to the target effect of `b` relative to `a`. The identity scale is directly
  collapsible, so the conditional and the marginal effects agree here.
* **Anchored, any link, absolute constancy** (`anchored_link_identified`): both anchored
  estimators are marginal contrasts of standardized means. With absolute constancy of both trial
  arms they converge to the target marginal effect on the scale of `g`. On a non collapsible scale
  relative constancy alone does not identify this marginal effect
  (`AnchoredSetting.exists_anchoredEstimand_ne_marginalEffect`, and the logit instance
  `anchored_logit_marginalEffect_ne_linkConditional`), so no marginal claim is made under it.

In every theorem the reported aggregate quantity of the other study (`m̂_b`, or `d̂_bc`) is
assumed to converge in probability to the corresponding target quantity (`E_Q[Y(b)]`, or the
target marginal effect of `c` relative to `b`), as the summary of a randomized trial run in the
target population does.

## Main definitions

* `Trial.relabelArms`: the index trial with treatment labels.
* `commonLimitStandardized`: the standardized estimator of an arm mean.

## Main results

* `condExp_contrast_of_relativeConstancy`: relative constancy on the identity scale as a
  conditional mean of the target contrast.
* `unanchored_identified`, `anchored_identity_identified`, `anchored_link_identified`.

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

/-! ### The index trial with treatment labels -/

section Relabel

variable {Ω₁ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] [DecidableEq ι]

/-- The index trial with its arms named by treatments: arm `true` is treatment `a`, arm `false`
is treatment `c`. Every treatment other than `a` carries the outcome of arm `false`, so only the
labels `a` and `c` carry meaning. -/
def _root_.CausalInference.IndirectComparison.Trial.relabelArms (T : Trial Ω₁ 𝒳 Bool)
    (a c : ι) : Trial Ω₁ 𝒳 ι where
  μ := T.μ
  X := T.X
  Y s := if s = a then T.Y true else T.Y false
  A ω := if T.A ω then a else c

omit [MeasurableSpace 𝒳] in
/-- The conditional mean of `Y(a)` in the relabeled trial is that of arm `true`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.relabelArms_isCondMean_left
    [MeasurableSpace 𝒳] (T : Trial Ω₁ 𝒳 Bool) (a c : ι) (m : 𝒳 → ℝ) :
    (T.relabelArms a c).IsCondMean a m ↔ T.IsCondMean true m := by
  simp [Population.IsCondMean, Trial.relabelArms]

omit [MeasurableSpace 𝒳] in
/-- The conditional mean of `Y(c)` in the relabeled trial is that of arm `false`, for `a ≠ c`. -/
theorem _root_.CausalInference.IndirectComparison.Trial.relabelArms_isCondMean_right
    [MeasurableSpace 𝒳] (T : Trial Ω₁ 𝒳 Bool) {a c : ι} (hac : a ≠ c) (m : 𝒳 → ℝ) :
    (T.relabelArms a c).IsCondMean c m ↔ T.IsCondMean false m := by
  simp [Population.IsCondMean, Trial.relabelArms, Ne.symm hac]

end Relabel

/-! ### Relative constancy on the identity scale as a conditional mean -/

section Relative

variable {Ω₁ Ω₂ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]
  [DecidableEq ι]

/-- **Relative constancy on the identity scale gives the conditional mean of the target
contrast.** If the effect of `c` against `a` on the identity scale is conditionally constant from
the relabeled trial to the target, the trial conditional means of the two arms are `m_true` and
`m_false`, and the target covariate law is absolutely continuous with respect to the trial
covariate law, then `m_false(X) - m_true(X)` is the conditional mean of `Y(c) - Y(a)` in the
target. -/
theorem condExp_contrast_of_relativeConstancy {T : Trial Ω₁ 𝒳 Bool} {Q : Population Ω₂ 𝒳 ι}
    {a c : ι} (hac : a ≠ c) (hX₁ : Measurable T.X) (hX₂ : Measurable Q.X)
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ)
    (hov : Q.covLaw ≪ T.covLaw) {mt mf : 𝒳 → ℝ} (hmt : T.IsCondMean true mt)
    (hmf : T.IsCondMean false mf)
    (hcc : RelativeConstancy id (T.relabelArms a c).toPopulation Q a c) :
    (fun ω => mf (Q.X ω) - mt (Q.X ω)) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance] := by
  obtain ⟨τ, na, nc, na', nc', hna, hnc, hna', hnc', h₁, h₂⟩ := hcc
  have he := RelativeConstancy.ae_eq ⟨τ, na, nc, na', nc', hna, hnc, hna', hnc', h₁, h₂⟩ hX₁ hX₂
    hov ((T.relabelArms_isCondMean_left a c mt).2 hmt)
    ((T.relabelArms_isCondMean_right hac mf).2 hmf) hna' hnc'
  have he' := ae_of_ae_map hX₂.aemeasurable he
  have hsub : Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance] =ᵐ[Q.μ]
      Q.μ[Q.Y c | MeasurableSpace.comap Q.X inferInstance] -
        Q.μ[Q.Y a | MeasurableSpace.comap Q.X inferInstance] :=
    condExp_sub hYQc hYQa _
  filter_upwards [he', hna'.2, hnc'.2, hsub] with ω h hA hC hS
  simp only [linkContrast, id] at h
  rw [h, hS, Pi.sub_apply, ← hA, ← hC]

end Relative

/-! ### The final statements -/

section Identified

variable {Ω₁ Ω₂ Ω₃ Ξ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
  [MeasurableSpace Ξ] [MeasurableSpace 𝒳] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool}
  {Pb : Population Ω₂ 𝒳 ι} {Q : Population Ω₃ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ}
  {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}

/-- The standardized estimator of the regression of arm `e`: the fitted surface of the
interaction design averaged over the target covariate law. -/
noncomputable def commonLimitStandardized (φ : 𝒳 → Fin p → ℝ) (ν : Measure 𝒳)
    (O : ℕ → Ξ → 𝒳 × Bool × ℝ) (e : Bool) (n : ℕ) (ω : Ξ) : ℝ :=
  ∫ x, featureInteractionDesign φ e x ⬝ᵥ
    leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω ∂ν

/-- **The unanchored comparison: estimator limit, identified estimand and target effect.** Let
the index trial `T` be randomized, with potential outcomes of finite second moments and the
regression `E[Y | X, A] = z(A, X)ᵀξ₀` linear in the interaction design
`z(a, x) = (1, φ(x), 1[a], 1[a]φ(x))` of bounded measurable features with the margin condition at
`t`, and a bounded conditional residual variance of the records; let `O` be a measurable i.i.d.
sample of its individual data. Let the target `Q` have a probability law, measurable covariates,
feature means `t` and integrable `Y(a)`, `Y(b)`; let arm `true` of the trial carry over to
treatment `a` of the target (absolute constancy and overlap), and let a source `Pb` with
measurable covariates and a conditional mean `m_b` of `Y(b)` carry over to the target in the same
way. Let `g` be continuous at the two target means and the reported mean `m̂_b` converge in
probability to `E_Q[Y(b)]`. Then the weighted comparison `g(m̂_b) - g(μ̂_true)` and the
standardized comparison `g(m̂_b) - g(∫ z(true, x)ᵀξ̂ dQ_X)` both converge in probability to the
unanchored estimand `linkMarginal g Q_X m_a m_b` with `m_a = z(true, ·)ᵀξ₀`, this estimand is the
target marginal effect of `b` relative to `a`, and the difference of the two estimators converges
in probability to `0`. -/
theorem unanchored_identified [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - featureInteractionDesign φ o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b : ι}
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQb : Integrable (Q.Y b) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a)) (hova : Q.covLaw ≪ T.covLaw)
    (hXb : Measurable Pb.X) {mb : 𝒳 → ℝ} (hmb : Pb.IsCondMean b mb)
    (hsib : StructurallyInvariant Pb.μ Pb.X (Pb.Y b) Q.μ Q.X (Q.Y b))
    (hovb : Q.covLaw ≪ Pb.covLaw) {g : ℝ → ℝ} (hga : ContinuousAt g (Q.armMean a))
    (hgb : ContinuousAt g (Q.armMean b)) {mbh : ℕ → Ξ → ℝ}
    (hmbh : TendstoInMeasure P mbh atTop fun _ => Q.armMean b) :
    IsConsistent (unanchoredBalancedEstimate g φ t O mbh)
      (linkMarginal g Q.covLaw (fun x => featureInteractionDesign φ true x ⬝ᵥ ξ₀) mb) P ∧
      TendstoInMeasure P (fun n ω => g (mbh n ω) -
        g (commonLimitStandardized φ Q.covLaw O true n ω)) atTop
          (fun _ => linkMarginal g Q.covLaw (fun x => featureInteractionDesign φ true x ⬝ᵥ ξ₀)
            mb) ∧
      linkMarginal g Q.covLaw (fun x => featureInteractionDesign φ true x ⬝ᵥ ξ₀) mb =
        Q.marginalEffect g a b ∧
      TendstoInMeasure P (fun n ω => (g (mbh n ω) -
        g (commonLimitStandardized φ Q.covLaw O true n ω)) -
          unanchoredBalancedEstimate g φ t O mbh n ω) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  have hM := T.linearOutcomeModel_featureInteraction hT hY2 hφ hB hδ hmargin hreg
  have hQa := hM.isCondMean_target hT hX₂ hsia hova
  have hQb := Population.IsCondMean.of_structurallyInvariant hXb hX₂ hmb hsib hovb
  have heq : linkMarginal g Q.covLaw (fun x => featureInteractionDesign φ true x ⬝ᵥ ξ₀) mb =
      Q.marginalEffect g a b := by
    simp only [linkMarginal, Population.marginalEffect]
    rw [hQa.integral_eq hX₂ hYQa, hQb.integral_eq hX₂ hYQb]
  obtain ⟨hW, hS, hd⟩ := commonLimit_leastSquares_unanchored hT hM hO hOm hlaw hφ hB
    hδ hmargin hvar (featureInteractionDesign_dotProduct φ true · ξ₀) hX₂ ht
    (integrable_featureInteractionDesign hφ hB true) hYQa hsia hova hmbh hga hgb
  rw [← heq] at hW hS
  exact ⟨hW, hS, heq, hd⟩

/-- **The anchored comparison on the identity scale under relative constancy: estimator limit,
identified estimand and target effect.** Under the trial conditions of `unanchored_identified`,
let the target `Q` have a probability law, measurable covariates, feature means `t` and
integrable `Y(a)`, `Y(c)`, with `a ≠ c`; let the effect of `c` against `a` on the identity scale
be conditionally constant from the trial (arm `true` is `a`, arm `false` is `c`) to the target,
with overlap, and let the reported contrast `d̂_bc` converge in probability to
`E_Q[Y(c)] - E_Q[Y(b)]`. The arm means themselves need not carry over. Then the identified
conditional estimand `∫ (m_c - m_a) dQ_X` of the index comparison, with `m_a = z(true, ·)ᵀξ₀` and
`m_c = z(false, ·)ᵀξ₀`, is the target effect `E_Q[Y(c)] - E_Q[Y(a)]`; the weighted and the
standardized anchored comparisons on the identity scale both converge in probability to the
target effect `E_Q[Y(b)] - E_Q[Y(a)]`; and their difference converges in probability to `0`. -/
theorem anchored_identity_identified [DecidableEq ι] [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - featureInteractionDesign φ o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b c : ι} (hac : a ≠ c)
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ)
    (hcc : RelativeConstancy id (T.relabelArms a c).toPopulation Q a c)
    (hov : Q.covLaw ≪ T.covLaw) {dbc : ℕ → Ξ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect id b c) :
    linkConditional id Q.covLaw (fun x => featureInteractionDesign φ true x ⬝ᵥ ξ₀)
        (fun x => featureInteractionDesign φ false x ⬝ᵥ ξ₀) = Q.marginalEffect id a c ∧
      IsConsistent (anchoredBalancedEstimate id φ t O dbc) (Q.marginalEffect id a b) P ∧
      TendstoInMeasure P (fun n ω => commonLimitStandardized φ Q.covLaw O false n ω -
        commonLimitStandardized φ Q.covLaw O true n ω - dbc n ω) atTop
          (fun _ => Q.marginalEffect id a b) ∧
      TendstoInMeasure P (fun n ω => (commonLimitStandardized φ Q.covLaw O false n ω -
        commonLimitStandardized φ Q.covLaw O true n ω - dbc n ω) -
          anchoredBalancedEstimate id φ t O dbc n ω) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  have hM := T.linearOutcomeModel_featureInteraction hT hY2 hφ hB hδ hmargin hreg
  have hrel := condExp_contrast_of_relativeConstancy hac hT.measurable_X hX₂ hYQa hYQc hov
    (hT.isCondMean hM.integrable_Y hM.isOutcomeRegression true)
    (hT.isCondMean hM.integrable_Y hM.isOutcomeRegression false) hcc
  have hest : linkConditional id Q.covLaw (fun x => featureInteractionDesign φ true x ⬝ᵥ ξ₀)
      (fun x => featureInteractionDesign φ false x ⬝ᵥ ξ₀) = Q.marginalEffect id a c := by
    have h := Transport.integral_eq_integral_map_of_condExp hX₂ (hYQc.sub hYQa)
      ((measurable_linearSurface (measurable_featureInteractionDesign hφ) ξ₀ false).sub
        (measurable_linearSurface (measurable_featureInteractionDesign hφ) ξ₀ true)) hrel
    simp only [linkConditional, linkContrast, Population.marginalEffect, Population.armMean, id]
    rw [← integral_sub hYQc hYQa]
    exact h.symm
  obtain ⟨hW, hS, hd⟩ := commonLimit_leastSquares_anchored_identity hT hM hO hOm hlaw hφ hB hδ
    hmargin hvar (α := fun e => interactionIntercept ξ₀ + if e then interactionEffect ξ₀ else 0)
    (β := fun e => interactionMain ξ₀ + if e then interactionModifier ξ₀ else 0)
    (fun e x => featureInteractionDesign_dotProduct φ e x ξ₀) hX₂ ht
    (integrable_featureInteractionDesign hφ hB) hYQa hYQc hrel hdbc
  exact ⟨hest, hW, hS, hd⟩

/-- **The anchored comparison on a link scale under absolute constancy: estimator limit and
target effect.** Under the trial conditions of `unanchored_identified`, let the target `Q` have a
probability law, measurable covariates, feature means `t` and integrable `Y(a)`, `Y(c)`; let arm
`true` of the trial carry over to treatment `a` and arm `false` to treatment `c` (absolute
constancy and overlap); let `g` be continuous at the target means of `a` and `c` and the reported
contrast `d̂_bc` converge in probability to the target marginal effect of `c` relative to `b` on
the scale of `g`. Then the weighted and the standardized anchored comparisons both converge in
probability to the target marginal effect `g(E_Q[Y(b)]) - g(E_Q[Y(a)])`, and their difference
converges in probability to `0`. On a non collapsible scale this limit is in general not the
anchored estimand of averaged conditional contrasts, and relative constancy alone does not give
it (`AnchoredSetting.exists_anchoredEstimand_ne_marginalEffect`). -/
theorem anchored_link_identified [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    {σ2 : ℝ} (hvar : T.ipdLaw[fun o => (o.2.2 - featureInteractionDesign φ o.2.1 o.1 ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap (fun o : 𝒳 × Bool × ℝ => (o.1, o.2.1)) inferInstance]
        ≤ᵐ[T.ipdLaw] fun _ => σ2)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b c : ι}
    (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y c))
    (hov : Q.covLaw ≪ T.covLaw) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    IsConsistent (anchoredBalancedEstimate g φ t O dbc) (Q.marginalEffect g a b) P ∧
      TendstoInMeasure P (fun n ω => g (commonLimitStandardized φ Q.covLaw O false n ω) -
        g (commonLimitStandardized φ Q.covLaw O true n ω) - dbc n ω) atTop
          (fun _ => Q.marginalEffect g a b) ∧
      TendstoInMeasure P (fun n ω => (g (commonLimitStandardized φ Q.covLaw O false n ω) -
        g (commonLimitStandardized φ Q.covLaw O true n ω) - dbc n ω) -
          anchoredBalancedEstimate g φ t O dbc n ω) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  exact commonLimit_leastSquares_anchored hT
    (T.linearOutcomeModel_featureInteraction hT hY2 hφ hB hδ hmargin hreg) hO hOm hlaw hφ hB hδ
    hmargin hvar (α := fun e => interactionIntercept ξ₀ + if e then interactionEffect ξ₀ else 0)
    (β := fun e => interactionMain ξ₀ + if e then interactionModifier ξ₀ else 0)
    (fun e x => featureInteractionDesign_dotProduct φ e x ξ₀) hX₂ ht
    (integrable_featureInteractionDesign hφ hB) hYQa hYQc hsia hsic hov hdbc hga hgc

end Identified

end PopulationAdjustment

end CausalInference
