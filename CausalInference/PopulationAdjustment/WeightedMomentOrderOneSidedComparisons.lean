/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderOneSidedCommonLimit

/-!
# The common limit of the comparisons under one sided moments

The common limit theorems for the target arm mean and for the unanchored and anchored
comparisons at random reported moments (`commonLimit_reportedMoments_armMean_of_isMinOn`,
`_unanchored_of_isMinOn`, `_anchored_of_isMinOn`, `_anchored_identity_of_isMinOn`) assume
`E[exp(κ ‖φ(X) - t‖)] < ∞` for one `κ > 2 p ‖β*‖`. Here this moment is replaced by the two one
sided conditions of `commonLimit_reportedMoments_arm_of_isMinOn_oneSided`:

* a norm moment `E[exp(r ‖φ(X) - t‖)] < ∞` of some order `r > 0`, and
* the directional moment `E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`,

both under the covariate law of the trial, where `β*` minimizes the population dual objective.

**What each side needs.** The weighting side uses the interior condition, the minimizer and the
two one sided moments, and for each arm used a bounded conditional variance of the residual. The
least squares side uses the second moments of the potential outcomes and of the features; the
latter follow from the norm moment of order `r` (`memLp_feature_of_integrable_exp_pos`), and the
positive definiteness of the design second moment follows from the interior condition. The arm
level statement `commonLimit_reportedMoments_arm_of_isMinOn_oneSided` carries both sides; every
theorem below is derived from it.

## Main results

* `commonLimit_reportedMoments_armMean_of_isMinOn_oneSided`: the common limit is the target arm
  mean.
* `commonLimit_reportedMoments_unanchored_of_isMinOn_oneSided`: the unanchored comparisons.
* `commonLimit_reportedMoments_anchored_of_isMinOn_oneSided`: the anchored comparisons on a link
  scale.
* `commonLimit_reportedMoments_anchored_identity_of_isMinOn_oneSided`: the anchored comparisons on
  the identity scale under relative constancy.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

section Target

variable {Ω₁ Ω₂ Ξ 𝒳 ι 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool}
  {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ}
  {t : Fin p → ℝ} {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲}
  {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **The common limit is the target arm mean, under one sided moments.** The hypotheses of
`commonLimit_reportedMoments_armMean_of_isMinOn`, with the moment of order `κ > 2 p ‖β*‖`
replaced by `E[exp(r ‖φ(X) - t‖)] < ∞` for some `r > 0` and
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`. Then the weighted arm mean and the
standardized estimate at the random reported moments `tₙ` both converge in probability to
`E_Q[Y(s)]`, and their difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_armMean_of_isMinOn_oneSided [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) (a : Bool) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (Q.armMean s) P ∧
      TendstoInMeasure P (fun n ω => reportedMomentsArmFit φ O (G n (W ω)) a n ω) atTop
        (fun _ => Q.armMean s) ∧
      TendstoInMeasure P (fun n ω => reportedMomentsArmFit φ O (G n (W ω)) a n ω -
        sampleBalancedArmMean φ (G n (W ω)) O a n ω) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  have hM := T.linearOutcomeModel_of_interior_of_memLp hT hY2 hφ hint
    (memLp_feature_of_integrable_exp_pos hT.measurable_X hφ hr hexp) hreg
  obtain ⟨hW1, hS1⟩ := commonLimit_reportedMoments_arm_of_isMinOn_oneSided hT hY2 hφ hint hmin
    hr hexp hε hdir hreg hO hOm hlaw hW hWO hG htm a hvar
  have hlim : interactionDesign a t ⬝ᵥ ξ₀ = Q.armMean s := by
    rw [← (hM.isCondMean_target hT hX₂ hsi hov).integral_eq hX₂ hYQ]
    exact ((integral_featureInteractionDesign_dotProduct hQφ ht a ξ₀).2).symm
  rw [hlim] at hW1 hS1
  exact ⟨hW1, hS1, tendstoInMeasure_sub_zero_of_same_limit hS1 hW1⟩

/-- **The unanchored comparisons share their limit, under one sided moments.** The hypotheses of
`commonLimit_reportedMoments_unanchored_of_isMinOn` with the moment of order `κ > 2 p ‖β*‖`
replaced by a norm moment of some order `r > 0` and the directional moment
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`. The weighted and the standardized
comparisons both converge in probability to the target marginal effect of `b` relative to `a`,
and their difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_unanchored_of_isMinOn_oneSided [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y true ω - featureInteractionDesign φ true (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b : ι} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    {mb : ℕ → Ξ → ℝ} (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    IsConsistent (fun n ω => g (mb n ω) - g (sampleBalancedArmMean φ (G n (W ω)) O true n ω))
        (Q.marginalEffect g a b) P ∧
      TendstoInMeasure P (fun n ω => g (mb n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) atTop
        (fun _ => Q.marginalEffect g a b) ∧
      TendstoInMeasure P (fun n ω => (g (mb n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) -
          (g (mb n ω) - g (sampleBalancedArmMean φ (G n (W ω)) O true n ω))) atTop
        (fun _ => 0) := by
  obtain ⟨hW1, hS1, -⟩ := commonLimit_reportedMoments_armMean_of_isMinOn_oneSided hT hY2 hφ hint
    hmin hr hexp hε hdir hreg hO hOm hlaw hW hWO hG htm true hvar hX₂ hQφ ht hYQ hsi hov
  have hW' := (hmb.comp_continuousAt hgb).sub (hW1.comp_continuousAt hga)
  have hS' := (hmb.comp_continuousAt hgb).sub (hS1.comp_continuousAt hga)
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

/-- **The anchored comparisons on a link scale share their limit, under one sided moments.** The
hypotheses of `commonLimit_reportedMoments_anchored_of_isMinOn` with the moment of order
`κ > 2 p ‖β*‖` replaced by a norm moment of some order `r > 0` and the directional moment
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`; both arms share the covariate law and so
the minimizer and the two moments. The weighted and the standardized anchored comparisons both
converge in probability to the target marginal effect of `b` relative to `a`, and their
difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_anchored_of_isMinOn_oneSided [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) {σ2 : ℝ}
    (hvar : ∀ e : Bool, T.μ[fun ω => (T.Y e ω - featureInteractionDesign φ e (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y c))
    (hov : Q.covLaw ≪ T.covLaw) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    IsConsistent (fun n ω => (g (sampleBalancedArmMean φ (G n (W ω)) O false n ω) -
        g (sampleBalancedArmMean φ (G n (W ω)) O true n ω)) - dbc n ω)
        (Q.marginalEffect g a b) P ∧
      TendstoInMeasure P (fun n ω => (g (reportedMomentsArmFit φ O (G n (W ω)) false n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) - dbc n ω) atTop
        (fun _ => Q.marginalEffect g a b) ∧
      TendstoInMeasure P (fun n ω => ((g (reportedMomentsArmFit φ O (G n (W ω)) false n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) - dbc n ω) -
          ((g (sampleBalancedArmMean φ (G n (W ω)) O false n ω) -
            g (sampleBalancedArmMean φ (G n (W ω)) O true n ω)) - dbc n ω)) atTop
        (fun _ => 0) := by
  obtain ⟨hWa, hSa, -⟩ := commonLimit_reportedMoments_armMean_of_isMinOn_oneSided hT hY2 hφ hint
    hmin hr hexp hε hdir hreg hO hOm hlaw hW hWO hG htm true (hvar true) hX₂ hQφ ht hYQa hsia hov
  obtain ⟨hWc, hSc, -⟩ := commonLimit_reportedMoments_armMean_of_isMinOn_oneSided hT hY2 hφ hint
    hmin hr hexp hε hdir hreg hO hOm hlaw hW hWO hG htm false (hvar false) hX₂ hQφ ht hYQc hsic
    hov
  have hlim : g (Q.armMean c) - g (Q.armMean a) - Q.marginalEffect g b c =
      Q.marginalEffect g a b := by
    simp only [Population.marginalEffect]; ring
  have hW' := isConsistent_link_contrast hWa hWc hdbc hga hgc
  have hS' := isConsistent_link_contrast hSa hSc hdbc hga hgc
  rw [hlim] at hW' hS'
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

/-- **The anchored comparisons on the identity scale share their limit under relative constancy
only, under one sided moments.** The hypotheses of
`commonLimit_reportedMoments_anchored_identity_of_isMinOn` with the moment of order
`κ > 2 p ‖β*‖` replaced by a norm moment of some order `r > 0` and the directional moment
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`. The weighted and the standardized
anchored comparisons both converge in probability to `E_Q[Y(b)] - E_Q[Y(a)]`, and their
difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_anchored_identity_of_isMinOn_oneSided
    [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) {σ2 : ℝ}
    (hvar : ∀ e : Bool, T.μ[fun ω => (T.Y e ω - featureInteractionDesign φ e (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hrel : (fun ω => featureInteractionDesign φ false (Q.X ω) ⬝ᵥ ξ₀ -
        featureInteractionDesign φ true (Q.X ω) ⬝ᵥ ξ₀) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance])
    {dbc : ℕ → Ξ → ℝ} (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect id b c) :
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
        (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  obtain ⟨hWt, hSt⟩ := commonLimit_reportedMoments_arm_of_isMinOn_oneSided hT hY2 hφ hint hmin
    hr hexp hε hdir hreg hO hOm hlaw hW hWO hG htm true (hvar true)
  obtain ⟨hWf, hSf⟩ := commonLimit_reportedMoments_arm_of_isMinOn_oneSided hT hY2 hφ hint hmin
    hr hexp hε hdir hreg hO hOm hlaw hW hWO hG htm false (hvar false)
  obtain ⟨hif, hef⟩ := integral_featureInteractionDesign_dotProduct hQφ ht false ξ₀
  obtain ⟨hit, het⟩ := integral_featureInteractionDesign_dotProduct hQφ ht true ξ₀
  have hid : ∫ ω, (Q.Y c ω - Q.Y a ω) ∂Q.μ =
      ∫ x, (featureInteractionDesign φ false x ⬝ᵥ ξ₀ - featureInteractionDesign φ true x ⬝ᵥ ξ₀)
        ∂Q.covLaw :=
    Transport.integral_eq_integral_map_of_condExp (Y := fun ω => Q.Y c ω - Q.Y a ω)
      (f := fun x => featureInteractionDesign φ false x ⬝ᵥ ξ₀ -
        featureInteractionDesign φ true x ⬝ᵥ ξ₀) hX₂ (hYQc.sub hYQa)
      ((measurable_linearSurface (measurable_featureInteractionDesign hφ) ξ₀ false).sub
        (measurable_linearSurface (measurable_featureInteractionDesign hφ) ξ₀ true)) hrel
  rw [integral_sub hYQc hYQa, integral_sub hif hit, hef, het] at hid
  have hval : id (interactionDesign false t ⬝ᵥ ξ₀) - id (interactionDesign true t ⬝ᵥ ξ₀) -
      Q.marginalEffect id b c = Q.marginalEffect id a b := by
    simp only [Population.marginalEffect, Population.armMean, id] at hid ⊢
    linarith
  have hW' := isConsistent_link_contrast hWt hWf hdbc continuousAt_id continuousAt_id
  have hS' := isConsistent_link_contrast hSt hSf hdbc continuousAt_id continuousAt_id
  rw [hval] at hW' hS'
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

end Target

end PopulationAdjustment

end CausalInference
