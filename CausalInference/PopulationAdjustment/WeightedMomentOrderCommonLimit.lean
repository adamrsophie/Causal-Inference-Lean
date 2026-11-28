/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencySharpCommonLimit
public import CausalInference.PopulationAdjustment.WeightedMomentOrderSetting

/-!
# The common limit at random reported moments under one exponential moment

The common limit theorems of weighting and standardization at random reported moments
(`commonLimit_reportedMoments_arm`, `_armMean`, `_unanchored`, `_anchored`, `_anchored_identity`)
assume `E[exp(κ ‖φ(X) - t‖)] < ∞` for every `κ`. Here one order suffices.

**The joint condition.** The two estimators need different moments.

* The weighted estimate needs `E[exp(κ ‖φ(X) - t‖)] < ∞` for one `κ > 2 p ‖β*‖`, where `β*`
  minimizes the population dual objective of the trial covariate law, and, for the arm used, a
  square integrable residual with bounded conditional variance.
* The least squares fit needs finite second moments of the design, that is of the features
  `φ(X)`, and of the potential outcomes `Y(a)` of both arms, and a positive definite design second
  moment.

The second moments of the features follow from an exponential moment of any positive order
(`memLp_feature_of_integrable_exp_pos`), and `κ > 2 p ‖β*‖ ≥ 0`; the positive definiteness follows
from the interior condition (`posDef_featureInteractionDesign_gram_of_memLp`); the residual of the
weighting side follows from the second moments of `Y(a)` and of the design. So the joint condition
is the condition of the weighting side together with `E[Y(a)²] < ∞` for both arms: the least
squares side needs no further moment of the features. The order `1` of the exponential moment
used by `Trial.linearOutcomeModel_of_interior` is not needed
(`Trial.linearOutcomeModel_of_interior_of_memLp`).

## Main results

* `memLp_feature_of_integrable_exp_pos`, `posDef_featureInteractionDesign_gram_of_memLp`,
  `Trial.linearOutcomeModel_of_interior_of_memLp`.
* `commonLimit_reportedMoments_arm_of_isMinOn`, `commonLimit_reportedMoments_armMean_of_isMinOn`,
  `commonLimit_reportedMoments_unanchored_of_isMinOn`,
  `commonLimit_reportedMoments_anchored_of_isMinOn`,
  `commonLimit_reportedMoments_anchored_identity_of_isMinOn`.

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

/-! ### The linear outcome model from second moments of the features -/

section Model

variable {Ω₁ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] {p : ℕ}
  {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {T : Trial Ω₁ 𝒳 Bool}

/-- **Second moments of the features from an exponential moment of any positive order**: if
`E[exp(κ ‖φ(X) - t‖)] < ∞` under the covariate law for some `κ > 0`, every coordinate of `φ(X)`
is square integrable in the trial. -/
theorem memLp_feature_of_integrable_exp_pos [IsProbabilityMeasure T.μ] (hX : Measurable T.X)
    (hφ : Measurable φ) {κ : ℝ} (hκ : 0 < κ)
    (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw) (j : Fin p) :
    MemLp (fun ω => φ (T.X ω) j) 2 T.μ := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hX
  have hsq : Integrable (fun x => ‖φ x - t‖ ^ 2) T.covLaw :=
    integrable_sq_of_integrable_exp_pos (g := fun x => ‖φ x - t‖) (hφ.sub_const t).norm
      (fun _ => norm_nonneg _) hκ hexp
  have hj : Measurable fun x => φ x j := (measurable_pi_apply j).comp hφ
  have h2 : MemLp (fun x => φ x j) 2 T.covLaw := by
    refine (memLp_two_iff_integrable_sq hj.aestronglyMeasurable).2 ?_
    refine ((hsq.const_mul 2).add (integrable_const (2 * ‖t‖ ^ 2))).mono'
      (hj.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |φ x j| ≤ ‖φ x - t‖ + ‖t‖ :=
      calc |φ x j| = ‖φ x j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) j
        _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖φ x - t‖ + ‖t‖ := norm_add_le _ _
    have h3 : φ x j ^ 2 ≤ (‖φ x - t‖ + ‖t‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖φ x - t‖ - ‖t‖)]
  rw [Population.covLaw] at h2
  exact (memLp_map_measure_iff (by rw [← Population.covLaw]; exact hj.aestronglyMeasurable)
    hX.aemeasurable).1 h2

/-- **The design second moment is positive definite under the interior condition, for square
integrable features.** For a randomized two arm trial, measurable features with square
integrable coordinates `φ(X)ⱼ` and `t` in the interior of the closed convex hull of the support
of the law of `φ(X)`, the second moment matrix of the interaction design is positive definite. -/
theorem posDef_featureInteractionDesign_gram_of_memLp [IsProbabilityMeasure T.μ]
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hφX : ∀ j, MemLp (fun ω => φ (T.X ω) j) 2 T.μ) :
    (Matrix.of fun j k => ∫ ω, featureInteractionDesign φ (T.A ω) (T.X ω) j *
      featureInteractionDesign φ (T.A ω) (T.X ω) k ∂T.μ).PosDef := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin_of_mem_interior_map (ν := T.covLaw) hφ hint
  have hz2 : ∀ a k, MemLp (fun ω => featureInteractionDesign φ a (T.X ω) k) 2 T.μ := by
    intro a k
    rcases k with (_ | j) | (_ | j) <;> cases a <;>
      simp only [featureInteractionDesign, interactionDesign, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact memLp_const _ | exact hφX j
  have hd2 : ∀ k, MemLp (fun ω => featureInteractionDesign φ (T.A ω) (T.X ω) k) 2 T.μ :=
    fun k => memLp_two_select (f := fun a ω => featureInteractionDesign φ a (T.X ω) k)
      hT.measurable_A (fun a => (measurable_featureInteractionDesign hφ a k).comp hT.measurable_X)
      fun a => hz2 a k
  refine posDef_gram_of_ae hd2 fun v hv => ?_
  have hsm : ∀ a, Measurable fun x => featureInteractionDesign φ a x ⬝ᵥ v := fun a =>
    Finset.measurable_sum _ fun k _ => (measurable_featureInteractionDesign hφ a k).mul_const _
  have harm : ∀ a : Bool, ∀ᵐ x ∂T.covLaw, featureInteractionDesign φ a x ⬝ᵥ v = 0 := by
    intro a
    have hS : MeasurableSet {x | ¬ featureInteractionDesign φ a x ⬝ᵥ v = 0} :=
      (measurableSet_eq_fun (hsm a) measurable_const).compl
    rw [ae_iff, Population.covLaw, Measure.map_apply hT.measurable_X hS]
    have h0 : T.μ (T.X ⁻¹' {x | ¬ featureInteractionDesign φ a x ⬝ᵥ v = 0} ∩ T.A ⁻¹' {a}) = 0 :=
      measure_mono_null (fun ω hω => by
        obtain ⟨h1, h2⟩ := hω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff] at h1 h2 ⊢
        rw [h2]; exact h1) (ae_iff.1 hv)
    rw [hT.indepFun_X_A.measure_inter_preimage_eq_mul _ _ hS (measurableSet_singleton a)]
      at h0
    have hpa : T.μ (T.A ⁻¹' {a}) ≠ 0 := by
      intro h
      have := hT.prob_arm_pos a
      rw [measureReal_def, h, ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    exact (mul_eq_zero.1 h0).resolve_right hpa
  have hf := eq_zero_of_ae_affine_of_margin hφ hδ hmargin ((harm false).mono fun x hx => by
    rw [featureInteractionDesign_dotProduct] at hx; simpa using hx)
  have ht := eq_zero_of_ae_affine_of_margin hφ hδ hmargin
    (c := interactionIntercept v + interactionEffect v)
    (w := interactionMain v + interactionModifier v) ((harm true).mono fun x hx => by
      rw [featureInteractionDesign_dotProduct] at hx; simpa [add_dotProduct] using hx)
  obtain ⟨hmain, hint0⟩ := hf
  obtain ⟨hmod, heff⟩ := ht
  rw [hint0, zero_add] at heff
  rw [hmain, zero_add] at hmod
  funext k
  rcases k with (_ | j) | (_ | j)
  · exact hint0
  · exact congrFun hmain j
  · exact heff
  · exact congrFun hmod j

/-- **The linear outcome model from square integrable features.** A randomized two arm trial with
measurable, square integrable features `φ(X)`, the interior condition at `t`, potential outcomes
of finite second moments and a regression linear in the interaction design is a linear outcome
model. No exponential moment is used. -/
theorem _root_.CausalInference.IndirectComparison.Trial.linearOutcomeModel_of_interior_of_memLp
    [IsProbabilityMeasure T.μ] (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hφ : Measurable φ) (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hφX : ∀ j, MemLp (fun ω => φ (T.X ω) j) 2 T.μ)
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀) :
    T.LinearOutcomeModel (featureInteractionDesign φ) ξ₀ where
  measurable_z a k := measurable_featureInteractionDesign hφ a k
  memLp_z a k := by
    rcases k with (_ | j) | (_ | j) <;> cases a <;>
      simp only [featureInteractionDesign, interactionDesign, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact memLp_const _ | exact hφX j
  memLp_Y := hY2
  posDef := posDef_featureInteractionDesign_gram_of_memLp hT hφ hint hφX
  isOutcomeRegression := hreg

end Model

/-! ### The two estimators of an arm -/

section Arm

variable {Ω₁ Ξ 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ξ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲} {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **Both estimators of an arm converge to `α_a + β_aᵀ t`, under one exponential moment.** The
hypotheses of `commonLimit_reportedMoments_arm`, with the exponential moments of all orders
replaced by a minimizer `β*` of the population dual objective of the trial covariate law and
`E[exp(κ ‖φ(X) - t‖)] < ∞` for one `κ > 2 p ‖β*‖`. Then the weighted arm mean and the
standardized estimate `z(a, tₙ)ᵀξ̂` at the reported moments `tₙ` converge in probability to
`z(a, t)ᵀξ₀`. -/
theorem commonLimit_reportedMoments_arm_of_isMinOn [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P]
    (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hκ : 2 * p * ‖βs‖ < κ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) (a : Bool) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω)
        (interactionDesign a t ⬝ᵥ ξ₀) P ∧
      TendstoInMeasure P (fun n ω => reportedMomentsArmFit φ O (G n (W ω)) a n ω) atTop
        (fun _ => interactionDesign a t ⬝ᵥ ξ₀) := by
  have hκ0 : 0 < κ := lt_of_le_of_lt (by positivity) hκ
  have hφX := memLp_feature_of_integrable_exp_pos hT.measurable_X hφ hκ0 hexp
  have hM := T.linearOutcomeModel_of_interior_of_memLp hT hY2 hφ hint hφX hreg
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  have hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ := by
    cases a
    · exact hT.indepFun.comp measurable_id (measurable_fst.prodMk measurable_snd.fst)
    · exact hT.indepFun.comp measurable_id (measurable_fst.prodMk measurable_snd.snd)
  have hm : T.IsCondMean a (fun x => featureInteractionDesign φ a x ⬝ᵥ ξ₀) :=
    hT.isCondMean hM.integrable_Y hM.isOutcomeRegression a
  have hres2 : Integrable (fun ω => (T.Y a ω - featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) ^ 2)
      T.μ := by
    have hd2 : MemLp (fun ω => featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) 2 T.μ := by
      simp only [dotProduct]
      exact memLp_finsetSum _ fun j _ => (hM.memLp_z a j).mul_const _
    exact ((hY2 a).sub hd2).integrable_sq
  have hval : (interactionIntercept ξ₀ + if a then interactionEffect ξ₀ else 0) +
      (interactionMain ξ₀ + if a then interactionModifier ξ₀ else 0) ⬝ᵥ t =
        interactionDesign a t ⬝ᵥ ξ₀ :=
    (featureInteractionDesign_dotProduct (fun s => s) a t ξ₀).symm
  have hW1 := sampleBalancedArmMean_isConsistent_trial_of_isMinOn hT.measurable_X
    hT.measurable_A hYo a (hT.measurable_Y a) hrand hO hOm hlaw hφ hint hmin hexp hκ hW hWO hG
    htm (hT.prob_arm_pos a) hm hres2 hvar (featureInteractionDesign_dotProduct φ a · ξ₀)
  rw [hval] at hW1
  refine ⟨hW1, ?_⟩
  have hc : Continuous fun q : (Option (Fin p) ⊕ Option (Fin p) → ℝ) × (Fin p → ℝ) =>
      interactionDesign a q.2 ⬝ᵥ q.1 :=
    ((continuous_interactionDesign a).comp continuous_snd).dotProduct continuous_fst
  exact ((hM.tendstoInMeasure hT hO hlaw).prodMk htm).comp_continuousAt hc.continuousAt

end Arm

/-! ### The target quantities -/

section Target

variable {Ω₁ Ω₂ Ξ 𝒳 ι 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool}
  {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ}
  {t : Fin p → ℝ} {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲}
  {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **The common limit is the target arm mean, under one exponential moment.** The hypotheses of
`commonLimit_reportedMoments_armMean` with the moments of all orders replaced by a minimizer `β*`
and `E[exp(κ ‖φ(X) - t‖)] < ∞` for one `κ > 2 p ‖β*‖`. Then the weighted arm mean and the
standardized estimate at the random reported moments `tₙ` both converge in probability to
`E_Q[Y(s)]`, and their difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_armMean_of_isMinOn [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hκ : 2 * p * ‖βs‖ < κ)
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
  have hκ0 : 0 < κ := lt_of_le_of_lt (by positivity) hκ
  have hM := T.linearOutcomeModel_of_interior_of_memLp hT hY2 hφ hint
    (memLp_feature_of_integrable_exp_pos hT.measurable_X hφ hκ0 hexp) hreg
  obtain ⟨hW1, hS1⟩ := commonLimit_reportedMoments_arm_of_isMinOn hT hY2 hφ hint hmin hexp hκ
    hreg hO hOm hlaw hW hWO hG htm a hvar
  have hlim : interactionDesign a t ⬝ᵥ ξ₀ = Q.armMean s := by
    rw [← (hM.isCondMean_target hT hX₂ hsi hov).integral_eq hX₂ hYQ]
    exact ((integral_featureInteractionDesign_dotProduct hQφ ht a ξ₀).2).symm
  rw [hlim] at hW1 hS1
  exact ⟨hW1, hS1, tendstoInMeasure_sub_zero_of_same_limit hS1 hW1⟩

/-- **The unanchored comparisons share their limit, under one exponential moment.** The
hypotheses of `commonLimit_reportedMoments_unanchored` with the moments of all orders replaced by
a minimizer `β*` and one moment of order `κ > 2 p ‖β*‖`. The weighted and the standardized
comparisons both converge in probability to the target marginal effect of `b` relative to `a`,
and their difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_unanchored_of_isMinOn [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hκ : 2 * p * ‖βs‖ < κ)
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
  obtain ⟨hW1, hS1, -⟩ := commonLimit_reportedMoments_armMean_of_isMinOn hT hY2 hφ hint hmin
    hexp hκ hreg hO hOm hlaw hW hWO hG htm true hvar hX₂ hQφ ht hYQ hsi hov
  have hW' := (hmb.comp_continuousAt hgb).sub (hW1.comp_continuousAt hga)
  have hS' := (hmb.comp_continuousAt hgb).sub (hS1.comp_continuousAt hga)
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

/-- **The anchored comparisons on a link scale share their limit, under one exponential
moment.** The hypotheses of `commonLimit_reportedMoments_anchored` with the moments of all orders
replaced by a minimizer `β*` and one moment of order `κ > 2 p ‖β*‖`; both arms share the covariate
law and so the minimizer and the moment. The weighted and the standardized anchored comparisons
both converge in probability to the target marginal effect of `b` relative to `a`, and their
difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_anchored_of_isMinOn [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hκ : 2 * p * ‖βs‖ < κ)
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
  obtain ⟨hWa, hSa, -⟩ := commonLimit_reportedMoments_armMean_of_isMinOn hT hY2 hφ hint hmin
    hexp hκ hreg hO hOm hlaw hW hWO hG htm true (hvar true) hX₂ hQφ ht hYQa hsia hov
  obtain ⟨hWc, hSc, -⟩ := commonLimit_reportedMoments_armMean_of_isMinOn hT hY2 hφ hint hmin
    hexp hκ hreg hO hOm hlaw hW hWO hG htm false (hvar false) hX₂ hQφ ht hYQc hsic hov
  have hlim : g (Q.armMean c) - g (Q.armMean a) - Q.marginalEffect g b c =
      Q.marginalEffect g a b := by
    simp only [Population.marginalEffect]; ring
  have hW' := isConsistent_link_contrast hWa hWc hdbc hga hgc
  have hS' := isConsistent_link_contrast hSa hSc hdbc hga hgc
  rw [hlim] at hW' hS'
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

/-- **The anchored comparisons on the identity scale share their limit under relative constancy
only, under one exponential moment.** The hypotheses of
`commonLimit_reportedMoments_anchored_identity` with the moments of all orders replaced by a
minimizer `β*` and one moment of order `κ > 2 p ‖β*‖`. The weighted and the standardized anchored
comparisons both converge in probability to `E_Q[Y(b)] - E_Q[Y(a)]`, and their difference
converges in probability to `0`. -/
theorem commonLimit_reportedMoments_anchored_identity_of_isMinOn [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hκ : 2 * p * ‖βs‖ < κ)
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
  obtain ⟨hWt, hSt⟩ := commonLimit_reportedMoments_arm_of_isMinOn hT hY2 hφ hint hmin hexp hκ
    hreg hO hOm hlaw hW hWO hG htm true (hvar true)
  obtain ⟨hWf, hSf⟩ := commonLimit_reportedMoments_arm_of_isMinOn hT hY2 hφ hint hmin hexp hκ
    hreg hO hOm hlaw hW hWO hG htm false (hvar false)
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
