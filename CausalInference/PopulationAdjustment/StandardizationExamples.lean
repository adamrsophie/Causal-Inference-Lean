/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationIdentification

/-!
# Concrete models for identification by standardization

* **Two populations on a binary covariate** (`standardization_identification_example`). The
  source has two equally likely strata, the target has strata of probabilities `1/4` (for
  `true`) and `3/4`; both have the conditional means
  `m_t(x) = (t + 1)/4 + 1{x}/8` for the three treatments `t = 0, 1, 2`, so every arm has absolute
  constancy, and the target covariate law is absolutely continuous with respect to the source
  one. The target means are `9/32` and `17/32` for `t = 0, 1`, the target marginal log risk ratio
  of `1` against `0` is `log (17/9)`, and it is recovered by standardizing the source surfaces,
  by the unanchored and anchored comparisons, and by density ratio weighting of the source
  outcomes; the anchored average conditional effect is the anchored estimand.
* **A trial with a trivial covariate** (`standardization_trial_example`): a trial on `Bool` with
  the two arms equally likely, the trivial covariate, and outcomes `0` and `1`. The observed
  regression `m(t) = 1{t}` is a correct outcome model of each arm, and the target effect of `true`
  against `false` on the identity scale is `1`.

## Main results

* `standardization_identification_example`, `standardization_weighting_example`,
  `standardization_trial_example`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison Transport PointTreatment
  MissingData

/-! ### Two populations on a binary covariate -/

/-- The conditional means `m_t(x) = (t + 1)/4 + 1{x}/8` of the three treatments. -/
noncomputable def standardizationSurface (t : Fin 3) (x : Bool) : ℝ :=
  ((t : ℕ) + 1 : ℝ) / 4 + if x then 1 / 8 else 0

/-- The target covariate law: `true` with probability `1/4`. -/
noncomputable def standardizationTargetLaw : Measure Bool :=
  stratumLaw fun v => if v then 1 / 4 else 3 / 4

instance : IsProbabilityMeasure standardizationTargetLaw :=
  isProbabilityMeasure_stratumLaw ⟨fun v => by cases v <;> norm_num, by simp; norm_num⟩

/-- The source population: two equally likely strata. -/
noncomputable def standardizationSource : Population Bool Bool (Fin 3) :=
  ⟨halfLaw, id, standardizationSurface⟩

/-- The target population. -/
noncomputable def standardizationTarget : Population Bool Bool (Fin 3) :=
  ⟨standardizationTargetLaw, id, standardizationSurface⟩

instance : IsProbabilityMeasure standardizationSource.μ := by
  simp only [standardizationSource]; infer_instance

instance : IsProbabilityMeasure standardizationTarget.μ := by
  simp only [standardizationTarget]; infer_instance

theorem standardizationSource_isCondMean (t : Fin 3) :
    standardizationSource.IsCondMean t (standardizationSurface t) :=
  Population.isCondMean_of_eq_comp measurable_id (measurable_of_finite _) rfl Integrable.of_finite

theorem standardizationTarget_isCondMean (t : Fin 3) :
    standardizationTarget.IsCondMean t (standardizationSurface t) :=
  Population.isCondMean_of_eq_comp measurable_id (measurable_of_finite _) rfl Integrable.of_finite

theorem standardization_structurallyInvariant (t : Fin 3) :
    StructurallyInvariant standardizationSource.μ standardizationSource.X
      (standardizationSource.Y t) standardizationTarget.μ standardizationTarget.X
      (standardizationTarget.Y t) :=
  ⟨_, (Population.isCommonRegression_iff t _).2
    ⟨standardizationSource_isCondMean t, standardizationTarget_isCondMean t⟩⟩

theorem standardizationTarget_covLaw : standardizationTarget.covLaw = standardizationTargetLaw := by
  simp [standardizationTarget, Population.covLaw]

theorem standardization_absolutelyContinuous :
    standardizationTarget.covLaw ≪ standardizationSource.covLaw := by
  intro s hs
  have hsrc : standardizationSource.covLaw = halfLaw := by
    simp [standardizationSource, Population.covLaw]
  rw [hsrc, measure_eq_zero_iff_ae_notMem, ae_halfLaw_iff] at hs
  rw [Set.eq_empty_of_forall_notMem hs, measure_empty]

theorem integral_standardizationSurface (t : Fin 3) :
    ∫ x, standardizationSurface t x ∂standardizationTargetLaw = ((t : ℕ) + 1 : ℝ) / 4 + 1 / 32 := by
  rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
  simp [standardizedRisk, standardizationSurface]
  ring

/-- **An instance of identification by standardization.** In the two populations on a binary
covariate the target means of arms `0` and `1` are `9/32` and `17/32`, and the target marginal
log risk ratio of `1` against `0` is `log (17/9)`; it is the marginal estimand of the source
surfaces under the target covariate law, the unanchored comparison, the anchored comparison
through `2`, and the density ratio weighting of the source outcomes; and the anchored average
conditional effect is the anchored estimand. -/
theorem standardization_identification_example :
    standardizationTarget.armMean 0 = 9 / 32 ∧ standardizationTarget.armMean 1 = 17 / 32 ∧
      standardizationTarget.marginalEffect Real.log 0 1 = Real.log (17 / 9) ∧
      standardizationTarget.marginalEffect Real.log 0 1 =
        linkMarginal Real.log standardizationTarget.covLaw (standardizationSurface 0)
          (standardizationSurface 1) ∧
      (⟨standardizationSource, standardizationSource, standardizationTarget, 0, 1⟩ :
          UnanchoredSetting Bool Bool Bool Bool (Fin 3)).target.marginalEffect Real.log 0 1 =
        linkMarginal Real.log standardizationTarget.covLaw (standardizationSurface 0)
          (standardizationSurface 1) ∧
      standardizationTarget.marginalEffect Real.log 0 1 =
        Real.log (standardizationTarget.armMean 1) -
          linkPosition Real.log standardizationTarget.covLaw (standardizationSurface 0) ∧
      standardizationTarget.marginalEffect Real.log 0 1 =
        linkMarginal Real.log standardizationTarget.covLaw (standardizationSurface 0)
            (standardizationSurface 2) -
          standardizationTarget.marginalEffect Real.log 1 2 ∧
      linkConditional Real.log standardizationTarget.covLaw (standardizationSurface 0)
          (standardizationSurface 1) =
        anchoredEstimand standardizationTarget.covLaw
          (linkContrast Real.log (standardizationSurface 0) (standardizationSurface 2))
          (linkContrast Real.log (standardizationSurface 1) (standardizationSurface 2)) ∧
      standardizationTarget.marginalEffect Real.log 0 1 =
        Real.log (∫ ω, densityRatio standardizationSource.μ standardizationSource.X
            standardizationTarget.μ standardizationTarget.X (standardizationSource.X ω) *
              standardizationSource.Y 1 ω ∂standardizationSource.μ) -
          Real.log (∫ ω, densityRatio standardizationSource.μ standardizationSource.X
            standardizationTarget.μ standardizationTarget.X (standardizationSource.X ω) *
              standardizationSource.Y 0 ω ∂standardizationSource.μ) := by
  set P := standardizationSource
  set Q := standardizationTarget
  have hX : Measurable P.X := measurable_id
  have hX' : Measurable Q.X := measurable_id
  have hYP : ∀ t, Integrable (P.Y t) P.μ := fun _ => Integrable.of_finite
  have hYQ : ∀ t, Integrable (Q.Y t) Q.μ := fun _ => Integrable.of_finite
  have hov := standardization_absolutelyContinuous
  have hsi := standardization_structurallyInvariant
  have hcm := standardizationSource_isCondMean
  have harm : ∀ t, Q.armMean t = ((t : ℕ) + 1 : ℝ) / 4 + 1 / 32 := fun t => by
    rw [← (integral_covLaw_eq_armMean_of_structurallyInvariant hX hX' (hYP t) (hYQ t) (hcm t)
      (hsi t) hov).2, standardizationTarget_covLaw, integral_standardizationSurface]
  have h0 : Q.armMean 0 = 9 / 32 := by rw [harm]; norm_num
  have h1 : Q.armMean 1 = 17 / 32 := by rw [harm]; norm_num
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX'
  have hmarg := marginalEffect_eq_linkMarginal_of_structurallyInvariant Real.log hX hX hX'
    (hYP 0) (hYP 1) (hYQ 0) (hYQ 1) (hcm 0) (hcm 1) (hsi 0) (hsi 1) hov hov
  refine ⟨h0, h1, ?_, hmarg,
    UnanchoredSetting.marginalEffect_target_eq
      ⟨P, P, Q, 0, 1⟩ Real.log hX hX hX' (hYP 0) (hYP 1) (hYQ 0) (hYQ 1) (hcm 0) (hcm 1)
      (hsi 0) (hsi 1) hov hov,
    marginalEffect_eq_sub_linkPosition Real.log hX hX' (hYP 0) (hYQ 0) (hcm 0) (hsi 0) hov,
    marginalEffect_anchored_of_structurallyInvariant Real.log hX hX' (hYP 0) (hYP 2) (hYQ 0)
      (hYQ 2) (hcm 0) (hcm 2) (hsi 0) (hsi 2) hov,
    linkConditional_anchored_of_relativeConstancy Real.measurable_log hX hX'
      (relativeConstancy_of_structurallyInvariant (hsi 0) (hsi 2)) hov (hcm 0) (hcm 2)
      (standardizationTarget_isCondMean 0) (standardizationTarget_isCondMean 2)
      Integrable.of_finite Integrable.of_finite,
    (marginalEffect_eq_densityRatio_weighting Real.log hX hX' hov (hYP 0) (hYP 1) (hYQ 0)
      (hYQ 1) (hcm 0) (hcm 1) (hsi 0) (hsi 1) Integrable.of_finite Integrable.of_finite).2⟩
  rw [Population.marginalEffect, h0, h1, ← Real.log_div (by norm_num) (by norm_num)]
  norm_num

/-- **An instance of the weighting and transfer lemmas.** In the two populations on a binary
covariate: the source surface of arm `0` is a conditional mean function in the target; the
standardized surface and the density ratio weighted source outcome and surface all equal the
target mean `9/32`; and the marginal estimand under the target covariate law is the difference of
the logarithms of the target means of the surfaces over the target sample space. -/
theorem standardization_weighting_example :
    standardizationTarget.IsCondMean 0 (standardizationSurface 0) ∧
      ∫ x, standardizationSurface 0 x ∂standardizationTarget.covLaw = 9 / 32 ∧
      ∫ ω, densityRatio standardizationSource.μ standardizationSource.X standardizationTarget.μ
          standardizationTarget.X (standardizationSource.X ω) *
            standardizationSurface 0 (standardizationSource.X ω) ∂standardizationSource.μ =
        9 / 32 ∧
      ∫ ω, densityRatio standardizationSource.μ standardizationSource.X standardizationTarget.μ
          standardizationTarget.X (standardizationSource.X ω) *
            standardizationSource.Y 0 ω ∂standardizationSource.μ = 9 / 32 ∧
      standardizationTarget.armMean 0 =
        ∫ ω, densityRatio standardizationSource.μ standardizationSource.X standardizationTarget.μ
          standardizationTarget.X (standardizationSource.X ω) *
            standardizationSource.Y 0 ω ∂standardizationSource.μ ∧
      linkMarginal Real.log standardizationTarget.covLaw (standardizationSurface 0)
          (standardizationSurface 1) =
        Real.log (∫ ω, standardizationSurface 1 (standardizationTarget.X ω)
            ∂standardizationTarget.μ) -
          Real.log (∫ ω, standardizationSurface 0 (standardizationTarget.X ω)
            ∂standardizationTarget.μ) := by
  set P := standardizationSource
  set Q := standardizationTarget
  have hX : Measurable P.X := measurable_id
  have hX' : Measurable Q.X := measurable_id
  have hov := standardization_absolutelyContinuous
  have hcm := standardizationSource_isCondMean 0
  have hsi := standardization_structurallyInvariant 0
  have hw := integral_covLaw_eq_integral_densityRatio_mul hX hov Integrable.of_finite hcm
    Integrable.of_finite
  have hstd : ∫ x, standardizationSurface 0 x ∂Q.covLaw = 9 / 32 := by
    rw [standardizationTarget_covLaw, integral_standardizationSurface]; norm_num
  have harm := armMean_eq_integral_densityRatio_mul hX hX' hov Integrable.of_finite
    Integrable.of_finite hcm hsi Integrable.of_finite
  refine ⟨hcm.of_structurallyInvariant hX hX' hsi hov, hstd, hw.2.1 ▸ hstd, hw.2.2 ▸ hstd,
    harm.2, linkMarginal_covLaw Real.log hX' (measurable_of_finite _) (measurable_of_finite _)⟩

/-! ### A trial with a trivial covariate -/

/-- A trial on `Bool` with the two arms equally likely (`A = id`), the trivial covariate, and
potential outcomes `Y(true) = 1`, `Y(false) = 0`. -/
noncomputable def standardizationTrial : Trial Bool Unit Bool :=
  ⟨⟨halfLaw, fun _ => (), fun t _ => if t then 1 else 0⟩, id⟩

/-- The observed regression of `standardizationTrial`, `m(t) = 1{t}`. -/
noncomputable def standardizationTrialRegression (t : Bool) (_ : Unit) : ℝ := if t then 1 else 0

/-- **An instance of the surface from the observed trial regression.** In
`standardizationTrial` the observed regression is a version of `E[Y | X, A]`, the propensity
score is `1/2`, both arms are mean ignorable and positive, so `m(t) = 1{t}` is a correct outcome
model of each arm; with the trial population as its own target the effect of `true` against
`false` on the identity scale is `1`. -/
theorem standardization_trial_example :
    (∀ t, standardizationTrial.toPopulation.IsCondMean t (standardizationTrialRegression t)) ∧
      standardizationTrial.toPopulation.marginalEffect id false true = 1 := by
  set T := standardizationTrial
  have hX : Measurable T.X := measurable_const
  have hA : Measurable T.A := measurable_id
  have hμ : IsProbabilityMeasure T.μ := by simp only [T, standardizationTrial]; infer_instance
  have hYi : ∀ t, Integrable (T.Y t) T.μ := fun _ => Integrable.of_finite
  have hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome standardizationTrialRegression := by
    refine ⟨fun _ => measurable_of_finite _, ?_⟩
    have hm : Measurable[MeasurableSpace.comap (fun ω => (T.X ω, T.A ω)) inferInstance]
        T.obsOutcome :=
      (measurable_of_finite fun q : Unit × Bool => standardizationTrialRegression q.2 q.1).comp
        (comap_measurable _)
    rw [condExp_of_stronglyMeasurable (hX.prodMk hA).comap_le hm.stronglyMeasurable
      Integrable.of_finite]
    exact Filter.Eventually.of_forall fun ω => rfl
  have hps : IsPropensityScore T.μ T.A T.X fun _ => 1 / 2 := by
    refine ⟨measurable_const, ?_⟩
    have : MeasurableSpace.comap T.X inferInstance = ⊥ := MeasurableSpace.comap_const _
    rw [this, condExp_bot]
    refine Filter.Eventually.of_forall fun _ => ?_
    simp only [T, standardizationTrial]
    rw [integral_halfLaw]
    simp [respInd]
  have hconst : ∀ t, T.Y t = fun _ => if t then (1 : ℝ) else 0 := fun _ => rfl
  have hmi : ∀ t, MeanIgnorable T.μ T.A T.X T.Y t := fun t => by
    rw [MeanIgnorable, hconst t, condExp_const (hX.prodMk hA).comap_le, condExp_const hX.comap_le]
  have hpos : ∀ t, ∀ᵐ ω ∂T.μ, 0 < armProb (fun _ => (1 : ℝ) / 2) t (T.X ω) := fun t =>
    Filter.Eventually.of_forall fun _ => by cases t <;> norm_num [armProb]
  have hcm : ∀ t, T.toPopulation.IsCondMean t (standardizationTrialRegression t) := fun t =>
    T.isCondMean_of_isOutcomeRegression hX hA hYi hreg hps t (hmi t) (hpos t)
  have hsi : ∀ t, StructurallyInvariant T.μ T.X (T.Y t) T.toPopulation.μ T.toPopulation.X
      (T.toPopulation.Y t) := fun t =>
    ⟨_, (Population.isCommonRegression_iff t _).2 ⟨hcm t, hcm t⟩⟩
  refine ⟨hcm, ?_⟩
  rw [T.marginalEffect_eq_of_isOutcomeRegression (Q' := T.toPopulation) id hX hA hX hYi hYi
    hreg hps hmi hpos hsi Measure.AbsolutelyContinuous.rfl]
  have : IsProbabilityMeasure T.toPopulation.covLaw := T.toPopulation.isProbabilityMeasure_covLaw hX
  simp [linkMarginal, standardizationTrialRegression]

end PopulationAdjustment

end CausalInference
