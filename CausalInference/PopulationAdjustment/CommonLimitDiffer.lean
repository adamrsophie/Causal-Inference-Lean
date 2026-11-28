/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitExamples

/-!
# Weighting and standardization with different limits

When the arm regression is not linear in the matched features, the weighted estimator and the
standardized estimator can converge to different numbers. This file gives a concrete model with
both limits computed.

The trial and the target are those of `CommonLimitExamples`: a binary covariate `x`, equally likely
in the trial and `true` with probability `1/4` in the target, and `Y(true) = 1 + 2 · 1[x]`. The
standardized estimator fits the correct regression in the interaction design of `1[x]` and
converges to the target mean `E_Q[Y(true)] = 3/2` (`commonLimitExample_armMean`). The weighted
estimator matches no feature: the covariate is an effect modifier left out of the matched
features, so the regression `1 + 2 · 1[x]` is not affine in them. Its weights are uniform and it
converges to the trial mean `E[Y(true)] = 2`. The difference of the two estimators converges in
probability to `-1/2`, not to `0`.

The weighted limit is computed from the consistency theorem `sampleBalancedArmMean_isConsistent`
applied to the coarsened records `((), A, Y)`, whose regression on the arm alone is the trial arm
mean: the estimator sees only the matched features, so its limit is set by the regression of the
outcome on the matched features and the arm.

## Main definitions

* `commonLimitDifferFeature`: the empty feature vector.
* `commonLimitDifferRecord`, `commonLimitDifferSample`: the coarsened records.

## Main results

* `commonLimitDiffer_condExp`: the regression of the outcome on the arm alone.
* `commonLimitDiffer_weighted`: the weighted estimator converges in probability to `2`.
* `commonLimitDiffer`: the two estimators converge in probability to `2` and `3/2`, and their
  difference to `-1/2`.

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

/-- The empty feature vector: the weighted estimator matches no feature. -/
def commonLimitDifferFeature {𝒳 : Type*} (_ : 𝒳) : Fin 0 → ℝ := fun _ => 0

/-- The coarsened record `((), A, Y)` of a unit of the trial. -/
noncomputable def commonLimitDifferRecord (ω : Bool × Bool) : Unit × Bool × ℝ :=
  ((), ω.1, lsExampleOutcome ω.1 ω.2)

/-- The coarsened records of the sample. -/
noncomputable def commonLimitDifferSample (i : ℕ) (ω : ℕ → Bool × Bool) : Unit × Bool × ℝ :=
  commonLimitDifferRecord (ω i)

/-- The regression of the outcome on the arm alone: the trial arm mean. -/
noncomputable def commonLimitDifferMean (a : Bool) (_ : Unit) : ℝ :=
  (lsExampleOutcome a false + lsExampleOutcome a true) / 2

theorem commonLimitDiffer_real_singleton (ω : Bool × Bool) : lsExampleTrial.μ.real {ω} = 1 / 4 := by
  rcases ω with ⟨a, x⟩
  change (halfLaw.prod halfLaw).real {(a, x)} = _
  rw [← Set.singleton_prod_singleton, measureReal_def, Measure.prod_prod]
  cases a <;> cases x <;> simp [halfLaw, stratumLaw] <;> norm_num

theorem commonLimitDiffer_integral (F : Bool × Bool → ℝ) :
    ∫ ω, F ω ∂lsExampleTrial.μ =
      (F (false, false) + F (false, true) + F (true, false) + F (true, true)) / 4 := by
  rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  simp [commonLimitDiffer_real_singleton]
  ring

/-- **The regression of the outcome on the arm alone** in the trial is the arm mean
`(f(a, false) + f(a, true)) / 2` of the outcome `f(a, x)`. -/
theorem commonLimitDiffer_condExp (F : Bool × Bool → ℝ) :
    lsExampleTrial.μ[F | MeasurableSpace.comap (fun ω : Bool × Bool => ((), ω.1)) inferInstance]
      =ᵐ[lsExampleTrial.μ] fun ω => (F (ω.1, false) + F (ω.1, true)) / 2 := by
  have hm : MeasurableSpace.comap (fun ω : Bool × Bool => ((), ω.1))
      (inferInstance : MeasurableSpace (Unit × Bool)) ≤ (inferInstance : MeasurableSpace
        (Bool × Bool)) := (measurable_of_finite (fun ω : Bool × Bool => ((), ω.1))).comap_le
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm Integrable.of_finite
    (fun _ _ _ => Integrable.of_finite.integrableOn) (fun s hs _ => ?_) ?_).symm
  · obtain ⟨S, hSm, rfl⟩ := hs
    have hS : MeasurableSet ((fun ω : Bool × Bool => ((), ω.1)) ⁻¹' S) :=
      (measurable_of_finite _) hSm
    rw [← integral_indicator hS, ← integral_indicator hS, commonLimitDiffer_integral,
      commonLimitDiffer_integral]
    by_cases h1 : ((), true) ∈ S <;> by_cases h2 : ((), false) ∈ S
    all_goals simp [Set.indicator, h1, h2]
    ring
  · exact ((measurable_of_finite fun c : Unit × Bool =>
      (F (c.2, false) + F (c.2, true)) / 2).comp (comap_measurable _)).aestronglyMeasurable

theorem commonLimitDiffer_map (i : ℕ) :
    lsExampleSampleLaw.map (commonLimitDifferSample i) =
      lsExampleTrial.μ.map commonLimitDifferRecord := by
  have : commonLimitDifferSample i = commonLimitDifferRecord ∘ fun x : ℕ → Bool × Bool => x i :=
    rfl
  rw [this, ← Measure.map_map (g := commonLimitDifferRecord) (measurable_of_finite _)
    (measurable_pi_apply i), lsExampleSampleLaw, Measure.infinitePi_map_eval]

theorem isIIDSample_commonLimitDifferSample :
    IsIIDSample commonLimitDifferSample lsExampleSampleLaw where
  indep := iIndepFun_infinitePi (P := fun _ => lsExampleTrial.μ) fun _ => measurable_of_finite _
  ident i := ⟨((measurable_of_finite commonLimitDifferRecord).comp
      (measurable_pi_apply i)).aemeasurable,
    ((measurable_of_finite commonLimitDifferRecord).comp (measurable_pi_apply 0)).aemeasurable,
    (commonLimitDiffer_map i).trans (commonLimitDiffer_map 0).symm⟩

theorem measurable_commonLimitDifferSample (i : ℕ) : Measurable (commonLimitDifferSample i) :=
  (measurable_of_finite commonLimitDifferRecord).comp (measurable_pi_apply i)

/-- **The weighted estimator without matched features converges to the trial mean.** -/
theorem commonLimitDiffer_weighted :
    IsConsistent (sampleBalancedArmMean commonLimitDifferFeature 0 lsExampleSample true) 2
      lsExampleSampleLaw := by
  have heq : sampleBalancedArmMean commonLimitDifferFeature 0 lsExampleSample true =
      sampleBalancedArmMean commonLimitDifferFeature 0 commonLimitDifferSample true := rfl
  rw [heq]
  set R := lsExampleSampleLaw.map (commonLimitDifferSample 0) with hR
  have hR' : R = lsExampleTrial.μ.map commonLimitDifferRecord := commonLimitDiffer_map 0
  have hrec : AEMeasurable commonLimitDifferRecord lsExampleTrial.μ :=
    (measurable_of_finite _).aemeasurable
  have hint : ∀ g : Unit × Bool × ℝ → ℝ, Measurable g → Integrable g R := fun g hg => by
    rw [hR', integrable_map_measure hg.aestronglyMeasurable hrec]
    exact Integrable.of_finite
  -- independence of the (constant) feature and the arm
  have hind : IndepFun (fun z : Unit × Bool × ℝ => z.1) (fun z => z.2.1) R := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s u _ _
    by_cases hs : () ∈ s
    · have h1 : (fun z : Unit × Bool × ℝ => z.1) ⁻¹' s = Set.univ :=
        Set.eq_univ_of_forall fun z => by simpa [Subsingleton.elim z.1 ()] using hs
      simp [h1]
    · have h1 : (fun z : Unit × Bool × ℝ => z.1) ⁻¹' s = ∅ :=
        Set.eq_empty_of_forall_notMem fun z hz => hs (by simpa [Subsingleton.elim z.1 ()] using hz)
      simp [h1]
  have hq : 0 < R.real {z : Unit × Bool × ℝ | z.2.1 = true} := by
    have hset : {z : Unit × Bool × ℝ | z.2.1 = true} = (fun z => z.2.1) ⁻¹' {true} := rfl
    rw [hR', hset, map_measureReal_apply (measurable_of_finite _)
      (measurable_snd.fst (measurableSet_singleton true))]
    exact lsExampleTrial_isRandomizedTwoArm.prob_arm_pos true
  have hreg : R[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : Unit × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[R]
        fun z => commonLimitDifferMean z.2.1 z.1 := by
    rw [hR']
    exact condExp_map_ae_eq (measurable_of_finite _) (measurable_fst.prodMk measurable_snd.fst)
      measurable_snd.snd Integrable.of_finite (h := fun c => commonLimitDifferMean c.2 c.1)
      (measurable_of_finite _) (commonLimitDiffer_condExp fun ω => lsExampleOutcome ω.1 ω.2)
  have hgm : Measurable fun z : Unit × Bool × ℝ => (z.2.2 - commonLimitDifferMean z.2.1 z.1) ^ 2 :=
    (measurable_snd.snd.sub ((measurable_of_finite fun c : Unit × Bool =>
      commonLimitDifferMean c.2 c.1).comp (measurable_fst.prodMk measurable_snd.fst))).pow_const 2
  have hle : (fun z : Unit × Bool × ℝ => (z.2.2 - commonLimitDifferMean z.2.1 z.1) ^ 2)
      ≤ᵐ[R] fun _ => 1 := by
    rw [hR', Filter.EventuallyLE, ae_map_iff hrec (measurableSet_le hgm measurable_const)]
    refine ae_of_all _ fun ω => ?_
    rcases ω with ⟨a, x⟩
    cases a <;> cases x <;>
      norm_num [commonLimitDifferRecord, commonLimitDifferMean, lsExampleOutcome]
  have hvar : R[fun z => (z.2.2 - commonLimitDifferMean z.2.1 z.1) ^ 2 | MeasurableSpace.comap
      (fun z : Unit × Bool × ℝ => (z.1, z.2.1)) inferInstance] ≤ᵐ[R] fun _ => 1 := by
    have h := condExp_mono (m := MeasurableSpace.comap
      (fun z : Unit × Bool × ℝ => (z.1, z.2.1)) inferInstance) (hint _ hgm)
      (integrable_const (1 : ℝ)) hle
    rwa [condExp_const ((measurable_fst.prodMk measurable_snd.fst).comap_le)] at h
  have h := sampleBalancedArmMean_isConsistent isIIDSample_commonLimitDifferSample
    measurable_commonLimitDifferSample (φ := commonLimitDifferFeature) (measurable_of_finite _)
    (t := 0) (B := 0) (fun _ => by simp) one_pos
    (fun v hv => absurd hv (by rw [Subsingleton.elim v 0, norm_zero]; norm_num)) hind true hq
    (fun _ => measurable_of_finite _) (hint _ hgm) hreg hvar (a0 := 2) (b := 0)
    (fun _ => by norm_num [commonLimitDifferMean, lsExampleOutcome])
  simpa using h

/-- **Weighting and standardization with different limits.** In the model of
`CommonLimitExamples`, the regression `Y(true) = 1 + 2 · 1[x]` is not affine in the matched
features (none), the weighted estimator converges in probability to the trial mean `2`, the
standardized estimator of the correct interaction model converges in probability to the target
mean `3/2`, and their difference converges in probability to `-1/2`, not to `0`. -/
theorem commonLimitDiffer :
    (¬ ∃ (a0 : ℝ) (b : Fin 0 → ℝ), ∀ x, lsExampleOutcome true x =
      a0 + b ⬝ᵥ commonLimitDifferFeature x) ∧
    IsConsistent (sampleBalancedArmMean commonLimitDifferFeature 0 lsExampleSample true) 2
      lsExampleSampleLaw ∧
    TendstoInMeasure lsExampleSampleLaw (fun n ω => ∫ x,
      featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
        leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
          recordResponse lsExampleSample n ω ∂lsExampleTarget.covLaw) atTop (fun _ => 3 / 2) ∧
    TendstoInMeasure lsExampleSampleLaw (fun n ω => ∫ x,
      featureInteractionDesign commonLimitExampleFeature true x ⬝ᵥ
        leastSquaresFit (recordDesign (featureInteractionDesign commonLimitExampleFeature))
          recordResponse lsExampleSample n ω ∂lsExampleTarget.covLaw -
        sampleBalancedArmMean commonLimitDifferFeature 0 lsExampleSample true n ω) atTop
      (fun _ => -1 / 2) := by
  have hS := commonLimitExample_armMean.2.1
  have hW := commonLimitDiffer_weighted
  have hD := hS.sub hW
  simp only [Pi.sub_def] at hD
  refine ⟨?_, hW, hS, ?_⟩
  · rintro ⟨a0, b, h⟩
    have h1 := h false
    have h2 := h true
    simp [lsExampleOutcome, dotProduct] at h1 h2
    linarith
  · convert hD using 2
    norm_num

end PopulationAdjustment

end CausalInference
