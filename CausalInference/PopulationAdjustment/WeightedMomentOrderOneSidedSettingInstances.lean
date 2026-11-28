/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderOneSidedComparisonsInstances
public import CausalInference.PopulationAdjustment.WeightedMomentOrderOneSidedSetting

/-!
# Instances of the setting theorems under one sided moments

An anchored and an unanchored setting built on the coin trial over the standard exponential
feature law (`X` standard exponential, a fair coin assignment, `Y(true) = 1 + 2X`,
`Y(false) = X`) with the target `oneSidedInstTarget`, in which the covariate is uniform on
`[0, 1]`. Both settings satisfy their identification assumptions on the identity scale
(`oneSidedInstAnchoredSetting_identificationAssumptions`,
`oneSidedInstUnanchoredSetting_identificationAssumptions`).

At the target mean `t = 1/2` the population dual minimizer is `β* = -1` and no norm moment of an
order `κ > 2 |β*|` is finite (`not_exists_order_momentOrderExpLaw_one_half`), so the theorems
under one norm moment do not apply; the one sided conditions hold (`oneSidedInst_weighting`).
With the reported moments `tₙ = 1/2 + 1/(n + 1)` every hypothesis of the five setting theorems
under one sided moments is discharged, and each estimator converges in probability to
`E_Q[Y(false)] - E_Q[Y(true)] = 1/2 - 2 = -3/2`, or to `E_Q[Y(true)] = 2` for the arm mean.

## Main definitions

* `oneSidedInstAnchoredSetting`: individual data trial the exponential coin trial of `a = true`
  against `c = false`, aggregate data trial the same trial with `b = c = false`.
* `oneSidedInstUnanchoredSetting`: both sources the exponential coin trial, `a = true`,
  `b = false`.

## Main results

* `oneSidedInst_trial_armMean`, `oneSidedInst_trial_unanchored`,
  `oneSidedInst_trial_anchored_identity`.
* `oneSidedInst_setting_anchored`, `oneSidedInst_setting_unanchored`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### The trial hypotheses of the exponential coin trial -/

section Hypotheses

theorem integrable_oneSidedInstTarget_covLaw {h : (Fin 1 → ℝ) → ℝ} (hh : Continuous h) :
    Integrable h oneSidedInstTarget.covLaw := by
  change Integrable h (oneSidedInstTarget.μ.map featureLineVec)
  rw [integrable_map_measure hh.measurable.aestronglyMeasurable
    measurable_featureLineVec.aemeasurable]
  exact integrable_oneSidedInstTarget (hh.comp (continuous_pi fun _ => continuous_id))

theorem continuous_sharpInstOutcome (a : Bool) : Continuous (sharpInstOutcome a) := by
  cases a
  · exact continuous_apply 0
  · exact continuous_const.add (continuous_const.mul (continuous_apply 0))

theorem oneSidedInst_affine_false (x : Fin 1 → ℝ) :
    sharpInstOutcome false x = 0 + featureLineVec 1 ⬝ᵥ x := by
  simp [sharpInstOutcome, featureLineVec, dotProduct]

theorem oneSidedInst_contrast_zero :
    ∫ x, linkContrast id (sharpInstOutcome false) (sharpInstOutcome false) x
      ∂oneSidedInstTarget.covLaw = 0 := by
  simp [linkContrast]

end Hypotheses

/-! ### The settings -/

section Settings

/-- The anchored setting of the instances: the individual data trial is the exponential coin
trial of `a = true` against `c = false`, the aggregate data trial is the same trial with
`b = c = false`, and the target is `oneSidedInstTarget`. -/
noncomputable def oneSidedInstAnchoredSetting :
    AnchoredSetting ((Fin 1 → ℝ) × Bool) ((Fin 1 → ℝ) × Bool) ℝ (Fin 1 → ℝ) Bool :=
  ⟨sharpInstTrial momentOrderExpLaw sharpInstOutcome,
    sharpInstTrial momentOrderExpLaw sharpInstOutcome, oneSidedInstTarget, true, false, false⟩

instance oneSidedInstAnchoredSetting_ipd_isFiniteMeasure :
    IsFiniteMeasure oneSidedInstAnchoredSetting.ipdTrial.μ := by
  unfold oneSidedInstAnchoredSetting; infer_instance

instance oneSidedInstAnchoredSetting_agd_isFiniteMeasure :
    IsFiniteMeasure oneSidedInstAnchoredSetting.agdTrial.μ := by
  unfold oneSidedInstAnchoredSetting; infer_instance

instance oneSidedInstAnchoredSetting_target_isProbabilityMeasure :
    IsProbabilityMeasure oneSidedInstAnchoredSetting.target.μ := by
  unfold oneSidedInstAnchoredSetting; infer_instance

/-- **The anchored setting of the instances satisfies the identification assumptions** on the
identity scale, with the conditional means `sharpInstOutcome` in both trials and the target. -/
theorem oneSidedInstAnchoredSetting_identificationAssumptions :
    oneSidedInstAnchoredSetting.IdentificationAssumptions id Set.univ sharpInstOutcome
      sharpInstOutcome sharpInstOutcome where
  measurable_ipd := measurable_fst
  measurable_agd := measurable_fst
  measurable_target := measurable_featureLineVec
  integrable_ipd_a := (unboundedInst_memLp true).integrable one_le_two
  integrable_ipd_c := (unboundedInst_memLp false).integrable one_le_two
  integrable_agd_b := (unboundedInst_memLp false).integrable one_le_two
  integrable_agd_c := (unboundedInst_memLp false).integrable one_le_two
  integrable_target t _ := oneSidedInstTarget_integrable t
  isCondMean_ipd_a := (sharpInstTrial_hypotheses measurable_sharpInstOutcome true
    (integrable_sharpInstOutcome_momentOrderExpLaw true)).2.2.2.2.2.2.1
  isCondMean_ipd_c := (sharpInstTrial_hypotheses measurable_sharpInstOutcome false
    (integrable_sharpInstOutcome_momentOrderExpLaw false)).2.2.2.2.2.2.1
  isCondMean_agd_b := (sharpInstTrial_hypotheses measurable_sharpInstOutcome false
    (integrable_sharpInstOutcome_momentOrderExpLaw false)).2.2.2.2.2.2.1
  isCondMean_agd_c := (sharpInstTrial_hypotheses measurable_sharpInstOutcome false
    (integrable_sharpInstOutcome_momentOrderExpLaw false)).2.2.2.2.2.2.1
  isCondMean_target t _ := oneSidedInstTarget_isCondMean t
  mem_ipd := Eventually.of_forall fun _ => ⟨trivial, trivial⟩
  mem_agd := Eventually.of_forall fun _ => ⟨trivial, trivial⟩
  mem_target := Eventually.of_forall fun _ => ⟨trivial, trivial, trivial⟩
  relativeConstancy_ipd := relativeConstancy_of_structurallyInvariant
    (oneSidedInst_structurallyInvariant true) (oneSidedInst_structurallyInvariant false)
  relativeConstancy_agd := relativeConstancy_of_structurallyInvariant
    (oneSidedInst_structurallyInvariant false) (oneSidedInst_structurallyInvariant false)
  overlap_ipd := oneSidedInstTarget_absolutelyContinuous
  overlap_agd := oneSidedInstTarget_absolutelyContinuous
  integrable_ipd_contrast := integrable_oneSidedInstTarget_covLaw
    ((continuous_sharpInstOutcome false).sub (continuous_sharpInstOutcome true))
  integrable_agd_contrast := integrable_oneSidedInstTarget_covLaw
    ((continuous_sharpInstOutcome false).sub (continuous_sharpInstOutcome false))

/-- The unanchored setting of the instances: both sources are the exponential coin trial, with
`a = true` and `b = false`, and the target is `oneSidedInstTarget`. -/
noncomputable def oneSidedInstUnanchoredSetting :
    UnanchoredSetting ((Fin 1 → ℝ) × Bool) ((Fin 1 → ℝ) × Bool) ℝ (Fin 1 → ℝ) Bool :=
  ⟨(sharpInstTrial momentOrderExpLaw sharpInstOutcome).toPopulation,
    (sharpInstTrial momentOrderExpLaw sharpInstOutcome).toPopulation, oneSidedInstTarget, true,
    false⟩

instance oneSidedInstUnanchoredSetting_sourceA_isFiniteMeasure :
    IsFiniteMeasure oneSidedInstUnanchoredSetting.sourceA.μ := by
  unfold oneSidedInstUnanchoredSetting
  change IsFiniteMeasure (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ; infer_instance

instance oneSidedInstUnanchoredSetting_sourceB_isFiniteMeasure :
    IsFiniteMeasure oneSidedInstUnanchoredSetting.sourceB.μ := by
  unfold oneSidedInstUnanchoredSetting
  change IsFiniteMeasure (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ; infer_instance

instance oneSidedInstUnanchoredSetting_target_isProbabilityMeasure :
    IsProbabilityMeasure oneSidedInstUnanchoredSetting.target.μ := by
  unfold oneSidedInstUnanchoredSetting; infer_instance

/-- The density ratio weighted outcome of an arm is integrable in the exponential coin trial:
the outcome is a continuous function of the covariate, integrable under the target law. -/
theorem oneSidedInst_integrable_weighted (a : Bool) :
    Integrable (fun ω => densityRatio (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).X oneSidedInstTarget.μ
      oneSidedInstTarget.X ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).X ω) *
        (sharpInstTrial momentOrderExpLaw sharpInstOutcome).Y a ω)
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ :=
  (integrable_densityRatio_mul_iff (g := sharpInstOutcome a) measurable_fst
    oneSidedInstTarget_absolutelyContinuous (measurable_sharpInstOutcome a)).2
    (integrable_oneSidedInstTarget_covLaw (continuous_sharpInstOutcome a))

/-- **The unanchored setting of the instances satisfies the identification assumptions** on the
identity scale, with `m_a = sharpInstOutcome true` and `m_b = sharpInstOutcome false`. -/
theorem oneSidedInstUnanchoredSetting_identificationAssumptions :
    oneSidedInstUnanchoredSetting.IdentificationAssumptions Set.univ (sharpInstOutcome true)
      (sharpInstOutcome false) where
  measurable_sourceA := measurable_fst
  measurable_sourceB := measurable_fst
  measurable_target := measurable_featureLineVec
  integrable_sourceA := (unboundedInst_memLp true).integrable one_le_two
  integrable_sourceB := (unboundedInst_memLp false).integrable one_le_two
  integrable_target_a := oneSidedInstTarget_integrable true
  integrable_target_b := oneSidedInstTarget_integrable false
  mem_a := trivial
  mem_b := trivial
  isCondMean_a := (sharpInstTrial_hypotheses measurable_sharpInstOutcome true
    (integrable_sharpInstOutcome_momentOrderExpLaw true)).2.2.2.2.2.2.1
  isCondMean_b := (sharpInstTrial_hypotheses measurable_sharpInstOutcome false
    (integrable_sharpInstOutcome_momentOrderExpLaw false)).2.2.2.2.2.2.1
  structurallyInvariant_a := oneSidedInst_structurallyInvariant true
  structurallyInvariant_b := oneSidedInst_structurallyInvariant false
  overlap_a := oneSidedInstTarget_absolutelyContinuous
  overlap_b := oneSidedInstTarget_absolutelyContinuous
  integrable_weighted_a := oneSidedInst_integrable_weighted true
  integrable_weighted_b := oneSidedInst_integrable_weighted false

end Settings

/-! ### The trial level theorems -/

section TrialLevel

/-- **An instance of `sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn_oneSided`.**
The weighted arm mean of arm `true` of the exponential coin trial at the reported moments `tₙ`
converges in probability to the target mean `E_Q[Y(true)] = 2`. -/
theorem oneSidedInst_trial_armMean :
    IsConsistent (fun n ω => sampleBalancedArmMean id (oneSidedInstReported n)
      (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) 2
      (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses
    measurable_sharpInstOutcome true (integrable_sharpInstOutcome_momentOrderExpLaw true)
  have h := sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn_oneSided
    (W := fun _ => ()) (G := fun n _ => oneSidedInstReported n) (Q := oneSidedInstTarget)
    (s := true) hX hA hYo true hYa hrand
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_id hint hmin (by norm_num)
    hexp hε hdir measurable_const (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_oneSidedInstReported hq hm hres2 hvar sharpInstOutcome_true
    measurable_featureLineVec oneSidedInstTarget_featureIntegrable
    oneSidedInstTarget_featureMean (oneSidedInstTarget_integrable true)
    (oneSidedInstTarget_isCondMean true)
  rw [oneSidedInstTarget_armMean_true] at h
  exact h

/-- **An instance of `unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn_oneSided`.** In
the unanchored setting of the instances, with the target mean of `Y(false)` reported exactly,
the weighted comparison `m̂_b - μ̂_true` at the reported moments converges in probability to
`1/2 - 2 = -3/2`. -/
theorem oneSidedInst_trial_unanchored :
    IsConsistent (fun n ω => id (∫ x, sharpInstOutcome false x ∂oneSidedInstTarget.covLaw) -
      id (sampleBalancedArmMean id (oneSidedInstReported n)
        (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω)) (-3 / 2)
      (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses
    measurable_sharpInstOutcome true (integrable_sharpInstOutcome_momentOrderExpLaw true)
  have h := unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn_oneSided
    (W := fun _ => ()) (G := fun n _ => oneSidedInstReported n)
    (S := oneSidedInstUnanchoredSetting) (T := sharpInstTrial momentOrderExpLaw sharpInstOutcome)
    (g := id) (mB := fun _ _ => ∫ x, sharpInstOutcome false x ∂oneSidedInstTarget.covLaw)
    oneSidedInstUnanchoredSetting_identificationAssumptions hX hA hYo hYa hrand
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_id hint hmin (by norm_num)
    hexp hε hdir measurable_const (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_oneSidedInstReported hq hm hres2 hvar sharpInstOutcome_true
    oneSidedInstTarget_featureIntegrable oneSidedInstTarget_featureMean
    (tendstoInMeasure_const _) continuousAt_id continuousAt_id
  have he : oneSidedInstUnanchoredSetting.target.marginalEffect id
      oneSidedInstUnanchoredSetting.a oneSidedInstUnanchoredSetting.b = -3 / 2 :=
    oneSidedInstTarget_marginalEffect
  rw [he] at h
  exact h

/-- **An instance of `anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn_oneSided`.**
In the anchored setting of the instances, with the reported contrast `d̂_bc = 0`, the weighted
comparison `(μ̂_false - μ̂_true) - d̂_bc` at the reported moments converges in probability to
`-3/2`. -/
theorem oneSidedInst_trial_anchored_identity :
    IsConsistent (fun n ω => (sampleBalancedArmMean id (oneSidedInstReported n)
      (sharpInstSample momentOrderExpLaw sharpInstOutcome) false n ω - sampleBalancedArmMean id
        (oneSidedInstReported n) (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) -
          0) (-3 / 2) (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  obtain ⟨hX, hA, -, hYt, hrt, hqt, hmA, hrA, hvA⟩ := sharpInstTrial_hypotheses
    measurable_sharpInstOutcome true (integrable_sharpInstOutcome_momentOrderExpLaw true)
  obtain ⟨-, -, -, hYf, hrf, hqf, hmC, hrC, hvC⟩ := sharpInstTrial_hypotheses
    measurable_sharpInstOutcome false (integrable_sharpInstOutcome_momentOrderExpLaw false)
  have h := anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn_oneSided
    (W := fun _ => ()) (G := fun n _ => oneSidedInstReported n)
    (S := oneSidedInstAnchoredSetting) (T := sharpInstTrial momentOrderExpLaw sharpInstOutcome)
    (dBC := fun _ _ => 0) oneSidedInstAnchoredSetting_identificationAssumptions hX hA hYt hYf
    hrt hrf (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_id hint hmin (by norm_num)
    hexp hε hdir measurable_const (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_oneSidedInstReported hqt hqf hmA hmC hrA hrC hvA hvC sharpInstOutcome_true
    oneSidedInst_affine_false oneSidedInstTarget_featureIntegrable
    oneSidedInstTarget_featureMean
    (by change IsConsistent _ (∫ x, linkContrast id (sharpInstOutcome false)
          (sharpInstOutcome false) x ∂oneSidedInstTarget.covLaw) _
        rw [oneSidedInst_contrast_zero]; exact tendstoInMeasure_const 0)
  have he : oneSidedInstAnchoredSetting.target.marginalEffect id oneSidedInstAnchoredSetting.a
      oneSidedInstAnchoredSetting.b = -3 / 2 := oneSidedInstTarget_marginalEffect
  rw [he] at h
  exact h

end TrialLevel

/-! ### The theorems for the trials of the settings -/

section SettingLevel

/-- **An instance of `anchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided`.** In
the anchored setting of the instances, the anchored weighted estimate with the treatment labels
of the records, the entropy balancing weights at the reported moments `tₙ` and the reported
contrast `d̂_bc = 0` converges in probability to `E_Q[Y(false)] - E_Q[Y(true)] = -3/2`. -/
theorem oneSidedInst_setting_anchored :
    IsConsistent (fun n => anchoredWeightedEstimate id
        (fun ω => balancingWeights fun i : Fin n =>
          id (sharpInstSample momentOrderExpLaw sharpInstOutcome i ω).1 - oneSidedInstReported n)
        (fun ω i => (sharpInstSample momentOrderExpLaw sharpInstOutcome i ω).2.1)
        (fun ω i => (sharpInstSample momentOrderExpLaw sharpInstOutcome i ω).2.2) true false
        (fun _ => 0)) (-3 / 2) (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  obtain ⟨-, hA, -, hYt, hrt, hqt, -, hrA, hvA⟩ := sharpInstTrial_hypotheses
    measurable_sharpInstOutcome true (integrable_sharpInstOutcome_momentOrderExpLaw true)
  obtain ⟨-, -, -, hYf, hrf, hqf, -, hrC, hvC⟩ := sharpInstTrial_hypotheses
    measurable_sharpInstOutcome false (integrable_sharpInstOutcome_momentOrderExpLaw false)
  have h := anchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided (W := fun _ => ())
    (G := fun n _ => oneSidedInstReported n) (S := oneSidedInstAnchoredSetting)
    (dBC := fun _ _ => 0) (hS := oneSidedInstAnchoredSetting_identificationAssumptions)
    (hac := by simp [oneSidedInstAnchoredSetting]) (hA := hA) (hYa := hYt) (hYc := hYf)
    (hAac := ae_of_all _ fun ω => by
      change ω.2 = true ∨ ω.2 = false
      cases ω.2 <;> simp)
    (hra := hrt) (hrc := hrf) (hqa := hqt) (hqc := hqf)
    (hR := isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (hRm := measurable_sharpInstSample measurable_sharpInstOutcome)
    (hlaw := map_sharpInstSample measurable_sharpInstOutcome 0) (hφ := measurable_id)
    (hint := hint) (hmin := hmin) (hr := by norm_num) (hexp := hexp) (hε := hε) (hdir := hdir)
    (hW := measurable_const) (hWR := indepFun_const_left _ _) (hG := fun _ => measurable_const)
    (htm := tendstoInMeasure_oneSidedInstReported) (hrA := hrA) (hrC := hrC) (hvA := hvA)
    (hvC := hvC) (hafA := sharpInstOutcome_true) (hafC := oneSidedInst_affine_false)
    (hQφ := oneSidedInstTarget_featureIntegrable) (ht := oneSidedInstTarget_featureMean)
    (hd := by
      change IsConsistent _ (∫ x, linkContrast id (sharpInstOutcome false)
        (sharpInstOutcome false) x ∂oneSidedInstTarget.covLaw) _
      rw [oneSidedInst_contrast_zero]; exact tendstoInMeasure_const 0)
  have he : oneSidedInstAnchoredSetting.target.marginalEffect id oneSidedInstAnchoredSetting.a
      oneSidedInstAnchoredSetting.b = -3 / 2 := oneSidedInstTarget_marginalEffect
  rw [he] at h
  exact h

/-- **An instance of `unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided`.** In
the unanchored setting of the instances, with the exponential coin trial the trial of `a = true`
against `c = false` and the target mean of `Y(false)` reported exactly, `m̂_b - μ̂_true` with the
weighted mean of the records labeled `true` at the reported moments converges in probability to
`-3/2`. -/
theorem oneSidedInst_setting_unanchored :
    IsConsistent (fun n ω => id (∫ x, sharpInstOutcome false x ∂oneSidedInstTarget.covLaw) -
      id (weightedArmMean (balancingWeights fun i : Fin n =>
        id (sharpInstSample momentOrderExpLaw sharpInstOutcome i ω).1 - oneSidedInstReported n)
          (fun i => (sharpInstSample momentOrderExpLaw sharpInstOutcome i ω).2.1)
          (fun i => (sharpInstSample momentOrderExpLaw sharpInstOutcome i ω).2.2) true))
      (-3 / 2) (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  obtain ⟨-, hA, -, hYt, hrt, hqt, -, hres2, hvar⟩ := sharpInstTrial_hypotheses
    measurable_sharpInstOutcome true (integrable_sharpInstOutcome_momentOrderExpLaw true)
  have h := unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn_oneSided
    (W := fun _ => ()) (G := fun n _ => oneSidedInstReported n)
    (S := oneSidedInstUnanchoredSetting) (T := sharpInstTrial momentOrderExpLaw sharpInstOutcome)
    (c := false) (g := id)
    (mB := fun _ _ => ∫ x, sharpInstOutcome false x ∂oneSidedInstTarget.covLaw)
    (hS := oneSidedInstUnanchoredSetting_identificationAssumptions) (hsrc := rfl)
    (hac := by simp [oneSidedInstUnanchoredSetting]) (hA := hA) (hYa := hYt)
    (hYc := (measurable_sharpInstOutcome false).comp measurable_fst)
    (hAac := ae_of_all _ fun ω => by
      change ω.2 = true ∨ ω.2 = false
      cases ω.2 <;> simp)
    (hra := hrt) (hqa := hqt)
    (hR := isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (hRm := measurable_sharpInstSample measurable_sharpInstOutcome)
    (hlaw := map_sharpInstSample measurable_sharpInstOutcome 0) (hφ := measurable_id)
    (hint := hint) (hmin := hmin) (hr := by norm_num) (hexp := hexp) (hε := hε) (hdir := hdir)
    (hW := measurable_const) (hWR := indepFun_const_left _ _) (hG := fun _ => measurable_const)
    (htm := tendstoInMeasure_oneSidedInstReported) (hres2 := hres2) (hvar := hvar)
    (haff := sharpInstOutcome_true) (hQφ := oneSidedInstTarget_featureIntegrable)
    (ht := oneSidedInstTarget_featureMean) (hmB := tendstoInMeasure_const _)
    (hga := continuousAt_id) (hgb := continuousAt_id)
  have he : oneSidedInstUnanchoredSetting.target.marginalEffect id
      oneSidedInstUnanchoredSetting.a oneSidedInstUnanchoredSetting.b = -3 / 2 :=
    oneSidedInstTarget_marginalEffect
  rw [he] at h
  exact h

end SettingLevel

end PopulationAdjustment

end CausalInference
