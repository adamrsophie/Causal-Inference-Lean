/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderCommonLimitInstances

/-!
# Instances of the setting theorems under one exponential moment

An anchored and an unanchored setting built on the two arm example `lsExampleTrial` (a fair coin
assignment, a fair binary covariate `x`, the feature `φ(x) = 1[x]` and the outcomes
`Y(t) = 1[x] + 1[t](1 + 1[x])`) with the target `lsExampleTarget`, in which `x` is `true` with
probability `1/4`. Both settings satisfy their identification assumptions on the identity scale
(`lsInstAnchoredSetting_identificationAssumptions`,
`lsInstUnanchoredSetting_identificationAssumptions`). With the reported moments
`tₙ = 1/4 + 1/(n + 1)` every hypothesis of the five finite order theorems of the setting is
discharged, and each estimator converges in probability to the target effect
`E_Q[Y(false)] - E_Q[Y(true)] = 1/4 - 3/2 = -5/4`, or to `E_Q[Y(true)] = 3/2` for the arm mean.

## Main definitions

* `lsInstAnchoredSetting`: individual data trial `lsExampleTrial` of `a = true` against
  `c = false`, aggregate data trial `lsExampleTrial` with `b = c = false`.
* `lsInstUnanchoredSetting`: both sources `lsExampleTrial`, `a = true`, `b = false`.

## Main results

* `lsInst_trial_armMean`, `lsInst_trial_unanchored`, `lsInst_trial_anchored_identity`.
* `lsInst_setting_anchored`, `lsInst_setting_unanchored`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### Conditional means and residuals of the example -/

/-- In the trial of the example `lsExampleOutcome t` is a conditional mean function of `Y(t)`. -/
theorem lsInst_isCondMean_trial (t : Bool) :
    lsExampleTrial.IsCondMean t (lsExampleOutcome t) := by
  have hm : Measurable[MeasurableSpace.comap lsExampleTrial.X inferInstance]
      (lsExampleTrial.Y t) :=
    (measurable_of_finite (lsExampleOutcome t)).comp (comap_measurable _)
  exact ⟨measurable_of_finite _, EventuallyEq.of_eq (condExp_of_stronglyMeasurable
    lsExampleTrial_isRandomizedTwoArm.measurable_X.comap_le hm.stronglyMeasurable
    Integrable.of_finite).symm⟩

/-- In the target of the example `lsExampleOutcome t` is a conditional mean function of
`Y(t)`. -/
theorem lsInst_isCondMean_target (t : Bool) :
    lsExampleTarget.IsCondMean t (lsExampleOutcome t) := by
  have hm : Measurable[MeasurableSpace.comap lsExampleTarget.X inferInstance]
      (lsExampleTarget.Y t) :=
    (measurable_of_finite (lsExampleOutcome t)).comp (comap_measurable _)
  have hX : Measurable lsExampleTarget.X := measurable_id
  exact ⟨measurable_of_finite _, EventuallyEq.of_eq (condExp_of_stronglyMeasurable hX.comap_le
    hm.stronglyMeasurable Integrable.of_finite).symm⟩

/-- The outcome of the example equals its conditional mean, so the conditional variance of the
residual is `0`. -/
theorem lsInst_residual_variance (t : Bool) :
    lsExampleTrial.μ[fun ω => (lsExampleTrial.Y t ω - lsExampleOutcome t (lsExampleTrial.X ω)) ^ 2 |
      MeasurableSpace.comap lsExampleTrial.X inferInstance] ≤ᵐ[lsExampleTrial.μ] fun _ => 0 := by
  have h0 : (fun ω => (lsExampleTrial.Y t ω - lsExampleOutcome t (lsExampleTrial.X ω)) ^ 2) =
      0 := funext fun ω => by simp [lsExampleTrial]
  rw [h0, condExp_zero]
  rfl

theorem lsInst_affine_true (x : Bool) :
    lsExampleOutcome true x = 1 + (fun _ => (2 : ℝ)) ⬝ᵥ commonLimitExampleFeature x := by
  cases x <;> norm_num [lsExampleOutcome, commonLimitExampleFeature, dotProduct]

theorem lsInst_affine_false (x : Bool) :
    lsExampleOutcome false x = 0 + (fun _ => (1 : ℝ)) ⬝ᵥ commonLimitExampleFeature x := by
  cases x <;> simp [lsExampleOutcome, commonLimitExampleFeature, dotProduct]

theorem lsInst_indepFun (t : Bool) :
    IndepFun lsExampleTrial.A (fun ω => (lsExampleTrial.X ω, lsExampleTrial.Y t ω))
      lsExampleTrial.μ := by
  have hT := lsExampleTrial_isRandomizedTwoArm
  cases t
  · exact hT.indepFun.comp measurable_id (measurable_fst.prodMk measurable_snd.fst)
  · exact hT.indepFun.comp measurable_id (measurable_fst.prodMk measurable_snd.snd)

theorem lsInst_measurable_obsOutcome : Measurable lsExampleTrial.obsOutcome :=
  measurable_of_finite _

/-! ### The settings -/

/-- The anchored setting of the example: the individual data trial `lsExampleTrial` of
`a = true` against `c = false`, the aggregate data trial `lsExampleTrial` with `b = c = false`,
and the target `lsExampleTarget`. -/
noncomputable def lsInstAnchoredSetting :
    AnchoredSetting (Bool × Bool) (Bool × Bool) Bool Bool Bool :=
  ⟨lsExampleTrial, lsExampleTrial, lsExampleTarget, true, false, false⟩

instance : IsFiniteMeasure lsInstAnchoredSetting.ipdTrial.μ := by
  unfold lsInstAnchoredSetting; infer_instance

instance : IsFiniteMeasure lsInstAnchoredSetting.agdTrial.μ := by
  unfold lsInstAnchoredSetting; infer_instance

instance : IsProbabilityMeasure lsInstAnchoredSetting.target.μ := by
  unfold lsInstAnchoredSetting; infer_instance

instance : IsProbabilityMeasure lsInstAnchoredSetting.target.covLaw := by
  unfold lsInstAnchoredSetting; change IsProbabilityMeasure lsExampleTarget.covLaw; infer_instance

/-- **The anchored setting of the example satisfies the identification assumptions** on the
identity scale, with the conditional means `lsExampleOutcome` in both trials and the target. -/
theorem lsInstAnchoredSetting_identificationAssumptions :
    lsInstAnchoredSetting.IdentificationAssumptions id Set.univ lsExampleOutcome lsExampleOutcome
      lsExampleOutcome where
  measurable_ipd := lsExampleTrial_isRandomizedTwoArm.measurable_X
  measurable_agd := lsExampleTrial_isRandomizedTwoArm.measurable_X
  measurable_target := measurable_id
  integrable_ipd_a := Integrable.of_finite
  integrable_ipd_c := Integrable.of_finite
  integrable_agd_b := Integrable.of_finite
  integrable_agd_c := Integrable.of_finite
  integrable_target _ _ := Integrable.of_finite
  isCondMean_ipd_a := lsInst_isCondMean_trial true
  isCondMean_ipd_c := lsInst_isCondMean_trial false
  isCondMean_agd_b := lsInst_isCondMean_trial false
  isCondMean_agd_c := lsInst_isCondMean_trial false
  isCondMean_target t _ := lsInst_isCondMean_target t
  mem_ipd := Eventually.of_forall fun _ => ⟨trivial, trivial⟩
  mem_agd := Eventually.of_forall fun _ => ⟨trivial, trivial⟩
  mem_target := Eventually.of_forall fun _ => ⟨trivial, trivial, trivial⟩
  relativeConstancy_ipd := relativeConstancy_of_structurallyInvariant
    (lsExample_structurallyInvariant true) (lsExample_structurallyInvariant false)
  relativeConstancy_agd := relativeConstancy_of_structurallyInvariant
    (lsExample_structurallyInvariant false) (lsExample_structurallyInvariant false)
  overlap_ipd := lsExample_absolutelyContinuous
  overlap_agd := lsExample_absolutelyContinuous
  integrable_ipd_contrast := Integrable.of_finite
  integrable_agd_contrast := Integrable.of_finite

/-- The unanchored setting of the example: both sources are the trial `lsExampleTrial`, with
`a = true` and `b = false`, and the target is `lsExampleTarget`. -/
noncomputable def lsInstUnanchoredSetting :
    UnanchoredSetting (Bool × Bool) (Bool × Bool) Bool Bool Bool :=
  ⟨lsExampleTrial.toPopulation, lsExampleTrial.toPopulation, lsExampleTarget, true, false⟩

instance : IsFiniteMeasure lsInstUnanchoredSetting.sourceA.μ := by
  unfold lsInstUnanchoredSetting; change IsFiniteMeasure lsExampleTrial.μ; infer_instance

instance : IsFiniteMeasure lsInstUnanchoredSetting.sourceB.μ := by
  unfold lsInstUnanchoredSetting; change IsFiniteMeasure lsExampleTrial.μ; infer_instance

instance : IsProbabilityMeasure lsInstUnanchoredSetting.target.μ := by
  unfold lsInstUnanchoredSetting; infer_instance

instance : IsProbabilityMeasure lsInstUnanchoredSetting.target.covLaw := by
  unfold lsInstUnanchoredSetting; change IsProbabilityMeasure lsExampleTarget.covLaw
  infer_instance

/-- **The unanchored setting of the example satisfies the identification assumptions** on the
identity scale, with `m_a = lsExampleOutcome true` and `m_b = lsExampleOutcome false`. -/
theorem lsInstUnanchoredSetting_identificationAssumptions :
    lsInstUnanchoredSetting.IdentificationAssumptions Set.univ (lsExampleOutcome true)
      (lsExampleOutcome false) where
  measurable_sourceA := lsExampleTrial_isRandomizedTwoArm.measurable_X
  measurable_sourceB := lsExampleTrial_isRandomizedTwoArm.measurable_X
  measurable_target := measurable_id
  integrable_sourceA := Integrable.of_finite
  integrable_sourceB := Integrable.of_finite
  integrable_target_a := Integrable.of_finite
  integrable_target_b := Integrable.of_finite
  mem_a := trivial
  mem_b := trivial
  isCondMean_a := lsInst_isCondMean_trial true
  isCondMean_b := lsInst_isCondMean_trial false
  structurallyInvariant_a := lsExample_structurallyInvariant true
  structurallyInvariant_b := lsExample_structurallyInvariant false
  overlap_a := lsExample_absolutelyContinuous
  overlap_b := lsExample_absolutelyContinuous
  integrable_weighted_a := Integrable.of_finite
  integrable_weighted_b := Integrable.of_finite

theorem lsInst_contrast_zero :
    ∫ x, linkContrast id (lsExampleOutcome false) (lsExampleOutcome false) x
      ∂lsExampleTarget.covLaw = 0 := by
  simp [linkContrast]

/-! ### The trial level theorems -/

/-- **An instance of `sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn`.** The
weighted arm mean of arm `true` at the reported moments `tₙ` converges in probability to the
target mean `E_Q[Y(true)] = 3/2`. -/
theorem lsInst_trial_armMean :
    IsConsistent (fun n ω => sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n)
      lsExampleSample true n ω) (3 / 2) lsExampleSampleLaw := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := sampleBalancedArmMean_isConsistent_trial_armMean_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (Q := lsExampleTarget) (s := true)
    lsExampleTrial_isRandomizedTwoArm.measurable_X lsExampleTrial_isRandomizedTwoArm.measurable_A
    lsInst_measurable_obsOutcome true (measurable_of_finite _) (lsInst_indepFun true)
    isIIDSample_lsExampleSample measurable_lsExampleSample (map_lsExampleSample 0)
    (measurable_of_finite _) hint hmin hexp hκ measurable_const (indepFun_const_left _ _)
    (fun _ => measurable_const) lsInst_tendsto
    (lsExampleTrial_isRandomizedTwoArm.prob_arm_pos true) (lsInst_isCondMean_trial true)
    Integrable.of_finite (lsInst_residual_variance true) lsInst_affine_true measurable_id
    (fun _ => Integrable.of_finite) commonLimitExample_featureMean Integrable.of_finite
    (lsInst_isCondMean_target true)
  rw [commonLimitExample_armMean_value] at h
  exact h

/-- **An instance of `unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn`.** In the
unanchored setting of the example, with the target mean of `Y(false)` reported exactly, the
weighted comparison `m̂_b - μ̂_true` at the reported moments converges in probability to
`-5/4`. -/
theorem lsInst_trial_unanchored :
    IsConsistent (fun n ω => id (∫ x, lsExampleOutcome false x ∂lsExampleTarget.covLaw) -
      id (sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n) lsExampleSample true
        n ω)) (-5 / 4) lsExampleSampleLaw := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := unanchoredBalancedEstimate_isConsistent_trial_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (S := lsInstUnanchoredSetting) (T := lsExampleTrial)
    (g := id) (mB := fun _ _ => ∫ x, lsExampleOutcome false x ∂lsExampleTarget.covLaw)
    lsInstUnanchoredSetting_identificationAssumptions
    lsExampleTrial_isRandomizedTwoArm.measurable_X lsExampleTrial_isRandomizedTwoArm.measurable_A
    lsInst_measurable_obsOutcome (measurable_of_finite _) (lsInst_indepFun true)
    isIIDSample_lsExampleSample measurable_lsExampleSample (map_lsExampleSample 0)
    (measurable_of_finite _) hint hmin hexp hκ measurable_const (indepFun_const_left _ _)
    (fun _ => measurable_const) lsInst_tendsto
    (lsExampleTrial_isRandomizedTwoArm.prob_arm_pos true) (lsInst_isCondMean_trial true)
    Integrable.of_finite (lsInst_residual_variance true) lsInst_affine_true
    (fun _ => Integrable.of_finite) commonLimitExample_featureMean (tendstoInMeasure_const _)
    continuousAt_id continuousAt_id
  have he : lsInstUnanchoredSetting.target.marginalEffect id lsInstUnanchoredSetting.a
      lsInstUnanchoredSetting.b = -5 / 4 := commonLimitExample_marginalEffect
  rw [he] at h
  exact h

/-- **An instance of `anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn`.** In the
anchored setting of the example, with the reported contrast `d̂_bc = 0`, the weighted
comparison `(μ̂_false - μ̂_true) - d̂_bc` at the reported moments converges in probability to
`-5/4`. -/
theorem lsInst_trial_anchored_identity :
    IsConsistent (fun n ω => (sampleBalancedArmMean commonLimitExampleFeature (lsInstReported n)
      lsExampleSample false n ω - sampleBalancedArmMean commonLimitExampleFeature
        (lsInstReported n) lsExampleSample true n ω) - 0) (-5 / 4) lsExampleSampleLaw := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := anchoredBalancedEstimate_isConsistent_identity_trial_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (S := lsInstAnchoredSetting) (T := lsExampleTrial)
    (dBC := fun _ _ => 0) lsInstAnchoredSetting_identificationAssumptions
    lsExampleTrial_isRandomizedTwoArm.measurable_X lsExampleTrial_isRandomizedTwoArm.measurable_A
    (measurable_of_finite _) (measurable_of_finite _) (lsInst_indepFun true)
    (lsInst_indepFun false) isIIDSample_lsExampleSample measurable_lsExampleSample
    (map_lsExampleSample 0) (measurable_of_finite _) hint hmin hexp hκ measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const) lsInst_tendsto
    (lsExampleTrial_isRandomizedTwoArm.prob_arm_pos true)
    (lsExampleTrial_isRandomizedTwoArm.prob_arm_pos false) (lsInst_isCondMean_trial true)
    (lsInst_isCondMean_trial false) Integrable.of_finite Integrable.of_finite
    (lsInst_residual_variance true) (lsInst_residual_variance false) lsInst_affine_true
    lsInst_affine_false (fun _ => Integrable.of_finite) commonLimitExample_featureMean
    (by change IsConsistent _ (∫ x, linkContrast id (lsExampleOutcome false)
          (lsExampleOutcome false) x ∂lsExampleTarget.covLaw) _
        rw [lsInst_contrast_zero]; exact tendstoInMeasure_const 0)
  have he : lsInstAnchoredSetting.target.marginalEffect id lsInstAnchoredSetting.a
      lsInstAnchoredSetting.b = -5 / 4 := commonLimitExample_marginalEffect
  rw [he] at h
  exact h

/-! ### The theorems for the trials of the settings -/

/-- **An instance of `anchoredWeightedEstimate_isConsistent_setting_of_isMinOn`.** In the
anchored setting of the example, the anchored weighted estimate with the treatment labels of the
records, the entropy balancing weights at the reported moments `tₙ` and the reported contrast
`d̂_bc = 0` converges in probability to `E_Q[Y(false)] - E_Q[Y(true)] = -5/4`. -/
theorem lsInst_setting_anchored :
    IsConsistent (fun n => anchoredWeightedEstimate id
        (fun ω => balancingWeights fun i : Fin n =>
          commonLimitExampleFeature (lsExampleSample i ω).1 - lsInstReported n)
        (fun ω i => (lsExampleSample i ω).2.1) (fun ω i => (lsExampleSample i ω).2.2) true false
        (fun _ => 0)) (-5 / 4) lsExampleSampleLaw := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := anchoredWeightedEstimate_isConsistent_setting_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (S := lsInstAnchoredSetting) (dBC := fun _ _ => 0)
    (hS := lsInstAnchoredSetting_identificationAssumptions) (hac := by simp [lsInstAnchoredSetting])
    (hA := lsExampleTrial_isRandomizedTwoArm.measurable_A)
    (hYa := measurable_of_finite _) (hYc := measurable_of_finite _)
    (hAac := ae_of_all _ fun ω => by
      change ω.1 = true ∨ ω.1 = false
      cases ω.1 <;> simp)
    (hra := lsInst_indepFun true) (hrc := lsInst_indepFun false)
    (hqa := lsExampleTrial_isRandomizedTwoArm.prob_arm_pos true)
    (hqc := lsExampleTrial_isRandomizedTwoArm.prob_arm_pos false)
    (hR := isIIDSample_lsExampleSample) (hRm := measurable_lsExampleSample)
    (hlaw := map_lsExampleSample 0) (hφ := measurable_of_finite _) (hint := hint)
    (hmin := hmin) (hexp := hexp) (hκ := hκ) (hW := measurable_const)
    (hWR := indepFun_const_left _ _) (hG := fun _ => measurable_const) (htm := lsInst_tendsto)
    (hrA := Integrable.of_finite) (hrC := Integrable.of_finite)
    (hvA := lsInst_residual_variance true) (hvC := lsInst_residual_variance false)
    (hafA := lsInst_affine_true) (hafC := lsInst_affine_false)
    (hQφ := fun _ => Integrable.of_finite) (ht := commonLimitExample_featureMean)
    (hd := by
      change IsConsistent _ (∫ x, linkContrast id (lsExampleOutcome false)
        (lsExampleOutcome false) x ∂lsExampleTarget.covLaw) _
      rw [lsInst_contrast_zero]; exact tendstoInMeasure_const 0)
  have he : lsInstAnchoredSetting.target.marginalEffect id lsInstAnchoredSetting.a
      lsInstAnchoredSetting.b = -5 / 4 := commonLimitExample_marginalEffect
  rw [he] at h
  exact h

/-- **An instance of `unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn`.** In the
unanchored setting of the example, with `lsExampleTrial` the trial of `a = true` against
`c = false` and the target mean of `Y(false)` reported exactly, `m̂_b - μ̂_true` with the
weighted mean of the records labeled `true` at the reported moments converges in probability to
`-5/4`. -/
theorem lsInst_setting_unanchored :
    IsConsistent (fun n ω => id (∫ x, lsExampleOutcome false x ∂lsExampleTarget.covLaw) -
      id (weightedArmMean (balancingWeights fun i : Fin n =>
        commonLimitExampleFeature (lsExampleSample i ω).1 - lsInstReported n)
          (fun i => (lsExampleSample i ω).2.1) (fun i => (lsExampleSample i ω).2.2) true))
      (-5 / 4) lsExampleSampleLaw := by
  obtain ⟨hint, βs, hmin, κ, hexp, hκ⟩ := lsInst_exists_isMinOn
  have h := unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn (W := fun _ => ())
    (G := fun n _ => lsInstReported n) (S := lsInstUnanchoredSetting) (T := lsExampleTrial)
    (c := false) (g := id)
    (mB := fun _ _ => ∫ x, lsExampleOutcome false x ∂lsExampleTarget.covLaw)
    (hS := lsInstUnanchoredSetting_identificationAssumptions) (hsrc := rfl)
    (hac := by simp [lsInstUnanchoredSetting])
    (hA := lsExampleTrial_isRandomizedTwoArm.measurable_A)
    (hYa := measurable_of_finite _) (hYc := measurable_of_finite _)
    (hAac := ae_of_all _ fun ω => by
      change ω.1 = true ∨ ω.1 = false
      cases ω.1 <;> simp)
    (hra := lsInst_indepFun true)
    (hqa := lsExampleTrial_isRandomizedTwoArm.prob_arm_pos true)
    (hR := isIIDSample_lsExampleSample) (hRm := measurable_lsExampleSample)
    (hlaw := map_lsExampleSample 0) (hφ := measurable_of_finite _) (hint := hint)
    (hmin := hmin) (hexp := hexp) (hκ := hκ) (hW := measurable_const)
    (hWR := indepFun_const_left _ _) (hG := fun _ => measurable_const) (htm := lsInst_tendsto)
    (hres2 := Integrable.of_finite) (hvar := lsInst_residual_variance true)
    (haff := lsInst_affine_true) (hQφ := fun _ => Integrable.of_finite)
    (ht := commonLimitExample_featureMean) (hmB := tendstoInMeasure_const _)
    (hga := continuousAt_id) (hgb := continuousAt_id)
  have he : lsInstUnanchoredSetting.target.marginalEffect id lsInstUnanchoredSetting.a
      lsInstUnanchoredSetting.b = -5 / 4 := commonLimitExample_marginalEffect
  rw [he] at h
  exact h

end PopulationAdjustment

end CausalInference
