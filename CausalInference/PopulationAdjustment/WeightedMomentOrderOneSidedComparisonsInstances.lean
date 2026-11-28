/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderOneSidedComparisons

/-!
# Instances of the comparisons under one sided moments

The common limit theorems of the comparisons under one sided moments
(`commonLimit_reportedMoments_armMean_of_isMinOn_oneSided`, `_unanchored_`, `_anchored_`,
`_anchored_identity_of_isMinOn_oneSided`) are instantiated on the coin trial over the standard
exponential feature law at a target mean where the theorems under one norm moment do not apply.

**The trial.** `X` is standard exponential, the assignment is a fair coin independent of `X`, and
`Y(true) = 1 + 2X`, `Y(false) = X` (`sharpInstTrial momentOrderExpLaw sharpInstOutcome`), with the
regression `z(a, x)ᵀξ₀` in the interaction design (`commonLimitExampleCoef`).

**The target.** The covariate of the target population is uniform on `[0, 1]`
(`oneSidedInstTarget`), with mean `t = 1/2`; its law is absolutely continuous with respect to the
exponential law (`oneSidedInstTarget_absolutelyContinuous`), and both arms are transported. The
target means are `E_Q[Y(true)] = 2` and `E_Q[Y(false)] = 1/2`.

**The moments.** At `t = 1/2` the population dual minimizer is `β* = 1 - 1/t = -1`. The norm
moment `E[exp(κ |X - t|)]` is finite exactly for `κ < 1`, so no order `κ > 2 |β*| = 2` has a
finite moment (`not_exists_order_momentOrderExpLaw_one_half`), while the norm moment of order
`1/2` and a directional moment `E[exp(2 (1 + ε) β* (X - t))] < ∞` are finite
(`oneSidedInst_weighting`).

**The limits.** With reported moments `tₙ = 1/2 + 1/(n + 1) → 1/2`:

* both estimators of arm `true` converge in probability to `E_Q[Y(true)] = 2`
  (`oneSidedInst_armMean`);
* with `E_Q[Y(false)] = 1/2` reported exactly, both unanchored comparisons of `false` against
  `true` converge in probability to `1/2 - 2 = -3/2` (`oneSidedInst_unanchored`);
* with `b = c = false` and the reported contrast `0`, both anchored comparisons converge in
  probability to `-3/2`, on the identity link (`oneSidedInst_anchored`) and under relative
  constancy on the identity scale (`oneSidedInst_anchored_identity`).

## Main definitions

* `oneSidedInstReported`, `oneSidedInstTarget`.

## Main results

* `not_exists_order_momentOrderExpLaw_one_half`, `oneSidedInst_weighting`.
* `oneSidedInst_armMean`, `oneSidedInst_unanchored`, `oneSidedInst_anchored`,
  `oneSidedInst_anchored_identity`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport
open scoped ENNReal

/-! ### The weighting hypotheses at `t = 1/2` -/

section Weighting

/-- The reported feature means `tₙ = 1/2 + 1/(n + 1)` of the instances. -/
noncomputable def oneSidedInstReported (n : ℕ) : Fin 1 → ℝ :=
  featureLineVec (1 / 2 + 1 / ((n : ℝ) + 1))

theorem tendsto_oneSidedInstReported :
    Tendsto oneSidedInstReported atTop (𝓝 (featureLineVec (1 / 2))) :=
  tendsto_pi_nhds.2 fun _ => by
    simpa [oneSidedInstReported, featureLineVec] using
      (tendsto_const_nhds (x := (1 / 2 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tendstoInMeasure_oneSidedInstReported :
    TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
      (fun n (_ : ℕ → (Fin 1 → ℝ) × Bool) => oneSidedInstReported n) atTop
      (fun _ => featureLineVec (1 / 2)) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (ae_of_all _ fun _ => tendsto_oneSidedInstReported)

/-- **The norm condition fails at `t = 1/2`**: with `β* = 1 - 2 = -1`, no order
`κ > 2 |β*| = 2` has `E[exp(κ |X - 1/2|)] < ∞` under the exponential law. -/
theorem not_exists_order_momentOrderExpLaw_one_half :
    ¬ ∃ κ : ℝ, Integrable (fun y => Real.exp (κ * ‖y - featureLineVec (1 / 2)‖))
        momentOrderExpLaw ∧ 2 * (1 : ℕ) * ‖featureLineVec (1 - 1 / (1 / 2 : ℝ))‖ < κ := by
  rintro ⟨κ, hi, hκ⟩
  rw [integrable_exp_momentOrderExpLaw_iff] at hi
  rw [norm_featureLineVec] at hκ
  norm_num at hκ
  linarith

/-- **The one sided weighting hypotheses of the instance** at `t = 1/2`: the interior condition,
the minimizer `β* = -1`, the norm moment of order `1/2` and a directional moment
`E[exp(2 (1 + ε) β* (X - t))] < ∞` for some `ε > 0`. -/
theorem oneSidedInst_weighting :
    featureLineVec (1 / 2) ∈ interior (closedConvexHull ℝ
      ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw.map id).support) ∧
    IsMinOn (sharpDualObjective (sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw id
      (featureLineVec (1 / 2))) Set.univ (featureLineVec (1 - 1 / (1 / 2))) ∧
    Integrable (fun x => Real.exp (1 / 2 * ‖id x - featureLineVec (1 / 2)‖))
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw ∧
    ∃ ε, 0 < ε ∧ Integrable (fun x => Real.exp (2 * (1 + ε) *
      (featureLineVec (1 - 1 / (1 / 2)) ⬝ᵥ (id x - featureLineVec (1 / 2)))))
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw := by
  have ht : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨hexp, ε, hε, hdir⟩ := oneSided_hypotheses_momentOrderExpLaw ht (by norm_num)
  rw [sharpInstTrial_covLaw, Measure.map_id]
  exact ⟨mem_interior_momentOrderExpLaw ht, isMinOn_sharpDualObjective_momentOrderExpLaw ht,
    hexp, ε, hε, hdir⟩

end Weighting

/-! ### The target population -/

section Target

/-- The target population of the instances: the covariate is uniform on `[0, 1]` and the outcomes
are those of the trial, `Y(true) = 1 + 2X`, `Y(false) = X`. -/
noncomputable def oneSidedInstTarget : Population ℝ (Fin 1 → ℝ) Bool :=
  ⟨volume.restrict (Set.Icc 0 1), featureLineVec,
    fun a ω => sharpInstOutcome a (featureLineVec ω)⟩

instance oneSidedInstTarget_isProbabilityMeasure : IsProbabilityMeasure oneSidedInstTarget.μ :=
  ⟨by simp [oneSidedInstTarget, Real.volume_Icc]⟩

theorem integrable_oneSidedInstTarget {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g oneSidedInstTarget.μ :=
  hg.integrableOn_Icc

theorem integral_oneSidedInstTarget_id : ∫ x, x ∂oneSidedInstTarget.μ = 1 / 2 := by
  change ∫ x in Set.Icc (0 : ℝ) 1, x = 1 / 2
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    integral_id]
  norm_num

/-- **The target law is absolutely continuous with respect to the exponential law**: on `[0, 1]`
the exponential density is at least `exp(-1)`. -/
theorem oneSidedInstTarget_absolutelyContinuous :
    oneSidedInstTarget.covLaw ≪ (sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw := by
  rw [sharpInstTrial_covLaw, momentOrderExpLaw]
  refine Measure.AbsolutelyContinuous.map ?_ measurable_featureLineVec
  refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
  have hmS : Measurable (S.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hS
  have hle : ENNReal.ofReal (Real.exp (-1)) * volume.restrict (Set.Icc (0 : ℝ) 1) S ≤
      expMeasure 1 S := by
    calc ENNReal.ofReal (Real.exp (-1)) * volume.restrict (Set.Icc (0 : ℝ) 1) S
        = ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-1)) * S.indicator 1 x := by
          rw [lintegral_const_mul _ hmS, lintegral_indicator_one hS]
      _ ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-x)) * S.indicator 1 x :=
          setLIntegral_mono ((by fun_prop : Measurable fun x : ℝ =>
            ENNReal.ofReal (Real.exp (-x))).mul hmS) fun x hx => by
            exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.2 (by linarith [hx.2]))) (by simp)
      _ ≤ ∫⁻ x in Set.Ici 0, ENNReal.ofReal (Real.exp (-x)) * S.indicator 1 x :=
          lintegral_mono_set fun x hx => Set.mem_Ici.2 hx.1
      _ = expMeasure 1 S := by
          rw [← lintegral_expMeasure_one hmS, lintegral_indicator_one hS]
  rw [hS0, nonpos_iff_eq_zero, mul_eq_zero] at hle
  change volume.restrict (Set.Icc (0 : ℝ) 1) S = 0
  exact hle.resolve_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem oneSidedInstTarget_featureMean (k : Fin 1) :
    ∫ x, x k ∂oneSidedInstTarget.covLaw = featureLineVec (1 / 2) k := by
  change ∫ x, x k ∂(oneSidedInstTarget.μ.map featureLineVec) = _
  rw [integral_map measurable_featureLineVec.aemeasurable
    (by fun_prop : Measurable fun x : Fin 1 → ℝ => x k).aestronglyMeasurable]
  exact integral_oneSidedInstTarget_id

theorem oneSidedInstTarget_featureIntegrable (k : Fin 1) :
    Integrable (fun x => x k) oneSidedInstTarget.covLaw := by
  change Integrable _ (oneSidedInstTarget.μ.map featureLineVec)
  rw [integrable_map_measure
    (by fun_prop : Measurable fun x : Fin 1 → ℝ => x k).aestronglyMeasurable
    measurable_featureLineVec.aemeasurable]
  exact integrable_oneSidedInstTarget continuous_id

theorem oneSidedInstTarget_integrable (a : Bool) :
    Integrable (oneSidedInstTarget.Y a) oneSidedInstTarget.μ := by
  cases a
  · exact integrable_oneSidedInstTarget continuous_id
  · exact integrable_oneSidedInstTarget (continuous_const.add (continuous_const.mul continuous_id))

/-- In the target, `sharpInstOutcome a` is a conditional mean function of `Y(a)`. -/
theorem oneSidedInstTarget_isCondMean (a : Bool) :
    oneSidedInstTarget.IsCondMean a (sharpInstOutcome a) :=
  Population.isCondMean_of_eq_comp measurable_featureLineVec (measurable_sharpInstOutcome a)
    rfl (oneSidedInstTarget_integrable a)

/-- **Both arms are transported**: the regression of `Y(a)` on the covariate is
`sharpInstOutcome a` in the trial and in the target. -/
theorem oneSidedInst_structurallyInvariant (a : Bool) :
    StructurallyInvariant (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).X
      ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).Y a)
      oneSidedInstTarget.μ oneSidedInstTarget.X (oneSidedInstTarget.Y a) := by
  obtain ⟨-, -, -, -, -, -, hm, -, -⟩ := sharpInstTrial_hypotheses measurable_sharpInstOutcome a
    (integrable_sharpInstOutcome_momentOrderExpLaw a)
  refine ⟨sharpInstOutcome a, (Population.isCommonRegression_iff
    (P := (sharpInstTrial momentOrderExpLaw sharpInstOutcome).toPopulation)
    (Q := oneSidedInstTarget) a _).2 ⟨hm, ?_⟩⟩
  exact oneSidedInstTarget_isCondMean a

theorem oneSidedInstTarget_armMean_true : oneSidedInstTarget.armMean true = 2 := by
  change ∫ x, (1 + 2 * x) ∂oneSidedInstTarget.μ = 2
  rw [integral_add (integrable_oneSidedInstTarget (g := fun _ => (1 : ℝ)) continuous_const)
    (integrable_oneSidedInstTarget (g := fun x => 2 * x) (continuous_const.mul continuous_id)),
    integral_const_mul, integral_oneSidedInstTarget_id, integral_const, probReal_univ]
  norm_num

theorem oneSidedInstTarget_armMean_false : oneSidedInstTarget.armMean false = 1 / 2 :=
  integral_oneSidedInstTarget_id

theorem oneSidedInstTarget_marginalEffect :
    oneSidedInstTarget.marginalEffect id true false = -3 / 2 := by
  rw [Population.marginalEffect, oneSidedInstTarget_armMean_true,
    oneSidedInstTarget_armMean_false]
  norm_num

end Target

/-! ### The comparisons -/

section Comparisons

/-- Relative constancy on the identity scale in the target of the instances: the contrast of the
regressions is the conditional mean of `Y(false) - Y(true)` given the covariate. -/
theorem oneSidedInst_relativeConstancy :
    (fun ω => featureInteractionDesign id false (oneSidedInstTarget.X ω) ⬝ᵥ
        commonLimitExampleCoef - featureInteractionDesign id true (oneSidedInstTarget.X ω) ⬝ᵥ
          commonLimitExampleCoef) =ᵐ[oneSidedInstTarget.μ]
      oneSidedInstTarget.μ[fun ω => oneSidedInstTarget.Y false ω - oneSidedInstTarget.Y true ω |
        MeasurableSpace.comap oneSidedInstTarget.X inferInstance] := by
  have hX : Measurable oneSidedInstTarget.X := measurable_featureLineVec
  have hm : Measurable[MeasurableSpace.comap oneSidedInstTarget.X inferInstance]
      (fun ω => oneSidedInstTarget.Y false ω - oneSidedInstTarget.Y true ω) :=
    ((measurable_sharpInstOutcome false).sub (measurable_sharpInstOutcome true)).comp
      (comap_measurable _)
  rw [condExp_of_stronglyMeasurable hX.comap_le hm.stronglyMeasurable
    ((oneSidedInstTarget_integrable false).sub (oneSidedInstTarget_integrable true))]
  refine EventuallyEq.of_eq (funext fun ω => ?_)
  rw [featureInteractionDesign_dotProduct_sharpInstOutcome,
    featureInteractionDesign_dotProduct_sharpInstOutcome]
  rfl

/-- **An instance of `commonLimit_reportedMoments_armMean_of_isMinOn_oneSided` at `t = 1/2`.**
In the exponential coin trial, both estimators of arm `true` at the reported moments
`tₙ = 1/2 + 1/(n + 1)` converge in probability to the target mean `E_Q[Y(true)] = 2`, and their
difference converges in probability to `0`. No order `κ > 2 |β*|` has a finite norm moment here
(`not_exists_order_momentOrderExpLaw_one_half`). -/
theorem oneSidedInst_armMean :
    IsConsistent (fun n ω => sampleBalancedArmMean id (oneSidedInstReported n)
        (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) 2
        (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          (oneSidedInstReported n) true n ω) atTop (fun _ => 2) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          (oneSidedInstReported n) true n ω - sampleBalancedArmMean id (oneSidedInstReported n)
            (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) atTop
        (fun _ => 0) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  have h := commonLimit_reportedMoments_armMean_of_isMinOn_oneSided (W := fun _ => ())
    (G := fun n _ => oneSidedInstReported n)
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id hint hmin (by norm_num) hexp hε hdir unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_oneSidedInstReported true (unboundedInst_variance true)
    measurable_featureLineVec oneSidedInstTarget_featureIntegrable
    oneSidedInstTarget_featureMean (oneSidedInstTarget_integrable true)
    (oneSidedInst_structurallyInvariant true) oneSidedInstTarget_absolutelyContinuous
  rw [oneSidedInstTarget_armMean_true] at h
  exact h

/-- **An instance of `commonLimit_reportedMoments_unanchored_of_isMinOn_oneSided` at
`t = 1/2`.** With the target mean of `Y(false)` reported exactly (`m̂_b = E_Q[Y(false)] = 1/2`)
and the identity link, the weighted and the standardized unanchored comparisons of `false`
against `true` both converge in probability to `1/2 - 2 = -3/2`, and their difference converges
in probability to `0`. -/
theorem oneSidedInst_unanchored :
    IsConsistent (fun n ω => id (oneSidedInstTarget.armMean false) - id (sampleBalancedArmMean
        id (oneSidedInstReported n) (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          true n ω)) (-3 / 2) (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => id (oneSidedInstTarget.armMean false) - id (reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (oneSidedInstReported n)
            true n ω)) atTop (fun _ => -3 / 2) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => (id (oneSidedInstTarget.armMean false) - id (reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (oneSidedInstReported n)
            true n ω)) - (id (oneSidedInstTarget.armMean false) - id (sampleBalancedArmMean
              id (oneSidedInstReported n) (sharpInstSample momentOrderExpLaw sharpInstOutcome)
                true n ω))) atTop (fun _ => 0) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  have h := commonLimit_reportedMoments_unanchored_of_isMinOn_oneSided (W := fun _ => ())
    (G := fun n _ => oneSidedInstReported n) (a := true) (b := false)
    (mb := fun _ _ => oneSidedInstTarget.armMean false) (g := id)
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id hint hmin (by norm_num) hexp hε hdir unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_oneSidedInstReported (unboundedInst_variance true)
    measurable_featureLineVec oneSidedInstTarget_featureIntegrable
    oneSidedInstTarget_featureMean (oneSidedInstTarget_integrable true)
    (oneSidedInst_structurallyInvariant true) oneSidedInstTarget_absolutelyContinuous
    (tendstoInMeasure_const _) continuousAt_id continuousAt_id
  rw [oneSidedInstTarget_marginalEffect] at h
  exact h

/-- **An instance of `commonLimit_reportedMoments_anchored_of_isMinOn_oneSided` at `t = 1/2`.**
With `a = true`, `b = c = false`, the identity link and the reported contrast `d̂_bc = 0`, the
weighted and the standardized anchored comparisons both converge in probability to `-3/2`, and
their difference converges in probability to `0`. -/
theorem oneSidedInst_anchored :
    IsConsistent (fun n ω => (id (sampleBalancedArmMean id (oneSidedInstReported n)
        (sharpInstSample momentOrderExpLaw sharpInstOutcome) false n ω) -
          id (sampleBalancedArmMean id (oneSidedInstReported n)
            (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω)) - 0)
        (-3 / 2) (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => (id (reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (oneSidedInstReported n) false n ω) -
            id (reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
              (oneSidedInstReported n) true n ω)) - 0) atTop (fun _ => -3 / 2) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => ((id (reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (oneSidedInstReported n) false n ω) -
            id (reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
              (oneSidedInstReported n) true n ω)) - 0) -
          ((id (sampleBalancedArmMean id (oneSidedInstReported n)
            (sharpInstSample momentOrderExpLaw sharpInstOutcome) false n ω) -
              id (sampleBalancedArmMean id (oneSidedInstReported n)
                (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω)) - 0)) atTop
        (fun _ => 0) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  have h0 : oneSidedInstTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have h := commonLimit_reportedMoments_anchored_of_isMinOn_oneSided (W := fun _ => ())
    (G := fun n _ => oneSidedInstReported n) (a := true) (b := false) (c := false)
    (dbc := fun _ _ => 0) (g := id)
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id hint hmin (by norm_num) hexp hε hdir unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_oneSidedInstReported unboundedInst_variance
    measurable_featureLineVec oneSidedInstTarget_featureIntegrable
    oneSidedInstTarget_featureMean (oneSidedInstTarget_integrable true)
    (oneSidedInstTarget_integrable false) (oneSidedInst_structurallyInvariant true)
    (oneSidedInst_structurallyInvariant false) oneSidedInstTarget_absolutelyContinuous
    (by rw [h0]; exact tendstoInMeasure_const 0) continuousAt_id continuousAt_id
  rw [oneSidedInstTarget_marginalEffect] at h
  exact h

/-- **An instance of `commonLimit_reportedMoments_anchored_identity_of_isMinOn_oneSided` at
`t = 1/2`.** With `a = true`, `b = c = false` and the reported contrast `d̂_bc = 0`, under
relative constancy on the identity scale, the weighted and the standardized anchored comparisons
both converge in probability to `E_Q[Y(false)] - E_Q[Y(true)] = -3/2`, and their difference
converges in probability to `0`. -/
theorem oneSidedInst_anchored_identity :
    IsConsistent (fun n ω => (sampleBalancedArmMean id (oneSidedInstReported n)
        (sharpInstSample momentOrderExpLaw sharpInstOutcome) false n ω -
          sampleBalancedArmMean id (oneSidedInstReported n)
            (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) - 0)
        (-3 / 2) (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => (reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (oneSidedInstReported n) false n ω -
            reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
              (oneSidedInstReported n) true n ω) - 0) atTop (fun _ => -3 / 2) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => ((reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (oneSidedInstReported n) false n ω -
            reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
              (oneSidedInstReported n) true n ω) - 0) -
          ((sampleBalancedArmMean id (oneSidedInstReported n)
            (sharpInstSample momentOrderExpLaw sharpInstOutcome) false n ω -
              sampleBalancedArmMean id (oneSidedInstReported n)
                (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) - 0)) atTop
        (fun _ => 0) := by
  obtain ⟨hint, hmin, hexp, ε, hε, hdir⟩ := oneSidedInst_weighting
  have h0 : oneSidedInstTarget.marginalEffect id false false = 0 := by
    simp [Population.marginalEffect]
  have h := commonLimit_reportedMoments_anchored_identity_of_isMinOn_oneSided (W := fun _ => ())
    (G := fun n _ => oneSidedInstReported n) (a := true) (b := false) (c := false)
    (dbc := fun _ _ => 0)
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id hint hmin (by norm_num) hexp hε hdir unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_oneSidedInstReported unboundedInst_variance
    measurable_featureLineVec oneSidedInstTarget_featureIntegrable
    oneSidedInstTarget_featureMean (oneSidedInstTarget_integrable true)
    (oneSidedInstTarget_integrable false) oneSidedInst_relativeConstancy
    (by rw [h0]; exact tendstoInMeasure_const 0)
  rw [oneSidedInstTarget_marginalEffect] at h
  exact h

end Comparisons

end PopulationAdjustment

end CausalInference
