/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyExamples
public import CausalInference.PopulationAdjustment.StandardizationInstancesLogistic
public import CausalInference.IndirectComparison.TrialSummary
public import CausalInference.IndirectComparison.CommonComparator

/-!
# An anchored comparison of three distinct treatments: every hypothesis verified

The anchored comparison standardizes both arms of an index trial of `a` against the common
comparator `c` to a target population and subtracts the reported contrast of `c` against `b` in
the target. This file gives an instance with three distinct treatments `a = 0`, `b = 1`, `c = 2`.

* **The index trial** is the randomized trial `lsExampleTrial` with the linear outcome model
  `lsExample_linearOutcomeModel` (a binary covariate, a fair coin, potential outcomes
  `Y(t) = 1[x] + 1[t](1 + 1[x])`); its arm `true` stands for `a` and its arm `false` for `c`, and
  its records are the i.i.d. sample `lsExampleSample`.
* **The target** (`anchoredInstTarget`): `P(X = 1) = 1/4`, the outcomes of `a` and `c` are those
  of the two arms of the trial, and `b` has the outcome `1 + 1[x]`. The target means are `3/2`,
  `5/4` and `1/4`.
* **The reported contrast** of `c` against `b` is the deterministic sequence `-1 + 1/(n + 1)`: it
  converges to the target contrast `E_Q[Y(c)] - E_Q[Y(b)] = -1`, as an aggregate estimate from a
  growing trial of `b` against `c` in the target does.

`anchoredInst_anchored`: the anchored estimator converges in probability to the target effect
`E_Q[Y(b)] - E_Q[Y(a)] = -1/4`. The naive indirect comparison, which uses the unadjusted contrast
`-3/2` of the index trial in its own population, gives `-1/2` instead
(`anchoredInst_naive_ne`): the covariate is an effect modifier and its law differs between the
trial and the target.

## Main definitions

* `anchoredInstOutcome`, `anchoredInstTarget`.

## Main results

* `anchoredInst_structurallyInvariant`, `anchoredInst_absolutelyContinuous`,
  `anchoredInstTarget_armMean`, `anchoredInst_anchored`, `lsExampleTrial_aggregateContrast`,
  `anchoredInst_naive_ne`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The target outcomes of `a = 0`, `b = 1`, `c = 2` as functions of the covariate. -/
noncomputable def anchoredInstOutcome : Fin 3 → Bool → ℝ :=
  ![lsExampleOutcome true, fun x => 1 + if x then 1 else 0, lsExampleOutcome false]

/-- The target of the anchored instance: the covariate is `true` with probability `1/4`. -/
noncomputable def anchoredInstTarget : Population Bool Bool (Fin 3) :=
  ⟨standardizationTargetLaw, id, anchoredInstOutcome⟩

instance : IsProbabilityMeasure anchoredInstTarget.μ := by
  unfold anchoredInstTarget; infer_instance

theorem anchoredInstTarget_covLaw : anchoredInstTarget.covLaw = standardizationTargetLaw :=
  Measure.map_id

instance : IsProbabilityMeasure anchoredInstTarget.covLaw := by
  rw [anchoredInstTarget_covLaw]; infer_instance

/-- **The arms of the trial are transported**: arm `true` stands for `a = 0`, arm `false` for
`c = 2`; the regression of the outcome on the covariate is the same function in the trial and in
the target. -/
theorem anchoredInst_structurallyInvariant (t : Bool) (s : Fin 3)
    (hst : anchoredInstOutcome s = lsExampleOutcome t) :
    StructurallyInvariant lsExampleTrial.μ lsExampleTrial.X (lsExampleTrial.Y t)
      anchoredInstTarget.μ anchoredInstTarget.X (anchoredInstTarget.Y s) := by
  refine ⟨lsExampleOutcome t, measurable_of_finite _, ?_, ?_⟩
  · have hm : Measurable[MeasurableSpace.comap lsExampleTrial.X inferInstance]
        (lsExampleTrial.Y t) :=
      (measurable_of_finite (lsExampleOutcome t)).comp (comap_measurable _)
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable
      lsExampleTrial_isRandomizedTwoArm.measurable_X.comap_le hm.stronglyMeasurable
      Integrable.of_finite).symm
  · have hm : Measurable[MeasurableSpace.comap anchoredInstTarget.X inferInstance]
        (anchoredInstTarget.Y s) := by
      change Measurable[MeasurableSpace.comap anchoredInstTarget.X inferInstance]
        (anchoredInstOutcome s ∘ anchoredInstTarget.X)
      exact (measurable_of_finite (anchoredInstOutcome s)).comp (comap_measurable _)
    have hX : Measurable anchoredInstTarget.X := measurable_id
    refine EventuallyEq.of_eq ?_
    rw [condExp_of_stronglyMeasurable hX.comap_le hm.stronglyMeasurable Integrable.of_finite]
    funext x
    change lsExampleOutcome t x = anchoredInstOutcome s x
    rw [hst]

/-- **Overlap**: the target covariate law is dominated by the trial covariate law. -/
theorem anchoredInst_absolutelyContinuous :
    anchoredInstTarget.covLaw ≪ lsExampleTrial.covLaw := by
  rw [anchoredInstTarget_covLaw]
  exact anchoredInstTarget_covLaw ▸ lsExample_absolutelyContinuous

/-- **The target means**: `3/2` for `a`, `5/4` for `b` and `1/4` for `c`. -/
theorem anchoredInstTarget_armMean :
    anchoredInstTarget.armMean 0 = 3 / 2 ∧ anchoredInstTarget.armMean 1 = 5 / 4 ∧
      anchoredInstTarget.armMean 2 = 1 / 4 := by
  have hint : ∀ f : Bool → ℝ, ∫ x, f x ∂standardizationTargetLaw = f true / 4 + 3 * f false / 4 :=
    fun f => by
      rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
      simp [standardizedRisk]; ring
  simp only [Population.armMean, anchoredInstTarget, hint]
  simp [anchoredInstOutcome, lsExampleOutcome]
  norm_num

/-- **The anchored comparison with three distinct treatments is consistent.** The index trial
`lsExampleTrial` compares `a` (arm `true`) with `c` (arm `false`); both arms of the least squares
fit are standardized to the target, and the reported contrast of `c` against `b` is the
deterministic sequence `-1 + 1/(n + 1)`, which converges to the target contrast `-1`. The
anchored estimator converges in probability to the target effect `-1/4` of `b` relative to `a`.
Every hypothesis of `tendstoInMeasure_leastSquares_anchored` is verified. -/
theorem anchoredInst_anchored :
    TendstoInMeasure lsExampleSampleLaw
      (fun (n : ℕ) ω => linkMarginal id anchoredInstTarget.covLaw
        (fun x => lsExampleDesign true x ⬝ᵥ
          leastSquaresFit (recordDesign lsExampleDesign) recordResponse lsExampleSample n ω)
        (fun x => lsExampleDesign false x ⬝ᵥ
          leastSquaresFit (recordDesign lsExampleDesign) recordResponse lsExampleSample n ω) -
        (-1 + 1 / ((n : ℝ) + 1)))
      atTop (fun _ => -1 / 4) := by
  obtain ⟨h0, h1, h2⟩ := anchoredInstTarget_armMean
  have hlim : anchoredInstTarget.marginalEffect id 0 1 = -1 / 4 := by
    simp only [Population.marginalEffect, id, h0, h1]; norm_num
  have hd : TendstoInMeasure lsExampleSampleLaw
      (fun (n : ℕ) (_ : ℕ → Bool × Bool) => -1 + 1 / ((n : ℝ) + 1)) atTop
      (fun _ => anchoredInstTarget.marginalEffect id 1 2) := by
    have : anchoredInstTarget.marginalEffect id 1 2 = -1 := by
      simp only [Population.marginalEffect, id, h1, h2]; norm_num
    rw [this]
    exact tendstoInMeasure_add_one_div_succ _ _
  rw [← hlim]
  exact tendstoInMeasure_leastSquares_anchored (ta := true) (tc := false) (a := 0) (b := 1)
    (c := 2) lsExampleTrial_isRandomizedTwoArm lsExample_linearOutcomeModel
    isIIDSample_lsExampleSample (map_lsExampleSample 0) measurable_id Integrable.of_finite
    Integrable.of_finite (anchoredInst_structurallyInvariant true 0 rfl)
    (anchoredInst_structurallyInvariant false 2 rfl) anchoredInst_absolutelyContinuous
    (fun _ _ => Integrable.of_finite) hd continuousAt_id continuousAt_id

/-- **The unadjusted contrast of the index trial** of `c` against `a` in its own population is
`E[Y | A = false] - E[Y | A = true] = 1/2 - 2 = -3/2`; the arm summaries of the randomized trial
are its arm means (`Trial.armSummary_eq_armMean`). -/
theorem lsExampleTrial_aggregateContrast :
    lsExampleTrial.aggregateContrast id true false = -3 / 2 := by
  have hT := lsExampleTrial_isRandomizedTwoArm
  have hne : ∀ t : Bool, lsExampleTrial.μ (lsExampleTrial.A ⁻¹' {t}) ≠ 0 := fun t => by
    change (halfLaw.prod halfLaw) (Prod.fst ⁻¹' {t}) ≠ 0
    rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    simp [halfLaw, stratumLaw]
  have hs1 := (Trial.armSummary_eq_armMean (t := true) hT.measurable_A
    (hT.indepFun.comp measurable_id (measurable_snd.comp measurable_snd)) Integrable.of_finite
    (hne true)).2
  have hs0 := (Trial.armSummary_eq_armMean (t := false) hT.measurable_A
    (hT.indepFun.comp measurable_id (measurable_fst.comp measurable_snd)) Integrable.of_finite
    (hne false)).2
  have hmean : ∀ t, lsExampleTrial.toPopulation.armMean t =
      (lsExampleOutcome t true + lsExampleOutcome t false) / 2 := fun t => by
    change ∫ ω, lsExampleOutcome t ω.2 ∂(halfLaw.prod halfLaw) = _
    rw [integral_prod _ Integrable.of_finite]
    simp only [integral_const, smul_eq_mul, probReal_univ, one_mul, integral_halfLaw]
  rw [Trial.aggregateContrast, hs1, hs0, hmean, hmean]
  simp [lsExampleOutcome]
  norm_num

/-- **The anchored limit differs from the naive indirect comparison.** The naive indirect
comparison `d_ac - d_bc` with the unadjusted contrast `d_ac = -3/2` of the index trial and the
target contrast `d_bc = -1` is `-1/2`, while the target effect of `b` relative to `a`, the limit
of the anchored estimator, is `-1/4`. -/
theorem anchoredInst_naive_ne :
    indirectEstimate (fun _ : Unit => lsExampleTrial.aggregateContrast id true false)
        (fun _ => anchoredInstTarget.marginalEffect id 1 2) () = -1 / 2 ∧
      anchoredInstTarget.marginalEffect id 0 1 = -1 / 4 ∧ (-1 / 2 : ℝ) ≠ -1 / 4 := by
  obtain ⟨h0, h1, h2⟩ := anchoredInstTarget_armMean
  refine ⟨?_, ?_, by norm_num⟩
  · simp only [indirectEstimate, lsExampleTrial_aggregateContrast, Population.marginalEffect, id,
      h1, h2]
    norm_num
  · simp only [Population.marginalEffect, id, h0, h1]; norm_num

end PopulationAdjustment

end CausalInference
