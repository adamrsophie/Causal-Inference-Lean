/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageDelay
public import CausalInference.StructuralNested.TwoStageTwoArm

/-!
# Two-stage estimation: the delay families as two-arm trials

Both delay families of `TwoStageDelay` become randomized trials with `TwoArm.trial`: the
control arm is the delay trial, the experimental arm survives `4` with no adjusted switch, the
arm is a fair coin. The censoring time `C = 100` is beyond every survival time, so no one is
censored; the stage-two contrast is the difference of arm means.

## Main results

* `DelayBaseline.twoArm`: with the baseline form, the stage-two mean contrast at the stage-one
  root is `1 - d`, equal to the true hypothetical effect, at every delay `d ≥ 0`. The bias of
  the mean contrast is zero, so it does not grow with the delay: the errors of the two
  switchers, `∓ d / (d + 6)` (`DelayBaseline.adjusted_sub_U`), cancel in the mean
  (`DelayBaseline.expect_adjusted`). What grows is the mean absolute error of the transformed
  control times, `DelayBaseline.expect_abs_error`: it equals `delayRootBias d`, zero at `0` and
  strictly increasing.
* `DelayConfounded.twoArm`: with time-dependent confounding, the stage-two mean contrast is
  `1 - delayBias d` against the true effect `1`; the bias `-delayBias d` is zero at delay `0`
  and its size grows strictly on `[0, 1]` (`DelayConfounded.twoArm_bias_mono`).
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageCounterexample

open TwoArm

namespace DelayBaseline

/-- The stage-one root of the baseline form at delay `d`. -/
noncomputable def ψhat (d : ℝ) : ℝ := Real.log (baselineRatio d)

/-- The time ratio of the stage-one root. -/
theorem exp_ψhat {d : ℝ} (hd : 0 ≤ d) : Real.exp (ψhat d) = baselineRatio d :=
  Real.exp_log (div_pos (by linarith) (by linarith))

/-- `ψhat d` is the stage-one root of the baseline form. -/
theorem root_ψhat {d : ℝ} (hd : 0 ≤ d) :
    (M d).stageOne p univ L (fun _ => 1) (M d).S (ψhat d) = 0 :=
  (root_S hd _).2 (exp_ψhat hd)

/-- The transformed time of a switcher minus its untreated time: `± d / (d + 6)`. -/
theorem adjusted_sub_U {d : ℝ} (hd : 0 ≤ d) (h : Bool) :
    (M d).adjusted (M d).S (ψhat d) (h, true) - (M d).U (h, true) =
      (if h then -1 else 1) * (d / (d + 6)) := by
  have h6 : d + 6 ≠ 0 := by linarith
  rw [(M d).adjusted_of_switch _ _ (ω := (h, true)) rfl, exp_ψhat hd, baselineRatio]
  cases h <;> simp [M, r] <;> field_simp <;> ring

/-- **The mean of the transformed control arm is the untreated mean at every delay**:
`E[adjusted] = E[U] = d + 3`. -/
theorem expect_adjusted {d : ℝ} (hd : 0 ≤ d) :
    p.expect ((M d).adjusted (M d).S (ψhat d)) = d + 3 ∧ p.expect (M d).U = d + 3 := by
  have h6 : d + 6 ≠ 0 := by linarith
  constructor
  · simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, p_apply]
    rw [(M d).adjusted_of_switch _ _ (ω := (true, true)) rfl,
      (M d).adjusted_of_switch _ _ (ω := (false, true)) rfl,
      (M d).adjusted_of_not_switch _ _ (ω := (true, false)) rfl,
      (M d).adjusted_of_not_switch _ _ (ω := (false, false)) rfl, exp_ψhat hd, baselineRatio]
    simp [M, r]
    field_simp
    ring
  · simp [FiniteDist.expect, Fintype.sum_prod_type, p_apply, M, r]
    ring

/-- **The two-arm contrast at delay `d`**: the stage-two mean contrast is `1 - d`, equal to the
true hypothetical effect `1 - d`, at every delay: the bias of the mean contrast is zero for
every delay `d ≥ 0`. -/
theorem twoArm {d : ℝ} (hd : 0 ≤ d) :
    (((trial (M d) T1).toSwitchingTrial fun z => (M d).S z.2).meanContrast (law p).toMeasure
        ((trial (M d) T1).analysisTime (fun z => (M d).S z.2) (ψhat d)) = 1 - d) ∧
      ((trial (M d) T1).toSwitchingTrial fun z => (M d).S z.2).hypotheticalEffect
        (law p).toMeasure = 1 - d := by
  obtain ⟨e1, e2⟩ := expect_adjusted hd
  refine ⟨?_, ?_⟩
  · rw [meanContrast_trial, e1, expect_T1]; ring
  · rw [hypotheticalEffect_trial, e2, expect_T1]; ring

/-- **What grows with the delay**: the mean absolute error of the transformed control times,
`E|adjusted - U| = d / (2 (d + 6)) = delayRootBias d`, which is `0` at delay `0` and strictly
increasing (`delayRootBias_strictMonoOn`). The errors of the two switchers cancel in the
mean. -/
theorem expect_abs_error {d : ℝ} (hd : 0 ≤ d) :
    p.expect (fun ω => |(M d).adjusted (M d).S (ψhat d) ω - (M d).U ω|) = delayRootBias d := by
  have h6 : 0 < d + 6 := by linarith
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, p_apply]
  rw [adjusted_sub_U hd, adjusted_sub_U hd,
    (M d).adjusted_of_not_switch _ _ (ω := (true, false)) rfl,
    (M d).adjusted_of_not_switch _ _ (ω := (false, false)) rfl]
  have hq : 0 ≤ d / (d + 6) := div_nonneg hd h6.le
  simp only [ite_true, Bool.false_eq_true, ite_false, neg_one_mul, one_mul, abs_neg,
    abs_of_nonneg hq, M, sub_self, abs_zero, mul_zero, add_zero, delayRootBias]
  field_simp
  ring

end DelayBaseline

namespace DelayConfounded

open SwitchingCounterexamples.TimeDependent

/-- **The two-arm contrast at delay `d`** (time-dependent confounding): the stage-two mean
contrast at the stage-one root is `1 - delayBias d`, the true hypothetical effect is `1`, and
the bias is `-delayBias d = -d (2 - d) / (3 - d)`: zero at delay `0` and strictly decreasing on
`[0, 1]`, so its size grows strictly with the delay. -/
theorem twoArm (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) :
    (((trial (M d) T1).toSwitchingTrial fun z => (M d).W z.2).meanContrast
        (law (pd d hd)).toMeasure
        ((trial (M d) T1).analysisTime (fun z => (M d).W z.2) (-Real.log (delayFactor d))) =
        1 - delayBias d) ∧
      ((trial (M d) T1).toSwitchingTrial fun z => (M d).W z.2).hypotheticalEffect
        (law (pd d hd)).toMeasure = 1 := by
  have hb := bias d hd
  have hU : (pd d hd).expect (M d).U = 3 := delay_expect_T0 d hd
  refine ⟨?_, ?_⟩
  · rw [meanContrast_trial, expect_T1]
    rw [hU] at hb
    linarith
  · rw [hypotheticalEffect_trial, expect_T1, hU]; norm_num

/-- The contrast bias is `0` at delay `0` and its size strictly increases on `[0, 1]`. -/
theorem twoArm_bias_mono : delayBias 0 = 0 ∧ StrictMonoOn delayBias (Set.Icc 0 1) :=
  ⟨delay_zero.2, delayBias_strictMonoOn⟩

end DelayConfounded

end TwoStageCounterexample

end StructuralNested

end CausalInference
