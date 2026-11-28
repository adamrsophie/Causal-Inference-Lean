/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageWeibullBridge

/-!
# Two-stage Weibull fit with the secondary baseline at progression

`CausalInference.StructuralNested.TwoStageWeibullBridge` puts the time-dependent confounding
countermodel `SwitchingCounterexamples.TimeDependent` in the two-stage form with the secondary
baseline at the switch decision (time `1`), where the time after the secondary baseline is the
residual survival `Y` and the Weibull fit returns `weibullFactor k`. Here the secondary baseline
is at progression (time `0`), so the time after the secondary baseline is `1 + Y`; the switch is
still at the decision time `1`.

## Main results

* `WeibullProgression.powerMean_true`, `WeibullProgression.powerMean_false`: the power means
  of `1 + Y` are `(3 · 3^k + 7^k)/4` among switchers and `(2^k + 3 · 4^k)/4` among
  non-switchers.
* `WeibullProgression.exp_coef_eq`: at any solution of the intercept and switch scores with
  shape `k ≠ 0`, the fitted factor is
  `exp b₁ = progressionFactor k = ((3 · 3^k + 7^k)/(2^k + 3 · 4^k))^(1/k)`; the fit exists
  (`WeibullProgression.exists_fit`).
* `WeibullProgression.progressionFactor_one`, `WeibullProgression.progressionFactor_two`: the
  factor is `8/7` at `k = 1` and `√(19/13)` at `k = 2`, against `weibullFactor 1 = 6/5` and
  `weibullFactor 2 = 2 √(3/7) = √(12/7)` with the secondary baseline at the switch decision
  (`WeibullProgression.lt_weibullFactor_one`, `WeibullProgression.lt_weibullFactor_two`).
* The truth. The switch doubles the residual survival after the decision time, so the
  structural model holds from the switch time with time ratio `1/2`
  (`WeibullProgression.model_switchTime`), true factor `2`. With the switch counted from
  progression no time ratio fits (`WeibullProgression.not_model_progression`): undoing the
  effect over the whole time from progression would need the factor `3/2` for deteriorated
  switchers and `7/4` for the others. The fitted factor is below `2` at every shape `k > 0`
  (`WeibullProgression.progressionFactor_lt_two`, `WeibullProgression.exp_coef_ne_truth`).
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageCounterexample

namespace WeibullProgression

open SwitchingCounterexamples.TimeDependent

/-- **The countermodel as a two-stage trial with the secondary baseline at progression.** The
secondary baseline is time `0`, the switch is at the decision time `1`, the observed survival
from progression is `1 + Y`, and the untreated survival is `T0 = 1 + Y0`. -/
noncomputable def Mp : TwoStageTrial SwitchingCounterexamples.TimeDependent.Ω where
  R _ := false
  S _ := 0
  X := S
  W _ := decisionTime
  T ω := decisionTime + Y ω
  C _ := 100
  U := T0

theorem time_eq (ω : SwitchingCounterexamples.TimeDependent.Ω) : Mp.T ω - Mp.S ω = 1 + Y ω := by
  simp [Mp, decisionTime]

/-- Each switch group has mass `1/2`. -/
theorem wmass_group (x : Bool) : wmass p (univ ∩ ev Mp.X x) = 1 / 2 := by
  simp only [wmass, ev, univ_inter, sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, Mp, S, switchRule, L1]
  cases x <;> norm_num

/-- The power mean of order `k` of `1 + Y` among switchers: `(3 · 3^k + 7^k) / 4`. -/
theorem powerMean_true (k : ℝ) : Mp.powerMean p univ k true = (3 * 3 ^ k + 7 ^ k) / 4 := by
  rw [TwoStageTrial.powerMean, WeibullBridge.condMean_ev_eq]
  simp only [time_eq, SwitchingCounterexamples.condMean, FiniteDist.expect, FiniteDist.probOf,
    FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, Mp, S, switchRule, L1, Y, Y1, Y0, y0]
  norm_num
  ring

/-- The power mean of order `k` of `1 + Y` among non-switchers: `(2^k + 3 · 4^k) / 4`. -/
theorem powerMean_false (k : ℝ) : Mp.powerMean p univ k false = (2 ^ k + 3 * 4 ^ k) / 4 := by
  rw [TwoStageTrial.powerMean, WeibullBridge.condMean_ev_eq]
  simp only [time_eq, SwitchingCounterexamples.condMean, FiniteDist.expect, FiniteDist.probOf,
    FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, Mp, S, switchRule, L1, Y, Y1, Y0, y0]
  norm_num
  ring

/-- The population target of the Weibull fit with known shape `k` and the secondary baseline
at progression: `((3 · 3^k + 7^k) / (2^k + 3 · 4^k))^(1/k)`. -/
noncomputable def progressionFactor (k : ℝ) : ℝ :=
  ((3 * 3 ^ k + 7 ^ k) / (2 ^ k + 3 * 4 ^ k)) ^ k⁻¹

/-- **The fitted factor with the secondary baseline at progression**: at any solution of the
intercept and switch scores with shape `k ≠ 0`, `exp b₁ = progressionFactor k`. -/
theorem exp_coef_eq {k : ℝ} (hk : k ≠ 0) {b₀ b₁ : ℝ}
    (hfit : Mp.weibullScore₀ p univ k b₀ b₁ = 0 ∧ Mp.weibullScore₁ p univ k b₀ b₁ = 0) :
    Real.exp b₁ = progressionFactor k := by
  have h := Mp.weibull_coef_eq p univ hk (by rw [wmass_group]; norm_num)
    (by rw [wmass_group]; norm_num) hfit
  rw [powerMean_true, powerMean_false, div_div_div_cancel_right₀ four_ne_zero] at h
  have hq : (0 : ℝ) < (3 * 3 ^ k + 7 ^ k) / (2 ^ k + 3 * 4 ^ k) := by positivity
  rw [h, progressionFactor, Real.rpow_def_of_pos hq, div_eq_mul_inv]

/-- `T > S` for every patient. -/
theorem time_pos (ω : SwitchingCounterexamples.TimeDependent.Ω) : Mp.S ω < Mp.T ω := by
  rw [← sub_pos, time_eq]; unfold Y Y1 Y0 y0; split_ifs <;> norm_num

/-- The fit exists at every shape `k ≠ 0`. -/
theorem exists_fit {k : ℝ} (hk : k ≠ 0) :
    ∃ b₀ b₁, Mp.weibullScore₀ p univ k b₀ b₁ = 0 ∧ Mp.weibullScore₁ p univ k b₀ b₁ = 0 :=
  ⟨_, _, Mp.weibullScores_of_shape p univ hk (by rw [wmass_group]; norm_num)
    (by rw [wmass_group]; norm_num) fun ω _ => time_pos ω⟩

/-- At shape `k = 1` the factor is the ratio of means `16/14 = 8/7`. -/
theorem progressionFactor_one : progressionFactor 1 = 8 / 7 := by
  rw [progressionFactor]; norm_num

/-- At shape `k = 2` the factor is `√(76/52) = √(19/13)`. -/
theorem progressionFactor_two : progressionFactor 2 = Real.sqrt (19 / 13) := by
  rw [progressionFactor, Real.sqrt_eq_rpow]
  norm_num

/-- At `k = 1` the factor is below the factor `6/5` of the fit with the secondary baseline at
the switch decision. -/
theorem lt_weibullFactor_one : progressionFactor 1 < weibullFactor 1 := by
  rw [progressionFactor_one, weibullFactor_one]; norm_num

/-- At `k = 2` the factor `√(19/13)` is below `weibullFactor 2 = 2 √(3/7) = √(12/7)`. -/
theorem lt_weibullFactor_two : progressionFactor 2 < weibullFactor 2 := by
  rw [progressionFactor_two, weibullFactor_two]
  have h : 2 * Real.sqrt (3 / 7) = Real.sqrt (12 / 7) := by
    rw [show (12 : ℝ) / 7 = 2 ^ 2 * (3 / 7) by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The factor is below the true `2` at every shape `k > 0`.** -/
theorem progressionFactor_lt_two {k : ℝ} (hk : 0 < k) : progressionFactor k < 2 := by
  have h37 : (3 : ℝ) ^ k < 8 ^ k := Real.rpow_lt_rpow (by norm_num) (by norm_num) hk
  have h34 : (3 : ℝ) ^ k < 4 ^ k := Real.rpow_lt_rpow (by norm_num) (by norm_num) hk
  have h78 : (7 : ℝ) ^ k < 8 ^ k := Real.rpow_lt_rpow (by norm_num) (by norm_num) hk
  have e4 : (2 : ℝ) ^ k * 2 ^ k = 4 ^ k := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have e8 : (2 : ℝ) ^ k * 4 ^ k = 8 ^ k := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hd : 0 < (2 : ℝ) ^ k + 3 * 4 ^ k := by positivity
  have hr : (3 * 3 ^ k + 7 ^ k) / (2 ^ k + 3 * 4 ^ k) < (2 : ℝ) ^ k := by
    rw [div_lt_iff₀ hd, mul_add, e4, mul_left_comm, e8]
    linarith
  have h2 : ((2 : ℝ) ^ k) ^ k⁻¹ = 2 := Real.rpow_rpow_inv (by norm_num) hk.ne'
  have := Real.rpow_lt_rpow (by positivity) hr (inv_pos.2 hk)
  rwa [h2] at this

/-- **The structural model holds from the switch time** with time ratio `1/2`: the switch
doubles the residual survival after the decision time. -/
theorem model_switchTime : Mp.ModelOn univ Mp.W (Real.log (1 / 2)) := by
  intro ω _
  have h2 : Real.exp (Real.log (1 / 2)) = 1 / 2 := Real.exp_log (by norm_num)
  cases hS : S ω
  · rw [Mp.adjusted_of_not_switch _ _ hS]
    simp [Mp, T0, Y, hS]
  · rw [Mp.adjusted_of_switch _ _ hS, h2]
    simp only [Mp, T0, Y, Y1, hS, ite_true]
    ring

/-- **No time ratio fits with the switch counted from progression**: the deteriorated
switcher `(true, 0)` would need `exp ψ = 2/3` and the switcher `(false, 0)` would need
`exp ψ = 4/7`. -/
theorem not_model_progression (ψ : ℝ) : ¬ Mp.ModelOn univ Mp.S ψ := by
  intro h
  have h1 := h (true, 0) (mem_univ _)
  have h2 := h (false, 0) (mem_univ _)
  rw [Mp.adjusted_of_switch _ _ (by decide)] at h1 h2
  simp only [Mp, T0, Y, Y1, Y0, y0, S, switchRule, L1, decisionTime] at h1 h2
  norm_num at h1 h2
  have he : Real.exp ψ = 2 / 3 := by linarith
  rw [he] at h2
  norm_num at h2

/-- **The fitted factor misses the truth**: for every shape `k > 0`, `exp b₁ < 2`, so
`b₁ ≠ -log (1/2)`. -/
theorem exp_coef_ne_truth {k : ℝ} (hk : 0 < k) {b₀ b₁ : ℝ}
    (hfit : Mp.weibullScore₀ p univ k b₀ b₁ = 0 ∧ Mp.weibullScore₁ p univ k b₀ b₁ = 0) :
    Real.exp b₁ < 2 ∧ b₁ ≠ -Real.log (1 / 2) := by
  have hlt : Real.exp b₁ < 2 := exp_coef_eq hk.ne' hfit ▸ progressionFactor_lt_two hk
  refine ⟨hlt, fun h => ?_⟩
  rw [h, Real.exp_neg, Real.exp_log (by norm_num)] at hlt
  norm_num at hlt

end WeibullProgression

end TwoStageCounterexample

end StructuralNested

end CausalInference
