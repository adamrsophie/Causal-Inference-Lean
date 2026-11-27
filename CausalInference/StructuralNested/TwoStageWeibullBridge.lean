/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageWeibullShape
public import CausalInference.StructuralNested.TwoStageWeibullStrata
public import CausalInference.Survival.SwitchingCounterexamples

/-!
# Two-stage estimation: the Weibull fit on the time-dependent confounding countermodel

`SwitchingCounterexamples.TimeDependent.weibullFactor k` is the population target of a Weibull
stage one with known shape on the time-dependent confounding countermodel, a ratio of power
means of the residual survival `Y` after the switch decision. `TwoStageWeibull` proves that the
Weibull fit at any shape returns the truth under mean independence of `(U - S)^k`. This file
puts the countermodel in the two-stage form (`WeibullBridge.Mb`, secondary baseline at the
switch decision) and connects the two.

## Main results

* `WeibullBridge.exp_coef_eq_weibullFactor`: at any solution of the intercept and switch scores
  of `TwoStageTrial.weibullScore₀`, `TwoStageTrial.weibullScore₁` with shape `k ≠ 0`, the fitted
  factor is `exp b₁ = weibullFactor k`; the fit exists (`WeibullBridge.exists_fit`). So the two
  developments describe the same estimator. With the secondary baseline at progression instead
  (as in `TwoStageDelay.DelayConfounded`), the time after the secondary baseline would be
  `1 + Y`, a different estimator, not treated here.
* `WeibullBridge.not_nuc`: the hypothesis of `TwoStageTrial.weibull_coef_eq_neg` that fails is
  the mean independence of `(U - S)^k` and the switch, for every shape `k ≠ 0`: the power means
  of `Y0` are `(3 + 3^k)/4` among switchers and `(1 + 3 · 3^k)/4` among non-switchers
  (`WeibullBridge.condMean_untreated`). The structural model (`WeibullBridge.model`),
  positivity (`WeibullBridge.wmass_group`) and `T > S` (`WeibullBridge.time_pos`) hold.
  Consequently the factor misses the true `2` (`WeibullBridge.weibullFactor_ne_truth`).
* `WeibullBridge.strata_exp_coef`: with one intercept per stratum of the deterioration `L1`,
  measured by the switch decision, mean independence holds within strata
  (`WeibullBridge.nuc_strata`) and the stratified Weibull fit of `TwoStageWeibullStrata` returns
  the true factor `2` at every shape.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageCounterexample

namespace WeibullBridge

open SwitchingCounterexamples.TimeDependent

/-- A conditional mean of `Longitudinal` over a switch group is the conditional mean of
`SwitchingCounterexamples` given the switch value. -/
theorem condMean_ev_eq {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (q : FiniteDist Ω')
    (X : Ω' → Bool) (x : Bool) (f : Ω' → ℝ) :
    Longitudinal.condMean q (univ ∩ ev X x) f =
      SwitchingCounterexamples.condMean q (fun ω => X ω = x) f := by
  simp only [Longitudinal.condMean, SwitchingCounterexamples.condMean, wsum, wmass, ev,
    univ_inter, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob, sum_filter, mul_ite,
    mul_zero]

/-- **The countermodel as a two-stage trial with the secondary baseline at the switch
decision.** The secondary baseline and the switch are at the decision time `1`, the observed
survival is `1 + Y`, the untreated survival is `T0 = 1 + Y0`, so the time after the secondary
baseline is the residual survival `Y` of the countermodel. -/
noncomputable def Mb : TwoStageTrial SwitchingCounterexamples.TimeDependent.Ω where
  R _ := false
  S _ := decisionTime
  X := S
  W _ := decisionTime
  T ω := decisionTime + Y ω
  C _ := 100
  U := T0

theorem time_eq (ω : SwitchingCounterexamples.TimeDependent.Ω) : Mb.T ω - Mb.S ω = Y ω := by
  simp [Mb]

theorem untreated_eq (ω : SwitchingCounterexamples.TimeDependent.Ω) :
    Mb.U ω - Mb.S ω = Y0 ω := by
  simp [Mb, T0]

/-- **The power means of the fit are those of `weibullFactor`.** -/
theorem powerMean_eq (k : ℝ) (x : Bool) :
    Mb.powerMean p univ k x =
      SwitchingCounterexamples.condMean p (fun ω => S ω = x) (fun ω => Y ω ^ k) := by
  rw [TwoStageTrial.powerMean, ← condMean_ev_eq]
  simp only [time_eq]
  rfl

/-- Each switch group has mass `1/2`. -/
theorem wmass_group (x : Bool) : wmass p (univ ∩ ev Mb.X x) = 1 / 2 := by
  simp only [wmass, ev, univ_inter, sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, Mb, S, switchRule, L1]
  cases x <;> norm_num

/-- **The fitted acceleration factor of the Weibull fit at the shape `k` is `weibullFactor k`**:
at any solution of the intercept and switch scores, `exp b₁ = weibullFactor k`. The two
developments describe the same estimator, with the secondary baseline at the switch
decision. -/
theorem exp_coef_eq_weibullFactor {k : ℝ} (hk : k ≠ 0) {b₀ b₁ : ℝ}
    (hfit : Mb.weibullScore₀ p univ k b₀ b₁ = 0 ∧ Mb.weibullScore₁ p univ k b₀ b₁ = 0) :
    Real.exp b₁ = weibullFactor k := by
  have h := Mb.weibull_coef_eq p univ hk (by rw [wmass_group]; norm_num)
    (by rw [wmass_group]; norm_num) hfit
  have hq : 0 < Mb.powerMean p univ k true / Mb.powerMean p univ k false := by
    rw [powerMean_eq, powerMean_eq, condMean_rpow_switchers, condMean_rpow_stayers]
    positivity
  rw [h, weibullFactor, ← powerMean_eq, ← powerMean_eq, Real.rpow_def_of_pos hq, div_eq_mul_inv]

/-- **The structural model holds in the baseline form** with time ratio `1/2`. -/
theorem model : Mb.ModelOn univ Mb.S (Real.log (1 / 2)) := by
  intro ω _
  have h2 : Real.exp (Real.log (1 / 2)) = 1 / 2 := Real.exp_log (by norm_num)
  cases hS : S ω
  · rw [Mb.adjusted_of_not_switch _ _ hS]
    simp [Mb, T0, Y, hS]
  · rw [Mb.adjusted_of_switch _ _ hS, h2]
    simp only [Mb, T0, Y, Y1, hS, ite_true]
    ring

/-- `T > S` for every patient. -/
theorem time_pos (ω : SwitchingCounterexamples.TimeDependent.Ω) : Mb.S ω < Mb.T ω := by
  rw [← sub_pos, time_eq]; unfold Y Y1 Y0 y0; split_ifs <;> norm_num

/-- The fit exists at every shape `k ≠ 0`. -/
theorem exists_fit {k : ℝ} (hk : k ≠ 0) :
    ∃ b₀ b₁, Mb.weibullScore₀ p univ k b₀ b₁ = 0 ∧ Mb.weibullScore₁ p univ k b₀ b₁ = 0 :=
  ⟨_, _, Mb.weibullScores_of_shape p univ hk (by rw [wmass_group]; norm_num)
    (by rw [wmass_group]; norm_num) fun ω _ => time_pos ω⟩

/-- The power means of the untreated residual survival in the switch groups:
`E[Y0^k | switch] = (3 + 3^k) / 4`, `E[Y0^k | no switch] = (1 + 3 · 3^k) / 4`. -/
theorem condMean_untreated (k : ℝ) :
    Longitudinal.condMean p (univ ∩ ev Mb.X true) (fun ω => (Mb.U ω - Mb.S ω) ^ k) =
        (3 + 3 ^ k) / 4 ∧
      Longitudinal.condMean p (univ ∩ ev Mb.X false) (fun ω => (Mb.U ω - Mb.S ω) ^ k) =
        (1 + 3 * 3 ^ k) / 4 := by
  simp only [untreated_eq]
  constructor <;>
  · rw [condMean_ev_eq]
    simp only [SwitchingCounterexamples.condMean, FiniteDist.expect, FiniteDist.probOf,
      FiniteDist.prob, Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
      FiniteDist.prod_apply, FiniteDist.uniform_apply, Mb, S, switchRule, L1, Y0, y0]
    norm_num
    ring

/-- **The hypothesis of `weibull_coef_eq_neg` that fails**: for every shape `k ≠ 0`, the
`k`-th power of the untreated time after the secondary baseline is not mean independent of the
switch. The structural model (`model`), positivity (`wmass_group`) and `T > S` (`time_pos`)
hold. -/
theorem not_nuc {k : ℝ} (hk : k ≠ 0) :
    ¬ MeanIndepOn p univ (ev Mb.X true) fun ω => (Mb.U ω - Mb.S ω) ^ k := by
  intro h
  have heq := Mb.condMean_switch_eq h (by rw [wmass_group]; norm_num)
    (by rw [wmass_group]; norm_num)
  rw [(condMean_untreated k).1, (condMean_untreated k).2] at heq
  have h1 : (3 : ℝ) ^ k = 1 := by linarith
  rcases lt_or_gt_of_ne hk with h | h
  · exact absurd h1 (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) h).ne
  · exact absurd h1 (Real.one_lt_rpow (by norm_num) h).ne'

/-- Consistent with `weibull_coef_eq_neg`: had the hypothesis held, the fitted factor would be
`exp (-log (1/2)) = 2`; here it is `weibullFactor k < 2` for `k > 0`. -/
theorem weibullFactor_ne_truth {k : ℝ} (hk : 0 < k) {b₀ b₁ : ℝ}
    (hfit : Mb.weibullScore₀ p univ k b₀ b₁ = 0 ∧ Mb.weibullScore₁ p univ k b₀ b₁ = 0) :
    Real.exp b₁ < 2 ∧ b₁ ≠ -Real.log (1 / 2) := by
  have he := exp_coef_eq_weibullFactor hk.ne' hfit
  have hlt : Real.exp b₁ < 2 := he ▸ weibullFactor_lt_two k hk
  refine ⟨hlt, fun h => ?_⟩
  rw [h, Real.exp_neg, Real.exp_log (by norm_num)] at hlt
  norm_num at hlt

/-! ### With the deterioration as a stratum the Weibull fit is unbiased -/

/-- Within each stratum of `L1` the untreated residual survival is constant, so mean
independence holds within strata. -/
theorem nuc_strata (k : ℝ) (l : Bool) :
    MeanIndepOn p (univ ∩ ev L1 l) (ev Mb.X true) fun ω => (Mb.U ω - Mb.S ω) ^ k := by
  have hc : ∀ ω ∈ univ ∩ ev L1 l, (Mb.U ω - Mb.S ω) ^ k = y0 l ^ k := fun ω hω => by
    rw [untreated_eq]
    simp only [mem_inter, mem_ev, L1] at hω
    simp [Y0, hω.2]
  rw [MeanIndepOn, wsum_congr hc, wsum_congr fun ω hω => hc ω (mem_inter.1 hω).1, wsum_const,
    wsum_const]
  ring

/-- Both switch groups have positive mass in each stratum of `L1`. -/
theorem pos_strata (l : Bool) :
    0 < wmass p (Mb.cell univ L1 true l) ∧ 0 < wmass p (Mb.cell univ L1 false l) := by
  simp only [Mb.wmass_cell_univ]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, Mb, S, switchRule, L1]
  cases l <;> norm_num

/-- **With one intercept per stratum of the deterioration `L1`, the Weibull fit recovers the
true time ratio**: the fitted factor is `exp b₁ = 2` at every shape `k > 0`, by
`weibullStrata_coef_eq_neg`. Here `L1` is a covariate at the secondary baseline because the
secondary baseline is the switch decision. -/
theorem strata_exp_coef {k : ℝ} (hk : 0 < k) {a : Bool → ℝ} {b₁ : ℝ}
    (hfit : Mb.WeibullStrataFit p univ L1 k a b₁) : Real.exp b₁ = 2 := by
  have hb := Mb.weibullStrata_coef_eq_neg hk model (nuc_strata k) (fun l _ => pos_strata l)
    ⟨true, (pos_strata true).1.trans_le (wmass_mono p.nonneg inter_subset_left)⟩
    (fun ω _ => time_pos ω) hfit
  rw [hb, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

end WeibullBridge

end TwoStageCounterexample

end StructuralNested

end CausalInference
