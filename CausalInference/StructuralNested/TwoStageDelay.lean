/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageCounterexamples
public import CausalInference.Survival.SwitchingCounterexamples

/-!
# Two-stage estimation: the delay between the secondary baseline and the switch

TSD 16 (Sections 3.2.4 and 6) says that the potential bias of the two-stage method grows with
the delay between the secondary baseline and the switch. This file gives two explicit families
indexed by the delay `d`, as `TwoStageTrial`s. Each is one family that illustrates the claim;
neither is a general monotonicity law.

## The baseline form (`DelayBaseline`)

The secondary baseline is time `0` and switchers switch at time `d`; the switch doubles the
survival after the switch, and there is no confounding. Equation (1) holds from the switch time,
so stage one from the switch time recovers the true time ratio `1/2` at every delay
(`DelayBaseline.root_W`). Stage one in the baseline form, which applies the time ratio to all the
time after the secondary baseline, returns `exp ψ = (d + 3) / (d + 6)` (`DelayBaseline.root_S`),
with bias `d / (2 (d + 6))` (`DelayBaseline.baselineRatio_sub`): zero at delay zero
(`DelayBaseline.delayRootBias_zero`) and strictly increasing in the delay
(`DelayBaseline.delayRootBias_strictMonoOn`).

## Time-dependent confounding (`DelayConfounded`)

The delay family of `SwitchingCounterexamples.TimeDependent` (where the covariate measured at
the switch decision carries prognosis that the record at progression does not) is a two-stage
trial (`DelayConfounded.M`) that follows the structural model from the switch time
(`DelayConfounded.model_W`). Its stage-one equation, adjusted for the record at progression, is
the mean-balancing equation of that file (`DelayConfounded.stageOne_iff`), so its root is
`1 / delayFactor d` (`DelayConfounded.root`), and the bias of the adjusted mean is
`d (2 - d) / (3 - d)` (`DelayConfounded.bias`), zero at delay zero and strictly increasing on
`[0, 1]` by the results of that file.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageCounterexample

/-! ### The baseline form: a family indexed by the delay -/

namespace DelayBaseline

/-- A point `(h, x)`: the prognosis and the switch, independent and uniform. -/
abbrev Ω := Bool × Bool

/-- Uniform over the four points. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform

/-- Every point has mass `1/4`. -/
theorem p_apply (ω : Ω) : p ω = 1 / 4 := by
  simp [p, FiniteDist.uniform_apply, Fintype.card_prod]

/-- The untreated residual survival after the switch time: `2` or `4` according to the
prognosis. -/
noncomputable def r (ω : Ω) : ℝ := if ω.1 then 2 else 4

/-- **The trial with delay `d`**: the secondary baseline is time `0`, switchers switch at time
`d`, and the switch doubles the survival after the switch (time ratio `1/2`). Everybody lives
past `d`. -/
noncomputable def M (d : ℝ) : TwoStageTrial Ω where
  R _ := false
  S _ := 0
  X ω := ω.2
  W _ := d
  T ω := if ω.2 then d + 2 * r ω else d + r ω
  C _ := 100
  U ω := d + r ω

/-- No covariate: a single stratum. -/
def L (_ : Ω) : Unit := ()

/-- The true log time ratio, `exp ψs = 1/2`. -/
noncomputable def ψs : ℝ := Real.log (1 / 2)

/-- The true time ratio is `1/2`. -/
theorem exp_ψs : Real.exp ψs = 1 / 2 := Real.exp_log (by norm_num)

/-- The structural model holds from the switch time (Equation (1)) at every delay. -/
theorem model_W (d : ℝ) : (M d).ModelOn univ (M d).W ψs := by
  rintro ⟨h, x⟩ _
  cases x <;> simp [M, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
    TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψs]

/-- Switching happens at or after the secondary baseline for a nonnegative delay. -/
theorem switchAfterBaseline {d : ℝ} (hd : 0 ≤ d) : (M d).SwitchAfterBaseline := by
  rintro ⟨h, x⟩ hx
  simp only [M] at hx ⊢
  subst hx
  refine ⟨hd, ?_⟩
  cases h <;> simp [r]

/-- No unmeasured confounding holds at every delay: the prognosis is independent of the
switch. -/
theorem nuc (d : ℝ) : (M d).BaselineNUC p univ L := by
  intro l
  rw [MeanIndepOn, show univ ∩ ev L l ∩ ev (M d).X true = (M d).cell univ L true l from rfl,
    TwoStageTrial.wsum_cell_univ, TwoStageTrial.wmass_cell_univ,
    TwoStageTrial.wsum_stratum_univ, TwoStageTrial.wmass_stratum_univ]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, M, L, p_apply, r]
  norm_num
  ring

/-- Positivity: both arms of the single stratum have mass `1/2`. -/
theorem positive (d : ℝ) : (M d).BaselinePositive p univ L (fun _ => 1) := by
  intro l _
  simp only [TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p_apply]

/-- **With Equation (1) from the switch time, stage one recovers the true parameter at every
delay** (`TwoStageTrial.stageOne_eq_zero`). -/
theorem root_W (d : ℝ) (ψ : ℝ) :
    (M d).stageOne p univ L (fun _ => 1) (M d).W ψ = 0 ↔ ψ = ψs :=
  (M d).stageOne_eq_zero_iff ((M d).stageOne_eq_zero (model_W d) (nuc d) (positive d))
    ((M d).stageOneSlope_pos (fun _ => by norm_num) (positive d) (fun ω _ hX => by
      rcases ω with ⟨h, x⟩
      simp only [M] at hX ⊢
      subst hX
      cases h <;> simp [r]) (l₀ := ()) (by norm_num)) ψ

/-- The time ratio returned by the baseline form at delay `d`: `(d + 3) / (d + 6)`. -/
noncomputable def baselineRatio (d : ℝ) : ℝ := (d + 3) / (d + 6)

/-- **The stage-one root of the baseline form at delay `d`**: `exp ψ = (d + 3) / (d + 6)`. -/
theorem root_S {d : ℝ} (hd : 0 ≤ d) (ψ : ℝ) :
    (M d).stageOne p univ L (fun _ => 1) (M d).S ψ = 0 ↔ Real.exp ψ = baselineRatio d := by
  have hs : (M d).stageOneSlope p univ L (fun _ => 1) (M d).S = d + 6 := by
    simp only [TwoStageTrial.stageOneSlope, condMean, TwoStageTrial.wsum_cell_univ,
      TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [M, p_apply, r, TwoStageTrial.treated]
    norm_num
    ring
  have hi : (M d).stageOneIntercept p univ L (fun _ => 1) (M d).S = -(d + 3) := by
    simp only [TwoStageTrial.stageOneIntercept, condMean, TwoStageTrial.wsum_cell_univ,
      TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [M, p_apply, r, TwoStageTrial.treated, TwoStageTrial.baseResid]
    norm_num
    ring
  have h6 : d + 6 ≠ 0 := by linarith
  rw [TwoStageTrial.stageOne_eq, hs, hi, baselineRatio, eq_div_iff h6]
  constructor <;> intro h <;> linarith

/-- The bias of the time ratio returned by the baseline form: `d / (2 (d + 6))`. -/
noncomputable def delayRootBias (d : ℝ) : ℝ := d / (2 * (d + 6))

/-- The bias is the returned ratio minus the true ratio `exp ψs = 1/2`. -/
theorem baselineRatio_sub {d : ℝ} (hd : 0 ≤ d) :
    baselineRatio d - Real.exp ψs = delayRootBias d := by
  have h6 : d + 6 ≠ 0 := by linarith
  rw [baselineRatio, exp_ψs, delayRootBias]
  field_simp
  ring

/-- **No bias at delay zero.** -/
theorem delayRootBias_zero : delayRootBias 0 = 0 := by simp [delayRootBias]

/-- **The bias grows strictly with the delay.** -/
theorem delayRootBias_strictMonoOn : StrictMonoOn delayRootBias (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  rw [delayRootBias, delayRootBias, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end DelayBaseline

/-! ### The delay family with time-dependent confounding as a two-stage trial -/

namespace DelayConfounded

open SwitchingCounterexamples.TimeDependent

/-- The residual survival after the decision with the switch effect undone by the factor `ψ`,
`SwitchingCounterexamples.TimeDependent.untreatedTime`. -/
noncomputable abbrev uT (ψ : ℝ) : SwitchingCounterexamples.TimeDependent.Ω → ℝ :=
  SwitchingCounterexamples.TimeDependent.untreatedTime ψ

/-- **The delay family of `SwitchingCounterexamples.TimeDependent` as a two-stage trial.** The
secondary baseline (progression) is time `0`, the switch decision is at the delay `d`, the
observed survival is `d + Y`, and the untreated survival is `d + Y0` (`T0At d`). -/
noncomputable def M (d : ℝ) : TwoStageTrial SwitchingCounterexamples.TimeDependent.Ω where
  R _ := false
  S _ := 0
  X := S
  W _ := d
  T ω := d + Y ω
  C _ := 100
  U := T0At d

/-- The structural model holds from the switch time with time ratio `1/2`. -/
theorem model_W (d : ℝ) : (M d).ModelOn univ (M d).W (Real.log (1 / 2)) := by
  intro ω _
  have h2 : Real.exp (Real.log (1 / 2)) = 1 / 2 := Real.exp_log (by norm_num)
  cases hS : S ω
  · simp [M, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
      TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, hS, T0At, Y]
  · simp only [M, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
      TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, hS, ite_true, T0At, Y, Y1, h2]
    ring

/-- The transformation from the switch time with log time ratio `- log ψ` is the second-stage
time `adjustedTimeAt d ψ` of the family. -/
theorem adjusted_eq (d : ℝ) {ψ : ℝ} (hψ : 0 < ψ) (ω : SwitchingCounterexamples.TimeDependent.Ω) :
    (M d).adjusted (M d).W (-Real.log ψ) ω = adjustedTimeAt d ψ ω := by
  have he : Real.exp (-Real.log ψ) = ψ⁻¹ := by rw [Real.exp_neg, Real.exp_log hψ]
  cases hS : S ω
  · simp [M, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
      TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, hS, adjustedTimeAt,
      SwitchingCounterexamples.TimeDependent.untreatedTime]
  · simp [M, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
      TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, hS, adjustedTimeAt,
      SwitchingCounterexamples.TimeDependent.untreatedTime, he, div_eq_inv_mul]

/-- The conditional means of the two layers agree on the switch groups. -/
theorem condMean_eq_condMean (q : FiniteDist SwitchingCounterexamples.TimeDependent.Ω)
    (x : Bool) (f : SwitchingCounterexamples.TimeDependent.Ω → ℝ) :
    Longitudinal.condMean q ((M 0).cell univ L0 x ()) f =
      SwitchingCounterexamples.condMean q (fun ω => S ω = x) f := by
  have hs : (M 0).cell univ L0 x () = univ.filter fun ω => S ω = x := by
    ext ω; simp [TwoStageTrial.cell, M, L0]
  rw [Longitudinal.condMean, SwitchingCounterexamples.condMean, hs, wsum, wmass]
  congr 1
  · rw [FiniteDist.expect, sum_filter]
    exact sum_congr rfl fun ω _ => by split_ifs <;> simp

/-- **Stage one of the two-stage trial is the stage one of the family.** For a factor
`ψ > 0`, the stage-one equation from the switch time, with the record at progression, at the
log time ratio `- log ψ` vanishes exactly when the mean-balancing equation of
`SwitchingCounterexamples.TimeDependent.delay_stage_one_root` holds; so its root is
`exp ψ' = 1 / delayFactor d`. -/
theorem stageOne_iff (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) {ψ : ℝ} (hψ : 0 < ψ) :
    (M d).stageOne (pd d hd) univ L0 (fun _ => 1) (M d).W (-Real.log ψ) = 0 ↔
      SwitchingCounterexamples.condMean (pd d hd) (fun ω => S ω = true) (uT ψ) =
        SwitchingCounterexamples.condMean (pd d hd) (fun ω => S ω = false) (uT ψ) := by
  have hc : ∀ x, (M d).cell univ L0 x () = (M 0).cell univ L0 x () := fun _ => rfl
  have hr : ∀ ω, (M d).resid (M d).W (-Real.log ψ) ω = d + uT ψ ω := fun ω => by
    rw [TwoStageTrial.resid, adjusted_eq d hψ ω, adjustedTimeAt]
    simp [M]
  have hm : ∀ x, 0 < wmass (pd d hd) ((M d).cell univ L0 x ()) := by
    intro x
    rw [TwoStageTrial.wmass_cell_univ]
    cases x <;>
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, pd,
        deteriorationLaw, FiniteDist.prod_apply, FiniteDist.uniform_apply, M, S, switchRule, L1,
        L0] <;> norm_num <;> linarith [hd.1, hd.2]
  have hcm : ∀ x, Longitudinal.condMean (pd d hd) ((M d).cell univ L0 x ())
      ((M d).resid (M d).W (-Real.log ψ)) =
      d + SwitchingCounterexamples.condMean (pd d hd) (fun ω => S ω = x) (uT ψ) := by
    intro x
    rw [TwoStageTrial.condMean_congr (g := fun ω => (fun _ => d) ω + 1 * uT ψ ω)
      (fun ω _ => by rw [hr, one_mul]), TwoStageTrial.condMean_add_mul, one_mul]
    have hconst : Longitudinal.condMean (pd d hd) ((M d).cell univ L0 x ()) (fun _ => d) = d := by
      rw [Longitudinal.condMean, wsum_const, mul_div_cancel_left₀ d (hm x).ne']
    rw [hconst, hc, condMean_eq_condMean]
  rw [TwoStageTrial.stageOne, Fintype.sum_unique, one_mul, show (default : Unit) = () from rfl,
    hcm, hcm]
  constructor <;> intro h <;> linarith

/-- The stage-one factor of the family is positive. -/
theorem delayFactor_pos {d : ℝ} (hd : 0 ≤ d ∧ d ≤ 1) : 0 < delayFactor d := by
  rw [delayFactor]
  exact div_pos (by linarith [hd.2]) (mul_pos (by linarith [hd.1]) (by linarith [hd.2]))

/-- **The stage-one root of the family as a two-stage trial**: from the switch time, with the
record at progression, the root is `exp ψ' = 1 / delayFactor d`, unique. -/
theorem root (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) (ψ' : ℝ) :
    (M d).stageOne (pd d hd) univ L0 (fun _ => 1) (M d).W ψ' = 0 ↔
      Real.exp ψ' = (delayFactor d)⁻¹ := by
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ, 0 < ψ ∧ ψ' = -Real.log ψ :=
    ⟨Real.exp (-ψ'), Real.exp_pos _, by rw [Real.log_exp, neg_neg]⟩
  rw [stageOne_iff d hd hψ, delay_stage_one_root d hd ψ hψ.ne', Real.exp_neg, Real.exp_log hψ,
    inv_inj]

/-- **The bias of the adjusted mean of the two-stage trial is `delayBias d`**, which is `0` at
delay `0` (`SwitchingCounterexamples.TimeDependent.delay_zero`) and strictly increasing on
`[0, 1]` (`SwitchingCounterexamples.TimeDependent.delayBias_strictMonoOn`). -/
theorem bias (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) :
    (pd d hd).expect ((M d).adjusted (M d).W (-Real.log (delayFactor d))) -
      (pd d hd).expect (M d).U = delayBias d := by
  rw [show (M d).adjusted (M d).W (-Real.log (delayFactor d)) = adjustedTimeAt d (delayFactor d)
    from funext (adjusted_eq d (delayFactor_pos hd))]
  exact delay_bias d hd

end DelayConfounded

end TwoStageCounterexample

end StructuralNested

end CausalInference
