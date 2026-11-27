/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageCounterexamples
public import CausalInference.StructuralNested.TwoStageSwitchTypes

/-!
# Two-stage estimation: the modified method against the standard one

The `Modified` example of `TwoStageCounterexamples` posits the survival without subsequent
treatment `U0`. Here it is derived from structural equations for both subsequent treatments,
and the standard two-stage method is run on the same data.

## Main results

* `TwoStageCounterexample.Modified.U0s`, `TwoStageCounterexample.Modified.Ualts`: the survival
  without subsequent treatment and the survival with the alternative in place of the treatment
  of interest, from Equation (1) with one time ratio per subsequent treatment (`exp θ = 1/3`
  for the treatment of interest, `2/3` for the alternative); they are the latent times of the
  example (`U0s_eq`, `Ualts_eq`), with means `2` (`expect_U0s`) and `7/3` (`expect_Ualts`).
* `TwoStageCounterexample.Modified.Mstd`: the trial as analyzed by the standard method. With a
  pooled parameter the root is `exp ψ = 4/9` (`root_std`), which is neither effect; run within
  each type of subsequent treatment it recovers both (`root_type`, by
  `TwoStageTrial.typeStageOne_eq_zero_iff`), and transforming type by type recovers the mean `2`
  (`typeAdjusted_std`).
* `TwoStageCounterexample.Modified.modified_vs_standard`: the two analyses side by side.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageCounterexample

namespace Modified

/-! ### Structural equations for both subsequent treatments -/

/-- The type of subsequent treatment: `true` for the treatment of interest (patient `2`),
`false` for the alternative one (patient `1`, and patient `0`, who has none). -/
def κ (ω : Ω) : Bool := decide (ω = 2)

/-- The log time ratios of the two subsequent treatments against no subsequent treatment, after
the switch: `exp (θ true) = 1/3` for the treatment of interest, `exp (θ false) = 2/3` for the
alternative one. -/
noncomputable def θ (k : Bool) : ℝ := if k then Real.log (1 / 3) else Real.log (2 / 3)

theorem exp_θ_true : Real.exp (θ true) = 1 / 3 := by
  rw [show θ true = Real.log (1 / 3) from rfl]; exact Real.exp_log (by norm_num)

theorem exp_θ_false : Real.exp (θ false) = 2 / 3 := by
  rw [show θ false = Real.log (2 / 3) from rfl]; exact Real.exp_log (by norm_num)

/-- **The survival without subsequent treatment, from the structural equations**: the time
after the switch is shrunk by the time ratio of the treatment received, Equation (1) from the
switch time; the patient without subsequent treatment is unchanged. -/
noncomputable def U0s (ω : Ω) : ℝ :=
  if ω = 0 then M.T ω else M.W ω + Real.exp (θ (κ ω)) * (M.T ω - M.W ω)

/-- **The survival had the treatment of interest been replaced by the alternative one, from the
structural equations**: for patient `2` the time after the switch is multiplied by the ratio
`exp (θ true - θ false)`; the others are unchanged. -/
noncomputable def Ualts (ω : Ω) : ℝ :=
  if ω = 2 then M.W ω + Real.exp (θ true - θ false) * (M.T ω - M.W ω) else M.T ω

/-- The structural equations give `2` for every patient. -/
theorem U0s_eq : U0s = U0 := by
  funext ω
  fin_cases ω <;> norm_num [U0s, U0, M, κ, exp_θ_true, exp_θ_false]

/-- They give the latent time `Ualt` of the modified method. -/
theorem Ualts_eq : Ualts = Ualt := by
  funext ω
  fin_cases ω <;> norm_num [Ualts, Ualt, M, Real.exp_sub, exp_θ_true, exp_θ_false]

/-- **The mean survival without subsequent treatment is computed**: `E[U0] = 2`. -/
theorem expect_U0s : p.expect U0s = 2 := by
  rw [U0s_eq]; norm_num [FiniteDist.expect, p_apply, U0]

theorem expect_Ualts : p.expect Ualts = 7 / 3 := by
  rw [Ualts_eq]; norm_num [FiniteDist.expect, Fin.sum_univ_three, p_apply, Ualt]

/-! ### The standard two-stage analysis of the same data -/

/-- **The trial as analyzed by the standard method**: every patient who starts a subsequent
treatment is an adjusted switcher, at the switch time `1`, and the latent time is the survival
without subsequent treatment. -/
noncomputable def Mstd : TwoStageTrial Ω where
  R _ := false
  S _ := 1
  X ω := decide (ω ≠ 0)
  W _ := 1
  T := M.T
  C _ := 10
  U := U0s

/-- The standard trial follows the structural model with one parameter per subsequent
treatment. -/
theorem typeModel_std : Mstd.TypeModel Mstd.W κ θ := by
  intro ω
  fin_cases ω <;> simp [Mstd, U0s, M, κ, SwitchingTrial.Tc, TwoStageTrial.toSwitchingTrial,
    TwoStageTrial.treated]

theorem cell_std_true : Mstd.cell univ L true () = {1, 2} := by
  ext ω; fin_cases ω <;> simp [TwoStageTrial.cell, Mstd, L, ev]

theorem cell_std_false : Mstd.cell univ L false () = {0} := by
  ext ω; fin_cases ω <;> simp [TwoStageTrial.cell, Mstd, L, ev]

/-- **The standard method with a pooled parameter returns `exp ψ = 4/9`**, which is neither of
the two effects `1/3` and `2/3`. -/
theorem root_std (ψ : ℝ) :
    Mstd.stageOne p univ L (fun _ => 1) Mstd.W ψ = 0 ↔ Real.exp ψ = 4 / 9 := by
  have hs : Mstd.stageOneSlope p univ L (fun _ => 1) Mstd.W = 9 / 4 := by
    rw [TwoStageTrial.stageOneSlope, Fintype.sum_unique, one_mul, condMean, wsum, wmass,
      show (default : Unit) = () from rfl, cell_std_true]
    norm_num [p_apply, Mstd, M, TwoStageTrial.treated]
  have hi : Mstd.stageOneIntercept p univ L (fun _ => 1) Mstd.W = -1 := by
    rw [TwoStageTrial.stageOneIntercept, Fintype.sum_unique, one_mul, condMean, wsum, wmass,
      condMean, wsum, wmass, show (default : Unit) = () from rfl, cell_std_true, cell_std_false]
    norm_num [p_apply, Mstd, M, TwoStageTrial.treated, TwoStageTrial.baseResid]
  rw [TwoStageTrial.stageOne_eq, hs, hi]
  constructor <;> intro h <;> linarith

/-- At its root, the standard method gives the transformed data the mean `2` of survival
without subsequent treatment (with a single stratum, mean balancing fixes the mean). -/
theorem mean_std : p.expect (Mstd.adjusted Mstd.W (Real.log (4 / 9))) = 2 := by
  simp [FiniteDist.expect, Fin.sum_univ_three, p_apply, Mstd, M, TwoStageTrial.adjusted,
    SwitchingTrial.counterfactual, SwitchingTrial.Tc, TwoStageTrial.toSwitchingTrial,
    TwoStageTrial.treated, Real.exp_log]
  norm_num

/-- The population of each type: the non-switcher and the switcher of that type. -/
theorem typePop_std (k : Bool) :
    Mstd.typePop univ κ k = if k then {0, 2} else {0, 1} := by
  ext ω; cases k <;> fin_cases ω <;> simp [TwoStageTrial.typePop, Mstd, κ]

theorem nuc_type (k : Bool) : Mstd.BaselineNUC p (Mstd.typePop univ κ k) L := fun _ =>
  meanIndepOn_of_const (c := 1) fun ω _ => by
    have := congrFun U0s_eq ω
    simp only [Mstd, this, U0]; norm_num

theorem cell_type (k : Bool) (x : Bool) :
    Mstd.cell (Mstd.typePop univ κ k) L x () =
      if x then (if k then {2} else {1}) else {0} := by
  ext ω; cases k <;> cases x <;> fin_cases ω <;>
    simp [TwoStageTrial.cell, TwoStageTrial.typePop, Mstd, κ, L, ev]

theorem positive_type (k : Bool) :
    Mstd.BaselinePositive p (Mstd.typePop univ κ k) L (fun _ => 1) := by
  intro _ _
  rw [cell_type, cell_type]
  cases k <;> simp [wmass, p_apply]

/-- **The standard method run within each type recovers both effects** (the positive theorem
`TwoStageTrial.typeStageOne_eq_zero_iff`): the root on the alternative switcher and the
non-switcher is `θ false` (`exp = 2/3`), on the switcher to the treatment of interest and the
non-switcher it is `θ true` (`exp = 1/3`). -/
theorem root_type (k : Bool) (ψ : ℝ) :
    Mstd.stageOne p (Mstd.typePop univ κ k) L (fun _ => 1) Mstd.W ψ = 0 ↔ ψ = θ k :=
  Mstd.typeStageOne_eq_zero_iff typeModel_std (nuc_type k) (positive_type k)
    (Mstd.stageOneSlope_pos (fun _ => by norm_num) (positive_type k) (fun ω _ _ => by
      fin_cases ω <;> norm_num [Mstd, M]) (l₀ := ()) (by norm_num)) ψ

/-- Transforming type by type recovers the survival without subsequent treatment, mean `2`. -/
theorem typeAdjusted_std : p.expect (Mstd.typeAdjusted Mstd.W κ θ) = 2 := by
  rw [Mstd.typeAdjusted_eq typeModel_std]; exact expect_U0s

/-- **The two analyses side by side.** On the same data, the modified method returns the effect
of the treatment of interest against the alternative (`exp ψm = 1/2`) and the mean `7/3` of
survival with the alternative in place of the treatment of interest; the standard method with a
pooled parameter returns `exp ψ = 4/9` and the mean `2` of survival without subsequent
treatment; the standard method by type returns `1/3` and `2/3`. -/
theorem modified_vs_standard :
    (∀ ψ, M.stageOne p P L (fun _ => 1) M.W ψ = 0 ↔ ψ = ψm) ∧
      p.expect (M.adjusted M.W ψm) = p.expect Ualts ∧ p.expect Ualts = 7 / 3 ∧
      (∀ ψ, Mstd.stageOne p univ L (fun _ => 1) Mstd.W ψ = 0 ↔ Real.exp ψ = 4 / 9) ∧
      p.expect (Mstd.adjusted Mstd.W (Real.log (4 / 9))) = p.expect U0s ∧
      p.expect U0s = 2 ∧
      Real.exp (θ true) = 1 / 3 ∧ Real.exp (θ false) = 2 / 3 :=
  ⟨root, by rw [estimand_changes.1, expect_Ualts], expect_Ualts, root_std,
    by rw [mean_std, expect_U0s], expect_U0s, exp_θ_true, exp_θ_false⟩

end Modified

end TwoStageCounterexample

end StructuralNested

end CausalInference
