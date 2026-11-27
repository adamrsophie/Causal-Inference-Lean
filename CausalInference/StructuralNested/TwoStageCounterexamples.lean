/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStage
public import CausalInference.StructuralNested.TwoStageGEstimation

/-!
# Two-stage estimation: countermodels and variants

Finite models (`CausalInference.Basic.FiniteDistribution`) for the two-stage method of
`CausalInference.StructuralNested.TwoStage`. In each countermodel one assumption fails and the
others are checked in Lean.

## Main results

* Unmeasured confounding at the secondary baseline, `Unmeasured`: a measured covariate `l` and
  an unmeasured prognosis `h` at the secondary baseline; the switch depends on `h`. The
  structural model (`model`, time ratio `1/2`), switching at the secondary baseline
  (`switchAfterBaseline`) and positivity (`positive`) hold; no unmeasured confounding given `l`
  fails (`not_nuc`). The stage-one root is `exp ψ = 1/3` (`root`), and the transformed control
  arm has mean `2` against the untreated mean `5/2` (`biased`). With `h` measured, the general
  theorem gives the true root (`root_LH`).
* Heterogeneous effects among switchers, `Heterogeneous`: the switch doubles the residual
  survival (time ratio `1/2`) of switchers with `l = true` and has no effect for the others;
  no single parameter satisfies the structural model (`no_common_model`), while no unmeasured
  confounding, positivity and the timing hold. The stage-one root is `exp ψ = 4/5` (`root`) and
  the transformed control arm has mean `43/20` against `2` (`biased`). The switch proportion
  varies between the strata, which the equal stratum weights do not follow; this is where the
  bias of the mean comes from in this model.
* Switching before the secondary baseline, `BeforeBaseline`: switchers switch at time `0`, the
  secondary baseline is time `1`. The structural model from the switch time, no unmeasured
  confounding and positivity hold; `not_switchAfterBaseline`. Shrinking the time after the
  secondary baseline is wrong even at the true parameter (`adjusted_S_true`), its stage-one root
  is `exp ψ = 2/5` (`root`) and the adjusted survival at time `2` is `3/4` against `1/2`
  (`biased`). With Equation (1) applied from the switch time the identity of `TwoStage` does
  not use the timing assumption, and here gives the true root (`root_W`): in this model the
  secondary baseline and the covariates at it are not affected by the earlier switch, which is
  what the assumption protects against in general.
* Weighting instead of recensoring (TSD 24, Section 4.2.3.1), `Weighting`, on a discrete clock
  after the secondary baseline (natural number times, the layer of `Survival.IPCW`): the
  untreated time `Ud` depends on a covariate `l` that also drives the switch, and the
  transformed censoring time `Dd` is half the follow-up for switchers. Censoring at `Dd` is
  informative: the hazard at time `2` of the censored transformed data is `5/12` (`naive`), the
  untreated hazard is `1/2` (`hazard_two`). Inverse probability of censoring weights given `l`
  (no unmeasured confounding of `Dd` given `l`, `nuc`, and positivity, `pos`) give `1/2`
  (`weighted`, by `Survival.IPCW.weightedHazard_ipcWeight`); recensoring gives `1/2` as well
  (`recensored`). (Remark, not proved here: a weight model conditioning on the switch and
  the follow-up, which determine `Dd`, would give probabilities of remaining uncensored equal to
  `0` or `1`.)
* The modified method with the switch time as secondary baseline (TSD 24, Section 4.2.3.1,
  Ouwens et al.), `Modified`: non-switchers are excluded and the switchers to the treatment of
  interest are compared with the switchers to an alternative treatment. Stage one identifies
  the effect against the alternative treatment (`root`, `exp ψ = 1/2`), and the transformed data
  have the mean `7/3` of survival had the treatment of interest been replaced by the
  alternative, not the mean `2` of survival without subsequent treatment (`estimand_changes`).

## Scope

The weighting result is a discrete-time instance: `Survival.IPCW` has natural number times,
while the transformed times `B + exp ψ (T - B)` of `TwoStage` are real, so a general statement
joining the two layers needs a real-time version of the weighting identities (or a
discretization of the transformed times), which does not exist in the library. Time-dependent
confounding between the secondary baseline and the switch is
`SwitchingCounterexamples.TimeDependent` in
`CausalInference.Survival.SwitchingCounterexamples`.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014): Section 3.2.4.
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to TSD 16*
  (2024): Section 4.2.3 and Section 4.2.3.1.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageCounterexample

/-! ### Unmeasured confounding at the secondary baseline -/

namespace Unmeasured

/-- A point `(l, h, x)`: the measured covariate `l`, the unmeasured prognosis `h`, the switch
`x`. -/
abbrev Ω := Bool × Bool × Bool

/-- `l` and `h` independent and uniform; a patient with poor prognosis (`h = true`) switches
with probability `3/4`, another with probability `1/4`. -/
noncomputable def p : FiniteDist Ω where
  mass ω := if ω.2.2 = ω.2.1 then 3 / 16 else 1 / 16
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]; norm_num

/-- The indicator of a Boolean as a real number. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- The untreated residual survival after the secondary baseline: `1 + l + 2 h`. -/
noncomputable def u (ω : Ω) : ℝ := 1 + ind ω.1 + 2 * ind ω.2.1

/-- The trial: everybody is in the control arm, the secondary baseline is time `0`, switchers
switch at the secondary baseline and the switch doubles their residual survival. -/
noncomputable def M : TwoStageTrial Ω where
  R _ := false
  S _ := 0
  X ω := ω.2.2
  W _ := 0
  T ω := if ω.2.2 then 2 * u ω else u ω
  C _ := 10
  U := u

/-- The measured covariate. -/
def L (ω : Ω) : Bool := ω.1

/-- The true parameter: `exp ψs = 1/2`. -/
noncomputable def ψs : ℝ := Real.log (1 / 2)

theorem exp_ψs : Real.exp ψs = 1 / 2 := Real.exp_log (by norm_num)

theorem model : M.ModelOn univ M.S ψs := by
  intro ω _
  rcases ω with ⟨l, h, x⟩
  cases x <;> simp [M, TwoStageTrial.adjusted, SwitchingTrial.counterfactual,
    SwitchingTrial.Tc, TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψs]

theorem slope : M.stageOneSlope p univ L (fun _ => 1 / 2) M.S = 6 := by
  simp only [TwoStageTrial.stageOneSlope, condMean, TwoStageTrial.wsum_cell_univ,
    TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, L, p, u, ind, TwoStageTrial.treated]
  norm_num

theorem intercept : M.stageOneIntercept p univ L (fun _ => 1 / 2) M.S = -2 := by
  simp only [TwoStageTrial.stageOneIntercept, condMean, TwoStageTrial.wsum_cell_univ,
    TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, L, p, u, ind, TwoStageTrial.treated, TwoStageTrial.baseResid]
  norm_num

/-- Positivity: every stratum of `L` has switchers and non-switchers. -/
theorem positive : M.BaselinePositive p univ L (fun _ => 1 / 2) := by
  intro l _
  simp only [TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  cases l <;> simp [M, L, p] <;> norm_num

/-- Switching happens at the secondary baseline. -/
theorem switchAfterBaseline : M.SwitchAfterBaseline := by
  rintro ⟨l, h, x⟩ _
  refine ⟨le_rfl, ?_⟩
  cases l <;> cases h <;> cases x <;> simp [M, u, ind] <;> norm_num

/-- **No unmeasured confounding fails given the measured covariate**: in the stratum `l = false`
the untreated residual survival is not mean independent of the switch. -/
theorem not_nuc : ¬ M.BaselineNUC p univ L := by
  intro h
  have := h false
  rw [MeanIndepOn, show univ ∩ ev L false ∩ ev M.X true = M.cell univ L true false from rfl,
    TwoStageTrial.wsum_cell_univ, TwoStageTrial.wmass_cell_univ,
    TwoStageTrial.wsum_stratum_univ, TwoStageTrial.wmass_stratum_univ] at this
  simp [Fintype.sum_prod_type, M, L, p, u, ind] at this
  norm_num at this

/-- **The stage-one root is wrong**: the equation balanced within the strata of the measured
covariate has the unique root `exp ψ = 1/3`, while the true time ratio is `1/2`. -/
theorem root (ψ : ℝ) : M.stageOne p univ L (fun _ => 1 / 2) M.S ψ = 0 ↔ Real.exp ψ = 1 / 3 := by
  rw [TwoStageTrial.stageOne_eq, intercept, slope]
  constructor <;> intro h <;> linarith

/-- The covariates measured and unmeasured together. -/
def LH (ω : Ω) : Bool × Bool := (ω.1, ω.2.1)

/-- With the prognosis measured, no unmeasured confounding holds. -/
theorem nuc_LH : M.BaselineNUC p univ LH := fun l =>
  meanIndepOn_of_const (c := 1 + ind l.1 + 2 * ind l.2) fun ω hω => by
    have : LH ω = l := mem_ev.1 (mem_inter.1 hω).2
    simp [M, u, ← this, LH]

theorem positive_LH : M.BaselinePositive p univ LH (fun _ => 1 / 4) := by
  rintro ⟨l, h⟩ _
  simp only [TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  cases l <;> cases h <;> simp [M, LH, p]

/-- **With the prognosis measured, stage one recovers the true parameter** as the unique root
(`TwoStageTrial.stageOne_eq_zero`, `TwoStageTrial.stageOne_eq_zero_iff`). -/
theorem root_LH (ψ : ℝ) : M.stageOne p univ LH (fun _ => 1 / 4) M.S ψ = 0 ↔ ψ = ψs :=
  M.stageOne_eq_zero_iff (M.stageOne_eq_zero model nuc_LH positive_LH)
    (M.stageOneSlope_pos (fun _ => by norm_num) positive_LH (fun ω _ hX => by
      rcases ω with ⟨l, h, x⟩
      cases l <;> cases h <;> cases x <;> simp_all [M, u, ind] <;> norm_num)
      (l₀ := (true, true)) (by norm_num)) ψ

/-- The stage-one root of the measured-covariate analysis. -/
noncomputable def ψhat : ℝ := Real.log (1 / 3)

theorem exp_ψhat : Real.exp ψhat = 1 / 3 := Real.exp_log (by norm_num)

/-- **The adjusted comparison is biased**: the mean of the transformed control arm at the
stage-one root is `2`, while the untreated mean is `5/2`. -/
theorem biased :
    p.expect (M.adjusted M.S ψhat) = 2 ∧ p.expect M.U = 5 / 2 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p, u, ind, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
    TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψhat]
  norm_num

end Unmeasured

/-! ### Heterogeneous effects among switchers -/

namespace Heterogeneous

/-- A point `(l, x)`: the measured covariate and the switch. -/
abbrev Ω := Bool × Bool

/-- `l` uniform; a patient with `l = true` switches with probability `3/4`, another with
probability `1/4`. -/
noncomputable def p : FiniteDist Ω where
  mass ω := if ω.2 = ω.1 then 3 / 8 else 1 / 8
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]; norm_num

/-- The untreated residual survival: `1` if `l = true`, `3` otherwise. -/
noncomputable def u (ω : Ω) : ℝ := if ω.1 then 1 else 3

/-- The trial: the switch doubles the residual survival of switchers with `l = true` and does
nothing for the others. -/
noncomputable def M : TwoStageTrial Ω where
  R _ := false
  S _ := 0
  X ω := ω.2
  W _ := 0
  T ω := if ω.2 && ω.1 then 2 * u ω else u ω
  C _ := 10
  U := u

/-- The covariate measured at the secondary baseline. -/
def L (ω : Ω) : Bool := ω.1

/-- The log time ratio `log (1/2)`. -/
noncomputable def half : ℝ := Real.log (1 / 2)

theorem exp_half : Real.exp half = 1 / 2 := Real.exp_log (by norm_num)

/-- The unit specific parameters: `exp ψ = 1/2` for `l = true`, `exp ψ = 1` otherwise. -/
noncomputable def ψi (ω : Ω) : ℝ := if ω.1 then half else 0

theorem followsModel : (M.toSwitchingTrial M.S).FollowsModel ψi := by
  rintro ⟨l, x⟩
  cases l <;> cases x <;> simp [M, ψi, u, SwitchingTrial.Tc,
    TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_half]

/-- **The single factor model fails**: no parameter `ψ` makes `U = adjusted S ψ` for all
patients. -/
theorem no_common_model (ψ : ℝ) : ¬ M.ModelOn univ M.S ψ := by
  intro h
  refine M.not_pooled_of_ne followsModel (ω₁ := (true, true)) (ω₂ := (false, true))
    (by simp [M, u, TwoStageTrial.treated]) (by simp [M, u, TwoStageTrial.treated]) ?_ ψ
    ⟨h _ (mem_univ _), h _ (mem_univ _)⟩
  have : half ≠ 0 := by
    rw [half, Ne, Real.log_eq_zero]; norm_num
  simpa [ψi] using this

/-- No unmeasured confounding holds: the untreated residual survival is constant within the
strata of `L`. -/
theorem nuc : M.BaselineNUC p univ L := fun l =>
  meanIndepOn_of_const (c := if l then 1 - 0 else 3 - 0) fun ω hω => by
    have : ω.1 = l := mem_ev.1 (mem_inter.1 hω).2
    simp [M, u, this]

theorem positive : M.BaselinePositive p univ L (fun _ => 1 / 2) := by
  intro l _
  simp only [TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  cases l <;> simp [M, L, p]

theorem switchAfterBaseline : M.SwitchAfterBaseline := by
  rintro ⟨l, x⟩ _
  refine ⟨le_rfl, ?_⟩
  cases l <;> cases x <;> simp [M, u]

theorem slope : M.stageOneSlope p univ L (fun _ => 1 / 2) M.S = 5 / 2 := by
  simp only [TwoStageTrial.stageOneSlope, condMean, TwoStageTrial.wsum_cell_univ,
    TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, L, p, u, TwoStageTrial.treated]
  norm_num

theorem intercept : M.stageOneIntercept p univ L (fun _ => 1 / 2) M.S = -2 := by
  simp only [TwoStageTrial.stageOneIntercept, condMean, TwoStageTrial.wsum_cell_univ,
    TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, L, p, u, TwoStageTrial.treated, TwoStageTrial.baseResid]
  norm_num

/-- The stage-one root is `exp ψ = 4/5`, neither of the two switcher effects. -/
theorem root (ψ : ℝ) : M.stageOne p univ L (fun _ => 1 / 2) M.S ψ = 0 ↔ Real.exp ψ = 4 / 5 := by
  rw [TwoStageTrial.stageOne_eq, intercept, slope]
  constructor <;> intro h <;> linarith

/-- The stage-one root, `exp ψhat = 4/5`. -/
noncomputable def ψhat : ℝ := Real.log (4 / 5)

theorem exp_ψhat : Real.exp ψhat = 4 / 5 := Real.exp_log (by norm_num)

/-- **The adjusted comparison is biased**: the transformed control arm has mean `43/20`, the
untreated mean is `2`. -/
theorem biased : p.expect (M.adjusted M.S ψhat) = 43 / 20 ∧ p.expect M.U = 2 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p, u, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
    TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψhat]
  norm_num

end Heterogeneous

/-! ### Switching before the secondary baseline -/

namespace BeforeBaseline

/-- A point `(h, x)`: the prognosis and the switch, independent and uniform. -/
abbrev Ω := Bool × Bool

/-- Uniform over the four points. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform

theorem p_apply (ω : Ω) : p ω = 1 / 4 := by
  simp [p, FiniteDist.uniform_apply, Fintype.card_prod]

/-- The untreated survival: `2` or `4` according to the prognosis. -/
noncomputable def u (ω : Ω) : ℝ := if ω.1 then 2 else 4

/-- The trial: the secondary baseline is time `1` for everybody, switchers switch at time `0`,
before it, and the switch doubles the time from the switch: `U = exp ψs T` with
`exp ψs = 1/2`. -/
noncomputable def M : TwoStageTrial Ω where
  R _ := false
  S _ := 1
  X ω := ω.2
  W _ := 0
  T ω := if ω.2 then 2 * u ω else u ω
  C _ := 10
  U := u

/-- No covariate: a single stratum. -/
def L (_ : Ω) : Unit := ()

/-- The true log time ratio, `exp ψs = 1/2`. -/
noncomputable def ψs : ℝ := Real.log (1 / 2)

theorem exp_ψs : Real.exp ψs = 1 / 2 := Real.exp_log (by norm_num)

/-- The structural model holds in the form of Equation (1), from the switch time. -/
theorem model_W : M.ModelOn univ M.W ψs := by
  rintro ⟨h, x⟩ _
  cases h <;> cases x <;> simp [M, u, TwoStageTrial.adjusted, SwitchingTrial.counterfactual,
    SwitchingTrial.Tc, TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψs]

/-- The only assumption that fails: switching happens before the secondary baseline. -/
theorem not_switchAfterBaseline : ¬ M.SwitchAfterBaseline := by
  intro h
  have := (h (true, true) rfl).1
  norm_num [M] at this

theorem nuc : M.BaselineNUC p univ L := by
  intro l
  rw [MeanIndepOn, show univ ∩ ev L l ∩ ev M.X true = M.cell univ L true l from rfl,
    TwoStageTrial.wsum_cell_univ, TwoStageTrial.wmass_cell_univ,
    TwoStageTrial.wsum_stratum_univ, TwoStageTrial.wmass_stratum_univ]
  simp [Fintype.sum_prod_type, M, L, p_apply, u]
  norm_num

theorem positive : M.BaselinePositive p univ L (fun _ => 1) := by
  intro l _
  simp only [TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p_apply]

/-- **The baseline form is wrong even at the true parameter**: shrinking all the time after the
secondary baseline leaves the switchers' time on treatment before it, so the transformed time
exceeds the untreated time by `1/2`. -/
theorem adjusted_S_true (h : Bool) :
    M.adjusted M.S ψs (h, true) = M.U (h, true) + 1 / 2 := by
  rw [M.adjusted_S_eq ψs rfl, ← model_W _ (mem_univ _), exp_ψs]
  simp [M]; norm_num

theorem slope : M.stageOneSlope p univ L (fun _ => 1) M.S = 5 := by
  simp only [TwoStageTrial.stageOneSlope, condMean, TwoStageTrial.wsum_cell_univ,
    TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p_apply, u, TwoStageTrial.treated]
  norm_num

theorem intercept : M.stageOneIntercept p univ L (fun _ => 1) M.S = -2 := by
  simp only [TwoStageTrial.stageOneIntercept, condMean, TwoStageTrial.wsum_cell_univ,
    TwoStageTrial.wmass_cell_univ, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p_apply, u, TwoStageTrial.treated, TwoStageTrial.baseResid]
  norm_num

/-- **The stage-one root of the baseline form is wrong**: `exp ψ = 2/5` instead of `1/2`. -/
theorem root (ψ : ℝ) : M.stageOne p univ L (fun _ => 1) M.S ψ = 0 ↔ Real.exp ψ = 2 / 5 := by
  rw [TwoStageTrial.stageOne_eq, intercept, slope]
  constructor <;> intro h <;> linarith

/-- The stage-one root of the baseline form, `exp ψhat = 2/5`. -/
noncomputable def ψhat : ℝ := Real.log (2 / 5)

theorem exp_ψhat : Real.exp ψhat = 2 / 5 := Real.exp_log (by norm_num)

/-- **The adjusted survival curve is biased**: at time `2` the transformed control arm has
survival `3/4`, the untreated survival is `1/2`. (The means agree here, both `3`: with one
stratum mean balancing fixes the mean.) -/
theorem biased :
    p.probOf (fun ω => 2 < M.adjusted M.S ψhat ω) = 3 / 4 ∧
      p.probOf (fun ω => 2 < M.U ω) = 1 / 2 := by
  simp only [FiniteDist.probOf, FiniteDist.prob, sum_filter, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [M, p_apply, u, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
    TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψhat]
  norm_num

/-- With Equation (1) from the switch time instead, the stage-one identity of
`TwoStageTrial.stageOne_eq_zero` does not use the timing assumption, and here it recovers the
true parameter. -/
theorem root_W (ψ : ℝ) : M.stageOne p univ L (fun _ => 1) M.W ψ = 0 ↔ ψ = ψs :=
  M.stageOne_eq_zero_iff (M.stageOne_eq_zero model_W nuc positive)
    (M.stageOneSlope_pos (fun _ => by norm_num) positive (fun ω _ hX => by
      rcases ω with ⟨h, x⟩
      cases h <;> cases x <;> simp_all [M, u]) (l₀ := ()) (by norm_num)) ψ

end BeforeBaseline

/-! ### Weighting instead of recensoring on the transformed data -/

namespace Weighting

open Survival Survival.IPCW

/-- A point `(l, x, c)`: a prognostic covariate measured at the secondary baseline, the switch,
and the administrative follow-up after the secondary baseline (`4` if `c`, else `2`). -/
abbrev Ω := Bool × Bool × Bool

/-- `l` and `c` uniform and independent; a patient with `l = true` switches with probability
`3/4`, another with probability `1/4`. -/
noncomputable def p : FiniteDist Ω where
  mass ω := if ω.2.1 = ω.1 then 3 / 16 else 1 / 16
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]; norm_num

/-- The untreated survival after the secondary baseline, on the discrete clock: `2` if
`l = true`, `3` otherwise. It depends on `l` only, so the switch is independent of it given
`l` (no unmeasured confounding at the secondary baseline). -/
def Ud (ω : Ω) : ℕ := if ω.1 then 2 else 3

/-- The transformed censoring time, with time ratio `exp ψ = 1/2`: half the follow-up for
switchers, the follow-up for non-switchers. It depends on the switch. -/
def Dd (ω : Ω) : ℕ := if ω.2.1 then (if ω.2.2 then 2 else 1) else (if ω.2.2 then 4 else 2)

/-- The recensoring time `min (C - S, exp ψ (C - S))`, the same rule for everybody. -/
def Drec (ω : Ω) : ℕ := if ω.2.2 then 2 else 1

/-- The baseline covariate of the weight model: `l`. -/
def V (ω : Ω) : Bool := ω.1

/-- No time-varying covariate. -/
def Lh (_ : ℕ) (_ : Ω) : Unit := ()

theorem hazard_two : hazard p.toMeasure Ud 2 = 1 / 2 := by
  rw [hazard_toMeasure, wmass, wmass, sum_filter, sum_filter]
  simp [Fintype.sum_prod_type, p, Ud]; norm_num

/-- **Without recensoring or weighting, censoring at the transformed censoring time is
informative**: the hazard of the censored transformed data at time `2` is `5/12`, not `1/2`. -/
theorem naive : observedHazard (p.toMeasure.map (Survival.observed Ud Dd)) 2 = 5 / 12 := by
  rw [observedHazard_toMeasure, wmass, wmass, eventSet, riskSet, sum_filter, sum_filter]
  simp [Fintype.sum_prod_type, p, Ud, Dd]; norm_num

/-- **Recensoring** gives the right hazard here: `1/2`. -/
theorem recensored : observedHazard (p.toMeasure.map (Survival.observed Ud Drec)) 2 = 1 / 2 := by
  rw [observedHazard_toMeasure, wmass, wmass, eventSet, riskSet, sum_filter, sum_filter]
  simp [Fintype.sum_prod_type, p, Ud, Drec]; norm_num

/-- No unmeasured confounding of the transformed censoring given `l`: within a risk cell, `Ud`
is constant. -/
theorem nuc : SwitchNUC p Ud Dd V Lh 2 := by
  intro j _ ω t
  by_cases ht : Ud ω = t
  · have e : riskCell Ud Dd V Lh j ω ∩ ev Ud t = riskCell Ud Dd V Lh j ω :=
      inter_eq_left.2 fun ω' hω' => by
        have hV : ω'.1 = ω.1 := (mem_riskCell.1 hω').1.2.2
        simp [Ud, hV, ← ht]
    rw [MeanIndepOn, e]
  · have e : riskCell Ud Dd V Lh j ω ∩ ev Ud t = ∅ := by
      ext ω'
      simp only [mem_inter, mem_ev, Finset.notMem_empty, iff_false, not_and]
      intro hω' h'
      have hV : ω'.1 = ω.1 := (mem_riskCell.1 hω').1.2.2
      exact ht (by simpa [Ud, hV] using h')
    simp [MeanIndepOn, e, wsum, wmass]

/-- Positivity: in every risk cell of periods `0` and `1`, some patient of positive mass stays
uncensored. -/
theorem pos : SwitchPositive p Ud Dd V Lh 2 := by
  intro j hj ω _ _ _
  have hU : j < Ud (ω.1, true, true) := by unfold Ud; split_ifs <;> omega
  have hmem : (ω.1, true, true) ∈ riskCell Ud Dd V Lh j ω ∩ uncensored Dd (j + 1) :=
    mem_inter.2 ⟨mem_riskCell.2 ⟨⟨by simp [Dd]; omega, hU, rfl⟩, fun _ _ => rfl⟩,
      by simp [uncensored, Dd]; omega⟩
  have hp : 0 < p (ω.1, true, true) := by simp [p]; split_ifs <;> norm_num
  have h1 := wmass_pos_of_mem p.nonneg hmem hp
  exact div_pos h1 (h1.trans_le (wmass_mono p.nonneg inter_subset_left))

/-- **Weighting recovers the untreated hazard** (TSD 24, Section 4.2.3.1, inverse probability of
censoring weights on the two-stage adjusted data): weights given `l` for remaining uncensored
at the transformed censoring time give the hazard `1/2`, by
`Survival.IPCW.weightedHazard_ipcWeight`. -/
theorem weighted : weightedHazard p Ud Dd (ipcWeight p Ud Dd V Lh) 2 = 1 / 2 := by
  have hk : 0 < atRisk p.toMeasure Ud 2 := by
    rw [atRisk_toMeasure, wmass, sum_filter]
    simp [Fintype.sum_prod_type, p, Ud]; norm_num
  rw [(weightedHazard_ipcWeight p 2 nuc pos hk).2, hazard_two]

end Weighting

/-! ### The modified two-stage method with the switch time as secondary baseline -/

namespace Modified

/-- Three patients: `0` never starts a subsequent treatment, `1` starts the alternative
treatment, `2` starts the treatment of interest. -/
abbrev Ω := Fin 3

/-- Uniform over the three patients. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform

theorem p_apply (ω : Ω) : p ω = 1 / 3 := by
  simp [p, FiniteDist.uniform_apply]

/-- Survival without any subsequent treatment: `2` for everybody. -/
noncomputable def U0 (_ : Ω) : ℝ := 2

/-- Survival had the treatment of interest been replaced by the alternative one: the observed
time for patients `0` and `1`, and `5/2` for patient `2`. -/
noncomputable def Ualt (ω : Ω) : ℝ := if ω = 0 then 2 else 5 / 2

/-- The trial as analyzed by the modified method: the secondary baseline is the switch time
`1`; the switch adjusted for is to the treatment of interest; the latent time is `Ualt`. The
alternative treatment prolongs the time after the switch by a factor `3/2`
(`T = 5/2` for patient `1`), the treatment of interest by `3` (`T = 4` for patient `2`). -/
noncomputable def M : TwoStageTrial Ω where
  R _ := false
  S _ := 1
  X ω := ω = 2
  W _ := 1
  T ω := if ω = 0 then 2 else if ω = 1 then 5 / 2 else 4
  C _ := 10
  U := Ualt

/-- The stage-one population: the patients who start a subsequent treatment. Non-switchers are
excluded. -/
def P : Finset Ω := {1, 2}

/-- No covariate: a single stratum. -/
def L (_ : Ω) : Unit := ()

/-- The parameter of the modified method: `exp ψm = 1/2`, the effect of the treatment of
interest against the alternative one. -/
noncomputable def ψm : ℝ := Real.log (1 / 2)

theorem exp_ψm : Real.exp ψm = 1 / 2 := Real.exp_log (by norm_num)

theorem model : M.ModelOn P M.W ψm := by
  intro ω hω
  fin_cases ω <;> simp_all [P, M, Ualt, TwoStageTrial.adjusted, SwitchingTrial.counterfactual,
    SwitchingTrial.Tc, TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψm]; norm_num

theorem nuc : M.BaselineNUC p P L := fun _ =>
  meanIndepOn_of_const (c := 3 / 2) fun ω hω => by
    have : ω ∈ P := (mem_inter.1 hω).1
    fin_cases ω <;> simp_all [P, M, Ualt] <;> norm_num

theorem cell_true : M.cell P L true () = {2} := by
  ext ω; fin_cases ω <;> simp [TwoStageTrial.cell, P, M, L, ev]

theorem cell_false : M.cell P L false () = {1} := by
  ext ω; fin_cases ω <;> simp [TwoStageTrial.cell, P, M, L, ev]

theorem positive : M.BaselinePositive p P L (fun _ => 1) := by
  intro _ _
  rw [cell_true, cell_false]
  simp [wmass, p_apply]

/-- **The modified method identifies the effect against the alternative treatment**: stage one
on the patients who start a subsequent treatment has the unique root `ψm`. -/
theorem root (ψ : ℝ) : M.stageOne p P L (fun _ => 1) M.W ψ = 0 ↔ ψ = ψm :=
  M.stageOne_eq_zero_iff (M.stageOne_eq_zero model nuc positive)
    (M.stageOneSlope_pos (fun _ => by norm_num) positive (fun ω _ hX => by
      fin_cases ω <;> simp_all [M]) (l₀ := ()) (by norm_num)) ψ

/-- **The estimand changes**: the transformed data have mean `7/3`, the mean survival had the
treatment of interest been replaced by the alternative one, while the two-stage estimand (no
subsequent treatment) has mean `2`. The parameter is the effect of the treatment of interest
against the alternative (`exp ψm = 1/2`), not against no subsequent treatment (time ratio
`(U0 - W) / (T - W) = 1/3` for patient `2`). -/
theorem estimand_changes :
    p.expect (M.adjusted M.W ψm) = 7 / 3 ∧ p.expect Ualt = 7 / 3 ∧ p.expect U0 = 2 ∧
      (U0 2 - M.W 2) / (M.T 2 - M.W 2) = 1 / 3 := by
  simp only [FiniteDist.expect, Fin.sum_univ_three, p_apply]
  simp [M, Ualt, U0, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
    TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψm]
  norm_num

end Modified

end TwoStageCounterexample

end StructuralNested

end CausalInference
