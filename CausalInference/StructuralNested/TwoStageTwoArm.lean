/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageExamples

/-!
# Two-stage estimation: two-arm randomized countermodels

The countermodels of `TwoStageCounterexamples` and `TwoStageExamples` describe the control arm
only. Here each is extended to a randomized two-arm trial, so that the stage-two contrast can be
compared with the true hypothetical effect.

## The two-arm construction (`TwoArm`)

* `TwoArm.law`: the arm is a fair coin independent of the control-arm law `p`, on
  `Bool × Ω`; `TwoArm.trial M T1`: the experimental arm (`R = true`) has survival `T1` and no
  adjusted switching, the control arm is the trial `M`.
* `TwoArm.stageOne_trial`: stage one on the control arm of the two-arm trial is stage one of
  `M`.
* `TwoArm.meanContrast_trial`, `TwoArm.hypotheticalEffect_trial`, `TwoArm.bias_trial`: the
  stage-two mean contrast is `E[T1] - E[adjusted]`, the hypothetical effect is `E[T1] - E[U]`,
  and their difference is the bias of the transformed control mean.
* `TwoArm.survivalContrast_trial`, `TwoArm.hypotheticalSurvival_trial`: the same for the
  survival functions at a time `t`.

## The countermodels with two arms (experimental survival `4`)

* `TwoStageCounterexample.Unmeasured.twoArm`: contrast `2` against the effect `3/2`.
* `TwoStageCounterexample.Heterogeneous.twoArm`: contrast `37/20` with equal stratum weights
  and `2` with the switcher-mass weights, against the effect `2`.
* `TwoStageCounterexample.BeforeBaseline.twoArm`: the mean contrast `1` is the effect, but the
  survival contrast at time `2` is `1/4` against `1/2`.
* `TwoStageCounterexample.Modified.twoArm`: the modified method gives `5/3`, which is the
  contrast with the alternative subsequent treatment and not the effect `2` without subsequent
  treatment; the standard method gives `2`.

The censoring countermodel `Weighting` is treated in real time, on the control arm, in
`CausalInference.StructuralNested.TwoStageCensoring`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

/-- **Arm means on a finite law are conditional means**: for the measure of a finite
distribution, `E[f | R = r]` is the ratio `Longitudinal.condMean` over the event `{R = r}`. -/
theorem SwitchingTrial.armMean_toMeasure {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : FiniteDist Ω) (N : SwitchingTrial Ω)
    (f : Ω → ℝ) (r : Bool) : N.armMean p.toMeasure f r = condMean p (ev N.R r) f := by
  classical
  have hs : N.arm r = ↑(ev N.R r) := by ext ω; simp [SwitchingTrial.arm]
  rw [SwitchingTrial.armMean, hs, ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul, ← integral_indicator (Finset.measurableSet _),
    FiniteDist.integral_toMeasure, FiniteDist.toMeasure_real_finset, condMean, div_eq_inv_mul]
  congr 1
  simp only [FiniteDist.expect, wsum, Set.indicator_apply, Finset.mem_coe, mul_ite, mul_zero]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]

namespace TwoArm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **The randomized two-arm law**: the arm is a fair coin independent of the patient, whose
law is `p` in both arms. -/
noncomputable def law (p : FiniteDist Ω) : FiniteDist (Bool × Ω) where
  mass z := p z.2 / 2
  nonneg z := div_nonneg (p.nonneg _) (by norm_num)
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, ← sum_div, p.sum_eq_one]; norm_num

omit [DecidableEq Ω] in
/-- A weighted sum over an event of one arm under the two-arm law. -/
theorem wsum_law (p : FiniteDist Ω) {s' : Finset (Bool × Ω)} {s : Finset Ω} {r : Bool}
    (hs : ∀ z, z ∈ s' ↔ z.1 = r ∧ z.2 ∈ s) (g : Bool × Ω → ℝ) :
    wsum (law p) s' g = wsum p s (fun ω => g (r, ω)) / 2 := by
  have e : s' = s.map ⟨fun ω => (r, ω), fun a b h => (Prod.ext_iff.1 h).2⟩ := by
    ext ⟨b, ω⟩
    rw [hs, mem_map]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨ω, h, rfl⟩
    · rintro ⟨a, ha, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 he
      exact ⟨rfl, ha⟩
  rw [e, wsum, sum_map, wsum, sum_div]
  refine sum_congr rfl fun ω _ => ?_
  change p ω / 2 * g (r, ω) = p ω * g (r, ω) / 2
  ring

omit [DecidableEq Ω] in
theorem wmass_law (p : FiniteDist Ω) {s' : Finset (Bool × Ω)} {s : Finset Ω} {r : Bool}
    (hs : ∀ z, z ∈ s' ↔ z.1 = r ∧ z.2 ∈ s) : wmass (law p) s' = wmass p s / 2 := by
  have h := wsum_law p hs (fun _ => 1)
  simpa [wsum_const] using h

omit [DecidableEq Ω] in
/-- A conditional mean over an event of one arm under the two-arm law. -/
theorem condMean_law (p : FiniteDist Ω) {s' : Finset (Bool × Ω)} {s : Finset Ω} {r : Bool}
    (hs : ∀ z, z ∈ s' ↔ z.1 = r ∧ z.2 ∈ s) (g : Bool × Ω → ℝ) :
    condMean (law p) s' g = condMean p s (fun ω => g (r, ω)) := by
  rw [condMean, condMean, wsum_law p hs, wmass_law p hs,
    div_div_div_cancel_right₀ (two_ne_zero)]

omit [DecidableEq Ω] in
theorem condMean_law_arm (p : FiniteDist Ω) (r : Bool) (g : Bool × Ω → ℝ) :
    condMean (law p) (ev Prod.fst r) g = p.expect (fun ω => g (r, ω)) := by
  rw [condMean_law p (s := univ) (r := r) (fun z => by simp), condMean, wmass, p.sum_eq_one,
    div_one]
  rfl

/-- **The two-arm trial built from a control arm.** The control arm is the trial `M` (with its
switches, secondary baseline and censoring); in the experimental arm nobody makes an adjusted
switch and survival is `T1`, so its untreated time is `T1` too. -/
def trial (M : TwoStageTrial Ω) (T1 : Ω → ℝ) : TwoStageTrial (Bool × Ω) where
  R z := z.1
  S z := M.S z.2
  X z := !z.1 && M.X z.2
  W z := M.W z.2
  T z := if z.1 then T1 z.2 else M.T z.2
  C z := M.C z.2
  U z := if z.1 then T1 z.2 else M.U z.2

variable (M : TwoStageTrial Ω) (T1 : Ω → ℝ)

/-- The stage-one population of the two-arm trial: the control arm patients whose record lies
in `P`. -/
def control (P : Finset Ω) : Finset (Bool × Ω) := univ.filter fun z => z.1 = false ∧ z.2 ∈ P

omit [Fintype Ω] [DecidableEq Ω] in
theorem resid_trial (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) :
    (trial M T1).resid (fun z => B z.2) ψ (false, ω) = M.resid B ψ ω := rfl

omit [Fintype Ω] [DecidableEq Ω] in
theorem adjusted_trial (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) :
    (trial M T1).adjusted (fun z => B z.2) ψ (false, ω) = M.adjusted B ψ ω := rfl

/-- **Stage one on the control arm of the two-arm trial is stage one of `M`.** -/
theorem stageOne_trial {𝓛 : Type*} [Fintype 𝓛] [DecidableEq 𝓛] (p : FiniteDist Ω)
    (P : Finset Ω) (L : Ω → 𝓛) (w : 𝓛 → ℝ) (B : Ω → ℝ) (ψ : ℝ) :
    (trial M T1).stageOne (law p) (control P) (fun z => L z.2) w (fun z => B z.2) ψ =
      M.stageOne p P L w B ψ := by
  refine sum_congr rfl fun l _ => ?_
  have hc : ∀ x, ∀ z, z ∈ (trial M T1).cell (control P) (fun z => L z.2) x l ↔
      z.1 = false ∧ z.2 ∈ M.cell P L x l := fun x ⟨b, ω⟩ => by
    cases b <;> simp [TwoStageTrial.cell, control, trial]
  rw [condMean_law p (hc true), condMean_law p (hc false)]
  rfl

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

omit [DecidableEq Ω] in
/-- **The stage-two contrast of the two-arm trial**: experimental mean minus the mean of the
transformed control arm, `E[T1] - E[adjusted B ψ]`. -/
theorem meanContrast_trial (p : FiniteDist Ω) (B : Ω → ℝ) (ψ : ℝ) :
    ((trial M T1).toSwitchingTrial fun z => B z.2).meanContrast (law p).toMeasure
        ((trial M T1).analysisTime (fun z => B z.2) ψ) =
      p.expect T1 - p.expect (M.adjusted B ψ) := by
  simp only [SwitchingTrial.meanContrast, SwitchingTrial.armMean_toMeasure]
  rw [show ((trial M T1).toSwitchingTrial fun z => B z.2).R = Prod.fst from rfl,
    condMean_law_arm, condMean_law_arm]
  rfl

omit [DecidableEq Ω] in
/-- **The true hypothetical effect of the two-arm trial**: `E[T1] - E[U]`. -/
theorem hypotheticalEffect_trial (p : FiniteDist Ω) (B : Ω → ℝ) :
    ((trial M T1).toSwitchingTrial fun z => B z.2).hypotheticalEffect (law p).toMeasure =
      p.expect T1 - p.expect M.U := by
  simp only [SwitchingTrial.hypotheticalEffect, SwitchingTrial.armMean_toMeasure]
  rw [show ((trial M T1).toSwitchingTrial fun z => B z.2).R = Prod.fst from rfl,
    condMean_law_arm, condMean_law_arm]
  rfl

omit [DecidableEq Ω] in
/-- The bias of the stage-two contrast: `E[U] - E[adjusted B ψ]`. -/
theorem bias_trial (p : FiniteDist Ω) (B : Ω → ℝ) (ψ : ℝ) :
    ((trial M T1).toSwitchingTrial fun z => B z.2).meanContrast (law p).toMeasure
        ((trial M T1).analysisTime (fun z => B z.2) ψ) -
      ((trial M T1).toSwitchingTrial fun z => B z.2).hypotheticalEffect (law p).toMeasure =
      p.expect M.U - p.expect (M.adjusted B ψ) := by
  rw [meanContrast_trial, hypotheticalEffect_trial]; ring

omit [Fintype Ω] [DecidableEq Ω] in
/-- **Arm survival on a finite law is an arm mean of an indicator.** -/
theorem _root_.CausalInference.StructuralNested.SwitchingTrial.armSurvival_eq_armMean
    {Ω' : Type*} [Finite Ω'] [MeasurableSpace Ω'] [MeasurableSingletonClass Ω']
    (μ : Measure Ω') (N : SwitchingTrial Ω') (X : Ω' → ℝ) (r : Bool) (t : ℝ) :
    N.armSurvival μ X r t = N.armMean μ (fun ω => if t < X ω then 1 else 0) r := by
  rw [SwitchingTrial.armSurvival, SwitchingTrial.armMean,
    ← integral_indicator_one (Set.toFinite _).measurableSet]
  rfl

omit [DecidableEq Ω] in
/-- **The survival contrast of the two-arm trial at `t`**:
`P(T1 > t) - P(adjusted B ψ > t)`. -/
theorem survivalContrast_trial (p : FiniteDist Ω) (B : Ω → ℝ) (ψ : ℝ) (t : ℝ) :
    ((trial M T1).toSwitchingTrial fun z => B z.2).armSurvival (law p).toMeasure
        ((trial M T1).analysisTime (fun z => B z.2) ψ) true t -
      ((trial M T1).toSwitchingTrial fun z => B z.2).armSurvival (law p).toMeasure
        ((trial M T1).analysisTime (fun z => B z.2) ψ) false t =
      p.expect (fun ω => if t < T1 ω then 1 else 0) -
        p.expect (fun ω => if t < M.adjusted B ψ ω then 1 else 0) := by
  simp only [SwitchingTrial.armSurvival_eq_armMean, SwitchingTrial.armMean_toMeasure]
  rw [show ((trial M T1).toSwitchingTrial fun z => B z.2).R = Prod.fst from rfl,
    condMean_law_arm, condMean_law_arm]
  rfl

omit [DecidableEq Ω] in
/-- **The true hypothetical survival contrast at `t`**: `P(T1 > t) - P(U > t)`. -/
theorem hypotheticalSurvival_trial (p : FiniteDist Ω) (B : Ω → ℝ) (t : ℝ) :
    ((trial M T1).toSwitchingTrial fun z => B z.2).armSurvival (law p).toMeasure
        (trial M T1).T true t -
      ((trial M T1).toSwitchingTrial fun z => B z.2).armSurvival (law p).toMeasure
        (trial M T1).U false t =
      p.expect (fun ω => if t < T1 ω then 1 else 0) -
        p.expect (fun ω => if t < M.U ω then 1 else 0) := by
  simp only [SwitchingTrial.armSurvival_eq_armMean, SwitchingTrial.armMean_toMeasure]
  rw [show ((trial M T1).toSwitchingTrial fun z => B z.2).R = Prod.fst from rfl,
    condMean_law_arm, condMean_law_arm]
  rfl

end TwoArm

/-! ### The countermodels as two-arm randomized trials

In each, the experimental arm has survival `4` for everybody and no adjusted switch, the
control arm is the countermodel, and the arm is a fair coin independent of the patient. -/

namespace TwoStageCounterexample

open TwoArm

/-- The experimental arm survival used in the two-arm versions. -/
noncomputable def T1 {Ω : Type*} (_ : Ω) : ℝ := 4

theorem expect_T1 {Ω : Type*} [Fintype Ω] (p : FiniteDist Ω) : p.expect T1 = 4 :=
  p.expect_const 4

theorem expect_T1_gt_two {Ω : Type*} [Fintype Ω] (p : FiniteDist Ω) :
    p.expect (fun ω => if (2 : ℝ) < T1 ω then 1 else 0) = 1 := by
  norm_num [T1]

namespace Unmeasured

/-- **Unmeasured confounding, two arms.** Stage one on the control arm has the root
`exp ψ = 1/3`, and at that root the stage-two contrast is `2` while the true hypothetical effect
is `3/2`. -/
theorem twoArm :
    (∀ ψ, (trial M T1).stageOne (law p) (control univ) (fun z => L z.2) (fun _ => 1 / 2)
        (fun z => M.S z.2) ψ = 0 ↔ Real.exp ψ = 1 / 3) ∧
      ((trial M T1).toSwitchingTrial fun z => M.S z.2).meanContrast (law p).toMeasure
          ((trial M T1).analysisTime (fun z => M.S z.2) ψhat) = 2 ∧
      ((trial M T1).toSwitchingTrial fun z => M.S z.2).hypotheticalEffect (law p).toMeasure =
        3 / 2 := by
  refine ⟨fun ψ => by rw [stageOne_trial]; exact root ψ, ?_, ?_⟩
  · rw [meanContrast_trial, biased.1, expect_T1]; norm_num
  · rw [hypotheticalEffect_trial, biased.2, expect_T1]; norm_num

end Unmeasured

namespace Heterogeneous

/-- **Heterogeneous effects, two arms.** With equal stratum weights the stage-two contrast is
`37/20` against the true hypothetical effect `2`; with the switcher-mass weights it is `2`. -/
theorem twoArm :
    ((trial M T1).toSwitchingTrial fun z => M.S z.2).meanContrast (law p).toMeasure
        ((trial M T1).analysisTime (fun z => M.S z.2) ψhat) = 37 / 20 ∧
      ((trial M T1).toSwitchingTrial fun z => M.S z.2).meanContrast (law p).toMeasure
        ((trial M T1).analysisTime (fun z => M.S z.2) (Real.log (2 / 3))) = 2 ∧
      ((trial M T1).toSwitchingTrial fun z => M.S z.2).hypotheticalEffect (law p).toMeasure =
        2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [meanContrast_trial, biased.1, expect_T1]; norm_num
  · rw [meanContrast_trial, mean_switcherWeights.1, expect_T1]; norm_num
  · rw [hypotheticalEffect_trial, biased.2, expect_T1]; norm_num

end Heterogeneous

namespace BeforeBaseline

theorem expect_adjusted_ψhat : p.expect (M.adjusted M.S ψhat) = 3 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p_apply, u, TwoStageTrial.adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
    TwoStageTrial.toSwitchingTrial, TwoStageTrial.treated, exp_ψhat]
  norm_num

theorem expect_U : p.expect M.U = 3 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [M, p_apply, u]
  norm_num

/-- **Switching before the secondary baseline, two arms.** At the stage-one root of the
baseline form the mean contrast is `1`, equal to the true hypothetical effect, while the
survival contrast at time `2` is `1/4` against the true `1/2`. -/
theorem twoArm :
    ((trial M T1).toSwitchingTrial fun z => M.S z.2).meanContrast (law p).toMeasure
        ((trial M T1).analysisTime (fun z => M.S z.2) ψhat) = 1 ∧
      ((trial M T1).toSwitchingTrial fun z => M.S z.2).hypotheticalEffect (law p).toMeasure =
        1 ∧
      ((trial M T1).toSwitchingTrial fun z => M.S z.2).armSurvival (law p).toMeasure
          ((trial M T1).analysisTime (fun z => M.S z.2) ψhat) true 2 -
        ((trial M T1).toSwitchingTrial fun z => M.S z.2).armSurvival (law p).toMeasure
          ((trial M T1).analysisTime (fun z => M.S z.2) ψhat) false 2 = 1 / 4 ∧
      ((trial M T1).toSwitchingTrial fun z => M.S z.2).armSurvival (law p).toMeasure
          (trial M T1).T true 2 -
        ((trial M T1).toSwitchingTrial fun z => M.S z.2).armSurvival (law p).toMeasure
          (trial M T1).U false 2 = 1 / 2 := by
  have hs : ∀ f : Ω → ℝ, p.expect (fun ω => if (2 : ℝ) < f ω then 1 else 0) =
      p.probOf (fun ω => 2 < f ω) := fun f => by
    simp [FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob, sum_filter]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [meanContrast_trial, expect_adjusted_ψhat, expect_T1]; norm_num
  · rw [hypotheticalEffect_trial, expect_U, expect_T1]; norm_num
  · rw [survivalContrast_trial, hs (M.adjusted M.S ψhat), biased.1, expect_T1_gt_two]; norm_num
  · rw [hypotheticalSurvival_trial, hs M.U, biased.2, expect_T1_gt_two]; norm_num

end BeforeBaseline

namespace Modified

/-- **The modified and the standard methods, two arms.** The modified method (stage one on the
switchers, root `ψm`) gives the contrast `5/3` against its own estimand `E[T1] - E[Ualt] = 5/3`
and against the hypothetical effect `2` without subsequent treatment; the standard method with a
pooled parameter (root `exp ψ = 4/9`) gives the contrast `2`, equal to the hypothetical effect,
and so does the standard method by type. -/
theorem twoArm :
    ((trial M T1).toSwitchingTrial fun z => M.W z.2).meanContrast (law p).toMeasure
        ((trial M T1).analysisTime (fun z => M.W z.2) ψm) = 5 / 3 ∧
      ((trial M T1).toSwitchingTrial fun z => M.W z.2).hypotheticalEffect (law p).toMeasure =
        5 / 3 ∧
      ((trial Mstd T1).toSwitchingTrial fun z => Mstd.W z.2).meanContrast (law p).toMeasure
        ((trial Mstd T1).analysisTime (fun z => Mstd.W z.2) (Real.log (4 / 9))) = 2 ∧
      ((trial Mstd T1).toSwitchingTrial fun z => Mstd.W z.2).hypotheticalEffect
        (law p).toMeasure = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [meanContrast_trial, estimand_changes.1, expect_T1]; norm_num
  · rw [hypotheticalEffect_trial, show M.U = Ualts from Ualts_eq.symm, expect_Ualts]
    rw [expect_T1]; norm_num
  · rw [meanContrast_trial, mean_std, expect_T1]; norm_num
  · rw [hypotheticalEffect_trial, show Mstd.U = U0s from rfl, expect_U0s, expect_T1]; norm_num

end Modified

end TwoStageCounterexample

end StructuralNested

end CausalInference
