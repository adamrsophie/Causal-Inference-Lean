/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Recensoring
public import CausalInference.Survival.IPCW

/-!
# Two-stage estimation

The two-stage estimation (TSE) method for treatment switching. In a randomized trial patients
may switch treatment, but only at or after a disease-related secondary baseline (for example
disease progression). Stage one estimates the effect of the switch on survival after the
secondary baseline, by comparing switchers with non-switchers adjusted for covariates measured
at the secondary baseline. Stage two undoes that effect in the survival times of the switchers,
leaves the non-switchers untouched, and compares the arms on the adjusted data, with
recensoring or weighting for the transformed censoring. The method relies on no unmeasured
confounding at the secondary baseline instead of randomization, and does not assume a common
treatment effect: the parameter `ψ` is the effect of the switch treatment on the survival of
switchers after the switch, which need not be the effect of the experimental treatment in the
experimental arm.

## The transformation

Neither document prints the stage-two formula. TSD 16, Section 3.2.4 says that the estimated
acceleration factor is used to "shrink" the survival times of switchers; TSD 24, Section 4.2.3
says that the time ratio is used "in a counterfactual survival model similar to that described
in equation (1)". `TwoStageTrial.adjusted B ψ` is `B + exp ψ (T - B)` for switchers and `T`
for the others, with a start time `B`: `B = W` (the switch time) is Equation (1) applied from
the switch, the path form "on treatment from the switch" of Equation A2
(`TwoStageTrial.adjusted_eq_untreatedTime`); `B = S` shrinks all the time after the secondary
baseline, `S + exp ψ (T - S)`. The two agree when the switch happens at the secondary baseline,
and otherwise differ by `(1 - exp ψ) (W - S)` (`TwoStageTrial.adjusted_S_eq`). Every result is
stated for a general `B`.

## Main definitions

* `StructuralNested.TwoStageTrial`: arm `R`, secondary baseline `S`, adjusted switch `X` at
  time `W`, survival `T`, administrative censoring `C`, latent survival `U` had the adjusted
  switch not occurred. `TwoStageTrial.toSwitchingTrial B` is the trial of
  `CausalInference.StructuralNested.SwitchingTrial` with time on treatment `treated B`.
* `TwoStageTrial.SwitchAfterBaseline`: switching only at or after the secondary baseline.
* Stage one (finite population `P`, finite covariate `L` measured at the secondary baseline):
  `TwoStageTrial.stageOne`, the stratum-weighted contrast of the transformed residual survival
  between switchers and non-switchers; `TwoStageTrial.BaselineNUC` (no unmeasured confounding at
  the secondary baseline, mean form), `TwoStageTrial.BaselinePositive`, `TwoStageTrial.ModelOn`
  (the structural model on `P`).
* Stage two: `TwoStageTrial.ControlModel`, `TwoStageTrial.analysisTime` (experimental arm as
  observed, control arm transformed), `TwoStageTrial.perArmTime` (each arm transformed).
* Recensoring: `TwoStageTrial.postBaseline` (the trial with the origin moved to the secondary
  baseline, a `CausalInference.StructuralNested.CensoredTrial`), `TwoStageTrial.Cohort`,
  `TwoStageTrial.recensored`, `TwoStageTrial.ControlIndepCensoring`.

## Main results

* `TwoStageTrial.stageOne_eq_zero`: under the structural model at `ψs`, no unmeasured
  confounding at the secondary baseline and positivity, `ψs` solves the stage-one equation.
  `TwoStageTrial.stageOne_eq`: the equation is `c + exp ψ a`, with `a` the weighted mean time on
  the switch treatment among switchers; `TwoStageTrial.stageOne_eq_zero_iff`: under relevance
  (`0 < a`) the root is unique; `TwoStageTrial.stageOneSlope_pos`: relevance holds when
  switchers live beyond the start of the switch treatment;
  `TwoStageTrial.stageOne_const_of_slope_eq_zero`: without relevance nothing is identified.
* `TwoStageTrial.analysis_meanContrast`, `TwoStageTrial.control_armMean_armLaw`,
  `TwoStageTrial.control_armLaw_eq_map`: at the true parameter the transformed control arm has
  the mean and law of the untreated control arm, so the analysis targets the hypothetical
  estimand of `SwitchingTrial`: the experimental arm as delivered (with whatever subsequent
  treatments it received) against the control arm without the adjusted switch.
* `TwoStageTrial.perArm_meanContrast`, `TwoStageTrial.perArm_meanContrast_eq`,
  `TwoStageTrial.perArm_lt_analysis`: transforming each arm with its own parameter (TSD 24,
  Section 4.2.3.1) targets the contrast without the adjusted switches in either arm; it is
  smaller than the control-only estimand by `(1 - exp ψ₁) E[treated | R = 1]`.
  `TwoStageTrial.not_pooled_of_ne`: with separate effects per subsequent treatment, a pooled
  parameter cannot recover the untreated times.
* `TwoStageTrial.Cohort.recensored_eq`, `TwoStageTrial.recensored_eq_comp_observed`: on the
  post-baseline scale the recensored record is a function of the observed data, and at the true
  parameter it is `(min (U - S, D*), 1{U - S ≤ D*})` with `D* = min (C - S, exp ψ (C - S))`, which
  depends on the censoring time only (the reduction to `Survival.Recensoring` with the origin at
  the secondary baseline). `TwoStageTrial.Cohort.control_survival_eq_div`: under independent
  post-baseline censoring in the control arm the untreated post-baseline survival of the control
  arm is identified up to the recensored follow-up.

The countermodels (switching before the secondary baseline, unmeasured confounding at the
secondary baseline, heterogeneous effects among switchers), the weighting alternative to
recensoring (TSD 24, Section 4.2.3.1) and the modified method with the switch time as secondary
baseline are in `CausalInference.StructuralNested.TwoStageCounterexamples`; time-dependent
confounding between the secondary baseline and the switch is
`SwitchingCounterexamples.TimeDependent` in
`CausalInference.Survival.SwitchingCounterexamples`; the version with g-estimation is
`CausalInference.StructuralNested.TwoStageGEstimation`.

## Setting and scope

Two layers. Stage one is stated on a finite sample space with a finite distribution
(`CausalInference.Basic.FiniteDistribution`, conditional means `Longitudinal.condMean`), so that
conditioning on the covariate strata is elementary. Stage two and recensoring are stated on a
general measure space with real times, as `CausalInference.StructuralNested.FailureTime` and
`CausalInference.Survival.Recensoring`. Stage one is a population identity: the mean-balancing
estimating equation, not the parametric accelerated failure time fit of the documents, whose
target is not formalized. The no unmeasured confounding assumption is used in its mean form
(mean independence within strata), which is implied by the conditional independence printed in
TSD 24, Section 4.2.3. Not formalized: the claim that the bias of the simple method grows with
the delay between the secondary baseline and the switch; the finite-sample estimation of `ψ`
and bootstrapping.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014): Section 3.2.4 and Section 3.3.2.
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to TSD 16*
  (2024): Section 4.2.3 and Section 4.2.3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace StructuralNested

/-! ### The trial and the transformation of switchers -/

/-- A two-arm trial with a secondary baseline. `R ω = true` is the experimental arm. `S` is the
time of the secondary baseline (for example disease progression), `X` marks the patients whose
switch is adjusted for, `W` the time of that switch (meaningful when `X ω = true`), `T` the
observed survival time, `C` the administrative censoring time, and `U` the latent survival time
had the adjusted switch not occurred (the untreated time). Only `U` is not observed. -/
structure TwoStageTrial (Ω : Type*) where
  /-- The randomized arm: `true` for the experimental arm. -/
  R : Ω → Bool
  /-- The time of the secondary baseline. -/
  S : Ω → ℝ
  /-- Whether the patient made a switch that is adjusted for. -/
  X : Ω → Bool
  /-- The time of the switch. -/
  W : Ω → ℝ
  /-- The observed survival time. -/
  T : Ω → ℝ
  /-- The administrative censoring time. -/
  C : Ω → ℝ
  /-- The latent survival time had the adjusted switch not occurred. -/
  U : Ω → ℝ

namespace TwoStageTrial

variable {Ω : Type*} (M : TwoStageTrial Ω)

/-- **Switching only at or after the secondary baseline** (TSD 24, Section 4.2.3): every
adjusted switch happens at a time `W ≥ S`, and the patient is alive at the switch. -/
def SwitchAfterBaseline : Prop := ∀ ω, M.X ω = true → M.S ω ≤ M.W ω ∧ M.W ω ≤ M.T ω

/-- The time counted as spent on the switch treatment, from the start time `B ω` (the switch
time `W` for Equation (1), the secondary baseline `S` for the baseline form): `T - B` for
adjusted switchers, `0` for everybody else. -/
def treated (B : Ω → ℝ) (ω : Ω) : ℝ := if M.X ω then M.T ω - B ω else 0

/-- The switching trial of `CausalInference.StructuralNested.SwitchingTrial` whose time on
treatment is the treated time counted from `B`. -/
def toSwitchingTrial (B : Ω → ℝ) : SwitchingTrial Ω where
  R := M.R
  T := M.T
  Te := M.treated B
  U := M.U

/-- **The stage-two transformation.** For a candidate parameter `ψ` and a start time `B`, the
survival time with the effect of the adjusted switch undone: `B + exp ψ (T - B)` for adjusted
switchers and `T` for everybody else. With `B = W` this is the counterfactual survival model of
TSD 24, Equation (1), applied to switchers from their switch time; with `B = S` it shrinks all
the time after the secondary baseline. It is a function of the observed data. -/
noncomputable def adjusted (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) : ℝ :=
  (M.toSwitchingTrial B).counterfactual ψ ω

theorem adjusted_of_switch (B : Ω → ℝ) (ψ : ℝ) {ω : Ω} (h : M.X ω = true) :
    M.adjusted B ψ ω = B ω + Real.exp ψ * (M.T ω - B ω) := by
  simp [adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc, toSwitchingTrial, treated, h]

/-- Non-switchers are untouched. -/
theorem adjusted_of_not_switch (B : Ω → ℝ) (ψ : ℝ) {ω : Ω} (h : M.X ω = false) :
    M.adjusted B ψ ω = M.T ω := by
  simp [adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc, toSwitchingTrial, treated, h]

/-- At `ψ = 0` nothing is changed. -/
theorem adjusted_zero (B : Ω → ℝ) : M.adjusted B 0 = M.T :=
  (M.toSwitchingTrial B).counterfactual_zero

/-- **The path form.** For a switcher with `0 ≤ B ≤ T`, the transformation is the untreated time
of Equation A2 along the path "on treatment from `B` onwards" (the treatment group path of
`CausalInference.StructuralNested.treatmentGroupPath`):
`B + exp ψ (T - B) = ∫_0^T exp (ψ 1{s > B}) ds`. -/
theorem adjusted_eq_untreatedTime (B : Ω → ℝ) (ψ : ℝ) {ω : Ω} (h : M.X ω = true)
    (h0 : 0 ≤ B ω) (hB : B ω ≤ M.T ω) :
    M.adjusted B ψ ω = untreatedTime ψ (treatmentGroupPath (B ω)) (M.T ω) := by
  rw [M.adjusted_of_switch B ψ h,
    untreatedTime_eq (show MeasurableSet (treatmentGroupPath (B ω)) from measurableSet_Ioi),
    timeOn_treatmentGroupPath h0 (h0.trans hB), min_eq_left hB]
  ring

/-- **The baseline form against Equation (1).** For a switcher, shrinking all the time after the
secondary baseline instead of the time after the switch changes the result by
`(1 - exp ψ) (W - S)`: the two forms agree when the switch happens at the secondary baseline
(or when `ψ = 0`), and for `ψ < 0` and `W > S` the baseline form is shorter, since it also
shrinks the time between the secondary baseline and the switch. -/
theorem adjusted_S_eq (ψ : ℝ) {ω : Ω} (h : M.X ω = true) :
    M.adjusted M.S ψ ω = M.adjusted M.W ψ ω - (1 - Real.exp ψ) * (M.W ω - M.S ω) := by
  rw [M.adjusted_of_switch _ ψ h, M.adjusted_of_switch _ ψ h]; ring

theorem adjusted_S_eq_W {ω : Ω} (ψ : ℝ) (hW : M.W ω = M.S ω) :
    M.adjusted M.S ψ ω = M.adjusted M.W ψ ω := by
  simp [adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc, toSwitchingTrial, treated, hW]

/-- The transformed residual survival after the secondary baseline,
`adjusted B ψ - S`. -/
noncomputable def resid (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) : ℝ := M.adjusted B ψ ω - M.S ω

/-- The part of the transformed residual that does not depend on `ψ`:
`T - S - treated`. -/
def baseResid (B : Ω → ℝ) (ω : Ω) : ℝ := M.T ω - M.S ω - M.treated B ω

theorem resid_eq (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) :
    M.resid B ψ ω = M.baseResid B ω + Real.exp ψ * M.treated B ω := by
  simp only [resid, baseResid, adjusted, SwitchingTrial.counterfactual, SwitchingTrial.Tc,
    toSwitchingTrial]
  ring

/-! ### Stage one: the switch effect identified at the secondary baseline

Stage one is stated on a finite population with a finite covariate measured at the secondary
baseline, so that conditioning is a ratio of finite sums (`Longitudinal.condMean`). The
population `P` is the set of patients entering the stage-one comparison (for the simple method:
control arm patients who reached the secondary baseline). -/

section StageOne

open Longitudinal Finset

variable [Fintype Ω] [DecidableEq Ω] {𝓛 : Type*} [Fintype 𝓛] [DecidableEq 𝓛]

/-- The stage-one cell of switch status `x` in the covariate stratum `L = l` of the population
`P`. -/
def cell (P : Finset Ω) (L : Ω → 𝓛) (x : Bool) (l : 𝓛) : Finset Ω :=
  P ∩ ev L l ∩ ev M.X x

/-- **The stage-one estimating function** (TSD 16, Section 3.2.4; TSD 24, Section 4.2.3), in
mean-balancing form: the stratum-weighted contrast between switchers and non-switchers of the
transformed residual survival after the secondary baseline,
`Φ(ψ) = ∑_l w_l (E[U(ψ) - S | X = 1, L = l, P] - E[U(ψ) - S | X = 0, L = l, P])`.
The weights `w_l` are arbitrary (for instance the stratum probabilities). The documents fit a
parametric accelerated failure time model instead; its population target under a correct
specification is a root of an estimating equation of this kind, which is not formalized. -/
noncomputable def stageOne (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (w : 𝓛 → ℝ)
    (B : Ω → ℝ) (ψ : ℝ) : ℝ :=
  ∑ l, w l * (condMean p (M.cell P L true l) (M.resid B ψ) -
    condMean p (M.cell P L false l) (M.resid B ψ))

/-- **No unmeasured confounding at the secondary baseline**, in mean form: within every
stratum of the covariates `L` measured at the secondary baseline, the untreated residual
survival `U - S` is mean independent of the switch (`Longitudinal.MeanIndepOn`, stated without
division, empty for a stratum without switchers). It is implied by conditional independence of
the switch and `U - S` given `L`, the form printed in TSD 24, Section 4.2.3. -/
def BaselineNUC (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) : Prop :=
  ∀ l, MeanIndepOn p (P ∩ ev L l) (ev M.X true) (fun ω => M.U ω - M.S ω)

/-- **Positivity at the secondary baseline**: every stratum with a nonzero weight contains
switchers and non-switchers with positive probability. -/
def BaselinePositive (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (w : 𝓛 → ℝ) : Prop :=
  ∀ l, w l ≠ 0 → 0 < wmass p (M.cell P L true l) ∧ 0 < wmass p (M.cell P L false l)

/-- **The structural model on the population `P`**: `U = adjusted B ψ` for every patient of
`P`, that is `U = B + exp ψ (T - B)` for adjusted switchers and `U = T` for non-switchers. The
parameter `ψ` is the effect of the switch treatment on the survival of switchers after `B`; it
need not be the effect of the experimental treatment in the experimental arm (no common
treatment effect is assumed, TSD 16, Section 3.2.4). -/
def ModelOn (P : Finset Ω) (B : Ω → ℝ) (ψ : ℝ) : Prop := ∀ ω ∈ P, M.U ω = M.adjusted B ψ ω

omit [Fintype 𝓛] in
/-- A weighted sum over a stage-one cell of the whole population, as a sum over `Ω`. -/
theorem wsum_cell_univ (p : FiniteDist Ω) (L : Ω → 𝓛) (x : Bool) (l : 𝓛) (f : Ω → ℝ) :
    wsum p (M.cell univ L x l) f = ∑ ω, if L ω = l ∧ M.X ω = x then p ω * f ω else 0 := by
  rw [wsum, ← sum_filter]
  congr 1; ext ω; simp [cell]

omit [Fintype 𝓛] in
theorem wmass_cell_univ (p : FiniteDist Ω) (L : Ω → 𝓛) (x : Bool) (l : 𝓛) :
    wmass p (M.cell univ L x l) = ∑ ω, if L ω = l ∧ M.X ω = x then p ω else 0 := by
  rw [wmass, ← sum_filter]
  congr 1; ext ω; simp [cell]

omit [Fintype 𝓛] in
theorem wsum_stratum_univ (p : FiniteDist Ω) (L : Ω → 𝓛) (l : 𝓛) (f : Ω → ℝ) :
    wsum p (univ ∩ ev L l) f = ∑ ω, if L ω = l then p ω * f ω else 0 := by
  rw [wsum, ← sum_filter]
  congr 1; ext ω; simp

omit [Fintype 𝓛] in
theorem wmass_stratum_univ (p : FiniteDist Ω) (L : Ω → 𝓛) (l : 𝓛) :
    wmass p (univ ∩ ev L l) = ∑ ω, if L ω = l then p ω else 0 := by
  rw [wmass, ← sum_filter]
  congr 1; ext ω; simp

/-- Mean independence of a variable and the switch within an event, with both switch statuses
of positive mass, gives equal means among switchers and non-switchers. -/
theorem condMean_switch_eq {p : FiniteDist Ω} {s : Finset Ω} {f : Ω → ℝ}
    (h : MeanIndepOn p s (ev M.X true) f) (h1 : 0 < wmass p (s ∩ ev M.X true))
    (h0 : 0 < wmass p (s ∩ ev M.X false)) :
    condMean p (s ∩ ev M.X true) f = condMean p (s ∩ ev M.X false) f := by
  have e1 := wsum_eq_sum_ev (m := p) s M.X f
  have e2 := wmass_eq_sum_ev (m := p) s M.X
  simp only [Fintype.sum_bool] at e1 e2
  unfold MeanIndepOn at h
  rw [e1, e2] at h
  rw [condMean, condMean, div_eq_div_iff h1.ne' h0.ne']
  linear_combination h

omit [DecidableEq Ω] in
theorem condMean_congr {p : FiniteDist Ω} {s : Finset Ω} {f g : Ω → ℝ}
    (h : ∀ ω ∈ s, f ω = g ω) : condMean p s f = condMean p s g := by
  rw [condMean, condMean, wsum_congr h]

omit [DecidableEq Ω] in
theorem condMean_add_mul (p : FiniteDist Ω) (s : Finset Ω) (f g : Ω → ℝ) (c : ℝ) :
    condMean p s (fun ω => f ω + c * g ω) = condMean p s f + c * condMean p s g := by
  simp only [condMean, wsum, mul_add, sum_add_distrib, add_div]
  congr 1
  rw [mul_div_assoc', mul_sum]
  congr 1
  exact sum_congr rfl fun _ _ => by ring

/-- **The true parameter solves the stage-one equation.** Under the structural model on `P` at
`ψs`, no unmeasured confounding at the secondary baseline and positivity, `Φ(ψs) = 0`. -/
theorem stageOne_eq_zero {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {w : 𝓛 → ℝ}
    {B : Ω → ℝ} {ψs : ℝ} (hmodel : M.ModelOn P B ψs) (hnuc : M.BaselineNUC p P L)
    (hpos : M.BaselinePositive p P L w) : M.stageOne p P L w B ψs = 0 := by
  refine sum_eq_zero fun l _ => ?_
  by_cases hw : w l = 0
  · rw [hw, zero_mul]
  obtain ⟨h1, h0⟩ := hpos l hw
  have hc : ∀ x, condMean p (M.cell P L x l) (M.resid B ψs) =
      condMean p (M.cell P L x l) (fun ω => M.U ω - M.S ω) := fun x =>
    condMean_congr fun ω hω => by
      rw [resid, hmodel ω (mem_inter.1 (mem_inter.1 hω).1).1]
  rw [hc, hc, cell, cell, M.condMean_switch_eq (hnuc l) h1 h0, sub_self, mul_zero]

/-- The slope of the stage-one equation in `exp ψ`: the weighted mean time on the switch
treatment among switchers, `a = ∑_l w_l E[treated | X = 1, L = l, P]`. -/
noncomputable def stageOneSlope (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (w : 𝓛 → ℝ)
    (B : Ω → ℝ) : ℝ :=
  ∑ l, w l * condMean p (M.cell P L true l) (M.treated B)

/-- The intercept of the stage-one equation. -/
noncomputable def stageOneIntercept (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛)
    (w : 𝓛 → ℝ) (B : Ω → ℝ) : ℝ :=
  ∑ l, w l * (condMean p (M.cell P L true l) (M.baseResid B) -
    condMean p (M.cell P L false l) (M.baseResid B))

omit [Fintype 𝓛] in
/-- Non-switchers have no treated time. -/
theorem condMean_treated_nonswitchers (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (l : 𝓛)
    (B : Ω → ℝ) : condMean p (M.cell P L false l) (M.treated B) = 0 := by
  rw [condMean_congr (g := fun _ => 0) fun ω hω => by
    simp [treated, (mem_ev.1 (mem_inter.1 hω).2)]]
  simp [condMean, wsum]

/-- **The stage-one equation is affine in `exp ψ`:** `Φ(ψ) = c + exp ψ a`, with `a` the
weighted mean time on the switch treatment among switchers. -/
theorem stageOne_eq (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) (w : 𝓛 → ℝ)
    (B : Ω → ℝ) (ψ : ℝ) :
    M.stageOne p P L w B ψ =
      M.stageOneIntercept p P L w B + Real.exp ψ * M.stageOneSlope p P L w B := by
  simp only [stageOne, stageOneIntercept, stageOneSlope, mul_sum]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  have e : ∀ x, condMean p (M.cell P L x l) (M.resid B ψ) =
      condMean p (M.cell P L x l) (M.baseResid B) +
        Real.exp ψ * condMean p (M.cell P L x l) (M.treated B) := fun x => by
    rw [← condMean_add_mul]; exact condMean_congr fun ω _ => M.resid_eq B ψ ω
  rw [e, e, M.condMean_treated_nonswitchers]
  ring

/-- **Uniqueness of the root under relevance.** If the true parameter `ψs` solves the stage-one
equation and switchers spend positive weighted mean time on the switch treatment
(`0 < stageOneSlope`, the relevance condition), then `ψs` is its only root, and
`exp ψs = - c / a`. -/
theorem stageOne_eq_zero_iff {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {w : 𝓛 → ℝ}
    {B : Ω → ℝ} {ψs : ℝ} (hroot : M.stageOne p P L w B ψs = 0)
    (hrel : 0 < M.stageOneSlope p P L w B) (ψ : ℝ) :
    M.stageOne p P L w B ψ = 0 ↔ ψ = ψs := by
  refine ⟨fun h => ?_, fun h => h ▸ hroot⟩
  rw [stageOne_eq] at h hroot
  have : Real.exp ψ = Real.exp ψs := by
    have := mul_right_cancel₀ hrel.ne' (show Real.exp ψ * _ = Real.exp ψs * _ by linarith)
    exact this
  exact Real.exp_injective this

theorem exp_eq_of_stageOne_eq_zero {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛}
    {w : 𝓛 → ℝ} {B : Ω → ℝ} {ψs : ℝ} (hroot : M.stageOne p P L w B ψs = 0)
    (hrel : M.stageOneSlope p P L w B ≠ 0) :
    Real.exp ψs = - M.stageOneIntercept p P L w B / M.stageOneSlope p P L w B := by
  rw [stageOne_eq] at hroot
  field_simp
  linarith

/-- **Without relevance the equation does not identify the parameter:** if the slope vanishes,
`Φ` is constant, so either every `ψ` is a root or none is. -/
theorem stageOne_const_of_slope_eq_zero {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛}
    {w : 𝓛 → ℝ} {B : Ω → ℝ} (h : M.stageOneSlope p P L w B = 0) (ψ ψ' : ℝ) :
    M.stageOne p P L w B ψ = M.stageOne p P L w B ψ' := by
  rw [stageOne_eq, stageOne_eq, h]; ring

/-- **Relevance from primitive conditions.** With nonnegative weights, positivity, and switchers
of `P` alive strictly after the start `B`, the slope is positive as soon as one weight is
positive. -/
theorem stageOneSlope_pos {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {w : 𝓛 → ℝ}
    {B : Ω → ℝ} (hw : ∀ l, 0 ≤ w l) (hpos : M.BaselinePositive p P L w)
    (htreat : ∀ ω ∈ P, M.X ω = true → B ω < M.T ω) {l₀ : 𝓛} (hl₀ : 0 < w l₀) :
    0 < M.stageOneSlope p P L w B := by
  have hterm : ∀ l, 0 < w l → 0 < condMean p (M.cell P L true l) (M.treated B) := by
    intro l hl
    have h1 := (hpos l hl.ne').1
    obtain ⟨ω, hω, hne⟩ := exists_ne_zero_of_sum_ne_zero h1.ne'
    have hpω : 0 < p ω := (p.nonneg ω).lt_of_ne (Ne.symm hne)
    have hωP : ω ∈ P := (mem_inter.1 (mem_inter.1 hω).1).1
    have hX : M.X ω = true := mem_ev.1 (mem_inter.1 hω).2
    have hnn : ∀ ω' ∈ M.cell P L true l, 0 ≤ p ω' * M.treated B ω' := fun ω' hω' => by
      have hX' : M.X ω' = true := mem_ev.1 (mem_inter.1 hω').2
      have := htreat ω' (mem_inter.1 (mem_inter.1 hω').1).1 hX'
      simp only [treated, hX', ite_true]
      exact mul_nonneg (p.nonneg ω') (by linarith)
    have hlt : 0 < p ω * M.treated B ω := by
      simp only [treated, hX, ite_true]
      exact mul_pos hpω (by linarith [htreat ω hωP hX])
    exact div_pos (hlt.trans_le (single_le_sum hnn hω)) h1
  have hnn : ∀ l ∈ (univ : Finset 𝓛), 0 ≤ w l * condMean p (M.cell P L true l) (M.treated B) :=
    fun l _ => by
      rcases (hw l).eq_or_lt with h | h
      · rw [← h, zero_mul]
      · exact (mul_pos h (hterm l h)).le
  exact (mul_pos hl₀ (hterm l₀ hl₀)).trans_le (single_le_sum hnn (mem_univ l₀))

end StageOne

/-! ### Stage two: the transformed control arm -/

section StageTwo

/-- **The structural model in the control arm** (stage two of the simple method): every control
patient follows `U = adjusted B ψ`, with the adjusted switchers transformed and the others
untouched. -/
def ControlModel (B : Ω → ℝ) (ψ : ℝ) : Prop := ∀ ω, M.R ω = false → M.U ω = M.adjusted B ψ ω

/-- **The analysis data of the simple method:** the experimental arm as observed, the control
arm transformed with the parameter `ψ`. A function of the observed data. -/
noncomputable def analysisTime (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) : ℝ :=
  if M.R ω then M.T ω else M.adjusted B ψ ω

/-- **The per-arm analysis data** (TSD 24, Section 4.2.3.1, "Adjusting for multiple types of
switching"): each arm transformed with its own parameter, `ψ₁` in the experimental arm and `ψ₀`
in the control arm. -/
noncomputable def perArmTime (B : Ω → ℝ) (ψ₀ ψ₁ : ℝ) (ω : Ω) : ℝ :=
  M.adjusted B (if M.R ω then ψ₁ else ψ₀) ω

/-- The structural model with unit specific parameters, in terms of the transformation. -/
theorem U_eq_of_followsModel {B : Ω → ℝ} {ψi : Ω → ℝ}
    (h : (M.toSwitchingTrial B).FollowsModel ψi) (ω : Ω) : M.U ω = M.adjusted B (ψi ω) ω :=
  h ω

variable [MeasurableSpace Ω] {μ : Measure Ω}

variable {M} in
/-- Two variables that agree on an arm have the same mean and the same law in that arm. -/
theorem armMean_armLaw_congr {N : SwitchingTrial Ω} (hR : Measurable N.R) {f g : Ω → ℝ}
    {r : Bool} (h : ∀ ω, N.R ω = r → f ω = g ω) :
    N.armMean μ f r = N.armMean μ g r ∧ N.armLaw μ f r = N.armLaw μ g r := by
  have hae : f =ᵐ[μ[|N.arm r]] g := by
    filter_upwards [ae_cond_mem (μ := μ) (N.measurableSet_arm hR r)] with ω hω using h ω hω
  exact ⟨integral_congr_ae hae, Measure.map_congr hae⟩

/-- **Stage two recovers the untreated control arm.** Under the structural model in the control
arm at the true parameter `ψs`, the transformed control arm has the mean and the law of the
untreated times in the control arm. -/
theorem control_armMean_armLaw (B : Ω → ℝ) {ψs : ℝ} (hR : Measurable M.R)
    (h : M.ControlModel B ψs) :
    (M.toSwitchingTrial B).armMean μ (M.analysisTime B ψs) false =
        (M.toSwitchingTrial B).armMean μ M.U false ∧
      (M.toSwitchingTrial B).armLaw μ (M.analysisTime B ψs) false =
        (M.toSwitchingTrial B).armLaw μ M.U false :=
  armMean_armLaw_congr (N := M.toSwitchingTrial B) hR fun ω hω => by
    have hω' : M.R ω = false := hω
    rw [analysisTime, hω', h ω hω']; rfl

/-- **The simple two-stage method targets the hypothetical estimand** (TSD 16, Section 3.2.4;
TSD 24, Sections 3.2 and 4.2.3). Under the structural model in the control arm at the true
parameter, the mean contrast of the analysis data (experimental arm as observed against the
transformed control arm) is the hypothetical estimand of
`CausalInference.StructuralNested.SwitchingTrial`: `E[T | R = 1] - E[U | R = 0]`, the
experimental arm as delivered against a control arm without the adjusted switch.

When the experimental arm also receives subsequent treatments, they are part of the
experimental arm as delivered: this is not the effect under "no subsequent treatment in either
arm", which is `perArm_meanContrast`. No randomization is used: the identification of `ψs`
rests on stage one; randomization only lets the control arm untreated law stand for the
population one (`control_armLaw_eq_map`). -/
theorem analysis_meanContrast (B : Ω → ℝ) {ψs : ℝ} (hR : Measurable M.R)
    (h : M.ControlModel B ψs) :
    (M.toSwitchingTrial B).meanContrast μ (M.analysisTime B ψs) =
      (M.toSwitchingTrial B).hypotheticalEffect μ := by
  have e1 := (armMean_armLaw_congr (μ := μ) (N := M.toSwitchingTrial B) (f :=
    M.analysisTime B ψs) (g := M.T) hR (r := true) fun ω hω => by
      have hω' : M.R ω = true := hω
      simp [analysisTime, hω']).1
  rw [SwitchingTrial.meanContrast, SwitchingTrial.hypotheticalEffect, e1,
    (M.control_armMean_armLaw B hR h).1]
  rfl

/-- Under randomization (`U` independent of the arm), the transformed control arm has the
population law of the untreated time. -/
theorem control_armLaw_eq_map [IsFiniteMeasure μ] (B : Ω → ℝ) {ψs : ℝ} (hR : Measurable M.R)
    (hU : Measurable M.U) (h : M.ControlModel B ψs)
    (hrand : (M.toSwitchingTrial B).Randomized μ)
    (h0 : μ ((M.toSwitchingTrial B).arm false) ≠ 0) :
    (M.toSwitchingTrial B).armLaw μ (M.analysisTime B ψs) false = μ.map M.U := by
  rw [(M.control_armMean_armLaw B hR h).2]
  exact SwitchingTrial.armLaw_U_of_randomized hR hU hrand h0

omit [MeasurableSpace Ω] in
/-- **The per-arm method targets the estimand without the adjusted switches in either arm**
(TSD 24, Section 4.2.3.1). If both arms follow the structural model, each with its own
parameter (`ψ₁` for the subsequent treatment in the experimental arm, `ψ₀` in the control arm),
the per-arm data are the untreated times, so their mean contrast is `E[U | R = 1] - E[U | R = 0]`
and their arm laws are the laws of `U`. -/
theorem perArm_eq {B : Ω → ℝ} {ψ₀ ψ₁ : ℝ}
    (h : (M.toSwitchingTrial B).FollowsModel fun ω => if M.R ω then ψ₁ else ψ₀) :
    M.perArmTime B ψ₀ ψ₁ = M.U := by
  funext ω; rw [M.U_eq_of_followsModel h ω]; rfl

theorem perArm_meanContrast {B : Ω → ℝ} {ψ₀ ψ₁ : ℝ}
    (h : (M.toSwitchingTrial B).FollowsModel fun ω => if M.R ω then ψ₁ else ψ₀) :
    (M.toSwitchingTrial B).meanContrast μ (M.perArmTime B ψ₀ ψ₁) =
      (M.toSwitchingTrial B).meanContrast μ M.U := by
  rw [M.perArm_eq h]

/-- **The two estimands differ by the effect of subsequent treatment in the experimental arm.**
Under the per-arm structural model, with integrable `T` and treated time and an experimental arm
of positive probability,
`E[U | R = 1] - E[U | R = 0] = (E[T | R = 1] - E[U | R = 0]) - (1 - exp ψ₁) E[treated | R = 1]`.
So if the subsequent treatment in the experimental arm prolongs survival (`ψ₁ < 0`) and is
received for a positive mean time, the per-arm estimand is strictly smaller than the estimand of
the control-only analysis (`perArm_lt_analysis`). -/
theorem perArm_meanContrast_eq {B : Ω → ℝ} {ψ₀ ψ₁ : ℝ} (hR : Measurable M.R)
    (h : (M.toSwitchingTrial B).FollowsModel fun ω => if M.R ω then ψ₁ else ψ₀)
    (hT : Integrable M.T μ) (hTe : Integrable (M.treated B) μ)
    (h1 : μ ((M.toSwitchingTrial B).arm true) ≠ 0) :
    (M.toSwitchingTrial B).meanContrast μ (M.perArmTime B ψ₀ ψ₁) =
      (M.toSwitchingTrial B).hypotheticalEffect μ -
        (1 - Real.exp ψ₁) * (M.toSwitchingTrial B).armMean μ (M.treated B) true := by
  have eU := (armMean_armLaw_congr (μ := μ) (N := M.toSwitchingTrial B) (f := M.U)
    (g := (M.toSwitchingTrial B).counterfactual ψ₁) hR (r := true) fun ω hω => by
      have hω' : M.R ω = true := hω
      rw [M.U_eq_of_followsModel h ω, hω']; rfl).1
  have ec := SwitchingTrial.armMean_counterfactual (M := M.toSwitchingTrial B) hT hTe h1 ψ₁
  rw [perArm_meanContrast M h, SwitchingTrial.meanContrast, SwitchingTrial.hypotheticalEffect,
    eU, ec]
  simp only [toSwitchingTrial]
  ring

theorem perArm_lt_analysis {B : Ω → ℝ} {ψ₀ ψ₁ : ℝ} (hR : Measurable M.R)
    (h : (M.toSwitchingTrial B).FollowsModel fun ω => if M.R ω then ψ₁ else ψ₀)
    (hT : Integrable M.T μ) (hTe : Integrable (M.treated B) μ)
    (h1 : μ ((M.toSwitchingTrial B).arm true) ≠ 0) (hψ : ψ₁ < 0)
    (hpos : 0 < (M.toSwitchingTrial B).armMean μ (M.treated B) true) :
    (M.toSwitchingTrial B).meanContrast μ (M.perArmTime B ψ₀ ψ₁) <
      (M.toSwitchingTrial B).meanContrast μ (M.analysisTime B ψ₀) := by
  have hc : M.ControlModel B ψ₀ := fun ω hω => by rw [M.U_eq_of_followsModel h ω, hω]; rfl
  rw [M.perArm_meanContrast_eq hR h hT hTe h1, M.analysis_meanContrast B hR hc]
  have : Real.exp ψ₁ < 1 := by simpa using Real.exp_lt_exp.2 hψ
  nlinarith

omit [MeasurableSpace Ω] in
/-- **Separate effects per subsequent treatment** (TSD 24, Section 4.2.3.1). The structural
model with a parameter for each patient (`FollowsModel ψi`, for instance `ψi ω = θ (type ω)`
with one parameter per subsequent treatment and arm) is recovered by transforming each patient
with its own parameter. A pooled transformation with one parameter cannot recover the untreated
times of two switchers with positive treated time whose parameters differ. -/
theorem not_pooled_of_ne {B : Ω → ℝ} {ψi : Ω → ℝ} (h : (M.toSwitchingTrial B).FollowsModel ψi)
    {ω₁ ω₂ : Ω} (h₁ : 0 < M.treated B ω₁) (h₂ : 0 < M.treated B ω₂) (hne : ψi ω₁ ≠ ψi ω₂)
    (ψ : ℝ) : ¬ (M.U ω₁ = M.adjusted B ψ ω₁ ∧ M.U ω₂ = M.adjusted B ψ ω₂) := by
  rintro ⟨e₁, e₂⟩
  have k : ∀ ω, 0 < M.treated B ω → M.U ω = M.adjusted B ψ ω → ψi ω = ψ := fun ω hω e => by
    rw [M.U_eq_of_followsModel h ω] at e
    simp only [adjusted, SwitchingTrial.counterfactual, toSwitchingTrial, add_right_inj] at e
    exact Real.exp_injective (mul_right_cancel₀ hω.ne' e)
  exact hne ((k ω₁ h₁ e₁).trans (k ω₂ h₂ e₂).symm)

end StageTwo

/-! ### Recensoring on the post-baseline scale -/

section Recensoring

/-- **The post-baseline trial.** The time origin is moved to the secondary baseline: survival
`T - S`, censoring `C - S`, untreated time `U - S`, and the treatment path of an adjusted
switcher is "on treatment after `B - S`" (the switch time for Equation (1), `0` for the baseline
form); others are never treated. This is a trial of
`CausalInference.StructuralNested.CensoredTrial`, to which recensoring applies. -/
def postBaseline (B : Ω → ℝ) : CensoredTrial Ω where
  R := M.R
  T ω := M.T ω - M.S ω
  A ω := if M.X ω then Ioi (B ω - M.S ω) else ∅
  C ω := M.C ω - M.S ω
  U ω := M.U ω - M.S ω

/-- The cohort of patients who reached the secondary baseline before the end of follow-up, with
adjusted switches starting between the secondary baseline and death. -/
structure Cohort (B : Ω → ℝ) : Prop where
  S_le_T : ∀ ω, M.S ω ≤ M.T ω
  S_le_C : ∀ ω, M.S ω ≤ M.C ω
  S_le_B : ∀ ω, M.X ω = true → M.S ω ≤ B ω
  B_le_T : ∀ ω, M.X ω = true → B ω ≤ M.T ω

variable {M} in
theorem Cohort.wellFormed {B : Ω → ℝ} (h : M.Cohort B) : (M.postBaseline B).WellFormed where
  measurableSet_path ω := by
    simp only [postBaseline]; split_ifs
    · exact measurableSet_Ioi
    · exact MeasurableSet.empty
  T_nonneg ω := sub_nonneg.2 (h.S_le_T ω)
  C_nonneg ω := sub_nonneg.2 (h.S_le_C ω)

variable {M} in
/-- **The untreated post-baseline time along the post-baseline path is the transformed residual
survival:** `∫_0^{T - S} exp (ψ A(s)) ds = adjusted B ψ - S`. -/
theorem Cohort.untreatedTime_postBaseline {B : Ω → ℝ} (h : M.Cohort B) (ψ : ℝ) (ω : Ω) :
    untreatedTime ψ ((M.postBaseline B).A ω) ((M.postBaseline B).T ω) = M.resid B ψ ω := by
  simp only [postBaseline, resid]
  cases hX : M.X ω
  · simp [untreatedTime_empty, M.adjusted_of_not_switch B ψ hX]
  · have h0 : 0 ≤ B ω - M.S ω := sub_nonneg.2 (h.S_le_B ω hX)
    have h1 : B ω - M.S ω ≤ M.T ω - M.S ω := by linarith [h.B_le_T ω hX]
    simp only [ite_true]
    rw [StructuralNested.untreatedTime_eq
        (show MeasurableSet (Ioi (B ω - M.S ω)) from measurableSet_Ioi),
      ← treatmentGroupPath, timeOn_treatmentGroupPath h0 (h0.trans h1), min_eq_left h1,
      M.adjusted_of_switch B ψ hX]
    ring

/-- The recensored post-baseline record of each patient for a candidate `ψ`, computed from the
observed data: the transformed post-baseline follow-up censored at the recensoring time
`min (C - S, exp ψ (C - S))`, applied to switchers and non-switchers alike. -/
noncomputable def recensored (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) : ℝ × Bool :=
  (M.postBaseline B).recensored ψ ω

/-- **The recensored record is a function of the observed post-baseline data** (follow-up,
event indicator, time on the switch treatment during follow-up, censoring time). -/
theorem recensored_eq_comp_observed (B : Ω → ℝ) (ψ : ℝ) :
    M.recensored B ψ = (fun o ↦ recensorData ψ o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2) ∘
      (M.postBaseline B).observed :=
  rfl

variable {M} in
/-- **At the true parameter the recensored record is the untreated post-baseline time censored
at the recensoring time**: for every patient of the cohort who follows the structural model,
`(min (U - S, D*), 1{U - S ≤ D*})` with `D* = min (C - S, exp ψ (C - S))`, which depends on the
censoring time only, not on the switch. -/
theorem Cohort.recensored_eq {B : Ω → ℝ} (h : M.Cohort B) {ψ : ℝ} {ω : Ω}
    (hU : M.U ω = M.adjusted B ψ ω) :
    M.recensored B ψ ω = censorAt (M.U ω - M.S ω) (recensoringTime ψ (M.C ω - M.S ω)) := by
  have e := recensorData_eq (h.wellFormed.measurableSet_path ω) ψ
    (t := (M.postBaseline B).T ω) (h.wellFormed.C_nonneg ω)
  rw [h.untreatedTime_postBaseline ψ ω, resid, ← hU] at e
  exact e

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Independent censoring on the post-baseline scale within the control arm**: the untreated
post-baseline time `U - S` is independent of the post-baseline censoring time `C - S` given
`R = false`. This is an assumption of its own: the secondary baseline is prognostic, so it does
not follow from independence of `U` and `C`. -/
def ControlIndepCensoring : Prop :=
  IndepFun (fun ω => M.U ω - M.S ω) (fun ω => M.C ω - M.S ω) (μ[|M.R ⁻¹' {false}])

variable {M} in
/-- **Recensoring gives the untreated post-baseline survival of the control arm up to the
recensored follow-up** (TSD 16, Section 3.3.2 and TSD 24, Section 4.2.3.1: recensoring is needed
for two-stage methods as well). For the cohort, under the structural model in the control arm
at `ψs` and independent post-baseline censoring in the control arm, at every `t` at which the
recensoring time exceeds `t` with positive probability in the control arm,
`P(U - S > t | R = 0) = P(recensored time > t | R = 0) / P(D* > t | R = 0)`. -/
theorem Cohort.control_survival_eq_div (hR : Measurable M.R) {B : Ω → ℝ} (h : M.Cohort B)
    {ψs : ℝ} (hmodel : M.ControlModel B ψs) (hind : M.ControlIndepCensoring (μ := μ)) {t : ℝ}
    (hD : (μ[|M.R ⁻¹' {false}]).real
      {ω | t < recensoringTime ψs (M.C ω - M.S ω)} ≠ 0) :
    (μ[|M.R ⁻¹' {false}]).real {ω | t < M.U ω - M.S ω} =
      (μ[|M.R ⁻¹' {false}]).real {ω | t < (M.recensored B ψs ω).1} /
        (μ[|M.R ⁻¹' {false}]).real {ω | t < recensoringTime ψs (M.C ω - M.S ω)} := by
  have hprod := CensoredTrial.measureReal_recensored_gt (M := M.postBaseline B) hind ψs t
  have hae : {ω | t < (M.recensored B ψs ω).1} =ᵐ[μ[|M.R ⁻¹' {false}]]
      {ω | t < (censorAt ((M.postBaseline B).U ω) ((M.postBaseline B).recensTime ψs ω)).1} := by
    filter_upwards [ae_cond_mem (μ := μ) (hR (measurableSet_singleton false))] with ω hω
    have hω' : M.R ω = false := hω
    rw [h.recensored_eq (hmodel ω hω')]
    rfl
  rw [measureReal_congr hae, eq_div_iff hD]
  exact hprod.symm

end Recensoring

end TwoStageTrial

end StructuralNested

end CausalInference
