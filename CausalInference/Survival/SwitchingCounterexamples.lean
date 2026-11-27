/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.IPCW
public import CausalInference.Survival.SwitchDecision

/-!
# Treatment switching: counterexamples for the simple analyses

Concrete models in which a simple analysis of a trial with treatment switching misses the
hypothetical estimand (survival had the switches not occurred), while the other assumptions of
the setting hold: the arms are randomized, the relevant positivity condition holds, and the
analysis fails only through the assumption that the documents say can fail.

The models are finite (`FiniteDist`, conditional independence `FiniteDist.CondIndepFun`); the
model of `CensorExclude` is the measure `FiniteDist.toMeasure` of a finite distribution, so that
the product-limit functional of `CausalInference.Survival.Censoring` applies.

## Main results

* Censoring and excluding switchers (TSD 16, Section 3.1.2), `CensorExclude`: switching in the
  control arm depends on the unmeasured prognosis, with switchers and non-switchers in both
  prognosis groups (`overlap`). The censored data of the control arm are those of the untreated
  time (`observed_eq`), censoring is informative (`not_indepFun`), and the product-limit
  functional at time `2` is `3/4` while the untreated survival is `1/2`, so the per-protocol
  contrast is `1/4` instead of `1/2` (`censored_contrast`); the survival of the non-switchers
  is `3/4` (`excluded_survival`).
* Groups defined by the observed switch (TSD 24, Section 3.2), `PrincipalStrata`: under the
  sharp null, with randomized arms, the arm contrast within the observed non-switchers and
  within the observed switchers is `-1/2`, while the intention-to-treat contrast is `0`
  (`stratum_contrast_ne`). The observed switch status is not a principal stratum: within each
  principal stratum, defined by the pair of potential switch statuses `(S0, S1)`, the contrast
  is `0` (`principal_contrast`).
* Time-dependent confounding between the secondary baseline and the switch (TSD 16, Section
  3.2.4; TSD 24, Section 4.2.3), `TimeDependent`: progression at time `0`, a covariate measured
  in the first interval, the switch decision at time `1`. The covariate drives the switch and
  survival. No unmeasured confounding holds given the full covariate path
  (`condIndepFun_full`) and fails given the record at progression
  (`not_condIndepFun_baseline`). Stage one of the simple two-stage method, adjusted for the
  record at progression, gives the time ratio `6/5` instead of `2` (`tse_stage_one`); `6/5` is
  the unique root of the mean-balancing estimating equation (`tse_stage_one_root`). Stage two
  then gives the mean survival `7/2` instead of `3` (`tse_stage_two`). The log-time equation,
  the least-squares fit of `log Y` on the switch indicator, has the unique root `2 / √3`
  (`tse_stage_one_log_root`), which differs from `6/5` and from `2`; stage two then gives
  `(9 + 3 √3) / 4` instead of `3` (`tse_log_root_biased`).
* The delay between progression and the switch decision (TSD 16, Sections 3.2.4 and 6), same
  switch rule and outcomes: in a family indexed by the delay `d ∈ [0, 1]`, in which a patient
  has deteriorated by the decision time with probability `d / 2`, the stage-one factor is
  `6 (3 - d) / ((1 + d) (9 - 4 d))` (`delay_stage_one_root`) and the bias of the second-stage
  mean is `d (2 - d) / (3 - d)` (`delay_bias`): zero at zero delay (`delay_zero`) and strictly
  increasing in the delay (`delayBias_strictMonoOn`). This is one family illustrating the
  printed claim, not a general theorem.
* Covariate collection stopped at progression (TSD 24, Section 4.2.2.1), same model: inverse
  probability of censoring weights built from the full record recover the mean residual
  survival without switching, `2`; weights built from the record truncated at progression give
  `5/2` (`ipcw_truncated`). For the survival weighting functional of `Survival.IPCW`, the
  weighted hazard at time `2` is the true `1/2` with the full history and `1/4` with the
  truncated history, with positive stay probabilities in both (`weightedHazard_truncated`).

The first-stage factors are the population roots of two estimating equations without
censoring, the mean-balancing and the log-time least-squares equation; the parametric (for
instance Weibull) accelerated failure time fit of the documents solves a different score
equation and is not formalized.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014), Sections 3.1.2, 3.2.4 and 6.
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to TSD 16*
  (2024), Sections 3.2, 4.2.2.1 and 4.2.3.
-/

@[expose] public section

namespace CausalInference

namespace SwitchingCounterexamples

open Finset

section Helpers

variable {Ω : Type*} [Fintype Ω]

/-- The conditional mean `E[Y | P] = E[Y 1{P}] / P(P)` of a real random variable given an
event. It is a conditional mean only when `P(P) > 0`; every use below comes with that
positivity statement. -/
noncomputable def condMean (p : FiniteDist Ω) (P : Ω → Prop) [DecidablePred P] (Y : Ω → ℝ) :
    ℝ :=
  p.expect (fun ω => if P ω then Y ω else 0) / p.probOf P

/-- Under a product distribution, an event about the first coordinate and an event about the
second are independent. -/
theorem probOf_prod_and {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (p : FiniteDist Ω₁)
    (q : FiniteDist Ω₂) (A : Ω₁ → Prop) (B : Ω₂ → Prop) [DecidablePred A] [DecidablePred B] :
    (p.prod q).probOf (fun ω => A ω.1 ∧ B ω.2) = p.probOf A * q.probOf B := by
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter, Fintype.sum_prod_type,
    FiniteDist.prod_apply, Finset.sum_mul_sum, ite_and]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

end Helpers

/-! ### Principal strata defined by the observed switch -/

namespace PrincipalStrata

/-- The sample space: a point is `(r, l)`, the randomized arm (`true` for experimental) and a
prognostic level `l`, from good (`0`) to poor (`2`). -/
abbrev Ω := Bool × Fin 3

/-- Arm and prognosis are independent and uniform: the arm is randomized. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform.prod FiniteDist.uniform

/-- The randomized arm. -/
def R (ω : Ω) : Bool := ω.1

/-- The survival time, determined by the prognostic level alone: `3`, `2`, `1` for levels
`0`, `1`, `2`. Neither the randomized treatment nor the subsequent treatment affects it (sharp
null), so every potential survival time equals `Y`. -/
noncomputable def Y (ω : Ω) : ℝ := 3 - (ω.2 : ℕ)

/-- The observed switch to a subsequent treatment, which follows progression. The
experimental treatment delays progression: in the control arm patients of levels `1` and `2`
progress and switch, in the experimental arm only those of level `2`. -/
def S (ω : Ω) : Bool := if ω.1 then (ω.2 : ℕ) = 2 else 1 ≤ (ω.2 : ℕ)

/-- Randomization: the arm is independent of the prognostic level. -/
theorem randomized (r : Bool) (l : Fin 3) :
    p.probOf (fun ω => R ω = r ∧ ω.2 = l) =
      p.probOf (fun ω => R ω = r) * p.probOf (fun ω => ω.2 = l) := by
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, R]
  cases r <;> fin_cases l <;> norm_num

/-- Every arm-by-stratum event has positive probability, so the conditional means below are
genuine. -/
theorem stratum_pos (r s : Bool) : 0 < p.probOf (fun ω => R ω = r ∧ S ω = s) := by
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, R, S]
  cases r <;> cases s <;> norm_num

/-- Comparing the arms within the groups defined by the observed switch status is biased
(TSD 24, Section 3.2). The treatment has no effect on survival, and the intention-to-treat
contrast `E[Y | R = 1] - E[Y | R = 0]` is `0`; but within the observed non-switchers, and
within the observed switchers, the experimental arm has mean survival `1/2` lower than the
control arm. The observed switch status `S` is a consequence of treatment (through
progression) and of prognosis, so conditioning on it breaks the balance created by
randomization. It is not a principal stratum: the principal strata are defined by the pair
`(S0, S1)` of potential switch statuses, and within each of them the arm contrast is `0`
(`principal_contrast`). The `-1/2` compares different mixtures of principal strata. -/
theorem stratum_contrast_ne :
    condMean p (fun ω => R ω = true) Y - condMean p (fun ω => R ω = false) Y = 0 ∧
    condMean p (fun ω => R ω = true ∧ S ω = false) Y -
      condMean p (fun ω => R ω = false ∧ S ω = false) Y = -1 / 2 ∧
    condMean p (fun ω => R ω = true ∧ S ω = true) Y -
      condMean p (fun ω => R ω = false ∧ S ω = true) Y = -1 / 2 := by
  simp only [condMean, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, R, S, Y]
  norm_num

/-- The potential switch status under control: patients of levels `1` and `2` progress and
switch. -/
def S0 (ω : Ω) : Bool := 1 ≤ (ω.2 : ℕ)

/-- The potential switch status under the experimental treatment: only patients of level `2`
progress and switch. -/
def S1 (ω : Ω) : Bool := (ω.2 : ℕ) = 2

/-- Consistency: the observed switch status is the potential switch status of the assigned
arm. -/
theorem S_eq (ω : Ω) : S ω = if R ω then S1 ω else S0 ω := rfl

/-- The stratum `(S0, S1) = (false, true)` is empty: nobody switches only under the
experimental treatment. -/
theorem principal_empty (ω : Ω) : ¬ (S0 ω = false ∧ S1 ω = true) := by
  rcases ω with ⟨_, l⟩; fin_cases l <;> simp [S0, S1]

/-- The three other principal strata `(S0, S1)` have positive probability in each arm. -/
theorem principal_pos (r s0 s1 : Bool) (h : ¬ (s0 = false ∧ s1 = true)) :
    0 < p.probOf (fun ω => R ω = r ∧ S0 ω = s0 ∧ S1 ω = s1) := by
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, R, S0, S1]
  cases r <;> cases s0 <;> cases s1 <;> simp at h ⊢

/-- Within every principal stratum, the pair `(S0, S1)` of potential switch statuses, the arm
contrast of mean survival is `0`: the principal strata are baseline characteristics, balanced
by randomization, and under the sharp null every principal causal effect vanishes. Compare
`stratum_contrast_ne`, which conditions on the observed switch status. -/
theorem principal_contrast (s0 s1 : Bool) :
    condMean p (fun ω => R ω = true ∧ S0 ω = s0 ∧ S1 ω = s1) Y -
      condMean p (fun ω => R ω = false ∧ S0 ω = s0 ∧ S1 ω = s1) Y = 0 := by
  simp only [condMean, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, R, S0, S1, Y]
  cases s0 <;> cases s1 <;> norm_num

end PrincipalStrata

/-! ### Time-dependent confounding after the secondary baseline, and truncated collection -/

namespace TimeDependent

/-- The sample space of the control arm after the secondary baseline (disease progression):
a point is `(l, n)`, where `l = true` means that the patient deteriorated between progression
and the switch decision, and `n` is the noise of the decision.

The clock: time `0` is progression, the covariate `L1` is measured during the first interval,
and the switch decision is taken at time `1` (`decisionTime`); nobody dies before it. The
outcomes `Y0`, `Y1`, `Y` are residual survival times after the decision time, and
`T0 = 1 + Y0` is the survival time from progression without switching. -/
abbrev Ω := Bool × Fin 4

/-- Deterioration and noise are independent and uniform. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform.prod FiniteDist.uniform

/-- The covariate record at the secondary baseline. All patients are at a similar stage at
progression, so it is constant. -/
def L0 (_ : Ω) : Unit := ()

/-- The time-dependent covariate: deterioration after the secondary baseline, before the
switch. -/
def L1 (ω : Ω) : Bool := ω.1

/-- The switch decision, taken on the information `L1` with independent noise: a deteriorated
patient switches with probability `3/4`, another with probability `1/4`. -/
def switchRule (l : Bool) (n : Fin 4) : Bool := if l then (n : ℕ) < 3 else (n : ℕ) < 1

/-- The switch. -/
def S (ω : Ω) : Bool := switchRule (L1 ω) ω.2

/-- The time of the switch decision, measured from progression. -/
noncomputable def decisionTime : ℝ := 1

/-- The potential residual survival after the decision time without switching, as a function
of deterioration: `1` if deteriorated, `3` otherwise. -/
noncomputable def y0 (l : Bool) : ℝ := if l then 1 else 3

/-- The potential residual survival after the decision time without switching. -/
noncomputable def Y0 (ω : Ω) : ℝ := y0 ω.1

/-- The potential residual survival after the decision time with switching: the switch
doubles it, for every patient. So the switching time ratio is `2`. -/
noncomputable def Y1 (ω : Ω) : ℝ := 2 * Y0 ω

/-- The observed residual survival after the decision time. -/
noncomputable def Y (ω : Ω) : ℝ := if S ω then Y1 ω else Y0 ω

/-- The survival time from progression without switching: `T0 = decisionTime + Y0`. -/
noncomputable def T0 (ω : Ω) : ℝ := decisionTime + Y0 ω

/-- The sure event has probability one. -/
theorem probOf_true {Ω' : Type*} [Fintype Ω'] (q : FiniteDist Ω') :
    q.probOf (fun _ => True) = 1 := by
  rw [FiniteDist.probOf, Finset.filter_true, FiniteDist.prob_univ]

/-- The noise of the decision is jointly independent of the potential outcomes and of the
time-dependent covariate. -/
theorem noiseIndep : SwitchDecision.NoiseIndep p (fun ω => (Y0 ω, Y1 ω)) L1 (fun ω => ω.2) := by
  intro y i e
  have h1 := probOf_prod_and FiniteDist.uniform FiniteDist.uniform
    (fun l => (y0 l, 2 * y0 l) = y ∧ l = i) (fun n : Fin 4 => n = e)
  have h2 := probOf_prod_and FiniteDist.uniform FiniteDist.uniform
    (fun l => (y0 l, 2 * y0 l) = y ∧ l = i) (fun _ : Fin 4 => True)
  have h3 := probOf_prod_and FiniteDist.uniform FiniteDist.uniform
    (fun _ : Bool => True) (fun n : Fin 4 => n = e)
  rw [probOf_true] at h2 h3
  simp only [mul_one, one_mul] at h2 h3
  refine ((p.probOf_congr (Q := fun ω : Ω => ((y0 ω.1, 2 * y0 ω.1) = y ∧ ω.1 = i) ∧
      ω.2 = e) fun _ => and_assoc.symm).trans h1).trans ?_
  rw [← h2, ← h3]
  congr 1
  exact p.probOf_congr fun _ => by simp [Y0, Y1, L1]

/-- No unmeasured confounding holds given the full covariate path: the switch is
conditionally independent of the potential outcomes given the time-dependent covariate `L1`
(by `SwitchDecision.condIndepFun_of_decision`). -/
theorem condIndepFun_full : p.CondIndepFun S (fun ω => (Y0 ω, Y1 ω)) L1 :=
  SwitchDecision.condIndepFun_of_decision _ L1 (fun ω => ω.2) switchRule noiseIndep

/-- But it fails given the record at the secondary baseline: the switch is not conditionally
independent of the potential survival without switching given `L0`. -/
theorem not_condIndepFun_baseline : ¬ p.CondIndepFun S Y0 L0 := by
  intro h
  have := h true 1 ()
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter] at this
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1, Y0, y0] at this
  norm_num at this

/-- Every event `S = s, L1 = l` has positive probability (positivity). -/
theorem switch_pos (s l : Bool) : 0 < p.probOf (fun ω => S ω = s ∧ L1 ω = l) := by
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1]
  cases s <;> cases l <;> norm_num

/-- Time-dependent confounding biases the simple two-stage method (TSD 16, Section 3.2.4;
TSD 24, Section 4.2.3). Stage one compares residual survival after the decision time of
switchers and non-switchers adjusted for the covariates at the secondary baseline. Here these
are constant, so the adjusted ratio of mean residual survival is the crude ratio
`E[Y | S = 1] / E[Y | S = 0] = 6/5`, while the switching time ratio is `2` for every patient
(`Y1 = 2 Y0`), and `E[Y1] / E[Y0] = 2`. Adjusting for the time-dependent covariate, the
standardized ratio `∑_l P(L1 = l) E[Y | S = 1, L1 = l] / ∑_l P(L1 = l) E[Y | S = 0, L1 = l]`
recovers `2`. The factor is a ratio of means; `tse_stage_one_root` gives the estimating
equation it solves. -/
theorem tse_stage_one :
    (∀ ω, Y1 ω = 2 * Y0 ω) ∧ p.expect Y1 / p.expect Y0 = 2 ∧
    condMean p (fun ω => S ω = true) Y / condMean p (fun ω => S ω = false) Y = 6 / 5 ∧
    (∑ l : Bool, p.probOf (fun ω => L1 ω = l) * condMean p (fun ω => S ω = true ∧ L1 ω = l) Y) /
      (∑ l : Bool, p.probOf (fun ω => L1 ω = l) *
        condMean p (fun ω => S ω = false ∧ L1 ω = l) Y) = 2 := by
  refine ⟨fun _ => rfl, ?_⟩
  simp only [condMean, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1, Y, Y1, Y0, y0]
  norm_num

/-- The residual survival with the effect of switching undone by a time ratio `ψ`: `Y / ψ` for
switchers, `Y` for non-switchers. -/
noncomputable def untreatedTime (ψ : ℝ) (ω : Ω) : ℝ := if S ω then Y ω / ψ else Y ω

/-- The estimating equation of stage one (TSD 16, Section 3.2.4), in the mean form: with the
covariates at the secondary baseline (constant here), the factor `ψ` is chosen so that the
residual survival with the switch effect undone, `untreatedTime ψ`, has the same mean among
switchers and non-switchers. Its unique nonzero root is the ratio of means `6/5` of
`tse_stage_one`, not the true time ratio `2`. -/
theorem tse_stage_one_root (ψ : ℝ) (hψ : ψ ≠ 0) :
    condMean p (fun ω => S ω = true) (untreatedTime ψ) =
      condMean p (fun ω => S ω = false) (untreatedTime ψ) ↔ ψ = 6 / 5 := by
  have h1 : condMean p (fun ω => S ω = true) (untreatedTime ψ) = 3 / ψ := by
    simp only [condMean, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob,
      Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
      FiniteDist.prod_apply, FiniteDist.uniform_apply, untreatedTime, S, switchRule, L1, Y, Y1,
      Y0, y0]
    norm_num
    field_simp
    ring
  have h2 : condMean p (fun ω => S ω = false) (untreatedTime ψ) = 5 / 2 := by
    simp only [condMean, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob,
      Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
      FiniteDist.prod_apply, FiniteDist.uniform_apply, untreatedTime, S, switchRule, L1, Y, Y1,
      Y0, y0]
    norm_num
  rw [h1, h2, div_eq_div_iff hψ two_ne_zero]
  constructor <;> intro h <;> linarith

/-- The survival time from progression after the second stage: the decision time plus the
residual survival with the switch effect undone by `ψ`. -/
noncomputable def adjustedTime (ψ : ℝ) (ω : Ω) : ℝ := decisionTime + untreatedTime ψ ω

/-- The second stage of the simple two-stage method is biased by time-dependent confounding.
The mean survival from progression without switching is `E[T0] = 3`. Undoing the switch with
the stage-one factor `6/5` gives the adjusted mean `7/2`; undoing it with the true time ratio
`2` gives `3`. -/
theorem tse_stage_two :
    p.expect T0 = 3 ∧ p.expect (adjustedTime (6 / 5)) = 7 / 2 ∧
      p.expect (adjustedTime 2) = 3 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, adjustedTime, untreatedTime, T0,
    decisionTime, S, switchRule, L1, Y, Y1, Y0, y0]
  norm_num

/-- The mean residual survival with the switch undone by `ψ`, `E[untreatedTime ψ]`, plus the
decision time: `9/4 + 3 / (2 ψ)`. -/
theorem expect_adjustedTime (ψ : ℝ) : p.expect (adjustedTime ψ) = 9 / 4 + 3 / (2 * ψ) := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, adjustedTime, untreatedTime,
    decisionTime, S, switchRule, L1, Y, Y1, Y0, y0]
  norm_num
  ring

/-- The mean log residual survival of the switchers, with the switch undone by `ψ > 0`:
`log 2 + (log 3) / 4 - log ψ`. -/
theorem condMean_log_switchers (ψ : ℝ) (hψ : 0 < ψ) :
    condMean p (fun ω => S ω = true) (fun ω => Real.log (untreatedTime ψ ω)) =
      Real.log 2 + Real.log 3 / 4 - Real.log ψ := by
  simp only [condMean, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob,
    Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, untreatedTime, S, switchRule, L1, Y, Y1,
    Y0, y0]
  norm_num
  rw [Real.log_div (by norm_num) hψ.ne', Real.log_div (by norm_num) hψ.ne',
    show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- The mean log residual survival of the non-switchers: `3 (log 3) / 4`. -/
theorem condMean_log_stayers (ψ : ℝ) :
    condMean p (fun ω => S ω = false) (fun ω => Real.log (untreatedTime ψ ω)) =
      3 * Real.log 3 / 4 := by
  simp only [condMean, FiniteDist.expect, FiniteDist.probOf, FiniteDist.prob,
    Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, untreatedTime, S, switchRule, L1, Y, Y1,
    Y0, y0]
  norm_num
  ring

/-- The estimating equation of stage one in the log-time form (TSD 16, Section 3.2.4; TSD 24,
Section 4.2.3): the accelerated failure time model `log Y = β₀ + β S + error`, fitted by least
squares to the uncensored post-progression data of the control arm with the (constant)
covariates at the secondary baseline, has normal equations whose switch coefficient is the
difference of mean log residual times of switchers and non-switchers. Equivalently, the time
ratio `ψ = exp β` makes the mean log residual time with the switch undone,
`log (untreatedTime ψ)`, equal among switchers and non-switchers. For `ψ > 0` this holds
exactly when `ψ = 2 / √3`, so the root is unique. A parametric fit such as the Weibull model of
the documents solves a different score equation and is not formalized. -/
theorem tse_stage_one_log_root (ψ : ℝ) (hψ : 0 < ψ) :
    condMean p (fun ω => S ω = true) (fun ω => Real.log (untreatedTime ψ ω)) =
      condMean p (fun ω => S ω = false) (fun ω => Real.log (untreatedTime ψ ω)) ↔
      ψ = 2 / Real.sqrt 3 := by
  rw [condMean_log_switchers ψ hψ, condMean_log_stayers]
  have hr : Real.log (2 / Real.sqrt 3) = Real.log 2 - Real.log 3 / 2 := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_sqrt (by norm_num)]
  have hpos : 0 < 2 / Real.sqrt 3 := by positivity
  constructor
  · intro h
    exact Real.log_injOn_pos (Set.mem_Ioi.2 hψ) (Set.mem_Ioi.2 hpos) (by rw [hr]; linarith)
  · rintro rfl; rw [hr]; ring

/-- The log-time root `2 / √3` of stage one differs from the mean-balancing root `6/5`
(`tse_stage_one_root`) and from the true time ratio `2`. With it, the second stage gives the
mean survival from progression `(9 + 3 √3) / 4`, which differs from the true mean
`E[T0] = 3` (`tse_stage_two`). -/
theorem tse_log_root_biased :
    2 / Real.sqrt 3 ≠ 6 / 5 ∧ 2 / Real.sqrt 3 ≠ 2 ∧
      p.expect (adjustedTime (2 / Real.sqrt 3)) = (9 + 3 * Real.sqrt 3) / 4 ∧
      (9 + 3 * Real.sqrt 3) / 4 ≠ p.expect T0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := by positivity
  refine ⟨fun h => ?_, fun h => ?_, ?_, fun h => ?_⟩
  · have : Real.sqrt 3 = 5 / 3 := by field_simp at h; linarith
    rw [this] at h3; norm_num at h3
  · have : Real.sqrt 3 = 1 := by field_simp at h; linarith
    rw [this] at h3; norm_num at h3
  · rw [expect_adjustedTime]
    field_simp
    ring
  · rw [tse_stage_two.1] at h
    have : Real.sqrt 3 = 1 := by linarith
    rw [this] at h3; norm_num at h3

/-! #### The delay between progression and the switch decision

TSD 16, Section 6 (page 42), on two-stage methods: "their potential bias will be related to how
soon after this point switching occurs"; "if there are long delays until switching the
potential for bias associated with time-dependent confounding becomes important". Section
3.2.4: "if switching occurs soon after the secondary baseline any time-dependent confounding
associated with the lag between disease progression and treatment switching would be small".

The family below illustrates this claim; it is one explicit family, not a general theorem. The
delay `d ∈ [0, 1]` is the time from progression to the switch decision. The covariates at
progression are fixed (`L0` is constant); by the decision time a patient has deteriorated with
probability `d / 2`, so the covariate `L1` measured at the decision carries prognosis that the
baseline record does not as soon as `d > 0`. The switch rule, the potential outcomes and the
time ratio `2` are those of the model above, which is the member `d = 1` (`pd_one`). -/

/-- The law of deterioration by the decision time after a delay `d`: deteriorated with
probability `d / 2`. -/
noncomputable def deteriorationLaw (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) : FiniteDist Bool where
  mass l := if l then d / 2 else 1 - d / 2
  nonneg l := by cases l <;> simp <;> linarith [hd.1, hd.2]
  sum_eq_one := by simp

/-- The law of the model with delay `d`: deterioration and the noise of the decision are
independent, the noise uniform. -/
noncomputable def pd (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) : FiniteDist Ω :=
  (deteriorationLaw d hd).prod FiniteDist.uniform

/-- The delay `1` gives the model above. -/
theorem pd_one : pd 1 ⟨zero_le_one, le_rfl⟩ = p := by
  ext ω
  rcases ω with ⟨_ | _, _⟩ <;> simp [pd, p, deteriorationLaw]
  norm_num

/-- The stage-one factor (mean-balancing root) at delay `d`:
`6 (3 - d) / ((1 + d) (9 - 4 d))`. -/
noncomputable def delayFactor (d : ℝ) : ℝ := 6 * (3 - d) / ((1 + d) * (9 - 4 * d))

/-- The bias of the second-stage adjusted mean at delay `d`: `d (2 - d) / (3 - d)`. -/
noncomputable def delayBias (d : ℝ) : ℝ := d * (2 - d) / (3 - d)

/-- The survival time from progression after the second stage, at delay `d`: the decision time
`d` plus the residual survival with the switch undone by `ψ`. -/
noncomputable def adjustedTimeAt (d ψ : ℝ) (ω : Ω) : ℝ := d + untreatedTime ψ ω

/-- The survival time from progression without switching, at delay `d`: `d + Y0`. -/
noncomputable def T0At (d : ℝ) (ω : Ω) : ℝ := d + Y0 ω

/-- At every delay `d > 0` no unmeasured confounding fails given the record at progression:
the switch is not conditionally independent of the survival without switching given `L0`. -/
theorem delay_not_condIndepFun (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) (hpos : 0 < d) :
    ¬ (pd d hd).CondIndepFun S Y0 L0 := by
  intro h
  have := h true 1 ()
  simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter] at this
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, pd, deteriorationLaw,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1, Y0, y0] at this
  norm_num at this
  nlinarith [hd.2]

/-- Stage one at delay `d`, adjusted for the record at progression: for `ψ ≠ 0`, the
mean-balancing equation of `tse_stage_one_root` holds exactly when `ψ = delayFactor d`. -/
theorem delay_stage_one_root (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) (ψ : ℝ) (hψ : ψ ≠ 0) :
    condMean (pd d hd) (fun ω => S ω = true) (untreatedTime ψ) =
      condMean (pd d hd) (fun ω => S ω = false) (untreatedTime ψ) ↔ ψ = delayFactor d := by
  have a1 : (1 + d) ≠ 0 := by linarith [hd.1]
  have a2 : (3 - d) ≠ 0 := by linarith [hd.2]
  have a3 : (9 - 4 * d) ≠ 0 := by linarith [hd.2]
  have n1 : (pd d hd).expect (fun ω => if S ω = true then untreatedTime ψ ω else 0) =
      3 / (2 * ψ) := by
    simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
      pd, deteriorationLaw, FiniteDist.prod_apply, FiniteDist.uniform_apply, untreatedTime, S,
      switchRule, L1, Y, Y1, Y0, y0]
    norm_num
    field_simp
    ring
  have d1 : (pd d hd).probOf (fun ω => S ω = true) = (1 + d) / 4 := by
    simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, pd, deteriorationLaw,
      FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1]
    norm_num
    ring
  have n0 : (pd d hd).expect (fun ω => if S ω = false then untreatedTime ψ ω else 0) =
      (9 - 4 * d) / 4 := by
    simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
      pd, deteriorationLaw, FiniteDist.prod_apply, FiniteDist.uniform_apply, untreatedTime, S,
      switchRule, L1, Y, Y1, Y0, y0]
    norm_num
    ring
  have d0 : (pd d hd).probOf (fun ω => S ω = false) = (3 - d) / 4 := by
    simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, pd, deteriorationLaw,
      FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1]
    norm_num
    ring
  rw [condMean, condMean, n1, d1, n0, d0, delayFactor]
  rw [div_div_div_cancel_right₀ four_ne_zero, eq_div_iff (mul_ne_zero a1 a3)]
  field_simp
  constructor
  · intro h; linear_combination (-1 / 2 : ℝ) * h
  · intro h; linear_combination (-2 : ℝ) * h

/-- The second-stage adjusted mean at delay `d` with the factor `ψ`. -/
theorem delay_expect_adjusted (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) (ψ : ℝ) :
    (pd d hd).expect (adjustedTimeAt d ψ) = d + 3 / (2 * ψ) + (9 - 4 * d) / 4 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
    pd, deteriorationLaw, FiniteDist.prod_apply, FiniteDist.uniform_apply, adjustedTimeAt,
    untreatedTime, S, switchRule, L1, Y, Y1, Y0, y0]
  norm_num
  ring

/-- The true mean survival from progression without switching is `3` at every delay. -/
theorem delay_expect_T0 (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) : (pd d hd).expect (T0At d) = 3 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four,
    pd, deteriorationLaw, FiniteDist.prod_apply, FiniteDist.uniform_apply, T0At, Y0, y0]
  norm_num
  ring

/-- The bias of the simple two-stage method at delay `d`: the second-stage adjusted mean with
the stage-one factor `delayFactor d`, minus the true mean, is `delayBias d`. -/
theorem delay_bias (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) :
    (pd d hd).expect (adjustedTimeAt d (delayFactor d)) - (pd d hd).expect (T0At d) =
      delayBias d := by
  have a1 : (1 + d) ≠ 0 := by linarith [hd.1]
  have a2 : (3 - d) ≠ 0 := by linarith [hd.2]
  have a3 : (9 - 4 * d) ≠ 0 := by linarith [hd.2]
  rw [delay_expect_adjusted, delay_expect_T0, delayFactor, delayBias]
  field_simp
  ring

/-- At zero delay the covariate has no time to evolve: baseline adjustment recovers the true
time ratio `2`, and the bias is `0`. -/
theorem delay_zero : delayFactor 0 = 2 ∧ delayBias 0 = 0 := by
  norm_num [delayFactor, delayBias]

/-- At delay `1` the factor is `6/5` and the bias `1/2`, the values of `tse_stage_one` and
`tse_stage_two` (`7/2 - 3`). -/
theorem delay_one : delayFactor 1 = 6 / 5 ∧ delayBias 1 = 1 / 2 := by
  norm_num [delayFactor, delayBias]

/-- The bias of the simple two-stage method grows strictly with the delay on `[0, 1]`, in this
family. -/
theorem delayBias_strictMonoOn : StrictMonoOn delayBias (Set.Icc 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  simp only [delayBias]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (sub_pos.2 hab) (show (0 : ℝ) < 6 - 3 * (a + b) + a * b by nlinarith)]

/-- The probability of not switching given the time-dependent covariate,
`P(S = 0 | L1 = l)`: the denominator of the full-record censoring weight. -/
noncomputable def pNoSwitch (l : Bool) : ℝ :=
  p.probOf (fun ω => S ω = false ∧ L1 ω = l) / p.probOf (fun ω => L1 ω = l)

theorem pNoSwitch_true : pNoSwitch true = 1 / 4 := by
  simp only [pNoSwitch, FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1]
  norm_num

theorem pNoSwitch_false : pNoSwitch false = 3 / 4 := by
  simp only [pNoSwitch, FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1]
  norm_num

/-- Stopping covariate collection at the secondary baseline biases IPCW (TSD 24, Section
4.2.2.1). Censoring the switchers and weighting the non-switchers by the inverse probability
of not switching given the full covariate record, `1 / P(S = 0 | L1)`, recovers the mean
`E[Y0] = 2` of post-progression survival without switching; both weights are positive. With
the record truncated at progression the weight is `1 / P(S = 0)`, and the weighted mean is
`5/2`. This is the weighting identity for the mean of a residual time observed only for the
non-switchers; the failure of the survival weighting functional itself is
`weightedHazard_truncated`. -/
theorem ipcw_truncated :
    p.expect Y0 = 2 ∧ 0 < pNoSwitch true ∧ 0 < pNoSwitch false ∧
    p.expect (fun ω => if S ω then 0 else Y ω / pNoSwitch (L1 ω)) = 2 ∧
    p.expect (fun ω => if S ω then 0 else Y ω / p.probOf (fun ω => S ω = false)) = 5 / 2 := by
  have h0 : p.probOf (fun ω => S ω = false) = 1 / 2 := by
    simp only [FiniteDist.probOf, FiniteDist.prob, Finset.sum_filter]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
      FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1]
    norm_num
  rw [h0]
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, p,
    FiniteDist.prod_apply, FiniteDist.uniform_apply, S, switchRule, L1, Y, Y1, Y0, y0,
    pNoSwitch_true, pNoSwitch_false]
  norm_num

/-! #### The survival weighting functional with a truncated history

The same model on the discrete clock of `Survival.IPCW`: progression at `0`, the covariate
measured at time `1`, switches at the end of interval `1`. -/

section IPCWFunctional

open Survival Survival.IPCW

/-- The survival time from progression without switching, in periods: `1 + Y0`. -/
def Tn (ω : Ω) : ℕ := if ω.1 then 2 else 4

/-- The switching time used as censoring time: switchers are censored at the end of interval
`1`; the others are followed beyond death. -/
def Cs (ω : Ω) : ℕ := if S ω then 1 else 5

/-- No baseline covariates. -/
def Vb (_ : Ω) : Unit := ()

/-- The full covariate history: uninformative at progression (`i = 0`), deterioration `L1`
from time `1` on. -/
def Lfull (i : ℕ) (ω : Ω) : Bool := if i = 0 then false else L1 ω

/-- The covariate history truncated at progression: collection stopped at the secondary
baseline, so nothing is recorded after time `0`. -/
def Ltrunc (_ : ℕ) (_ : Ω) : Bool := false

theorem wmass_p (s : Finset Ω) :
    Longitudinal.wmass p s = ∑ ω, if ω ∈ s then (1 / 8 : ℝ) else 0 := by
  rw [Longitudinal.wmass, ← sum_filter, filter_mem_eq_inter, univ_inter]
  refine sum_congr rfl fun ω _ => ?_
  simp [p, FiniteDist.prod_apply, FiniteDist.uniform_apply]
  norm_num

theorem wmass_filter_p (P : Ω → Prop) [DecidablePred P] :
    Longitudinal.wmass p (univ.filter P) =
      ∑ a : Bool, ∑ b : Fin 4, if P (a, b) then (1 / 8 : ℝ) else 0 := by
  rw [wmass_p]
  simp only [mem_filter, mem_univ, true_and, Fintype.sum_prod_type]

theorem p_pos (ω : Ω) : 0 < p ω := by
  simp [p, FiniteDist.prod_apply, FiniteDist.uniform_apply]

theorem riskCell_full_zero (ω : Ω) : riskCell Tn Cs Vb Lfull 0 ω = univ := by
  revert ω; decide

theorem riskCell_full_one (ω : Ω) :
    riskCell Tn Cs Vb Lfull 1 ω = univ.filter fun x => x.1 = ω.1 := by
  revert ω; decide

theorem riskCell_trunc (j : ℕ) (hj : j < 2) (ω : Ω) : riskCell Tn Cs Vb Ltrunc j ω = univ := by
  interval_cases j <;> revert ω <;> decide

theorem stayProb_full_zero (ω : Ω) : stayProb p Tn Cs Vb Lfull 0 ω = 1 := by
  rw [stayProb, Longitudinal.condProb, riskCell_full_zero, univ_inter, wmass_p, wmass_p]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, uncensored,
    mem_univ, Cs, S, switchRule, L1]
  norm_num

theorem stayProb_full_one (ω : Ω) :
    stayProb p Tn Cs Vb Lfull 1 ω = if ω.1 then 1 / 4 else 3 / 4 := by
  rw [stayProb, Longitudinal.condProb, riskCell_full_one, wmass_p, wmass_p]
  rcases ω with ⟨_ | _, _⟩ <;>
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, uncensored,
    mem_filter, mem_inter, mem_univ, true_and, Cs, S, switchRule, L1] <;>
  norm_num

theorem stayProb_trunc (j : ℕ) (hj : j < 2) (ω : Ω) :
    stayProb p Tn Cs Vb Ltrunc j ω = if j = 0 then 1 else 1 / 2 := by
  rw [stayProb, Longitudinal.condProb, riskCell_trunc j hj, univ_inter, wmass_p, wmass_p]
  interval_cases j <;>
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, uncensored,
    mem_univ, Cs, S, switchRule, L1] <;>
  norm_num

/-- No unmeasured confounding of the switch holds given the full covariate history. -/
theorem switchNUC_full : SwitchNUC p Tn Cs Vb Lfull 2 := by
  intro j hj ω t
  interval_cases j
  · refine meanIndepOn_of_const _ (c := 1) fun x _ => ?_
    have : 1 ≤ Cs x := by unfold Cs; split_ifs <;> omega
    simp [this]
  · refine meanIndepOn_ev_of_const (fun x hx y hy => ?_) t _
    rw [riskCell_full_one] at hx hy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    simp [Tn, hx, hy]

/-- Positivity of not switching holds given the full history. -/
theorem switchPositive_full : SwitchPositive p Tn Cs Vb Lfull 2 := by
  intro j hj ω _ _ _
  interval_cases j
  · rw [stayProb_full_zero]; norm_num
  · rw [stayProb_full_one]; split_ifs <;> norm_num

/-- Positivity of not switching holds given the truncated history. -/
theorem switchPositive_trunc : SwitchPositive p Tn Cs Vb Ltrunc 2 := by
  intro j hj ω _ _ _
  rw [stayProb_trunc j hj]; split_ifs <;> norm_num

theorem hazard_two : hazard p.toMeasure Tn 2 = 1 / 2 := by
  rw [hazard_toMeasure, wmass_filter_p, wmass_filter_p]
  simp only [Fintype.sum_bool, Fin.sum_univ_four]
  norm_num [Tn]

/-- Stopping covariate collection at the secondary baseline biases the survival weighting
functional of `Survival.IPCW` (TSD 24, Section 4.2.2.1). The hazard of death at time `2`
without switching is `1/2`. With weights built from the full covariate history, no unmeasured
confounding and positivity hold and the weighted hazard is `1/2`. With the history truncated at
progression, positivity still holds (every stay probability is positive), the weighted hazard
is `1/4`, and no unmeasured confounding fails. -/
theorem weightedHazard_truncated :
    hazard p.toMeasure Tn 2 = 1 / 2 ∧
    SwitchNUC p Tn Cs Vb Lfull 2 ∧ SwitchPositive p Tn Cs Vb Lfull 2 ∧
      weightedHazard p Tn Cs (ipcWeight p Tn Cs Vb Lfull) 2 = 1 / 2 ∧
    SwitchPositive p Tn Cs Vb Ltrunc 2 ∧ ¬ SwitchNUC p Tn Cs Vb Ltrunc 2 ∧
      weightedHazard p Tn Cs (ipcWeight p Tn Cs Vb Ltrunc) 2 = 1 / 4 := by
  have hk : 0 < atRisk p.toMeasure Tn 2 := by
    rw [atRisk_toMeasure, wmass_filter_p]
    simp only [Fintype.sum_bool, Fin.sum_univ_four]
    norm_num [Tn]
  have hfull := (weightedHazard_ipcWeight p 2 switchNUC_full switchPositive_full hk).2
  rw [hazard_two] at hfull
  have hw : ipcWeight p Tn Cs Vb Ltrunc 2 = fun _ => 2 := by
    funext ω
    simp only [ipcWeight, prod_range_succ, range_zero, prod_empty,
      stayProb_trunc 0 (by norm_num), stayProb_trunc 1 (by norm_num)]
    norm_num
  have htrunc : weightedHazard p Tn Cs (ipcWeight p Tn Cs Vb Ltrunc) 2 = 1 / 4 := by
    rw [weightedHazard, hw, Longitudinal.wsum_const, Longitudinal.wsum_const, eventSet, riskSet,
      wmass_filter_p, wmass_filter_p]
    simp only [Fintype.sum_bool, Fin.sum_univ_four]
    norm_num [Tn, Cs, S, switchRule, L1]
  refine ⟨hazard_two, switchNUC_full, switchPositive_full, hfull, switchPositive_trunc,
    fun h => ?_, htrunc⟩
  have := (weightedHazard_ipcWeight p 2 h switchPositive_trunc hk).2
  rw [htrunc, hazard_two] at this
  norm_num at this

end IPCWFunctional

end TimeDependent

/-! ### Censoring and excluding switchers -/

namespace CensorExclude

open MeasureTheory ProbabilityTheory Survival Survival.IPCW

/-- The sample space of the control arm: a point is `(g, n)`, the prognosis (`true` for poor)
and the noise of the switch decision. -/
abbrev Ω := Bool × Fin 4

/-- Prognosis and noise are independent and uniform: poor and good prognosis each have
probability `1/2`. By randomization the experimental arm has the same prognostic law. -/
noncomputable def μ : Measure Ω := TimeDependent.p.toMeasure

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

/-- The untreated survival time, which is also the time in the control arm had nobody
switched: `2` for poor prognosis, `4` for good prognosis. -/
def U (ω : Ω) : ℕ := if ω.1 then 2 else 4

/-- The switchers: a control patient of poor prognosis switches with probability `3/4`, one of
good prognosis with probability `1/4`. -/
def switcher (ω : Ω) : Bool := TimeDependent.switchRule ω.1 ω.2

/-- The censoring time of the per-protocol analysis in the control arm: the switch time `1`
for switchers (alive and on control through time `1`, censored afterwards), the end of
follow-up `10` for the others. -/
def C (ω : Ω) : ℕ := if switcher ω then 1 else 10

/-- The observed survival time in the control arm: switching adds one period to the untreated
time of the switchers. -/
def T0 (ω : Ω) : ℕ := if switcher ω then U ω + 1 else U ω

/-- The survival time in the experimental arm, where nobody switches: the experimental
treatment adds one period to the untreated time. -/
def T1 (ω : Ω) : ℕ := U ω + 1

theorem measureReal_eq (P : Ω → Prop) [DecidablePred P] :
    μ.real {ω | P ω} = ∑ a : Bool, ∑ b : Fin 4, if P (a, b) then (1 / 8 : ℝ) else 0 := by
  rw [μ, toMeasure_real_setOf, TimeDependent.wmass_filter_p]

/-- Censoring at the switch uses only data from before the switch, where the observed time
and the untreated time agree: the censored data of the control arm are the censored data of
the untreated time. -/
theorem observed_eq : observed T0 C = observed U C := by
  funext ω
  simp only [observed, T0, C, U]
  split_ifs <;> simp

/-- The product-limit functional of the control arm censored at the switch is `3/4` at time
`2`: the hazard at `2` among the uncensored is `1/4`, the hazard of the non-switchers. -/
theorem productLimit_eq : productLimit (μ.map (observed T0 C)) 2 = 3 / 4 := by
  rw [observed_eq, productLimit]
  simp only [prod_range_succ, range_zero, prod_empty, one_mul,
    observedHazard_map_observed (Measurable.of_discrete) (Measurable.of_discrete),
    measureReal_eq]
  simp only [Fintype.sum_bool, Fin.sum_univ_four, U, C, switcher, TimeDependent.switchRule]
  norm_num

/-- The untreated survival at time `2` is `1/2`. -/
theorem survival_U : survival μ U 2 = 1 / 2 := by
  rw [survival, measureReal_eq]
  simp only [Fintype.sum_bool, Fin.sum_univ_four, U]
  norm_num

/-- The experimental survival at time `2` is `1`. -/
theorem survival_T1 : survival μ T1 2 = 1 := by
  rw [survival, measureReal_eq]
  simp only [Fintype.sum_bool, Fin.sum_univ_four, T1, U]
  norm_num

/-- The risk set has positive probability: the probability of being at risk and uncensored at
time `2` is positive. -/
theorem atRisk_pos : 0 < μ.real {ω | 2 ≤ U ω ∧ 2 ≤ C ω} := by
  rw [measureReal_eq]
  simp only [Fintype.sum_bool, Fin.sum_univ_four, U, C, switcher, TimeDependent.switchRule]
  norm_num

/-- Overlap in both prognosis groups: within each prognosis group, some patients switch and
some do not, each with positive probability. So the conditional positivity of not switching
given prognosis holds as well. -/
theorem overlap (g s : Bool) : 0 < μ.real {ω | ω.1 = g ∧ switcher ω = s} := by
  rw [measureReal_eq]
  simp only [Fintype.sum_bool, Fin.sum_univ_four, switcher, TimeDependent.switchRule]
  cases g <;> cases s <;> norm_num

/-- Censoring at the switch is informative: the untreated time and the censoring time are
not independent (otherwise `productLimit_map_observed_eq_survival` would apply). -/
theorem not_indepFun : ¬ IndepFun U C μ := fun h => by
  have := productLimit_map_observed_eq_survival (μ := μ) Measurable.of_discrete
    Measurable.of_discrete h 2 atRisk_pos
  rw [← observed_eq, productLimit_eq, survival_U] at this
  norm_num at this

/-- Censoring switchers is biased (TSD 16, Section 3.1.2). The arms are randomized (both have
the prognostic law of `μ`), the risk set at time `2` has positive probability (`atRisk_pos`),
both prognosis groups contain switchers and non-switchers (`overlap`), and switching depends on
prognosis, which is not measured; the assumption that fails is noninformative censoring
(`not_indepFun`). The hypothetical contrast at time `2` between the experimental arm and the
control arm without switching is `S₁(2) - S₀(2) = 1 - 1/2 = 1/2`; the per-protocol contrast
that censors switchers replaces `S₀(2)` by the product limit of the censored control data,
`3/4`, and gives `1/4`. -/
theorem censored_contrast :
    survival μ T1 2 - survival μ U 2 = 1 / 2 ∧
      survival μ T1 2 - productLimit (μ.map (observed T0 C)) 2 = 1 / 4 := by
  rw [survival_T1, survival_U, productLimit_eq]; norm_num

/-- Excluding switchers is biased (TSD 16, Section 3.1.2): among the control non-switchers
(an event of probability `1/2`), the survival beyond time `2` is `3/4`, while the control
survival without switching is `S₀(2) = 1/2` (`survival_U`). -/
theorem excluded_survival :
    μ.real {ω | switcher ω = false} = 1 / 2 ∧
      μ.real {ω | switcher ω = false ∧ 2 < T0 ω} / μ.real {ω | switcher ω = false} = 3 / 4 := by
  simp only [measureReal_eq]
  simp only [Fintype.sum_bool, Fin.sum_univ_four, switcher, TimeDependent.switchRule, T0, U]
  norm_num

end CensorExclude

end SwitchingCounterexamples

end CausalInference
