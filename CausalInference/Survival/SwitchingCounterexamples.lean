/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Censoring
public import CausalInference.Survival.SwitchDecision

/-!
# Treatment switching: counterexamples for the simple analyses

Concrete models in which a simple analysis of a trial with treatment switching misses the
hypothetical estimand (survival had the switches not occurred), while the other assumptions of
the setting hold: the arms are randomized, positivity holds, and the analysis fails only through
the assumption that the documents say can fail.

The models of `PrincipalStrata` and `TimeDependent` are finite (`FiniteDist`, conditional
independence `FiniteDist.CondIndepFun`); the model of `CensorExclude` is a probability measure
on `Bool` so that the product-limit functional of `CausalInference.Survival.Censoring` applies.

## Main results

* Censoring and excluding switchers (TSD 16, Section 3.1.2), `CensorExclude`: switching in the
  control arm depends on prognosis. The censored data of the control arm are those of the
  untreated time (`observed_eq`), censoring is informative (`not_indepFun`), and the
  product-limit functional at time `2` is `1` while the untreated survival is `1/2`, so the
  per-protocol contrast is `0` instead of `1/2` (`censored_contrast`); the survival of the
  non-switchers is `1` (`excluded_survival`).
* Principal strata defined by the observed switch (TSD 24, Section 3.2), `PrincipalStrata`:
  under the sharp null, with randomized arms, the arm contrast within the observed
  non-switchers and within the observed switchers is `-1/2`, while the intention-to-treat
  contrast is `0` (`stratum_contrast_ne`).
* Time-dependent confounding between the secondary baseline and the switch (TSD 16, Section
  3.2.4; TSD 24, Section 4.2.3), `TimeDependent`: a covariate that changes after progression
  drives the switch and survival. No unmeasured confounding holds given the full covariate path
  (`condIndepFun_full`) and fails given the record at progression
  (`not_condIndepFun_baseline`). The simple two-stage contrast, adjusted for the record at
  progression, gives a time ratio `6/5` instead of `2`; adjusting for the time-dependent
  covariate gives `2` (`tse_stage_one`).
* Covariate collection stopped at progression (TSD 24, Section 4.2.2.1), same model: inverse
  probability of censoring weights built from the full record recover the mean survival without
  switching, `2`; weights built from the record truncated at progression give `5/2`
  (`ipcw_truncated`).

The first-stage contrasts are stated for means (a ratio of standardized means for the time
ratio), the population identity of a point-treatment adjustment; the parametric accelerated
failure time fit of the documents is not formalized. The claim of TSD 16 that the bias of the
simple two-stage method grows with the delay between progression and switch is not formalized.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014), Sections 3.1.2 and 3.2.4.
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

/-- Comparing the arms within a principal stratum defined by the observed switch is biased
(TSD 24, Section 3.2). The treatment has no effect on survival, and the intention-to-treat
contrast `E[Y | R = 1] - E[Y | R = 0]` is `0`; but within the observed non-switchers, and
within the observed switchers, the experimental arm has mean survival `1/2` lower than the
control arm. The stratum is a consequence of treatment (through progression) and of
prognosis, so conditioning on it breaks the balance created by randomization. -/
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

end PrincipalStrata

/-! ### Time-dependent confounding after the secondary baseline, and truncated collection -/

namespace TimeDependent

/-- The sample space of the control arm after the secondary baseline (disease progression):
a point is `(l, n)`, where `l = true` means that the patient deteriorated between progression
and the switch decision, and `n` is the noise of the decision. -/
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

/-- The potential post-progression survival without switching, as a function of
deterioration: `1` if deteriorated, `3` otherwise. -/
noncomputable def y0 (l : Bool) : ℝ := if l then 1 else 3

/-- The potential post-progression survival without switching. -/
noncomputable def Y0 (ω : Ω) : ℝ := y0 ω.1

/-- The potential post-progression survival with switching: the switch doubles it, for every
patient. So the switching time ratio is `2`. -/
noncomputable def Y1 (ω : Ω) : ℝ := 2 * Y0 ω

/-- The observed post-progression survival. -/
noncomputable def Y (ω : Ω) : ℝ := if S ω then Y1 ω else Y0 ω

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
TSD 24, Section 4.2.3). Stage one compares post-progression survival of switchers and
non-switchers adjusted for the covariates at the secondary baseline. Here these are constant,
so the adjusted ratio of mean survival is the crude ratio `E[Y | S = 1] / E[Y | S = 0] = 6/5`,
while the switching time ratio is `2` for every patient (`Y1 = 2 Y0`), and `E[Y1] / E[Y0] = 2`.
Adjusting for the time-dependent covariate, the standardized ratio
`∑_l P(L1 = l) E[Y | S = 1, L1 = l] / ∑_l P(L1 = l) E[Y | S = 0, L1 = l]` recovers `2`. -/
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
`5/2`. -/
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

end TimeDependent

/-! ### Censoring and excluding switchers -/

namespace CensorExclude

open MeasureTheory ProbabilityTheory Survival
open scoped ENNReal

/-- The law of the prognostic variable, the same in both arms by randomization: poor
prognosis (`true`) and good prognosis (`false`) each with probability `1/2`. -/
noncomputable def μ : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure μ := ⟨by
  simp only [μ, smul_apply, add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- The untreated survival time, which is also the time in the control arm had nobody
switched: `2` for poor prognosis, `4` for good prognosis. -/
def U (ω : Bool) : ℕ := if ω then 2 else 4

/-- The switchers: control patients of poor prognosis switch to the experimental treatment. -/
def switcher (ω : Bool) : Bool := ω

/-- The censoring time of the per-protocol analysis in the control arm: the switch time `1`
for switchers (alive and on control through time `1`, censored afterwards), the end of
follow-up `10` for the others. -/
def C (ω : Bool) : ℕ := if ω then 1 else 10

/-- The observed survival time in the control arm: switching extends the survival of the poor
prognosis patients from `2` to `3`. -/
def T0 (ω : Bool) : ℕ := if ω then 3 else 4

/-- The survival time in the experimental arm, where nobody switches: the experimental
treatment adds one period to the untreated time. -/
def T1 (ω : Bool) : ℕ := U ω + 1

theorem measureReal_eq (s : Set Bool) [DecidablePred (· ∈ s)] :
    μ.real s = (if true ∈ s then 1 / 2 else 0) + (if false ∈ s then 1 / 2 else 0) := by
  simp only [μ, measureReal_def, smul_apply, add_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, smul_eq_mul]
  split_ifs <;> simp [ENNReal.toReal_add, ENNReal.toReal_inv]
  ring

/-- Censoring at the switch uses only data from before the switch, where the observed time
and the untreated time agree: the censored data of the control arm are the censored data of
the untreated time. -/
theorem observed_eq : observed T0 C = observed U C := by
  funext ω; cases ω <;> rfl

/-- The product-limit functional of the control arm censored at the switch is `1` at time
`2`: every death before time `3` is censored away. -/
theorem productLimit_eq : productLimit (μ.map (observed T0 C)) 2 = 1 := by
  rw [observed_eq, productLimit]
  refine Finset.prod_eq_one fun m hm => ?_
  rw [observedHazard_map_observed (Measurable.of_discrete) (Measurable.of_discrete),
    measureReal_eq]
  have hm : m < 3 := Finset.mem_range.1 hm
  have h1 : ¬ ((2 : ℕ) = m ∧ m ≤ 1) := by omega
  have h2 : ¬ ((4 : ℕ) = m ∧ m ≤ 10) := by omega
  simp [U, C, h1, h2]

/-- The untreated survival at time `2` is `1/2`. -/
theorem survival_U : survival μ U 2 = 1 / 2 := by
  rw [survival, measureReal_eq]; simp [U]

/-- The experimental survival at time `2` is `1`. -/
theorem survival_T1 : survival μ T1 2 = 1 := by
  rw [survival, measureReal_eq]; simp [T1, U]; norm_num

/-- Positivity holds: the probability of being at risk and uncensored at time `2` is
positive. -/
theorem atRisk_pos : 0 < μ.real {ω | 2 ≤ U ω ∧ 2 ≤ C ω} := by
  rw [measureReal_eq]; simp [U, C]

/-- Censoring at the switch is informative: the untreated time and the censoring time are
not independent (otherwise `productLimit_map_observed_eq_survival` would apply). -/
theorem not_indepFun : ¬ IndepFun U C μ := fun h => by
  have := productLimit_map_observed_eq_survival (μ := μ) Measurable.of_discrete
    Measurable.of_discrete h 2 atRisk_pos
  rw [← observed_eq, productLimit_eq, survival_U] at this
  norm_num at this

/-- Censoring switchers is biased (TSD 16, Section 3.1.2). The arms are randomized (both have
the prognostic law `μ`), positivity holds (`atRisk_pos`), and switching depends on prognosis.
The hypothetical contrast at time `2` between the experimental arm and the control arm without
switching is `S₁(2) - S₀(2) = 1 - 1/2 = 1/2`; the per-protocol contrast that censors switchers
replaces `S₀(2)` by the product limit of the censored control data, `1`, and gives `0`. -/
theorem censored_contrast :
    survival μ T1 2 - survival μ U 2 = 1 / 2 ∧
      survival μ T1 2 - productLimit (μ.map (observed T0 C)) 2 = 0 := by
  rw [survival_T1, survival_U, productLimit_eq]; norm_num

/-- Excluding switchers is biased (TSD 16, Section 3.1.2): among the control non-switchers
(an event of probability `1/2`), the survival beyond time `2` is `1`, while the control
survival without switching is `S₀(2) = 1/2` (`survival_U`). -/
theorem excluded_survival :
    μ.real {ω | switcher ω = false} = 1 / 2 ∧
      μ.real {ω | switcher ω = false ∧ 2 < T0 ω} / μ.real {ω | switcher ω = false} = 1 := by
  simp only [measureReal_eq]; simp [switcher, T0]

end CensorExclude

end SwitchingCounterexamples

end CausalInference
