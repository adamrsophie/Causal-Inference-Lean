/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Recensoring
public import CausalInference.StructuralNested.RPSFTMCounterexamples

/-!
# Counterexamples for recensoring

Two concrete randomized trials with switching and administrative censoring, on the eight point
space `Bool × Bool × Bool` with the uniform measure
(`CausalInference.Mediation.Counterexample.μ₀`). The first coordinate is the arm, the second a
prognostic type independent of it. In both trials the experimental treatment doubles survival
time (`exp ψ₀ = 1/2`), experimental patients are treated throughout, control patients of poor
prognosis switch at time `1` and control patients of good prognosis never switch; the common
treatment effect, randomization with respect to `(U, C)` and independent censoring all hold.

## Main results

`RecensoringCounterexample.Staggered`: the censoring time is `2` or `6` according to the third
coordinate (staggered entry), independent of everything else.

* `not_indepFun_naiveCensTime`: **naive censoring is informative** (TSD 16, Section 3.3.2 and
  Appendix A; TSD 24, Section 4.2.1.1): the transformed censoring time `∫_0^C exp (ψ₀ A(s)) ds`
  depends on the treatment history, hence on prognosis, and is not independent of the untreated
  time.
* `naive_biased`: **without recensoring the untreated survival is missed at the true
  parameter.** At `t = 19/10` the control arm survival of `U` is `1/2`; the identification formula
  of `CensoredTrial.armSurvival_U_eq_div` applied to the naive data gives `2/3` in the control arm
  (as does the product limit of the naive control data) and `1/2` in the experimental arm; with
  recensoring it gives `1/2`.
* `switchersOnly_biased`: recensoring only the switchers still gives `2/3` (TSD 24,
  Section 4.2.1.1: all patients of an arm in which switching occurred must be recensored).

`RecensoringCounterexample.Constant`: everyone is censored at `5`.

* `naive_armLaw_ne`, `armLaw_recensored`: the arm laws of the naive observations differ at the
  true parameter, those of the recensored observations agree.
* `event_lost`: the deaths of control non-switchers at `4 ≤ 5` become censored observations at
  `D* = 5/2`.
* `tail_not_identified`: a second trial with the same arms, paths, censoring and recensored
  observations, satisfying the same assumptions, has a different untreated survival beyond
  `5/2` (`P(U > 17/4)` is `0` against `1/2`), while the unrecensored observed data distinguish
  the two trials. Long-term survival is not identified from the recensored data (TSD 16,
  Section 3.3.2; TSD 24, Section 4.2.1.1).

## Sources

N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16* (2014), Section 3.3.2 and
Appendix A; H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24*
(2024), Section 4.2.1.1. The numbers are this file's own.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace StructuralNested

namespace RecensoringCounterexample

open CausalInference.Mediation.Counterexample RPSFTMCounterexample

/-- The untreated time along the path `(a, ∞)` started at `0 ≤ a ≤ t`: `a + exp ψ (t - a)`. -/
theorem untreatedTime_Ioi (ψ : ℝ) {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    untreatedTime ψ (Ioi a) t = a + Real.exp ψ * (t - a) := by
  rw [untreatedTime_eq measurableSet_Ioi, ← treatmentGroupPath,
    timeOn_treatmentGroupPath ha (ha.trans hat), min_eq_left hat]
  ring

/-- The true parameter: the experimental treatment doubles survival time, `exp ψ₀ = 1/2`. -/
noncomputable def ψ₀ : ℝ := Real.log (1 / 2)

theorem exp_ψ₀ : Real.exp ψ₀ = 1 / 2 := Real.exp_log (by norm_num)

/-- The treatment paths: experimental patients are always treated; in the control arm the
good prognosis type never switches and the poor prognosis type switches at time `1`. -/
def path (ω : Ω₀) : Set ℝ := if ω.1 then univ else if ω.2.1 then ∅ else Ioi 1

theorem measurableSet_path (ω : Ω₀) : MeasurableSet (path ω) := by
  simp only [path]; split_ifs
  exacts [MeasurableSet.univ, MeasurableSet.empty, measurableSet_Ioi]

theorem log_half_neg : ψ₀ < 0 := Real.log_neg (by norm_num) (by norm_num)

/-- Conditional probabilities given the arm on the eight point space. -/
theorem condReal_arm (M : SwitchingTrial Ω₀) (hR : ∀ ω, M.R ω = ω.1) (r : Bool) (s : Set Ω₀) :
    (μ₀[|M.arm r]).real s = 2 * μ₀.real (M.arm r ∩ s) := by
  have hs : M.arm r = {ω : Ω₀ | ω.1 = r} := by ext ω; simp [SwitchingTrial.arm, hR]
  have hcard : (Finset.univ.filter fun ω : Ω₀ ↦ ω.1 = r).card = 4 := by cases r <;> rfl
  have hreal : μ₀.real (M.arm r) = 1 / 2 := by
    rw [hs, μ₀_real_eq (fun ω : Ω₀ ↦ ω.1 = r), hcard]; norm_num
  rw [measureReal_def, cond_apply (Set.toFinite _).measurableSet, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, hreal]
  norm_num

/-! ### Staggered entry: naive censoring is informative -/

namespace Staggered

/-- **The countermodel with staggered entry.** Arm `ω.1`, prognosis `ω.2.1` (good or poor),
administrative censoring time `C = 6` or `2` according to `ω.2.2` (early or late entry).
Untreated time `4` (good) or `9/5` (poor); experimental patients are treated throughout and
survive `8` or `18/5`; control patients of good prognosis never switch and die at `4`; control
patients of poor prognosis switch at `1` and die at `13/5`. -/
noncomputable def trial : CensoredTrial Ω₀ where
  R ω := ω.1
  T ω := if ω.1 then (if ω.2.1 then 8 else 18 / 5) else if ω.2.1 then 4 else 13 / 5
  A := path
  C ω := if ω.2.2 then 6 else 2
  U ω := if ω.2.1 then 4 else 9 / 5

theorem wellFormed : trial.WellFormed where
  measurableSet_path := measurableSet_path
  T_nonneg ω := by simp only [trial]; split_ifs <;> norm_num
  C_nonneg ω := by simp only [trial]; split_ifs <;> norm_num

theorem pathModel : trial.PathModel ψ₀ := by
  rintro ⟨a, u, v⟩
  cases a <;> cases u <;>
    simp [trial, path, untreatedTime_univ, untreatedTime_empty, exp_ψ₀,
      untreatedTime_Ioi ψ₀ zero_le_one (show (1 : ℝ) ≤ 13 / 5 by norm_num)] <;> norm_num

theorem randomizedCensored : trial.RandomizedCensored μ₀ := by
  have e : (fun ω : Ω₀ ↦ (trial.U ω, trial.C ω)) =
      (fun x : Bool × Bool ↦ ((if x.1 then 4 else 9 / 5 : ℝ), (if x.2 then 6 else 2 : ℝ))) ∘
        fun ω ↦ ω.2 := by
    funext ω; simp [trial]
  rw [CensoredTrial.RandomizedCensored, e]
  exact indepFun_A_UV.comp measurable_id (measurable_of_countable _)

/-- Independent censoring holds: `U` depends on the prognosis, `C` on the entry time. -/
theorem independentCensoring : trial.IndependentCensoring μ₀ := by
  have eU : trial.U = (fun b : Bool ↦ (if b then 4 else 9 / 5 : ℝ)) ∘ fun ω : Ω₀ ↦ ω.2.1 := by
    funext ω; simp [trial]
  have eC : trial.C = (fun b : Bool ↦ (if b then 6 else 2 : ℝ)) ∘ fun ω : Ω₀ ↦ ω.2.2 := by
    funext ω; simp [trial]
  rw [CensoredTrial.IndependentCensoring, eU, eC]
  exact indepFun_U_V.comp (measurable_of_countable _) (measurable_of_countable _)

/-- The naive transformed censoring times: `C/2` in the experimental arm, `C` for control
non-switchers, `(C + 1)/2` for control switchers. -/
theorem naiveCensTime_eq (ω : Ω₀) : trial.naiveCensTime ψ₀ ω =
    if ω.1 then trial.C ω / 2 else if ω.2.1 then trial.C ω else (trial.C ω + 1) / 2 := by
  obtain ⟨a, u, v⟩ := ω
  cases a <;> cases u <;> cases v <;>
    simp [CensoredTrial.naiveCensTime, trial, path, untreatedTime_univ, untreatedTime_empty,
      exp_ψ₀, untreatedTime_Ioi ψ₀ zero_le_one (show (1 : ℝ) ≤ 2 by norm_num),
      untreatedTime_Ioi ψ₀ zero_le_one (show (1 : ℝ) ≤ 6 by norm_num)] <;> norm_num

theorem recensTime_eq (ω : Ω₀) : trial.recensTime ψ₀ ω = trial.C ω / 2 := by
  rw [CensoredTrial.recensTime, recensoringTime_of_nonpos log_half_neg.le
    (wellFormed.C_nonneg ω), exp_ψ₀]
  ring

/-- **Naive censoring is informative.** The naive transformed censoring time is not independent
of the untreated time: `P(U = 4, C(ψ₀) = 6) = 1/8`, while `P(U = 4) P(C(ψ₀) = 6) = 1/16`. -/
theorem not_indepFun_naiveCensTime : ¬ IndepFun trial.U (trial.naiveCensTime ψ₀) μ₀ := by
  intro h
  have key := h.measure_inter_preimage_eq_mul {4} {6} (measurableSet_singleton _)
    (measurableSet_singleton _)
  have r := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ← measureReal_def] at r
  simp only [μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator,
    mem_inter_iff, mem_preimage, mem_singleton_iff, naiveCensTime_eq] at r
  simp only [trial] at r
  norm_num at r

/-- **Counterexample: without recensoring the untreated survival is not recovered.** In the
control arm, at `t = 19/10`, the true untreated survival is `1/2`, but the identification formula
of `CensoredTrial.armSurvival_U_eq_div` applied to the naive data gives `2/3`, while in the
experimental arm it gives `1/2`: a censoring-aware comparison of the naive data (a product limit
estimate, which here has the same value) is not null at the true parameter. With recensoring the
formula gives `1/2` in both arms. -/
theorem naive_biased :
    trial.toSwitchingTrial.armSurvival μ₀ trial.U false (19 / 10) = 1 / 2 ∧
      (μ₀[|trial.toSwitchingTrial.arm false]).real {ω | 19 / 10 < (trial.naive ψ₀ ω).1} /
        (μ₀[|trial.toSwitchingTrial.arm false]).real
          {ω | 19 / 10 < trial.naiveCensTime ψ₀ ω} = 2 / 3 ∧
      (μ₀[|trial.toSwitchingTrial.arm true]).real {ω | 19 / 10 < (trial.naive ψ₀ ω).1} /
        (μ₀[|trial.toSwitchingTrial.arm true]).real
          {ω | 19 / 10 < trial.naiveCensTime ψ₀ ω} = 1 / 2 ∧
      (μ₀[|trial.toSwitchingTrial.arm false]).real {ω | 19 / 10 < (trial.recensored ψ₀ ω).1} /
        (μ₀[|trial.toSwitchingTrial.arm false]).real
          {ω | 19 / 10 < trial.recensTime ψ₀ ω} = 1 / 2 := by
  have hc := condReal_arm trial.toSwitchingTrial (fun _ ↦ rfl)
  have hn : ∀ ω, (trial.naive ψ₀ ω).1 = min (trial.U ω) (trial.naiveCensTime ψ₀ ω) := fun ω ↦ by
    rw [CensoredTrial.naive_eq wellFormed pathModel]; rfl
  have hr : ∀ ω, (trial.recensored ψ₀ ω).1 = min (trial.U ω) (trial.recensTime ψ₀ ω) :=
    fun ω ↦ by rw [CensoredTrial.recensored_eq wellFormed pathModel]; rfl
  simp only [SwitchingTrial.armSurvival, hc, hn, hr, recensTime_eq, naiveCensTime_eq]
  simp only [μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool, Set.indicator, mem_inter_iff,
    SwitchingTrial.arm, mem_preimage, mem_singleton_iff, mem_ofPred_eq, trial,
    CensoredTrial.toSwitchingTrial]
  norm_num

/-- **Recensoring only the switchers does not work** (TSD 24, Section 4.2.1.1: potential
censoring times are needed "for all patients in a treatment arm in which switching occurred,
not just for patients who switched"). If only the control switchers are censored at `D*` and the
control non-switchers keep their censoring time `C`, the identification formula still gives `2/3`
in the control arm at `t = 19/10`, against the true `1/2`. -/
theorem switchersOnly_biased :
    (μ₀[|trial.toSwitchingTrial.arm false]).real
        {ω | 19 / 10 < min (trial.U ω)
          (if !ω.1 && !ω.2.1 then trial.recensTime ψ₀ ω else trial.naiveCensTime ψ₀ ω)} /
      (μ₀[|trial.toSwitchingTrial.arm false]).real
        {ω | 19 / 10 <
          (if !ω.1 && !ω.2.1 then trial.recensTime ψ₀ ω else trial.naiveCensTime ψ₀ ω)} =
      2 / 3 := by
  have hc := condReal_arm trial.toSwitchingTrial (fun _ ↦ rfl)
  simp only [hc, recensTime_eq, naiveCensTime_eq]
  simp only [μ₀_real_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool, Set.indicator, mem_inter_iff, SwitchingTrial.arm, mem_preimage,
    mem_singleton_iff, mem_ofPred_eq, trial, CensoredTrial.toSwitchingTrial]
  norm_num

end Staggered

/-! ### Constant censoring: the cost of recensoring -/

namespace Constant

/-- **The countermodel with a common censoring time.** Arm `ω.1`, prognostic scale `s = 2`
(good) or `1` (poor). Untreated time `2 s`; administrative censoring at `5` for everyone;
experimental patients survive `4 s`; control patients of good prognosis never switch and die at
`4`; control patients of poor prognosis switch at `1` and die at `3`. -/
noncomputable def trial : CensoredTrial Ω₀ where
  R ω := ω.1
  T ω := if ω.1 then 4 * scale ω else if ω.2.1 then 4 else 3
  A := path
  C _ := 5
  U ω := 2 * scale ω

theorem wellFormed : trial.WellFormed where
  measurableSet_path := measurableSet_path
  T_nonneg ω := by simp only [trial, scale]; split_ifs <;> norm_num
  C_nonneg _ := by norm_num [trial]

/-- The common effect `ψ₀` holds in path form. -/
theorem pathModel : trial.PathModel ψ₀ := by
  rintro ⟨a, u, v⟩
  cases a <;> cases u <;>
    simp [trial, path, scale, untreatedTime_univ, untreatedTime_empty, exp_ψ₀,
      untreatedTime_Ioi ψ₀ zero_le_one (show (1 : ℝ) ≤ 3 by norm_num)] <;> norm_num

/-- Randomization with censoring holds: `(U, C)` depends on the prognostic type only. -/
theorem randomizedCensored : trial.RandomizedCensored μ₀ := by
  have e : (fun ω : Ω₀ ↦ (trial.U ω, trial.C ω)) =
      (fun x : Bool × Bool ↦ ((2 : ℝ) * if x.1 then 2 else 1, (5 : ℝ))) ∘ fun ω ↦ ω.2 := by
    funext ω; simp [trial, scale]
  rw [CensoredTrial.RandomizedCensored, e]
  exact indepFun_A_UV.comp measurable_id (measurable_of_countable _)

/-- Censoring is administrative and independent of the untreated time. -/
theorem independentCensoring : trial.IndependentCensoring μ₀ :=
  indepFun_const_right _ _

/-- The naive transformed censoring times: `5/2` in the experimental arm, `5` for control
non-switchers (good prognosis), `3` for control switchers (poor prognosis). -/
theorem naiveCensTime_eq (ω : Ω₀) : trial.naiveCensTime ψ₀ ω =
    if ω.1 then 5 / 2 else if ω.2.1 then 5 else 3 := by
  obtain ⟨a, u, v⟩ := ω
  cases a <;> cases u <;>
    simp [CensoredTrial.naiveCensTime, trial, path, untreatedTime_univ, untreatedTime_empty,
      exp_ψ₀, untreatedTime_Ioi ψ₀ zero_le_one (show (1 : ℝ) ≤ 5 by norm_num)] <;> norm_num

/-- The naive transformed follow-up of each patient. -/
theorem naive_fst (ω : Ω₀) : (trial.naive ψ₀ ω).1 =
    if ω.1 then (if ω.2.1 then 5 / 2 else 2) else (if ω.2.1 then 4 else 2) := by
  rw [CensoredTrial.naive_eq wellFormed pathModel, naiveCensTime_eq]
  obtain ⟨a, u, v⟩ := ω
  cases a <;> cases u <;> norm_num [censorAt, trial, scale]

/-- The recensored observation of each patient: `D* = 5/2` for everyone. -/
theorem recensored_eq (ω : Ω₀) : trial.recensored ψ₀ ω =
    if ω.2.1 then (5 / 2, false) else (2, true) := by
  rw [CensoredTrial.recensored_eq wellFormed pathModel, CensoredTrial.recensTime,
    recensoringTime_of_nonpos log_half_neg.le (by norm_num [trial]), exp_ψ₀]
  obtain ⟨a, u, v⟩ := ω
  cases u <;> norm_num [censorAt, trial, scale]

/-- **The arm laws of the naive observations differ at the true parameter.** The arm means of
the naive transformed follow-up are `9/4` and `3`, so the laws differ, while the recensored
follow-up has arm contrast zero. In this model the difference comes from the experimental arm
being censored at `5/2` and the control arm not at all; no control untreated time is censored
by the naive rule, so a censoring-aware comparison of the naive data is not refuted here (see
`Staggered.naive_biased` for that). -/
theorem naive_armLaw_ne :
    trial.toSwitchingTrial.meanContrast μ₀ (fun ω ↦ (trial.naive ψ₀ ω).1) = -3 / 4 ∧
      trial.toSwitchingTrial.armLaw μ₀ (fun ω ↦ (trial.naive ψ₀ ω).1) true ≠
        trial.toSwitchingTrial.armLaw μ₀ (fun ω ↦ (trial.naive ψ₀ ω).1) false ∧
      trial.toSwitchingTrial.meanContrast μ₀ (fun ω ↦ (trial.recensored ψ₀ ω).1) = 0 := by
  have hm := fun (X : Ω₀ → ℝ) r ↦ armMean_μ₀ trial.toSwitchingTrial (fun _ ↦ rfl) X r
  have hc : trial.toSwitchingTrial.meanContrast μ₀ (fun ω ↦ (trial.naive ψ₀ ω).1) = -3 / 4 := by
    simp only [SwitchingTrial.meanContrast, hm, naive_fst]; norm_num
  refine ⟨hc, fun hlaw ↦ ?_, ?_⟩
  · have hX : Measurable fun ω : Ω₀ ↦ (trial.naive ψ₀ ω).1 := measurable_of_countable _
    rw [SwitchingTrial.meanContrast, SwitchingTrial.armMean_eq_integral_armLaw hX,
      SwitchingTrial.armMean_eq_integral_armLaw hX, hlaw, sub_self] at hc
    norm_num at hc
  · simp only [SwitchingTrial.meanContrast, hm, recensored_eq]; norm_num

/-- The general theorem applies: the recensored observations have the same law in both arms. -/
theorem armLaw_recensored :
    (μ₀[|trial.toSwitchingTrial.arm true]).map (trial.recensored ψ₀) =
      (μ₀[|trial.toSwitchingTrial.arm false]).map (trial.recensored ψ₀) :=
  CensoredTrial.armLaw_recensored_eq wellFormed pathModel (measurable_of_countable _)
    (measurable_of_countable _) (measurable_of_countable _) randomizedCensored
    (arm_ne_zero trial.toSwitchingTrial (fun _ ↦ rfl) true)
    (arm_ne_zero trial.toSwitchingTrial (fun _ ↦ rfl) false)

/-- **Recensoring discards an observed event with positive probability.** The control patients
of good prognosis die at `4 ≤ 5`, but their untreated time `4` exceeds `D* = 5/2`. -/
theorem event_lost :
    μ₀ {ω | trial.event ω = true ∧ (trial.recensored ψ₀ ω).2 = false ∧
      (trial.recensored ψ₀ ω).1 < trial.obsTime ω} ≠ 0 :=
  CensoredTrial.measure_event_lost_ne_zero wellFormed pathModel
    log_half_neg
    (μ₀_ne_zero_of_mem (ω := (false, true, true)) (by
      simp [trial, path, timeOn, exp_ψ₀]; norm_num))

/-- The same observed data up to censoring, except that the untreated time of the good
prognosis type is `9/2`: experimental patients of good prognosis survive `9` (censored at `5`),
control patients of good prognosis die at `9/2`. -/
noncomputable def trial' : CensoredTrial Ω₀ :=
  { trial with
    T := fun ω ↦ if ω.1 then (if ω.2.1 then 9 else 4) else if ω.2.1 then 9 / 2 else 3
    U := fun ω ↦ if ω.2.1 then 9 / 2 else 2 }

theorem wellFormed' : trial'.WellFormed where
  measurableSet_path := wellFormed.measurableSet_path
  T_nonneg ω := by simp only [trial']; split_ifs <;> norm_num
  C_nonneg := wellFormed.C_nonneg

theorem pathModel' : trial'.PathModel ψ₀ := by
  rintro ⟨a, u, v⟩
  cases a <;> cases u <;>
    simp [trial', trial, path, untreatedTime_univ, untreatedTime_empty, exp_ψ₀,
      untreatedTime_Ioi ψ₀ zero_le_one (show (1 : ℝ) ≤ 3 by norm_num)] <;> norm_num

theorem randomizedCensored' : trial'.RandomizedCensored μ₀ := by
  have e : (fun ω : Ω₀ ↦ (trial'.U ω, trial'.C ω)) =
      (fun x : Bool × Bool ↦ ((if x.1 then 9 / 2 else 2 : ℝ), (5 : ℝ))) ∘ fun ω ↦ ω.2 := by
    funext ω; simp [trial', trial]
  rw [CensoredTrial.RandomizedCensored, e]
  exact indepFun_A_UV.comp measurable_id (measurable_of_countable _)

/-- **Counterexample: the untreated survival beyond the recensoring time is not identified by
the recensored data** (TSD 16, Section 3.3.2; TSD 24, Section 4.2.1.1: the loss of long-term
information can give poor extrapolations). `trial` and `trial'` both satisfy the path model at
`ψ₀`, randomization with censoring and independent censoring, and have the same recensored
observations, but `P(U > 17/4) = 0` in `trial` and `1/2` in `trial'`. The unrecensored observed
data do distinguish them: the observed follow-up of a control patient of good prognosis is `4`
in one and `9/2` in the other. -/
theorem tail_not_identified :
    trial.recensored ψ₀ = trial'.recensored ψ₀ ∧ trial'.IndependentCensoring μ₀ ∧
      μ₀.real {ω | 17 / 4 < trial.U ω} = 0 ∧ μ₀.real {ω | 17 / 4 < trial'.U ω} = 1 / 2 ∧
      trial.observed ≠ trial'.observed := by
  refine ⟨CensoredTrial.recensored_eq_of_agree wellFormed wellFormed' pathModel pathModel' rfl
    (τ := 5 / 2) (fun ω ↦ ?_) (fun ω ↦ ?_) (fun ω ↦ ?_), indepFun_const_right _ _, ?_, ?_, ?_⟩
  · rw [CensoredTrial.recensTime, recensoringTime_of_nonpos log_half_neg.le
      (by norm_num [trial]), exp_ψ₀]
    norm_num [trial]
  · obtain ⟨a, u, v⟩ := ω; cases u <;> norm_num [trial', trial, scale]
  · obtain ⟨a, u, v⟩ := ω; cases u <;> norm_num [trial', trial, scale]
  · have : {ω : Ω₀ | 17 / 4 < trial.U ω} = ∅ := by
      ext ⟨a, u, v⟩; cases u <;> norm_num [trial, scale]
    rw [this, measureReal_empty]
  · have : {ω : Ω₀ | 17 / 4 < trial'.U ω} = {ω | ω.2.1 = true} := by
      ext ⟨a, u, v⟩; cases u <;> norm_num [trial']
    rw [this, μ₀_real_eq]
    have c : (Finset.univ.filter fun ω : Ω₀ ↦ ω.2.1 = true).card = 4 := rfl
    rw [c]; norm_num
  · intro h
    have := congrArg (fun f ↦ (f (false, true, true)).2.1) h
    simp only [CensoredTrial.observed, CensoredTrial.obsTime, trial', trial] at this
    norm_num at this

end Constant

end RecensoringCounterexample

end StructuralNested

end CausalInference
