/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.RecensoringCounterexamples

/-!
# Recensoring bias under a treatment effect that changes over time

TSD 16, Section 3.3.2, states: "In addition, recensoring may lead to biased estimates of the
"average" treatment effect in circumstances where proportional treatment effect assumptions do
not hold, because longer term data on the effect of treatment may be lost." TSD 24,
Section 4.2.1.1, states that the loss of information "could result in poor extrapolations and
biased estimates of long-term treatment effects. This is likely to be the case when important
changes in hazards occur beyond the recensored follow-up times, and/or when important changes in
the treatment effect occur beyond the recensored follow-up times", and reports that analyses
with and without recensoring "often provided bias in opposite directions". This file makes these
statements precise in one explicit model, which illustrates them and proves nothing general
about them. The general results are only the monotonicity of the information loss and the
validity of the recensored estimating function under a common effect.

## Main definitions

* `StructuralNested.untreatedTimeVarying φ A t = ∫_0^t exp (φ s 1_A(s)) ds`: the untreated time
  under a log time ratio `φ s` that changes with time; `twoPhase ψ₁ ψ₂ τ` is `ψ₁` up to `τ` and
  `ψ₂` after it.
* `CensoredTrial.recMean ψ`, `CensoredTrial.naiveMean ψ`: the mean-form estimating function
  (arm contrast of the mean follow-up on the untreated scale) applied to the recensored and to
  the naive (unrecensored) data. Under censoring the mean of the uncensored untreated time is
  not available; these are means of censored follow-up times, which are functions of the
  observed data.

## Main results

* `event_lost_mono`, `CensoredTrial.eventLost_subset`, `CensoredTrial.measure_eventLost_mono`: for
  `ψ ≤ ψ' ≤ 0` every observed event lost by recensoring at `ψ'` is lost at `ψ`, for one patient
  and as a probability inequality.
* `CensoredTrial.recMean_trueParam`: under a common effect `ψ₀` and randomization with respect to
  `(U, C)`, `recMean ψ₀ = 0`, so `recMean` is a valid estimating function in the model of
  `CausalInference.Survival.Recensoring`.
* The model `RecensoringBias.trial`: experimental patients are treated throughout, control
  patients never; the treatment halves time during its first two time units and has no effect
  after (`φ = twoPhase (log (1/2)) 0 2`); untreated time `4` or `1` by a prognostic type
  independent of the arm; administrative censoring at `3`. Randomization with censoring and
  independent censoring hold (`randomizedCensored`, `independentCensoring`); no common effect
  fits (`not_pathModel`). There is no switching: recensoring at a candidate `ψ` is applied to
  all patients of both arms, as in g-estimation, and the mechanism is the one of the documents
  (loss of the late follow-up).
  * `gMean_eq_zero_iff`, `average`: with full follow-up the root is `ψ̄ = log (5/7)`, with
    `5/7 = (4/7)(1/2) + (3/7)(1)`, the average of the two time ratios weighted by the shares of
    the experimental arm's treated time before and after the change point.
  * `recMean_eq_zero_iff`: with recensoring the root is the early effect `log (1/2)`;
    `naiveMean_eq_zero_iff`: without recensoring it is `log (4/5)`; `roots_ordered`.
  * `bracket`: the plug-in mean untreated time of the experimental arm is `5/2` (the truth) for
    the uncensored root, `7/4` for the recensored root and `14/5` for the unrecensored root: the
    analyses with and without recensoring err in opposite directions here. Whether they do in
    general is not claimed (the documents say "often").

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16* (2014), Section 3.3.2.
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24* (2024),
  Section 4.2.1.1, "Issues relating to re-censoring", citing N. R. Latimer et al., *Causal
  inference for long-term survival in randomised trials with treatment switching: Should
  re-censoring be applied when estimating counterfactual survival times?*, Statistical Methods
  in Medical Research (2019).

The numbers of the model are this file's own.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace StructuralNested

/-! ### A time-varying effect -/

/-- **The untreated time under a time-varying effect.** With log time ratio `φ s` at time `s`,
the untreated time of a patient observed to survive to `t` along the path `A` is
`∫_0^t exp (φ s 1_A(s)) ds`. A constant `φ` gives `untreatedTime`. -/
noncomputable def untreatedTimeVarying (φ : ℝ → ℝ) (A : Set ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0)..t, Real.exp (φ s * A.indicator 1 s)

theorem untreatedTimeVarying_const (ψ : ℝ) (A : Set ℝ) (t : ℝ) :
    untreatedTimeVarying (fun _ ↦ ψ) A t = untreatedTime ψ A t := rfl

/-- A two-phase log time ratio: `ψ₁` up to time `τ`, `ψ₂` after it. -/
noncomputable def twoPhase (ψ₁ ψ₂ τ : ℝ) (s : ℝ) : ℝ := if s ≤ τ then ψ₁ else ψ₂

theorem untreatedTimeVarying_empty (φ : ℝ → ℝ) (t : ℝ) : untreatedTimeVarying φ ∅ t = t := by
  simp [untreatedTimeVarying]

theorem intervalIntegrable_exp_twoPhase (ψ₁ ψ₂ τ a b : ℝ) :
    IntervalIntegrable (fun s ↦ Real.exp (twoPhase ψ₁ ψ₂ τ s)) volume a b := by
  have hm : Measurable fun s ↦ Real.exp (twoPhase ψ₁ ψ₂ τ s) :=
    Real.measurable_exp.comp (Measurable.ite measurableSet_Iic measurable_const measurable_const)
  refine (intervalIntegrable_const (c := max (Real.exp ψ₁) (Real.exp ψ₂))).mono_fun
    hm.aestronglyMeasurable (ae_of_all _ fun s ↦ ?_)
  simp only [twoPhase, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [abs_of_pos (lt_max_of_lt_left (Real.exp_pos _))]
  split_ifs
  exacts [le_max_left _ _, le_max_right _ _]

/-- **Closed form for an always treated patient beyond the change point.** For `0 ≤ τ ≤ t`,
`∫_0^t exp (twoPhase ψ₁ ψ₂ τ s) ds = exp ψ₁ τ + exp ψ₂ (t - τ)`. -/
theorem untreatedTimeVarying_twoPhase_univ {ψ₁ ψ₂ τ t : ℝ} (hτ : 0 ≤ τ) (hτt : τ ≤ t) :
    untreatedTimeVarying (twoPhase ψ₁ ψ₂ τ) univ t =
      Real.exp ψ₁ * τ + Real.exp ψ₂ * (t - τ) := by
  simp only [untreatedTimeVarying, indicator_univ, Pi.one_apply, mul_one]
  have hi := intervalIntegrable_exp_twoPhase ψ₁ ψ₂ τ
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 τ) (hi τ t),
    intervalIntegral.integral_of_le hτ, intervalIntegral.integral_of_le hτt]
  have h1 : ∫ x in Ioc 0 τ, Real.exp (twoPhase ψ₁ ψ₂ τ x) = ∫ x in Ioc 0 τ, Real.exp ψ₁ :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by simp [twoPhase, hx.2]
  have h2 : ∫ x in Ioc τ t, Real.exp (twoPhase ψ₁ ψ₂ τ x) = ∫ x in Ioc τ t, Real.exp ψ₂ :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by simp [twoPhase, not_le.2 hx.1]
  rw [h1, h2]
  simp [hτ, hτt]
  ring

/-- Closed form before the change point: for `0 ≤ t ≤ τ`, the untreated time of an always
treated patient is `exp ψ₁ t`. -/
theorem untreatedTimeVarying_twoPhase_univ_le {ψ₁ ψ₂ τ t : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ) :
    untreatedTimeVarying (twoPhase ψ₁ ψ₂ τ) univ t = Real.exp ψ₁ * t := by
  simp only [untreatedTimeVarying, indicator_univ, Pi.one_apply, mul_one]
  rw [intervalIntegral.integral_of_le ht]
  have h1 : ∫ x in Ioc 0 t, Real.exp (twoPhase ψ₁ ψ₂ τ x) = ∫ x in Ioc 0 t, Real.exp ψ₁ :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by simp [twoPhase, hx.2.trans htτ]
  rw [h1]
  simp [ht]
  ring

/-! ### Information loss grows with the benefit -/

/-- **A larger benefit loses at least the same events, for one patient** (TSD 16,
Section 3.3.2; TSD 24, Section 4.2.1.1: "the larger the treatment effect, the more data are
lost"). For a measurable path, an observed event at `0 ≤ t ≤ c`, and candidate parameters
`ψ ≤ ψ' ≤ 0`: if recensoring at `ψ'` turns the event into a censored observation, so does
recensoring at `ψ`. -/
theorem event_lost_mono {A : Set ℝ} (hA : MeasurableSet A) {ψ ψ' : ℝ} (hψ : ψ ≤ ψ')
    (hψ' : ψ' ≤ 0) {t c : ℝ} (ht : 0 ≤ t) (htc : t ≤ c)
    (hlost : (censorAt (untreatedTime ψ' A t) (recensoringTime ψ' c)).2 = false) :
    (censorAt (untreatedTime ψ A t) (recensoringTime ψ c)).2 = false := by
  have hc : 0 ≤ c := ht.trans htc
  rw [event_lost_iff, recensoringTime_of_nonpos hψ' hc, untreatedTime_eq hA] at hlost
  rw [event_lost_iff, recensoringTime_of_nonpos (hψ.trans hψ') hc, untreatedTime_eq hA]
  have h0 := timeOn_nonneg A ht
  have h1 := timeOn_le hA ht
  have he : Real.exp ψ ≤ Real.exp ψ' := Real.exp_le_exp.2 hψ
  nlinarith [mul_le_mul_of_nonneg_right he (sub_nonneg.2 (h1.trans htc))]

namespace CensoredTrial

variable {Ω : Type*} {M : CensoredTrial Ω}

/-- **A larger benefit loses at least the same events, in a trial.** For a well formed trial
and `ψ ≤ ψ' ≤ 0`, the observed events lost by recensoring at `ψ'` are lost at `ψ`. No model
assumption is needed: the recensored observation at a candidate parameter is computed from the
observed data. -/
theorem eventLost_subset (hwf : M.WellFormed) {ψ ψ' : ℝ} (hψ : ψ ≤ ψ') (hψ' : ψ' ≤ 0) :
    {ω | M.event ω = true ∧ (M.recensored ψ' ω).2 = false} ⊆
      {ω | M.event ω = true ∧ (M.recensored ψ ω).2 = false} := by
  rintro ω ⟨he, hl⟩
  have hTC : M.T ω ≤ M.C ω := by simpa [event] using he
  have e : ∀ x, M.recensored x ω =
      censorAt (untreatedTime x (M.A ω) (M.T ω)) (recensoringTime x (M.C ω)) := fun x ↦
    recensorData_eq (hwf.measurableSet_path ω) x (hwf.C_nonneg ω)
  rw [e] at hl
  refine ⟨he, ?_⟩
  rw [e]
  exact event_lost_mono (hwf.measurableSet_path ω) hψ hψ' (hwf.T_nonneg ω) hTC hl

/-- **The probability of losing an observed event is antitone in `ψ` on the beneficial
side.** -/
theorem measure_eventLost_mono [MeasurableSpace Ω] (μ : Measure Ω) (hwf : M.WellFormed)
    {ψ ψ' : ℝ} (hψ : ψ ≤ ψ') (hψ' : ψ' ≤ 0) :
    μ {ω | M.event ω = true ∧ (M.recensored ψ' ω).2 = false} ≤
      μ {ω | M.event ω = true ∧ (M.recensored ψ ω).2 = false} :=
  measure_mono (eventLost_subset hwf hψ hψ')

/-! ### Mean-form estimating functions on censored data -/

variable [MeasurableSpace Ω] (μ : Measure Ω)

variable (M) in
/-- **The mean-form estimating function on recensored data**: the arm contrast of the mean of
the recensored follow-up `min (U(ψ), D*(ψ))`, computed from the observed data. -/
noncomputable def recMean (ψ : ℝ) : ℝ :=
  M.toSwitchingTrial.meanContrast μ fun ω ↦ (M.recensored ψ ω).1

variable (M) in
/-- **The same estimating function without recensoring**: the arm contrast of the mean of the
naive transformed follow-up. -/
noncomputable def naiveMean (ψ : ℝ) : ℝ :=
  M.toSwitchingTrial.meanContrast μ fun ω ↦ (M.naive ψ ω).1

variable {μ}

/-- **The recensored estimating function is valid under a common effect.** Under the path model
at `ψ₀`, randomization with respect to `(U, C)` and measurable `R`, `U`, `C`, the arm means of the
recensored follow-up agree at `ψ₀`: `recMean ψ₀ = 0`. -/
theorem recMean_trueParam [IsFiniteMeasure μ] (hwf : M.WellFormed) {ψ₀ : ℝ}
    (h : M.PathModel ψ₀) (hR : Measurable M.R) (hU : Measurable M.U) (hC : Measurable M.C)
    (hrand : M.RandomizedCensored μ) (h1 : μ (M.toSwitchingTrial.arm true) ≠ 0)
    (h0 : μ (M.toSwitchingTrial.arm false) ≠ 0) : M.recMean μ ψ₀ = 0 := by
  have hg : Measurable fun p : ℝ × ℝ ↦ (censorAt p.1 (recensoringTime ψ₀ p.2)).1 :=
    measurable_fst.comp (measurable_censorAt.comp
      (measurable_fst.prodMk ((measurable_recensoringTime ψ₀).comp measurable_snd)))
  have e : (fun ω ↦ (M.recensored ψ₀ ω).1) =
      fun ω ↦ (fun p : ℝ × ℝ ↦ (censorAt p.1 (recensoringTime ψ₀ p.2)).1) (M.U ω, M.C ω) := by
    funext ω; rw [recensored_eq hwf h]; rfl
  have hX : Measurable fun ω ↦
      (fun p : ℝ × ℝ ↦ (censorAt p.1 (recensoringTime ψ₀ p.2)).1) (M.U ω, M.C ω) :=
    hg.comp (hU.prodMk hC)
  rw [recMean, e, SwitchingTrial.meanContrast, SwitchingTrial.armMean_eq_integral_armLaw hX,
    SwitchingTrial.armMean_eq_integral_armLaw hX, SwitchingTrial.armLaw, SwitchingTrial.armLaw,
    map_cond_arm_of_randomizedCensored hR hU hC hrand hg h1,
    map_cond_arm_of_randomizedCensored hR hU hC hrand hg h0, sub_self]

end CensoredTrial

/-! ### One model: an early benefit that fades -/

namespace RecensoringBias

open CausalInference.Mediation.Counterexample RPSFTMCounterexample
open RecensoringCounterexample (ψ₀ exp_ψ₀ log_half_neg)

theorem timeOn_univ (t : ℝ) : timeOn univ t = t := by simp [timeOn]

theorem timeOn_empty (t : ℝ) : timeOn ∅ t = 0 := by simp [timeOn]

/-- The log time ratio of the model: `log (1/2)` (survival time doubled) during the first two
time units on treatment, `0` (no effect) afterwards. -/
noncomputable def φ : ℝ → ℝ := twoPhase ψ₀ 0 2

/-- Experimental patients are treated throughout; control patients are never treated. -/
def path (ω : Ω₀) : Set ℝ := if ω.1 then univ else ∅

/-- **The model.** Arm `ω.1`, prognostic type `ω.2.1` (long or short survivor), independent of
the arm. Untreated time `4` (long) or `1` (short); administrative censoring at `3` for everyone.
Under the time-varying effect `φ`, experimental patients survive `5` (long) or `2` (short),
control patients `4` or `1`. -/
noncomputable def trial : CensoredTrial Ω₀ where
  R ω := ω.1
  T ω := if ω.1 then (if ω.2.1 then 5 else 2) else (if ω.2.1 then 4 else 1)
  A := path
  C _ := 3
  U ω := if ω.2.1 then 4 else 1

theorem wellFormed : trial.WellFormed where
  measurableSet_path ω := by
    simp only [trial, path]; split_ifs
    exacts [MeasurableSet.univ, MeasurableSet.empty]
  T_nonneg ω := by simp only [trial]; split_ifs <;> norm_num
  C_nonneg _ := by norm_num [trial]

/-- The time-varying structural model holds:
`U = ∫_0^T exp (φ s 1_A(s)) ds` for every patient. -/
theorem timeVarying (ω : Ω₀) :
    trial.U ω = untreatedTimeVarying φ (trial.A ω) (trial.T ω) := by
  obtain ⟨a, u, v⟩ := ω
  cases a <;> cases u
  · simp [trial, path, untreatedTimeVarying_empty]
  · simp [trial, path, untreatedTimeVarying_empty]
  · simp only [trial, path, ite_true, Bool.false_eq_true, ite_false, φ]
    rw [untreatedTimeVarying_twoPhase_univ_le (by norm_num) le_rfl, exp_ψ₀]; norm_num
  · simp only [trial, path, ite_true, φ]
    rw [untreatedTimeVarying_twoPhase_univ (by norm_num) (by norm_num), exp_ψ₀]; norm_num

/-- No common treatment effect fits the model: short survivors force time ratio `1/2`, long
survivors `4/5`. -/
theorem not_pathModel (ψ : ℝ) : ¬ trial.PathModel ψ := by
  intro h
  have h1 := h (true, false, false)
  have h2 := h (true, true, false)
  simp only [trial, path, ite_true, Bool.false_eq_true, ite_false, untreatedTime_univ] at h1 h2
  linarith

theorem randomizedCensored : trial.RandomizedCensored μ₀ := by
  have e : (fun ω : Ω₀ ↦ (trial.U ω, trial.C ω)) =
      (fun x : Bool × Bool ↦ ((if x.1 then 4 else 1 : ℝ), (3 : ℝ))) ∘ fun ω ↦ ω.2 := by
    funext ω; simp [trial]
  rw [CensoredTrial.RandomizedCensored, e]
  exact indepFun_A_UV.comp measurable_id (measurable_of_countable _)

theorem independentCensoring : trial.IndependentCensoring μ₀ := indepFun_const_right _ _

theorem armMean_eq (X : Ω₀ → ℝ) (r : Bool) : trial.toSwitchingTrial.armMean μ₀ X r =
    (X (r, false, false) + X (r, false, true) + X (r, true, false) + X (r, true, true)) / 4 :=
  armMean_μ₀ trial.toSwitchingTrial (fun _ ↦ rfl) X r

/-- **The uncensored estimating function**: with full follow-up,
`gMean ψ = (7/2) exp ψ - 5/2`. -/
theorem gMean_eq (ψ : ℝ) : trial.toSwitchingTrial.gMean μ₀ ψ = 7 / 2 * Real.exp ψ - 5 / 2 := by
  simp only [SwitchingTrial.gMean, SwitchingTrial.meanContrast, armMean_eq]
  simp only [SwitchingTrial.counterfactual, SwitchingTrial.Tc, CensoredTrial.toSwitchingTrial,
    trial, path, ite_true, Bool.false_eq_true, ite_false, timeOn_univ, timeOn_empty]
  ring

/-- The naive transformed follow-up of each patient. -/
theorem naive_fst (ψ : ℝ) (ω : Ω₀) : (trial.naive ψ ω).1 =
    if ω.1 then (if ω.2.1 then 3 * Real.exp ψ else 2 * Real.exp ψ)
    else (if ω.2.1 then 3 else 1) := by
  obtain ⟨a, u, v⟩ := ω
  cases a <;> cases u <;>
    norm_num [CensoredTrial.naive, naiveData, CensoredTrial.obsTime, CensoredTrial.event,
      CensoredTrial.obsTimeOn, trial, path, timeOn_univ, timeOn_empty] <;> ring

/-- The recensored follow-up is the naive one cut at `D*(ψ) = min (3, 3 exp ψ)`. -/
theorem recensored_fst (ψ : ℝ) (ω : Ω₀) :
    (trial.recensored ψ ω).1 = min (trial.naive ψ ω).1 (recensoringTime ψ 3) := rfl

/-- **The estimating function without recensoring**: `naiveMean ψ = (5/2) exp ψ - 2`. -/
theorem naiveMean_eq (ψ : ℝ) : trial.naiveMean μ₀ ψ = 5 / 2 * Real.exp ψ - 2 := by
  simp only [CensoredTrial.naiveMean, SwitchingTrial.meanContrast, armMean_eq, naive_fst]
  norm_num
  ring

/-- **The estimating function with recensoring**:
`recMean ψ = (min (2 exp ψ, D*) - min (1, D*)) / 2` with `D* = min (3, 3 exp ψ)`. -/
theorem recMean_eq (ψ : ℝ) : trial.recMean μ₀ ψ =
    (min (2 * Real.exp ψ) (recensoringTime ψ 3) - min 1 (recensoringTime ψ 3)) / 2 := by
  have hD3 : recensoringTime ψ 3 ≤ 3 := recensoringTime_le_self ψ 3
  have hDe : recensoringTime ψ 3 ≤ 3 * Real.exp ψ := by
    rw [recensoringTime, mul_comm]; exact min_le_right _ _
  simp only [CensoredTrial.recMean, SwitchingTrial.meanContrast, armMean_eq, recensored_fst,
    naive_fst]
  norm_num [min_eq_right hD3, min_eq_right hDe]
  ring

/-- **(a) With full follow-up the root is a time-weighted average of the two effects:**
`gMean ψ = 0 ↔ ψ = log (5/7)`, and `5/7 = (4/7) exp ψ₁ + (3/7) exp ψ₂` with `exp ψ₁ = 1/2`,
`exp ψ₂ = 1`. The weights are the shares of the experimental arm's time on treatment spent
before (`2 + 2`) and after (`3`) the change point. -/
theorem eq_log_iff (ψ : ℝ) {x : ℝ} (hx : 0 < x) : ψ = Real.log x ↔ Real.exp ψ = x := by
  rw [← Real.exp_injective.eq_iff, Real.exp_log hx]

theorem gMean_eq_zero_iff (ψ : ℝ) :
    trial.toSwitchingTrial.gMean μ₀ ψ = 0 ↔ ψ = Real.log (5 / 7) := by
  rw [gMean_eq, eq_log_iff ψ (by norm_num)]
  constructor <;> intro h <;> linarith

theorem average : (5 / 7 : ℝ) = 4 / 7 * Real.exp ψ₀ + 3 / 7 * Real.exp 0 := by
  rw [exp_ψ₀, Real.exp_zero]; norm_num

/-- **Without recensoring the root is `log (4/5)`.** -/
theorem naiveMean_eq_zero_iff (ψ : ℝ) : trial.naiveMean μ₀ ψ = 0 ↔ ψ = Real.log (4 / 5) := by
  rw [naiveMean_eq, eq_log_iff ψ (by norm_num)]
  constructor <;> intro h <;> linarith

/-- **(b) With recensoring the root is the early effect `ψ₁ = log (1/2)`.** The recensored data
stop at `D* = 3 exp ψ ≤ 3`, inside the period in which the treatment halves the time, so the
late period without effect no longer contributes. -/
theorem recMean_eq_zero_iff (ψ : ℝ) : trial.recMean μ₀ ψ = 0 ↔ ψ = ψ₀ := by
  rw [recMean_eq, show ψ = ψ₀ ↔ Real.exp ψ = 1 / 2 from eq_log_iff ψ (by norm_num)]
  have hx := Real.exp_pos ψ
  rcases le_or_gt ψ 0 with hψ | hψ
  · rw [recensoringTime_of_nonpos hψ (by norm_num), min_eq_left (by nlinarith)]
    rcases le_or_gt (Real.exp ψ * 3) 1 with h3 | h3
    · rw [min_eq_right h3]
      constructor <;> intro h <;> nlinarith
    · rw [min_eq_left h3.le]
      constructor <;> intro h <;> linarith
  · have he : 1 < Real.exp ψ := by simpa using Real.exp_lt_exp.2 hψ
    rw [recensoringTime_of_nonneg hψ.le (by norm_num), min_eq_left (by norm_num : (1 : ℝ) ≤ 3)]
    constructor
    · intro h
      have : 1 < min (2 * Real.exp ψ) 3 := lt_min (by linarith) (by norm_num)
      linarith
    · intro h; linarith

/-- The three roots are ordered: recensored `<` uncensored `<` naive. -/
theorem roots_ordered : ψ₀ < Real.log (5 / 7) ∧ Real.log (5 / 7) < Real.log (4 / 5) := by
  refine ⟨?_, Real.log_lt_log (by norm_num) (by norm_num)⟩
  rw [RecensoringCounterexample.ψ₀]; exact Real.log_lt_log (by norm_num) (by norm_num)

/-- The plug-in estimate of the mean untreated time of the experimental arm for a parameter
`ψ`: `E[T^c + exp ψ T^e | R = 1]`, computed from the full survival times of the experimental arm
(that is, assuming the observed experimental arm survival is extrapolated without error, so that
only the estimate of `ψ` matters). -/
noncomputable def meanUntreatedEstimate (ψ : ℝ) : ℝ :=
  trial.toSwitchingTrial.armMean μ₀ (trial.toSwitchingTrial.counterfactual ψ) true

theorem meanUntreatedEstimate_eq (ψ : ℝ) : meanUntreatedEstimate ψ = 7 / 2 * Real.exp ψ := by
  simp only [meanUntreatedEstimate, armMean_eq]
  simp only [SwitchingTrial.counterfactual, SwitchingTrial.Tc, CensoredTrial.toSwitchingTrial,
    trial, path, ite_true, Bool.false_eq_true, ite_false, timeOn_univ]
  ring

/-- **(c) and the two analyses bracket the truth.** The true mean untreated time of the
experimental arm is `E[U | R = 1] = 5/2`. The uncensored analysis recovers it; the recensored
analysis gives `7/4` (too small: the benefit is overstated); the analysis without recensoring
gives `14/5` (too large: the benefit is understated). In this model the analyses with and
without recensoring are biased in opposite directions, as TSD 24 (Section 4.2.1.1) reports they
often are; this is one model, not a general theorem. -/
theorem bracket :
    trial.toSwitchingTrial.armMean μ₀ trial.U true = 5 / 2 ∧
      meanUntreatedEstimate (Real.log (5 / 7)) = 5 / 2 ∧
      meanUntreatedEstimate ψ₀ = 7 / 4 ∧
      meanUntreatedEstimate (Real.log (4 / 5)) = 14 / 5 ∧
      meanUntreatedEstimate ψ₀ < 5 / 2 ∧ 5 / 2 < meanUntreatedEstimate (Real.log (4 / 5)) := by
  have hU : trial.toSwitchingTrial.armMean μ₀ trial.U true = 5 / 2 := by
    simp only [armMean_eq]; norm_num [trial]
  simp only [meanUntreatedEstimate_eq, exp_ψ₀, Real.exp_log (show (0 : ℝ) < 5 / 7 by norm_num),
    Real.exp_log (show (0 : ℝ) < 4 / 5 by norm_num)]
  refine ⟨hU, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end RecensoringBias

end StructuralNested

end CausalInference
