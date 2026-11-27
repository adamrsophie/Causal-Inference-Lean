/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.FailureTime

/-!
# Recensoring

Administrative censoring in the rank preserving structural failure time model
(`CausalInference.StructuralNested.SwitchingTrial`). A patient followed until the data cut-off
at time `C` (known for every patient) is censored at `C` if still alive. Transforming the
follow-up to the untreated scale with Equation A2 turns the censoring time into
`∫_0^C exp (ψ A(s)) ds`, which depends on the treatment path; since switching depends on
prognosis, the transformed censoring is informative. Recensoring replaces it by
`D*(ψ) = min (C, exp ψ C)` for every patient: an event of the untreated time later than `D*` is
censored at `D*`.

## Main definitions

* `StructuralNested.recensoringTime ψ c = min c (exp ψ * c)`: the recensoring time.
* `StructuralNested.censorAt u d = (min u d, 1{u ≤ d})`: a time censored at `d`.
* `StructuralNested.recensorData`, `StructuralNested.naiveData`: the recensored and the naive
  observation of one patient, computed from the observed follow-up, event indicator, time on the
  experimental treatment during follow-up, and administrative censoring time.
* `StructuralNested.CensoredTrial`: a trial with arm `R`, survival time `T`, treatment path `A`,
  administrative censoring time `C`, untreated time `U`; `CensoredTrial.PathModel ψ` (Equation
  A2 with a common effect), `CensoredTrial.RandomizedCensored` (the arm is independent of the
  pair `(U, C)`), `CensoredTrial.IndependentCensoring` (`U` independent of `C`), and the
  observations `CensoredTrial.recensored`, `CensoredTrial.naive`.

## Main results

* `recensoringTime_isLeast`: `D*(ψ)` is the least transformed censoring time over all treatment
  paths, "the earliest possible censoring time given the treatment effect" (TSD 16, Appendix A).
* `recensorData_eq`, `CensoredTrial.recensored_eq`: the recensored observation computed from the
  observed data is the untreated time censored at `D*`, `(min (U, D*), 1{U ≤ D*})`;
  `CensoredTrial.recensored_eq_comp_observed`: it is a function of the observed data.
  `naiveData_eq`, `CensoredTrial.naive_eq`: the naive observation is the untreated time censored
  at the path dependent transformed censoring time.
* `CensoredTrial.map_cond_recensTime`, `CensoredTrial.map_cond_recensored`,
  `CensoredTrial.armLaw_recensored_eq`: under the path model at the true `ψ₀` and randomization
  with respect to `(U, C)`, the recensoring time and the recensored observation have the same
  law in each arm as in the trial, so the population target of a g-test on recensored data is
  null at `ψ₀`.
* `CensoredTrial.armSurvival_U_eq_div`: under independent censoring as well, the untreated
  survival in each arm is identified from the recensored data wherever `P(D* > t) > 0`,
  `P(U > t | R = r) = P(min (U, D*) > t | R = r) / P(D* > t | R = r)` ("valid estimates of
  treatment effects up to the maximum recensored follow-up time", TSD 24, Section 4.2.1.1).
  `CensoredTrial.recensored_eq_of_agree`: beyond a bound of the recensoring times the recensored
  data do not depend on the untreated times at all.
* The cost: `recensoringTime_le_self`, `recensoringTime_lt_self`, `recensoringTime_monotone`,
  `recensoringTime_strictMonoOn` (the larger the benefit, the earlier the recensoring time; for
  harmful effects `D* = C`, `recensoringTime_of_nonneg`); `CensoredTrial.recensored_le_naive`,
  `CensoredTrial.recensored_le_obsTime` (shorter follow-up, fewer events);
  `CensoredTrial.measure_event_lost_ne_zero` (under a beneficial effect, observed events are lost
  with positive probability as soon as untreated patients die between `exp ψ C` and `C`).

The countermodels (naive censoring is informative and misses the untreated survival at the true
parameter; recensoring only the switchers fails; events are lost; the tail beyond the
recensoring time is not identified) are in `CausalInference.Survival.RecensoringCounterexamples`.

## Setting and scope

Counterfactual variables on a general probability space (Mathlib `MeasureTheory`, independence
`ProbabilityTheory.IndepFun`); real times; treatment paths are measurable sets of times, as in
`CausalInference.StructuralNested.FailureTime`. Censoring is administrative: `C` is observed for
every patient. Recensoring is applied to every patient in both arms, with the same rule; in an
experimental arm treated throughout with `ψ ≤ 0` it changes nothing
(`untreatedTime_univ_eq_recensoringTime`). The discrete time layer of
`CausalInference.Survival.Censoring` (natural number times) is not used: the identification of
the untreated survival is stated directly for real times. Not formalized: the simulation findings
that recensoring may bias average effects when the treatment effect is not proportional (TSD 16,
Section 3.3.2) and that analyses with and without recensoring are both prone to bias, often in
opposite directions, so both should be presented (TSD 24, Section 4.2.1.1, citing Latimer et al.
2019; reporting guidelines RPSFTM9, IPE7, TSEs8, TSEg13 of Section 6); recensoring for two-stage
estimation (TSD 24, Section 4.2.3.1); the estimation of `ψ` from a finite sample.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014): Section 3.3.2 and Appendix A
  ("RPSFTM", the recensoring rule `min (C_i, exp (ψ) C_i)`).
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to TSD 16*
  (2024): Section 4.2.1 and Section 4.2.1.1, "Issues relating to re-censoring".
* I. R. White, A. G. Babiker, S. Walker, J. H. Darbyshire, *Randomization-based methods for
  correcting for treatment changes: examples from the Concorde trial*, Statistics in Medicine
  (1999).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace StructuralNested

/-! ### The recensoring time of one patient -/

/-- **The recensoring time** (TSD 16, Appendix A, RPSFTM; White et al.): for a candidate
parameter `ψ` and an administrative censoring time `c`, `D*(ψ) = min (c, exp ψ c)`. It depends
on `c` and `ψ` only, not on the treatment path. -/
noncomputable def recensoringTime (ψ c : ℝ) : ℝ := min c (Real.exp ψ * c)

theorem recensoringTime_eq_min_mul (ψ : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    recensoringTime ψ c = min 1 (Real.exp ψ) * c := by
  rw [recensoringTime, min_mul_of_nonneg _ _ hc, one_mul]

theorem untreatedTime_empty (ψ c : ℝ) : untreatedTime ψ ∅ c = c := by
  simp [untreatedTime]

theorem untreatedTime_univ (ψ c : ℝ) : untreatedTime ψ univ c = Real.exp ψ * c := by
  simp [untreatedTime, mul_comm]

/-- **The recensoring time is the earliest possible censoring time given `ψ`** (TSD 16,
Appendix A). For `c ≥ 0`, the transformed censoring time `untreatedTime ψ A c` of every
measurable treatment path `A` is at least `D*(ψ)`, and `D*(ψ)` is attained by the path that is
never treated or by the path that is always treated. -/
theorem recensoringTime_isLeast (ψ : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    IsLeast {x | ∃ A : Set ℝ, MeasurableSet A ∧ x = untreatedTime ψ A c}
      (recensoringTime ψ c) := by
  refine ⟨?_, ?_⟩
  · rcases min_cases c (Real.exp ψ * c) with ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨∅, MeasurableSet.empty, by rw [recensoringTime, h, untreatedTime_empty]⟩
    · exact ⟨univ, MeasurableSet.univ, by rw [recensoringTime, h, untreatedTime_univ]⟩
  · rintro x ⟨A, hA, rfl⟩
    rw [recensoringTime_eq_min_mul ψ hc]
    exact (untreatedTime_mem_Icc hA ψ hc).1

/-- The recensoring time is below the transformed censoring time of every measurable path. -/
theorem recensoringTime_le_untreatedTime {A : Set ℝ} (hA : MeasurableSet A) (ψ : ℝ) {c : ℝ}
    (hc : 0 ≤ c) : recensoringTime ψ c ≤ untreatedTime ψ A c :=
  (recensoringTime_isLeast ψ hc).2 ⟨A, hA, rfl⟩

theorem recensoringTime_nonneg (ψ : ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ recensoringTime ψ c :=
  le_min hc (mul_nonneg (Real.exp_pos ψ).le hc)

/-- Recensored follow-up never exceeds the administrative follow-up. -/
theorem recensoringTime_le_self (ψ c : ℝ) : recensoringTime ψ c ≤ c := min_le_left _ _

/-- For a beneficial or null effect (`ψ ≤ 0`), the recensoring time is `exp ψ c`. -/
theorem recensoringTime_of_nonpos {ψ : ℝ} (hψ : ψ ≤ 0) {c : ℝ} (hc : 0 ≤ c) :
    recensoringTime ψ c = Real.exp ψ * c :=
  min_eq_right (mul_le_of_le_one_left hc (Real.exp_le_one_iff.2 hψ))

/-- For a harmful or null effect (`ψ ≥ 0`), the recensoring time is the administrative
censoring time `c` itself, whatever the size of the effect. -/
theorem recensoringTime_of_nonneg {ψ : ℝ} (hψ : 0 ≤ ψ) {c : ℝ} (hc : 0 ≤ c) :
    recensoringTime ψ c = c :=
  min_eq_left (le_mul_of_one_le_left hc (Real.one_le_exp_iff.2 hψ))

/-- For a beneficial effect (`ψ < 0`) and positive follow-up, the recensoring time is strictly
earlier than the administrative censoring time. -/
theorem recensoringTime_lt_self {ψ : ℝ} (hψ : ψ < 0) {c : ℝ} (hc : 0 < c) :
    recensoringTime ψ c < c := by
  rw [recensoringTime_of_nonpos hψ.le hc.le]
  exact mul_lt_of_lt_one_left hc (by simpa using Real.exp_lt_exp.2 hψ)

/-- **The larger the benefit, the earlier the recensoring time** (TSD 16, Section 3.3.2; TSD 24,
Section 4.2.1.1). For `c ≥ 0`, `ψ ↦ D*(ψ)` is monotone; on the beneficial side `ψ ≤ 0` it is
`exp ψ c`, strictly increasing in `ψ` when `c > 0`, so a larger benefit (a more negative `ψ`)
gives a strictly earlier recensoring time. On the harmful side it is constant, equal to `c`. -/
theorem recensoringTime_monotone {c : ℝ} (hc : 0 ≤ c) :
    Monotone fun ψ ↦ recensoringTime ψ c := fun _ _ h ↦
  min_le_min le_rfl (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h) hc)

theorem recensoringTime_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun ψ ↦ recensoringTime ψ c) (Iic 0) := fun a ha b hb h ↦ by
  simp only [recensoringTime_of_nonpos ha hc.le, recensoringTime_of_nonpos hb hc.le]
  exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.2 h) hc

/-- For an always treated path and a beneficial or null effect, the transformed censoring time
already equals the recensoring time: recensoring changes nothing for such a patient. -/
theorem untreatedTime_univ_eq_recensoringTime {ψ : ℝ} (hψ : ψ ≤ 0) {c : ℝ} (hc : 0 ≤ c) :
    untreatedTime ψ univ c = recensoringTime ψ c := by
  rw [untreatedTime_univ, recensoringTime_of_nonpos hψ hc]

/-! ### Censored observations of one patient -/

/-- The observation `(min (u, d), 1{u ≤ d})` of a time `u` censored at `d`. -/
noncomputable def censorAt (u d : ℝ) : ℝ × Bool := (min u d, decide (u ≤ d))

/-- **The recensored observation computed from observed data** (TSD 16, Appendix A). The data of
a patient are the observed follow-up `x = min (T, C)`, the event indicator `δ = 1{T ≤ C}`, the
time `te` on the experimental treatment up to `x`, and the administrative censoring time `c`
(known for every patient, with or without an event). For a candidate `ψ`, the transformed
follow-up is `w = (x - te) + exp ψ te`; the recensored observation is `(min (w, D*), δ ∧ w ≤ D*)`.
The event indicator must keep `δ`: a censored patient can have `w = D*` exactly. -/
noncomputable def recensorData (ψ x : ℝ) (δ : Bool) (te c : ℝ) : ℝ × Bool :=
  (min ((x - te) + Real.exp ψ * te) (recensoringTime ψ c),
    δ && decide ((x - te) + Real.exp ψ * te ≤ recensoringTime ψ c))

/-- **The naive observation without recensoring**: the transformed follow-up with the original
event indicator, `((x - te) + exp ψ te, δ)`. -/
noncomputable def naiveData (ψ x : ℝ) (δ : Bool) (te : ℝ) : ℝ × Bool :=
  ((x - te) + Real.exp ψ * te, δ)

/-- **The recensored observation is the candidate untreated time censored at `D*`.** For a
measurable path `A`, an event time `t ≥ 0` and an administrative censoring time `c ≥ 0`, the
recensored observation computed from the observed data `(min (t, c), 1{t ≤ c}, timeOn A
(min (t, c)), c)` is `(min (U, D*), 1{U ≤ D*})` with `U = untreatedTime ψ A t` and
`D* = recensoringTime ψ c`. -/
theorem recensorData_eq {A : Set ℝ} (hA : MeasurableSet A) (ψ : ℝ) {t c : ℝ} (hc : 0 ≤ c) :
    recensorData ψ (min t c) (decide (t ≤ c)) (timeOn A (min t c)) c =
      censorAt (untreatedTime ψ A t) (recensoringTime ψ c) := by
  have hw : ∀ x, (x - timeOn A x) + Real.exp ψ * timeOn A x = untreatedTime ψ A x :=
    fun x ↦ (untreatedTime_eq hA ψ x).symm
  simp only [recensorData, hw, censorAt]
  rcases le_or_gt t c with htc | hct
  · simp [htc]
  · have hlt := untreatedTime_strictMono hA ψ hct
    have hle := recensoringTime_le_untreatedTime hA ψ hc
    simp only [min_eq_right hct.le, not_le.2 hct, decide_false, Bool.false_and]
    rw [min_eq_right hle, min_eq_right (hle.trans hlt.le)]
    simp [hle.trans_lt hlt]

/-- **The naive observation is the candidate untreated time censored at the transformed
censoring time** `untreatedTime ψ A c`, which depends on the treatment path. -/
theorem naiveData_eq {A : Set ℝ} (hA : MeasurableSet A) (ψ t c : ℝ) :
    naiveData ψ (min t c) (decide (t ≤ c)) (timeOn A (min t c)) =
      censorAt (untreatedTime ψ A t) (untreatedTime ψ A c) := by
  have hw : ∀ x, (x - timeOn A x) + Real.exp ψ * timeOn A x = untreatedTime ψ A x :=
    fun x ↦ (untreatedTime_eq hA ψ x).symm
  have hmono := untreatedTime_strictMono hA ψ
  simp only [naiveData, hw, censorAt]
  rcases le_or_gt t c with htc | hct
  · simp [htc, hmono.monotone htc]
  · simp [min_eq_right hct.le, not_le.2 hct, hmono hct, (hmono hct).le]

/-! ### What recensoring discards -/

/-- Censoring earlier shortens the observed time. -/
theorem censorAt_fst_mono (u : ℝ) {d d' : ℝ} (h : d ≤ d') : (censorAt u d).1 ≤ (censorAt u d').1 :=
  min_le_min le_rfl h

/-- Censoring earlier keeps only events that a later censoring time also keeps. -/
theorem censorAt_snd_mono (u : ℝ) {d d' : ℝ} (h : d ≤ d') (he : (censorAt u d).2 = true) :
    (censorAt u d').2 = true := by
  simp only [censorAt, decide_eq_true_eq] at he ⊢
  exact he.trans h

/-- **Recensoring loses follow-up and events, patient by patient** (TSD 16, Section 3.3.2). For
a measurable path, `t ≥ 0` and `c ≥ 0`: the recensored time is at most the naive transformed
follow-up, and a recensored event is an observed event (`t ≤ c`). -/
theorem recensored_le_naive {A : Set ℝ} (hA : MeasurableSet A) (ψ : ℝ) {t c : ℝ}
    (hc : 0 ≤ c) :
    (censorAt (untreatedTime ψ A t) (recensoringTime ψ c)).1 ≤
        (censorAt (untreatedTime ψ A t) (untreatedTime ψ A c)).1 ∧
      ((censorAt (untreatedTime ψ A t) (recensoringTime ψ c)).2 = true → t ≤ c) := by
  have hle := recensoringTime_le_untreatedTime hA ψ hc
  refine ⟨censorAt_fst_mono _ hle, fun he ↦ ?_⟩
  have := censorAt_snd_mono _ hle he
  simp only [censorAt, decide_eq_true_eq] at this
  exact (untreatedTime_strictMono hA ψ).le_iff_le.1 this

/-- For a beneficial or null effect (`ψ ≤ 0`), the recensored time is also at most the
observed follow-up `min (t, c)` on the original time scale. -/
theorem recensored_le_obs {A : Set ℝ} (hA : MeasurableSet A) {ψ : ℝ} (hψ : ψ ≤ 0) {t c : ℝ}
    (ht : 0 ≤ t) : (censorAt (untreatedTime ψ A t) (recensoringTime ψ c)).1 ≤ min t c :=
  min_le_min (untreatedTime_le_self hA hψ ht) (recensoringTime_le_self ψ c)

/-- **When an observed event is discarded.** For a patient with an observed event (`t ≤ c`), the
recensored observation loses the event exactly when the untreated time exceeds the recensoring
time. -/
theorem event_lost_iff {u d : ℝ} : (censorAt u d).2 = false ↔ d < u := by
  simp [censorAt]

/-- **A never treated patient loses an event between `exp ψ c` and `c`.** If `ψ < 0`, the
patient spent no time on the experimental treatment, and the event was observed at
`exp ψ c < t ≤ c`, recensoring turns the event into a censored observation at `exp ψ c < t`. -/
theorem event_lost_of_untreated {A : Set ℝ} (hA : MeasurableSet A) {ψ : ℝ} (hψ : ψ < 0)
    {t c : ℝ} (hc : 0 ≤ c) (hA0 : timeOn A t = 0) (hlt : Real.exp ψ * c < t) :
    censorAt (untreatedTime ψ A t) (recensoringTime ψ c) = (Real.exp ψ * c, false) := by
  have hU : untreatedTime ψ A t = t := by rw [untreatedTime_eq hA, hA0]; ring
  rw [hU, recensoringTime_of_nonpos hψ.le hc, censorAt, min_eq_right hlt.le]
  simp [hlt]

/-- **Recensored data carry no information beyond the recensoring time.** If `d ≤ τ`, two
untreated times `u` and `u'` that agree up to `τ` (equal when `u ≤ τ`, both beyond `τ`
otherwise) give the same observation censored at `d`. -/
theorem censorAt_eq_of_agree {u u' d τ : ℝ} (hd : d ≤ τ) (h1 : u ≤ τ → u' = u)
    (h2 : τ < u → τ < u') : censorAt u d = censorAt u' d := by
  rcases le_or_gt u τ with h | h
  · rw [h1 h]
  · have h' := h2 h
    simp [censorAt, min_eq_right (hd.trans h.le), min_eq_right (hd.trans h'.le),
      not_le.2 (hd.trans_lt h), not_le.2 (hd.trans_lt h')]

theorem measurable_censorAt : Measurable fun p : ℝ × ℝ ↦ censorAt p.1 p.2 := by
  refine (measurable_fst.min measurable_snd).prodMk (measurable_to_bool ?_)
  have : (fun p : ℝ × ℝ ↦ decide (p.1 ≤ p.2)) ⁻¹' {true} = {p | p.1 ≤ p.2} := by ext; simp
  rw [this]; exact measurableSet_le'

theorem measurable_recensoringTime (ψ : ℝ) : Measurable (recensoringTime ψ) :=
  measurable_id.min (measurable_id.const_mul _)

/-! ### A randomized trial with administrative censoring -/

/-- A two-arm randomized trial with switching and administrative censoring. `R ω = true` is the
experimental arm; `T` is the survival time (observed only up to `C`); `A ω ⊆ ℝ` the set of
times at which the patient is on the experimental treatment; `C` the administrative censoring
time (the time from entry to the data cut-off), known for every patient whether or not the
event occurs; `U` the latent untreated survival time. The observed data are the arm, the
follow-up `min (T, C)`, the event indicator `1{T ≤ C}`, the treatment path up to the follow-up
(through the time on treatment), and `C`. -/
structure CensoredTrial (Ω : Type*) where
  /-- The randomized arm: `true` for the experimental arm. -/
  R : Ω → Bool
  /-- The survival time. -/
  T : Ω → ℝ
  /-- The treatment path: the set of times on the experimental treatment. -/
  A : Ω → Set ℝ
  /-- The administrative censoring time. -/
  C : Ω → ℝ
  /-- The latent untreated survival time. -/
  U : Ω → ℝ

namespace CensoredTrial

variable {Ω : Type*} (M : CensoredTrial Ω)

/-- The uncensored switching trial of `CausalInference.StructuralNested.SwitchingTrial`, with
time on the experimental treatment `T^e = timeOn A T`. -/
noncomputable def toSwitchingTrial : SwitchingTrial Ω where
  R := M.R
  T := M.T
  Te ω := timeOn (M.A ω) (M.T ω)
  U := M.U

/-- Measurable treatment paths, nonnegative survival and censoring times. -/
structure WellFormed : Prop where
  measurableSet_path : ∀ ω, MeasurableSet (M.A ω)
  T_nonneg : ∀ ω, 0 ≤ M.T ω
  C_nonneg : ∀ ω, 0 ≤ M.C ω

/-- **The structural failure time model in path form with a common effect** (TSD 16,
Appendix A, Equation A2): `U = ∫_0^T exp (ψ A(s)) ds` for every patient. -/
def PathModel (ψ : ℝ) : Prop := ∀ ω, M.U ω = untreatedTime ψ (M.A ω) (M.T ω)

variable {M} in
/-- The path model is the common treatment effect of the step form (TSD 24, Equation (1)). -/
theorem pathModel_iff_commonEffect (hwf : M.WellFormed) (ψ : ℝ) :
    M.PathModel ψ ↔ M.toSwitchingTrial.CommonEffect ψ := by
  simp only [PathModel, SwitchingTrial.CommonEffect, SwitchingTrial.FollowsModel,
    SwitchingTrial.Tc, toSwitchingTrial, untreatedTime_eq (hwf.measurableSet_path _)]

/-- The observed follow-up `min (T, C)`. -/
def obsTime (ω : Ω) : ℝ := min (M.T ω) (M.C ω)

/-- The event indicator `1{T ≤ C}`. -/
noncomputable def event (ω : Ω) : Bool := decide (M.T ω ≤ M.C ω)

/-- The observed time on the experimental treatment, up to the observed follow-up. -/
noncomputable def obsTimeOn (ω : Ω) : ℝ := timeOn (M.A ω) (M.obsTime ω)

/-- The observed data of a patient: arm, follow-up, event indicator, time on the experimental
treatment during follow-up, administrative censoring time. -/
noncomputable def observed (ω : Ω) : Bool × ℝ × Bool × ℝ × ℝ :=
  (M.R ω, M.obsTime ω, M.event ω, M.obsTimeOn ω, M.C ω)

/-- The recensoring time `D*(ψ) = min (C, exp ψ C)` of each patient, in both arms. -/
noncomputable def recensTime (ψ : ℝ) (ω : Ω) : ℝ := recensoringTime ψ (M.C ω)

/-- The naive transformed censoring time `∫_0^C exp (ψ A(s)) ds`: it depends on the treatment
path. -/
noncomputable def naiveCensTime (ψ : ℝ) (ω : Ω) : ℝ := untreatedTime ψ (M.A ω) (M.C ω)

/-- The recensored observation of each patient for a candidate `ψ`, computed from the observed
data. -/
noncomputable def recensored (ψ : ℝ) (ω : Ω) : ℝ × Bool :=
  recensorData ψ (M.obsTime ω) (M.event ω) (M.obsTimeOn ω) (M.C ω)

/-- The naive observation of each patient for a candidate `ψ`: the transformed follow-up with
the original event indicator. -/
noncomputable def naive (ψ : ℝ) (ω : Ω) : ℝ × Bool :=
  naiveData ψ (M.obsTime ω) (M.event ω) (M.obsTimeOn ω)

/-- **The recensored observation is a function of the observed data.** -/
theorem recensored_eq_comp_observed (ψ : ℝ) :
    M.recensored ψ = (fun o ↦ recensorData ψ o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2) ∘ M.observed :=
  rfl

variable {M} in
/-- Two trials with the same observed data have the same recensored observations, whatever
their latent survival and untreated times. -/
theorem recensored_eq_of_observed_eq {M' : CensoredTrial Ω} (h : M.observed = M'.observed)
    (ψ : ℝ) : M.recensored ψ = M'.recensored ψ := by
  rw [recensored_eq_comp_observed, recensored_eq_comp_observed, h]

variable {M}

/-- **At the true parameter, the recensored observation is the untreated time censored at
`D*`:** `(min (U, D*), 1{U ≤ D*})`. -/
theorem recensored_eq (hwf : M.WellFormed) {ψ : ℝ} (h : M.PathModel ψ) (ω : Ω) :
    M.recensored ψ ω = censorAt (M.U ω) (M.recensTime ψ ω) := by
  rw [h ω]
  exact recensorData_eq (hwf.measurableSet_path ω) ψ (hwf.C_nonneg ω)

/-- At the true parameter, the naive observation is the untreated time censored at the
transformed censoring time, which depends on the treatment path. -/
theorem naive_eq (hwf : M.WellFormed) {ψ : ℝ} (h : M.PathModel ψ) (ω : Ω) :
    M.naive ψ ω = censorAt (M.U ω) (M.naiveCensTime ψ ω) := by
  rw [h ω]
  exact naiveData_eq (hwf.measurableSet_path ω) ψ _ _

/-- The recensoring time is at most the naive transformed censoring time. -/
theorem recensTime_le_naiveCensTime (hwf : M.WellFormed) (ψ : ℝ) (ω : Ω) :
    M.recensTime ψ ω ≤ M.naiveCensTime ψ ω :=
  recensoringTime_le_untreatedTime (hwf.measurableSet_path ω) ψ (hwf.C_nonneg ω)

variable [MeasurableSpace Ω] (μ : Measure Ω)

variable (M) in
/-- **Randomization with administrative censoring:** the arm is independent of the pair of the
untreated time and the administrative censoring time. -/
def RandomizedCensored : Prop := IndepFun M.R (fun ω ↦ (M.U ω, M.C ω)) μ

variable (M) in
/-- **Independent censoring:** the untreated time is independent of the administrative censoring
time. Not implied by `RandomizedCensored`. -/
def IndependentCensoring : Prop := IndepFun M.U M.C μ

variable {μ}

/-- The stronger randomization implies randomization of the uncensored model. -/
theorem RandomizedCensored.randomized (h : M.RandomizedCensored μ) :
    M.toSwitchingTrial.Randomized μ :=
  h.comp measurable_id measurable_fst

/-- **Laws within an arm.** If `Z` is independent of the arm `R` and the arm `R = r` has positive
probability, the law of `Z` given `R = r` is the law of `Z`. -/
theorem _root_.CausalInference.StructuralNested.map_cond_eq_map_of_indepFun
    {β : Type*} [MeasurableSpace β] [IsFiniteMeasure μ] {R : Ω → Bool} {Z : Ω → β}
    (hR : Measurable R) (hZ : Measurable Z) (h : IndepFun R Z μ) {r : Bool}
    (hpos : μ (R ⁻¹' {r}) ≠ 0) : (μ[|R ⁻¹' {r}]).map Z = μ.map Z := by
  ext B hB
  rw [Measure.map_apply hZ hB, Measure.map_apply hZ hB, cond_apply (hR (measurableSet_singleton r)),
    h.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton r) hB, ← mul_assoc,
    ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), one_mul]

/-- Any measurable function of `(U, C)` has the same law in each arm as in the trial. -/
theorem map_cond_arm_of_randomizedCensored [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hU : Measurable M.U) (hC : Measurable M.C) (hrand : M.RandomizedCensored μ)
    {β : Type*} [MeasurableSpace β] {g : ℝ × ℝ → β} (hg : Measurable g) {r : Bool}
    (hpos : μ (M.toSwitchingTrial.arm r) ≠ 0) :
    (μ[|M.toSwitchingTrial.arm r]).map (fun ω ↦ g (M.U ω, M.C ω)) =
      μ.map (fun ω ↦ g (M.U ω, M.C ω)) :=
  map_cond_eq_map_of_indepFun hR (hg.comp (hU.prodMk hC)) (hrand.comp measurable_id hg) hpos

/-- **The recensoring time has the same law in both arms** under randomization with
censoring: it is a function of `C` alone, not of the treatment history. -/
theorem map_cond_recensTime [IsFiniteMeasure μ] (hR : Measurable M.R) (hU : Measurable M.U)
    (hC : Measurable M.C) (hrand : M.RandomizedCensored μ) (ψ : ℝ) {r : Bool}
    (hpos : μ (M.toSwitchingTrial.arm r) ≠ 0) :
    (μ[|M.toSwitchingTrial.arm r]).map (M.recensTime ψ) = μ.map (M.recensTime ψ) :=
  map_cond_arm_of_randomizedCensored hR hU hC hrand
    ((measurable_recensoringTime ψ).comp measurable_snd) hpos

/-- **Recensoring restores randomization at the true parameter** (TSD 16, Appendix A; TSD 24,
Section 4.2.1.1). Under the path model with parameter `ψ₀`, randomization of the arm with respect
to `(U, C)`, measurable `R`, `U`, `C`, the law of the recensored observation
`(min (U(ψ₀), D*(ψ₀)), 1{U(ψ₀) ≤ D*(ψ₀)})` given `R = r` is its law in the whole trial, for each arm
of positive probability. -/
theorem map_cond_recensored [IsFiniteMeasure μ] (hwf : M.WellFormed) {ψ₀ : ℝ}
    (h : M.PathModel ψ₀) (hR : Measurable M.R) (hU : Measurable M.U) (hC : Measurable M.C)
    (hrand : M.RandomizedCensored μ) {r : Bool} (hpos : μ (M.toSwitchingTrial.arm r) ≠ 0) :
    (μ[|M.toSwitchingTrial.arm r]).map (M.recensored ψ₀) = μ.map (M.recensored ψ₀) := by
  have e : M.recensored ψ₀ = fun ω ↦
      (fun p : ℝ × ℝ ↦ censorAt p.1 (recensoringTime ψ₀ p.2)) (M.U ω, M.C ω) :=
    funext (recensored_eq hwf h)
  rw [e]
  exact map_cond_arm_of_randomizedCensored hR hU hC hrand
    (measurable_censorAt.comp (measurable_fst.prodMk
      ((measurable_recensoringTime ψ₀).comp measurable_snd))) hpos

/-- **The recensored observations have the same law in both arms at the true parameter.** So
every g-test that compares the recensored observations between arms (log-rank, Wilcoxon) has a
null population target at `ψ₀`. -/
theorem armLaw_recensored_eq [IsFiniteMeasure μ] (hwf : M.WellFormed) {ψ₀ : ℝ}
    (h : M.PathModel ψ₀) (hR : Measurable M.R) (hU : Measurable M.U) (hC : Measurable M.C)
    (hrand : M.RandomizedCensored μ) (h1 : μ (M.toSwitchingTrial.arm true) ≠ 0)
    (h0 : μ (M.toSwitchingTrial.arm false) ≠ 0) :
    (μ[|M.toSwitchingTrial.arm true]).map (M.recensored ψ₀) =
      (μ[|M.toSwitchingTrial.arm false]).map (M.recensored ψ₀) := by
  rw [map_cond_recensored hwf h hR hU hC hrand h1, map_cond_recensored hwf h hR hU hC hrand h0]

/-! ### Validity up to the recensoring time -/

/-- Independent censoring makes the untreated time independent of the recensoring time. -/
theorem IndependentCensoring.indepFun_recensTime (hind : M.IndependentCensoring μ) (ψ : ℝ) :
    IndepFun M.U (M.recensTime ψ) μ :=
  hind.comp measurable_id (measurable_recensoringTime ψ)

/-- **Survival of the recensored time.** Under independent censoring,
`P(min (U, D*) > t) = P(U > t) P(D* > t)` for every `t`. -/
theorem measureReal_recensored_gt (hind : M.IndependentCensoring μ) (ψ t : ℝ) :
    μ.real {ω | t < (censorAt (M.U ω) (M.recensTime ψ ω)).1} =
      μ.real {ω | t < M.U ω} * μ.real {ω | t < M.recensTime ψ ω} := by
  have hs : {ω | t < (censorAt (M.U ω) (M.recensTime ψ ω)).1} =
      M.U ⁻¹' Ioi t ∩ M.recensTime ψ ⁻¹' Ioi t := by
    ext ω; simp [censorAt, lt_min_iff]
  rw [hs, measureReal_def, (hind.indepFun_recensTime ψ).measure_inter_preimage_eq_mul _ _
    measurableSet_Ioi measurableSet_Ioi, ENNReal.toReal_mul]
  rfl

/-- Probabilities of events defined by `(U, C)` are the same in each arm as in the trial. -/
theorem measureReal_cond_arm [IsFiniteMeasure μ] (hR : Measurable M.R) (hU : Measurable M.U)
    (hC : Measurable M.C) (hrand : M.RandomizedCensored μ) {g : ℝ × ℝ → ℝ} (hg : Measurable g)
    {r : Bool} (hpos : μ (M.toSwitchingTrial.arm r) ≠ 0) (t : ℝ) :
    (μ[|M.toSwitchingTrial.arm r]).real {ω | t < g (M.U ω, M.C ω)} =
      μ.real {ω | t < g (M.U ω, M.C ω)} := by
  have hm : Measurable fun ω ↦ g (M.U ω, M.C ω) := hg.comp (hU.prodMk hC)
  have e := congrArg (fun ν : Measure ℝ ↦ ν.real (Ioi t))
    (map_cond_arm_of_randomizedCensored hR hU hC hrand hg hpos)
  simp only [measureReal_def, Measure.map_apply hm measurableSet_Ioi] at e
  exact e

/-- **Recensoring gives valid estimates up to the recensored follow-up** (TSD 24,
Section 4.2.1.1: "re-censoring results in valid estimates of treatment effects up to the maximum
recensored follow-up time"). Under the path model at `ψ₀`, randomization with censoring and
independent censoring, measurable `R`, `U`, `C`, for an arm of positive probability and a time
`t` at which the recensoring time exceeds `t` with positive probability in that arm, the
untreated survival in the arm is identified from the recensored data:
`P(U > t | R = r) = P(min (U, D*) > t | R = r) / P(D* > t | R = r)`.
Beyond the largest recensoring time the denominator vanishes: see
`CensoredTrial.recensored_eq_of_agree`. -/
theorem armSurvival_U_eq_div [IsFiniteMeasure μ] (hwf : M.WellFormed) {ψ₀ : ℝ}
    (h : M.PathModel ψ₀) (hR : Measurable M.R) (hU : Measurable M.U) (hC : Measurable M.C)
    (hrand : M.RandomizedCensored μ) (hind : M.IndependentCensoring μ) {r : Bool}
    (hpos : μ (M.toSwitchingTrial.arm r) ≠ 0) {t : ℝ}
    (hD : (μ[|M.toSwitchingTrial.arm r]).real {ω | t < M.recensTime ψ₀ ω} ≠ 0) :
    M.toSwitchingTrial.armSurvival μ M.U r t =
      (μ[|M.toSwitchingTrial.arm r]).real {ω | t < (M.recensored ψ₀ ω).1} /
        (μ[|M.toSwitchingTrial.arm r]).real {ω | t < M.recensTime ψ₀ ω} := by
  have hgD : Measurable fun p : ℝ × ℝ ↦ recensoringTime ψ₀ p.2 :=
    (measurable_recensoringTime ψ₀).comp measurable_snd
  have hgX : Measurable fun p : ℝ × ℝ ↦ (censorAt p.1 (recensoringTime ψ₀ p.2)).1 :=
    measurable_fst.comp (measurable_censorAt.comp (measurable_fst.prodMk hgD))
  have eU := measureReal_cond_arm hR hU hC hrand measurable_fst hpos t
  have eD := measureReal_cond_arm hR hU hC hrand hgD hpos t
  have eX := measureReal_cond_arm hR hU hC hrand hgX hpos t
  dsimp only at eU eD eX
  simp only [recensTime] at hD ⊢
  rw [eD] at hD
  simp only [recensored_eq hwf h, recensTime]
  rw [SwitchingTrial.armSurvival]
  rw [eU, eX, eD, eq_div_iff hD]
  exact (measureReal_recensored_gt hind ψ₀ t).symm

omit [MeasurableSpace Ω] in
/-- **Recensored data say nothing about the untreated survival beyond the recensoring time.**
Two trials with the same censoring times, both following the path model at `ψ`, whose untreated
times agree up to a bound `τ` of every recensoring time (equal where the first is at most `τ`,
both beyond `τ` otherwise), have the same recensored observations. Their untreated survival
beyond `τ` can differ (`RecensoringCounterexample.Constant.tail_not_identified`), so any
extrapolation of the recensored data beyond `τ` rests on assumptions that the recensored data
cannot check. -/
theorem recensored_eq_of_agree {M' : CensoredTrial Ω} (hwf : M.WellFormed)
    (hwf' : M'.WellFormed) {ψ τ : ℝ} (h : M.PathModel ψ) (h' : M'.PathModel ψ)
    (hC : M'.C = M.C) (hτ : ∀ ω, M.recensTime ψ ω ≤ τ) (h1 : ∀ ω, M.U ω ≤ τ → M'.U ω = M.U ω)
    (h2 : ∀ ω, τ < M.U ω → τ < M'.U ω) : M.recensored ψ = M'.recensored ψ := by
  funext ω
  rw [recensored_eq hwf h, recensored_eq hwf' h', recensTime, recensTime, hC]
  exact censorAt_eq_of_agree (hτ ω) (h1 ω) (h2 ω)

/-! ### The cost of recensoring -/

omit [MeasurableSpace Ω] in
/-- **Recensoring shortens follow-up and discards events** (TSD 16, Section 3.3.2). At the true
parameter, for every patient, the recensored time is at most the naive transformed follow-up,
and a recensored event is an observed event. -/
theorem recensored_le_naive (hwf : M.WellFormed) {ψ : ℝ} (h : M.PathModel ψ) (ω : Ω) :
    (M.recensored ψ ω).1 ≤ (M.naive ψ ω).1 ∧
      ((M.recensored ψ ω).2 = true → M.event ω = true) := by
  rw [recensored_eq hwf h, naive_eq hwf h, h ω]
  obtain ⟨h1, h2⟩ := StructuralNested.recensored_le_naive (hwf.measurableSet_path ω) ψ
    (t := M.T ω) (hwf.C_nonneg ω)
  exact ⟨h1, fun he ↦ by simpa [event] using h2 he⟩

omit [MeasurableSpace Ω] in
/-- For a beneficial or null effect, the recensored time is at most the observed follow-up
`min (T, C)`. -/
theorem recensored_le_obsTime (hwf : M.WellFormed) {ψ : ℝ} (h : M.PathModel ψ) (hψ : ψ ≤ 0)
    (ω : Ω) : (M.recensored ψ ω).1 ≤ M.obsTime ω := by
  rw [recensored_eq hwf h, h ω]
  exact StructuralNested.recensored_le_obs (hwf.measurableSet_path ω) hψ (hwf.T_nonneg ω)

/-- **Recensoring discards observed events with positive probability under a beneficial
effect** (TSD 16, Section 3.3.2: "some observed events will become censored if the recensoring
time is shorter than the counterfactual event time"). Under the path model at `ψ < 0`, if
patients who never receive the experimental treatment and have an observed event at a time `T`
with `exp ψ C < T ≤ C` have positive probability, then with positive probability an observed
event is censored by recensoring and the recensored time is strictly shorter than the observed
follow-up. -/
theorem measure_event_lost_ne_zero (hwf : M.WellFormed) {ψ : ℝ} (h : M.PathModel ψ)
    (hψ : ψ < 0)
    (hpos : μ {ω | timeOn (M.A ω) (M.T ω) = 0 ∧ Real.exp ψ * M.C ω < M.T ω ∧
      M.T ω ≤ M.C ω} ≠ 0) :
    μ {ω | M.event ω = true ∧ (M.recensored ψ ω).2 = false ∧
      (M.recensored ψ ω).1 < M.obsTime ω} ≠ 0 := by
  refine fun h0 ↦ hpos (measure_mono_null (fun ω hω ↦ ?_) h0)
  obtain ⟨hA0, hlt, hTC⟩ := hω
  have e : M.recensored ψ ω = (Real.exp ψ * M.C ω, false) := by
    rw [recensored_eq hwf h, h ω]
    exact event_lost_of_untreated (hwf.measurableSet_path ω) hψ (hwf.C_nonneg ω) hA0 hlt
  refine ⟨by simp [event, hTC], by rw [e], ?_⟩
  rw [e, obsTime, min_eq_left hTC]
  exact hlt

end CensoredTrial


end StructuralNested

end CausalInference
