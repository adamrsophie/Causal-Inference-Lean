/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Mediation.Identification
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Structural failure time models for treatment switching

The rank preserving structural failure time model (RPSFTM) of a randomized trial in which
patients may switch from the control to the experimental treatment. Every patient has a
counterfactual untreated survival time `U`, the time the patient would have survived without
the experimental treatment. The model links it to the observed survival time `T` and the
observed treatment path through one parameter `ψ`: time spent on the experimental treatment is
multiplied by `exp ψ`.

## Main definitions

Deterministic layer (one patient, real time):

* `StructuralNested.timeOn A t`: the time on treatment up to `t` for a treatment path given as
  the set `A ⊆ ℝ` of times on treatment, `∫_0^t 1_A`.
* `StructuralNested.untreatedTime ψ A t = ∫_0^t exp (ψ 1_A(s)) ds`: the counterfactual untreated
  time of a patient observed to survive to `t` along the path `A` (TSD 16, Appendix A,
  Equation A2).
* `StructuralNested.onTreatmentPath`, `treatmentGroupPath`, `laggedPath`: the "on treatment",
  "treatment group" and lagged choices of the path made from the same data (TSD 16,
  Section 3.3.1; TSD 24, Section 4.2.1).

Probability layer (a trial on a probability space):

* `StructuralNested.SwitchingTrial`: randomized arm `R`, observed survival time `T`, observed
  time on the experimental treatment `Te`, and the latent untreated survival time `U`.
* `SwitchingTrial.counterfactual ψ = T - Te + exp ψ * Te`: the untreated time computed from
  the data for a candidate value `ψ` (TSD 24, Section 4.2.1, Equation (1)).
* Assumptions, each a separate `Prop`: `SwitchingTrial.WellFormed` (`0 ≤ Te ≤ T`),
  `SwitchingTrial.FollowsModel` (a structural failure time model with unit specific parameters),
  `SwitchingTrial.CommonEffect` (one parameter for every patient), `SwitchingTrial.Randomized`
  (the arm is independent of the untreated time).
* Estimands: `SwitchingTrial.ittEffect` (treatment policy, the comparison as randomized),
  `SwitchingTrial.hypotheticalEffect` (experimental arm as delivered against the control arm had
  no switch occurred), `SwitchingTrial.bias`, and the corresponding arm laws
  `SwitchingTrial.armLaw` and survival functions `SwitchingTrial.armSurvival`.

## Main results

* `untreatedTime_eq`: Equation A2 equals Equation (1): `U = (t - timeOn A t) + exp ψ timeOn A t`
  for every measurable path, so the general integral model is the step form with
  `T^e = timeOn A t`.
* `untreatedTime_strictMono`: rank preservation along a fixed path; `t` is recovered from `U`
  (`untreatedTime_injective`).
* `untreatedTime_mem_Icc`: `min 1 (exp ψ) t ≤ U ≤ max 1 (exp ψ) t` for `t ≥ 0`.
* `timeOn_onTreatmentPath`, `timeOn_treatmentGroupPath`, `timeOn_laggedPath`: the time on
  treatment of the three path choices, and their order (`timeOn_onTreatment_le_lagged`,
  `timeOn_lagged_le_treatmentGroup`).
* `SwitchingTrial.T_eq_of_commonEffect`: `T = U + (1 - exp ψ) Te`, the linear structural
  equation used for identification in `CausalInference.StructuralNested.RPSFTM`.
* `SwitchingTrial.armMean_U_of_randomized`, `SwitchingTrial.armLaw_U_of_randomized`: under
  randomization the untreated time has the same mean and the same law in each arm as in the
  whole population; so the control arm untreated law in the hypothetical estimand is the
  population law of survival without the experimental treatment (TSD 16, Section 6, discussion
  of Step (3) of Figure 2). `SwitchingTrial.hypotheticalEffect_eq_of_randomized`: the same
  contrast computed within the experimental arm.
* `SwitchingTrial.ittEffect_le_hypotheticalEffect`,
  `SwitchingTrial.ittEffect_lt_hypotheticalEffect`,
  `SwitchingTrial.armSurvival_U_le_armSurvival_T`: intention-to-treat attenuation. If the
  treatment does not shorten survival (`ψ ≤ 0`), the ITT mean difference is at most the
  hypothetical one, strictly if `ψ < 0` and control patients with positive time on the
  experimental treatment have positive probability; the control arm survival curve under
  switching lies above the untreated one (TSD 16, Section 2 and Figure 1).

## Setting

Counterfactual variables live on a general probability space (Mathlib `MeasureTheory`,
independence `ProbabilityTheory.IndepFun`). Times are real. The probability layer uses the step
form of the model: the observed data of a patient are summarized by `T` and `Te`, which for a
general path is `timeOn A T` (`untreatedTime_eq`). Only switches from control to the
experimental treatment are modeled; the experimental arm is taken as delivered. Censoring is not
modeled here (see the recensoring work for administrative censoring).

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014): Section 2 (bias, Figure 1),
  Section 3.2.2 (RPSFTM, common treatment effect, randomization), Section 3.3.1 (on treatment,
  treatment group and lagged analyses), Section 6, Appendix A (Equation A2).
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to TSD 16*
  (2024): Section 3.2 (treatment policy and hypothetical strategies), Section 4.2.1
  (Equation (1)). That section calls `ψ` the time ratio; in Equation (1) the time ratio is
  `exp ψ` and `ψ` is its logarithm, which is the convention used here.
* J. M. Robins, A. A. Tsiatis, *Correcting for non-compliance in randomized trials using rank
  preserving structural failure time models*, Communications in Statistics: Theory and Methods
  (1991), the original model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace StructuralNested

/-! ### The deterministic model of one patient -/

/-- The time spent on treatment up to time `t`, for a treatment path given by the set `A ⊆ ℝ`
of times at which the patient is on treatment: `∫_0^t 1_A(s) ds`. -/
noncomputable def timeOn (A : Set ℝ) (t : ℝ) : ℝ := ∫ s in (0)..t, A.indicator 1 s

/-- **The structural failure time model, TSD 16 Equation A2.** The counterfactual untreated
survival time of a patient observed to survive to `t` with treatment indicator `A(s) = 1_A(s)`:
`U = ∫_0^t exp (ψ A(s)) ds`. Time off treatment counts once, time on treatment counts
`exp ψ` times. -/
noncomputable def untreatedTime (ψ : ℝ) (A : Set ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0)..t, Real.exp (ψ * A.indicator 1 s)

/-- For a `0`/`1` indicator, `exp (ψ a) = 1 + (exp ψ - 1) a`. -/
theorem exp_mul_indicator (ψ : ℝ) (A : Set ℝ) (s : ℝ) :
    Real.exp (ψ * A.indicator 1 s) = 1 + (Real.exp ψ - 1) * A.indicator 1 s := by
  by_cases h : s ∈ A <;> simp [h]

/-- The indicator of a measurable path is integrable on every interval. -/
theorem intervalIntegrable_indicator {A : Set ℝ} (hA : MeasurableSet A) (a b : ℝ) :
    IntervalIntegrable (A.indicator (1 : ℝ → ℝ)) volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    ((measurable_const.indicator hA).aestronglyMeasurable)
    (ae_of_all _ fun s ↦ by by_cases h : s ∈ A <;> simp [h])

/-- **Equation A2 is Equation (1).** For a measurable path, the untreated time is the time off
treatment plus `exp ψ` times the time on treatment:
`untreatedTime ψ A t = (t - timeOn A t) + exp ψ * timeOn A t` (TSD 24, Section 4.2.1,
Equation (1), with `T^c = t - timeOn A t` and `T^e = timeOn A t`). -/
theorem untreatedTime_eq {A : Set ℝ} (hA : MeasurableSet A) (ψ t : ℝ) :
    untreatedTime ψ A t = (t - timeOn A t) + Real.exp ψ * timeOn A t := by
  simp only [untreatedTime, exp_mul_indicator]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegrable_indicator hA 0 t).const_mul _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, timeOn]
  simp; ring

/-- At `ψ = 0` the untreated time is the observed time. -/
theorem untreatedTime_zero (A : Set ℝ) (t : ℝ) : untreatedTime 0 A t = t := by
  simp [untreatedTime]

/-- The time on treatment is nonnegative. -/
theorem timeOn_nonneg (A : Set ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ timeOn A t :=
  intervalIntegral.integral_nonneg ht fun s _ ↦ by by_cases h : s ∈ A <;> simp [h]

/-- The time on treatment is at most the elapsed time. -/
theorem timeOn_le {A : Set ℝ} (hA : MeasurableSet A) {t : ℝ} (ht : 0 ≤ t) :
    timeOn A t ≤ t := by
  have := intervalIntegral.integral_mono_on ht (intervalIntegrable_indicator hA 0 t)
    (intervalIntegrable_const (c := (1 : ℝ))) fun s _ ↦ by by_cases h : s ∈ A <;> simp [h]
  simpa [timeOn] using this

/-- The time on treatment is monotone in the path: a larger set of treated times gives at least
as much time on treatment. -/
theorem timeOn_mono_set {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) {t : ℝ} (ht : 0 ≤ t) : timeOn A t ≤ timeOn B t :=
  intervalIntegral.integral_mono_on ht (intervalIntegrable_indicator hA 0 t)
    (intervalIntegrable_indicator hB 0 t) fun s _ ↦
      indicator_le_indicator_of_subset hAB (fun _ ↦ zero_le_one) s

/-- **Rank preservation along a path.** For a fixed measurable treatment path and a fixed `ψ`,
the untreated time is strictly increasing in the observed time. -/
theorem untreatedTime_strictMono {A : Set ℝ} (hA : MeasurableSet A) (ψ : ℝ) :
    StrictMono (untreatedTime ψ A) := by
  intro a b hab
  have hi : ∀ c d : ℝ,
      IntervalIntegrable (fun s ↦ Real.exp (ψ * A.indicator 1 s)) volume c d := fun c d ↦ by
    simp only [exp_mul_indicator]
    exact intervalIntegrable_const.add ((intervalIntegrable_indicator hA c d).const_mul _)
  have h := intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (hi a b)
    (fun x _ ↦ Real.exp_pos _) hab
  simp only [untreatedTime]
  linarith

/-- The observed time is recovered from the untreated time, the path and `ψ`: two observed times
with the same untreated time along the same path are equal. -/
theorem untreatedTime_injective {A : Set ℝ} (hA : MeasurableSet A) (ψ : ℝ) :
    Function.Injective (untreatedTime ψ A) :=
  (untreatedTime_strictMono hA ψ).injective

/-- **Rank preservation between patients.** Two patients with the same treatment path have
observed times in the same order as their untreated times. -/
theorem untreatedTime_lt_iff {A : Set ℝ} (hA : MeasurableSet A) (ψ : ℝ) {t t' : ℝ} :
    untreatedTime ψ A t < untreatedTime ψ A t' ↔ t < t' :=
  (untreatedTime_strictMono hA ψ).lt_iff_lt

/-- **Bounds on the untreated time.** For `t ≥ 0` and any measurable path,
`min 1 (exp ψ) t ≤ untreatedTime ψ A t ≤ max 1 (exp ψ) t`. -/
theorem untreatedTime_mem_Icc {A : Set ℝ} (hA : MeasurableSet A) (ψ : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    untreatedTime ψ A t ∈ Icc (min 1 (Real.exp ψ) * t) (max 1 (Real.exp ψ) * t) := by
  rw [untreatedTime_eq hA]
  have h0 := timeOn_nonneg A ht
  have h1 := timeOn_le hA ht
  have hm1 := min_le_left 1 (Real.exp ψ)
  have hm2 := min_le_right 1 (Real.exp ψ)
  have hM1 := le_max_left 1 (Real.exp ψ)
  have hM2 := le_max_right 1 (Real.exp ψ)
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hm1 (sub_nonneg.2 h1),
    mul_le_mul_of_nonneg_left hm2 h0, mul_le_mul_of_nonneg_left hM1 (sub_nonneg.2 h1),
    mul_le_mul_of_nonneg_left hM2 h0]

/-- If the treatment does not shorten survival (`ψ ≤ 0`), the untreated time is at most the
observed time. -/
theorem untreatedTime_le_self {A : Set ℝ} (hA : MeasurableSet A) {ψ : ℝ} (hψ : ψ ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : untreatedTime ψ A t ≤ t := by
  rw [untreatedTime_eq hA]
  have := Real.exp_le_one_iff.2 hψ
  nlinarith [timeOn_nonneg A ht]

/-- If the treatment prolongs survival (`ψ < 0`) and the patient spent positive time on it, the
untreated time is strictly smaller than the observed time. -/
theorem untreatedTime_lt_self {A : Set ℝ} (hA : MeasurableSet A) {ψ : ℝ} (hψ : ψ < 0)
    {t : ℝ} (hpos : 0 < timeOn A t) : untreatedTime ψ A t < t := by
  rw [untreatedTime_eq hA]
  have : Real.exp ψ < 1 := by simpa using Real.exp_lt_exp.2 hψ
  nlinarith

/-! ### Choices of the treatment path -/

/-- **"On treatment" path** (TSD 16, Section 3.3.1): the patient is on treatment from the start
`a` to the discontinuation `b`, the half-open interval `(a, b]`; the effect stops at
discontinuation. -/
def onTreatmentPath (a b : ℝ) : Set ℝ := Ioc a b

/-- **"Treatment group" path** (TSD 16, Section 3.3.1; "ever treated" in TSD 24,
Section 4.2.1): the patient counts as on treatment at every time after the start `a`, whatever
discontinuation occurs. -/
def treatmentGroupPath (a : ℝ) : Set ℝ := Ioi a

/-- **Lagged path** (TSD 16, Section 3.3.1): the effect persists for a lag `ℓ` after
discontinuation at `b`. -/
def laggedPath (a b ℓ : ℝ) : Set ℝ := Ioc a (b + ℓ)

/-- Time on the treatment group path started at `a ≥ 0`, up to `t ≥ 0`: `t - min a t`. -/
theorem timeOn_treatmentGroupPath {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    timeOn (treatmentGroupPath a) t = t - min a t := by
  have hm0 : 0 ≤ min a t := le_min ha ht
  have hmt : min a t ≤ t := min_le_right a t
  have hi := intervalIntegrable_indicator (measurableSet_Ioi (a := a))
  rw [treatmentGroupPath, timeOn, ← intervalIntegral.integral_add_adjacent_intervals
    (hi 0 (min a t)) (hi (min a t) t), intervalIntegral.integral_of_le hm0,
    intervalIntegral.integral_of_le hmt]
  have h1 : ∫ x in Ioc 0 (min a t), (Ioi a).indicator (1 : ℝ → ℝ) x =
      ∫ x in Ioc 0 (min a t), 0 :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by
      have : ¬ a < x := not_lt.2 (hx.2.trans (min_le_left a t))
      simp [this]
  have h2 : ∫ x in Ioc (min a t) t, (Ioi a).indicator (1 : ℝ → ℝ) x =
      ∫ x in Ioc (min a t) t, 1 :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by
      have : a < x := by
        rcases min_cases a t with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h] at hx; exact hx.1
        · rw [h] at hx; exact absurd hx.2 (not_le.2 hx.1)
      simp [this]
  rw [h1, h2]
  simp [hmt]

/-- Time on the on-treatment path `(a, b]` with `0 ≤ a ≤ b`, up to `t ≥ 0`:
`min b t - min a t`. -/
theorem timeOn_onTreatmentPath {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) :
    timeOn (onTreatmentPath a b) t = min b t - min a t := by
  have hind : (onTreatmentPath a b).indicator (1 : ℝ → ℝ) =
      fun s ↦ (Ioi a).indicator 1 s - (Ioi b).indicator 1 s := by
    funext s
    by_cases h2 : b < s
    · have h1 : a < s := hab.trans_lt h2
      simp [onTreatmentPath, h1, h2, Set.indicator]
    · by_cases h1 : a < s <;> simp [onTreatmentPath, h1, h2, Set.indicator]
  have e := intervalIntegral.integral_sub
    (intervalIntegrable_indicator (measurableSet_Ioi (a := a)) 0 t)
    (intervalIntegrable_indicator (measurableSet_Ioi (a := b)) 0 t)
  rw [timeOn, hind, e]
  have ea := timeOn_treatmentGroupPath ha ht
  have eb := timeOn_treatmentGroupPath (ha.trans hab) ht
  simp only [timeOn, treatmentGroupPath] at ea eb
  rw [ea, eb]; ring

/-- Time on the lagged path `(a, b + ℓ]` with `0 ≤ a ≤ b` and lag `ℓ ≥ 0`, up to `t ≥ 0`:
`min (b + ℓ) t - min a t`. -/
theorem timeOn_laggedPath {a b ℓ t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hℓ : 0 ≤ ℓ)
    (ht : 0 ≤ t) : timeOn (laggedPath a b ℓ) t = min (b + ℓ) t - min a t :=
  timeOn_onTreatmentPath ha (by linarith) ht

/-- The on-treatment path gives at most the time on treatment of the lagged path. -/
theorem timeOn_onTreatment_le_lagged {a b ℓ t : ℝ} (hℓ : 0 ≤ ℓ) (ht : 0 ≤ t) :
    timeOn (onTreatmentPath a b) t ≤ timeOn (laggedPath a b ℓ) t :=
  timeOn_mono_set measurableSet_Ioc measurableSet_Ioc
    (Ioc_subset_Ioc_right (by linarith)) ht

/-- The lagged path gives at most the time on treatment of the treatment group path. -/
theorem timeOn_lagged_le_treatmentGroup {a b ℓ t : ℝ} (ht : 0 ≤ t) :
    timeOn (laggedPath a b ℓ) t ≤ timeOn (treatmentGroupPath a) t :=
  timeOn_mono_set measurableSet_Ioc measurableSet_Ioi Ioc_subset_Ioi_self ht

/-! ### A randomized trial with switching -/

/-- A two-arm randomized trial in which control patients may switch to the experimental
treatment. `R ω = true` is the experimental arm. `T` is the observed survival time, `Te` the
observed time spent on the experimental treatment (zero for control patients who never switch;
`timeOn A T` for a general path `A`, see `untreatedTime_eq`), and `U` the latent untreated
survival time: the time the patient would have survived without the experimental treatment.
Only `R`, `T` and `Te` are observed. Censoring is not modeled. -/
structure SwitchingTrial (Ω : Type*) where
  /-- The randomized arm: `true` for the experimental arm, `false` for control. -/
  R : Ω → Bool
  /-- The observed survival time. -/
  T : Ω → ℝ
  /-- The observed time on the experimental treatment. -/
  Te : Ω → ℝ
  /-- The latent counterfactual untreated survival time. -/
  U : Ω → ℝ

namespace SwitchingTrial

variable {Ω : Type*} (M : SwitchingTrial Ω)

/-- The observed time off the experimental treatment, `T^c = T - T^e`. -/
def Tc (ω : Ω) : ℝ := M.T ω - M.Te ω

/-- **The candidate untreated time, TSD 24 Equation (1).** For a candidate parameter `ψ`, the
untreated time computed from the observed data: `U(ψ) = T^c + exp ψ T^e`. It is a function of
`(T, Te)` and `ψ` only. -/
noncomputable def counterfactual (ψ : ℝ) (ω : Ω) : ℝ := M.Tc ω + Real.exp ψ * M.Te ω

/-- At `ψ = 0` the candidate untreated time is the observed time. -/
theorem counterfactual_zero : M.counterfactual 0 = M.T := by
  funext ω; simp [counterfactual, Tc]

/-- Observed times are consistent: `0 ≤ T^e ≤ T`. -/
structure WellFormed : Prop where
  te_nonneg : ∀ ω, 0 ≤ M.Te ω
  te_le : ∀ ω, M.Te ω ≤ M.T ω

/-- **A structural failure time model with unit specific effects.** Each patient `ω` has a
parameter `ψi ω`, and `U = T^c + exp (ψi ω) T^e`. Effects that differ between switchers and
patients randomized to the experimental arm are of this form. -/
def FollowsModel (ψi : Ω → ℝ) : Prop := ∀ ω, M.U ω = M.Tc ω + Real.exp (ψi ω) * M.Te ω

/-- **Common treatment effect** (TSD 16, Section 3.2.2): one parameter `ψ` for all patients,
whenever the treatment is received; equivalently `U = U(ψ)` for every patient. -/
def CommonEffect (ψ : ℝ) : Prop := M.FollowsModel fun _ ↦ ψ

theorem commonEffect_iff (ψ : ℝ) : M.CommonEffect ψ ↔ M.U = M.counterfactual ψ := by
  simp only [CommonEffect, FollowsModel, funext_iff, counterfactual]

/-- Under a common effect, observed time is the untreated time plus the gain from treatment:
`T = U + (1 - exp ψ) T^e`. With `Y = T`, `D = T^e` and slope `1 - exp ψ` this is the linear
structural equation of an instrumental variable model with instrument `R`. -/
theorem T_eq_of_commonEffect {ψ : ℝ} (h : M.CommonEffect ψ) (ω : Ω) :
    M.T ω = M.U ω + (1 - Real.exp ψ) * M.Te ω := by
  rw [h ω, Tc]; ring

/-- Under a common effect `ψ ≤ 0` and `T^e ≥ 0`, the untreated time is at most the observed
time. -/
theorem U_le_T {M : SwitchingTrial Ω} {ψ : ℝ} (h : M.CommonEffect ψ) (hψ : ψ ≤ 0)
    (hte : ∀ ω, 0 ≤ M.Te ω) (ω : Ω) :
    M.U ω ≤ M.T ω := by
  rw [M.T_eq_of_commonEffect h ω]
  have := Real.exp_le_one_iff.2 hψ
  nlinarith [hte ω]

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- **Randomization** (TSD 16, Section 3.2.2, the exclusion restriction of instrumental
variable methods): the untreated survival time is independent of the randomized arm. -/
def Randomized : Prop := IndepFun M.R M.U μ

/-- The event that a patient was randomized to arm `r`. -/
def arm (r : Bool) : Set Ω := M.R ⁻¹' {r}

/-- The mean of `X` in arm `r`, `E[X | R = r]`. -/
noncomputable def armMean (X : Ω → ℝ) (r : Bool) : ℝ := ∫ ω, X ω ∂μ[|M.arm r]

/-- The law of `X` in arm `r`, the image of `P( · | R = r)` under `X`. -/
noncomputable def armLaw (X : Ω → ℝ) (r : Bool) : Measure ℝ := (μ[|M.arm r]).map X

/-- The survival function of `X` in arm `r`: `P(X > t | R = r)`. -/
noncomputable def armSurvival (X : Ω → ℝ) (r : Bool) (t : ℝ) : ℝ :=
  (μ[|M.arm r]).real {ω | t < X ω}

/-- The difference of arm means `E[X | R = true] - E[X | R = false]`. -/
noncomputable def meanContrast (X : Ω → ℝ) : ℝ := M.armMean μ X true - M.armMean μ X false

/-- **Treatment policy estimand** (TSD 24, Section 3.2; the intention-to-treat comparison of
TSD 16, Section 3.1.1), in mean form: `E[T | R = true] - E[T | R = false]`. -/
noncomputable def ittEffect : ℝ := M.meanContrast μ M.T

/-- **Hypothetical estimand** (TSD 24, Section 3.2), in mean form: the experimental arm as
delivered against the control arm had no switch to the experimental treatment occurred,
`E[T | R = true] - E[U | R = false]`. -/
noncomputable def hypotheticalEffect : ℝ := M.armMean μ M.T true - M.armMean μ M.U false

/-- **Bias** (TSD 16, Section 2): the difference between an estimated effect `θ` and the effect
that would have been observed in the absence of switching. -/
noncomputable def bias (θ : ℝ) : ℝ := θ - M.hypotheticalEffect μ

variable {M μ}

theorem measurableSet_arm (hR : Measurable M.R) (r : Bool) : MeasurableSet (M.arm r) :=
  hR (measurableSet_singleton r)

/-- With measurable `T` and `T^e`, every candidate untreated time is measurable. -/
theorem measurable_counterfactual (hT : Measurable M.T) (hTe : Measurable M.Te) (ψ : ℝ) :
    Measurable (M.counterfactual ψ) :=
  (hT.sub hTe).add (hTe.const_mul _)

/-- With integrable `T` and `T^e`, every candidate untreated time is integrable. -/
theorem integrable_counterfactual (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (ψ : ℝ) :
    Integrable (M.counterfactual ψ) μ :=
  (hT.sub hTe).add (hTe.const_mul _)

/-- Under a common effect, integrable `T` and `T^e` make the untreated time integrable. -/
theorem integrable_U_of_commonEffect {ψ : ℝ} (h : M.CommonEffect ψ) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) : Integrable M.U μ := by
  rw [(M.commonEffect_iff ψ).1 h]; exact integrable_counterfactual hT hTe ψ

/-- **Arm means of the candidate untreated time.** With integrable `T` and `T^e` and an arm of
positive probability, `E[U(ψ) | R = r] = (E[T | R = r] - E[T^e | R = r]) + exp ψ E[T^e | R = r]`.
-/
theorem armMean_counterfactual (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) {r : Bool}
    (hpos : μ (M.arm r) ≠ 0) (ψ : ℝ) :
    M.armMean μ (M.counterfactual ψ) r =
      (M.armMean μ M.T r - M.armMean μ M.Te r) + Real.exp ψ * M.armMean μ M.Te r := by
  have hT' := Mediation.integrable_cond_of_integrable hT hpos
  have hTe' := Mediation.integrable_cond_of_integrable hTe hpos
  simp only [armMean, counterfactual, Tc]
  calc ∫ ω, M.T ω - M.Te ω + Real.exp ψ * M.Te ω ∂μ[|M.arm r]
      = ∫ ω, (M.T ω - M.Te ω) ∂μ[|M.arm r] + ∫ ω, Real.exp ψ * M.Te ω ∂μ[|M.arm r] :=
        integral_add (hT'.sub hTe') (hTe'.const_mul _)
    _ = _ := by rw [integral_sub hT' hTe', integral_const_mul]

/-- The bias of the ITT analysis is `E[U | R = false] - E[T | R = false]`: the switchers' gain
in the control arm, with a minus sign. -/
theorem bias_ittEffect :
    M.bias μ (M.ittEffect μ) = M.armMean μ M.U false - M.armMean μ M.T false := by
  simp only [bias, ittEffect, meanContrast, hypotheticalEffect]; ring

/-- **The untreated mean is the same in both arms under randomization.** If `U` is integrable,
independent of `R`, and arm `r` has positive probability, then `E[U | R = r] = E[U]`. -/
theorem armMean_U_of_randomized [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hrand : M.Randomized μ) (hU : Integrable M.U μ) {r : Bool} (hpos : μ (M.arm r) ≠ 0) :
    M.armMean μ M.U r = ∫ ω, M.U ω ∂μ :=
  Mediation.condMean_preimage_singleton_of_indepFun hrand.symm hR hU hpos

/-- **The untreated law is the same in both arms under randomization** (TSD 16, Section 6,
discussion of Step (3) of Figure 2): if `U` is independent of `R` and arm `r` has positive
probability, the law of `U` in arm `r` is the law of `U` in the whole trial population. So
comparing observed experimental times with the control arm's untreated times compares the
experimental arm as delivered with survival without the experimental treatment. -/
theorem armLaw_U_of_randomized [IsFiniteMeasure μ] (hR : Measurable M.R) (hUm : Measurable M.U)
    (hrand : M.Randomized μ) {r : Bool} (hpos : μ (M.arm r) ≠ 0) :
    M.armLaw μ M.U r = μ.map M.U := by
  ext B hB
  rw [armLaw, Measure.map_apply hUm hB, Measure.map_apply hUm hB,
    cond_apply (M.measurableSet_arm hR r), arm,
    hrand.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton r) hB, ← mul_assoc,
    ← arm, ENNReal.inv_mul_cancel hpos (measure_ne_top _ _), one_mul]

/-- **The hypothetical estimand under randomization.** If `U` is integrable and independent of
`R`, and both arms have positive probability, the hypothetical mean contrast is also
`E[T | R = true] - E[U | R = true]`: observed against untreated times within the experimental
arm as delivered (TSD 16, Section 6, discussion of Step (3) of Figure 2: untreated control times
are to be compared with the observed experimental times). -/
theorem hypotheticalEffect_eq_of_randomized [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hrand : M.Randomized μ) (hU : Integrable M.U μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) :
    M.hypotheticalEffect μ = M.armMean μ M.T true - M.armMean μ M.U true := by
  rw [hypotheticalEffect, armMean_U_of_randomized hR hrand hU h0,
    armMean_U_of_randomized hR hrand hU h1]

/-- **ITT attenuation of the survival curve** (TSD 16, Section 2 and Figure 1). If the
treatment does not shorten survival (common effect `ψ ≤ 0`) and `T^e ≥ 0`, then at every time
the control arm survival under switching is at least the control arm survival without
switching: `P(U > t | R = false) ≤ P(T > t | R = false)`. -/
theorem armSurvival_U_le_armSurvival_T [IsFiniteMeasure μ] {ψ : ℝ} (h : M.CommonEffect ψ)
    (hψ : ψ ≤ 0) (hte : ∀ ω, 0 ≤ M.Te ω) (r : Bool) (t : ℝ) :
    M.armSurvival μ M.U r t ≤ M.armSurvival μ M.T r t :=
  measureReal_mono fun ω (hω : t < M.U ω) ↦ hω.trans_le (U_le_T h hψ hte ω)

/-- **ITT attenuation in mean** (TSD 16, Section 2). Under a common effect `ψ ≤ 0`, `T^e ≥ 0`,
integrable `T` and `T^e`, and a control arm of positive probability, the ITT mean difference is
at most the hypothetical one: `E[T | R = true] - E[T | R = false] ≤
E[T | R = true] - E[U | R = false]`. -/
theorem ittEffect_le_hypotheticalEffect [IsFiniteMeasure μ] {ψ : ℝ} (h : M.CommonEffect ψ)
    (hψ : ψ ≤ 0) (hte : ∀ ω, 0 ≤ M.Te ω) (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) : M.ittEffect μ ≤ M.hypotheticalEffect μ := by
  have hU := integrable_U_of_commonEffect h hT hTe
  have hmono : M.armMean μ M.U false ≤ M.armMean μ M.T false :=
    integral_mono (Mediation.integrable_cond_of_integrable hU h0)
      (Mediation.integrable_cond_of_integrable hT h0) (U_le_T h hψ hte)
  simp only [ittEffect, meanContrast, hypotheticalEffect]
  linarith

/-- **Strict ITT attenuation** (TSD 16, Section 2: "provided switching patients benefit to any
extent from the new intervention, some bias will exist"). Under a common effect `ψ < 0`,
`T^e ≥ 0`, integrable `T` and `T^e`, if control patients with positive time on the experimental
treatment have positive probability, the ITT mean difference is strictly smaller than the
hypothetical one. -/
theorem ittEffect_lt_hypotheticalEffect [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ : ℝ}
    (h : M.CommonEffect ψ) (hψ : ψ < 0) (hte : ∀ ω, 0 ≤ M.Te ω) (hT : Integrable M.T μ)
    (hTe : Integrable M.Te μ) (hsw : μ (M.arm false ∩ {ω | 0 < M.Te ω}) ≠ 0) :
    M.ittEffect μ < M.hypotheticalEffect μ := by
  have h0 : μ (M.arm false) ≠ 0 := fun h0 ↦ hsw (measure_mono_null inter_subset_left h0)
  have hTe' := Mediation.integrable_cond_of_integrable hTe h0
  have hdiff : M.armMean μ M.T false - M.armMean μ M.U false =
      (1 - Real.exp ψ) * M.armMean μ M.Te false := by
    rw [(M.commonEffect_iff ψ).1 h, armMean_counterfactual hT hTe h0]
    ring
  have hpos : 0 < M.armMean μ M.Te false := by
    rw [armMean, integral_pos_iff_support_of_nonneg (fun ω ↦ hte ω) hTe']
    have hsupp : {ω | 0 < M.Te ω} = Function.support M.Te := by
      ext ω; simp only [mem_ofPred_eq, Function.mem_support]
      exact ⟨ne_of_gt, fun hne ↦ lt_of_le_of_ne (hte ω) (Ne.symm hne)⟩
    rw [← hsupp, cond_apply (M.measurableSet_arm hR false)]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hsw
  have : Real.exp ψ < 1 := by simpa using Real.exp_lt_exp.2 hψ
  have : 0 < (1 - Real.exp ψ) * M.armMean μ M.Te false := mul_pos (by linarith) hpos
  simp only [ittEffect, meanContrast, hypotheticalEffect]
  linarith

end SwitchingTrial

end StructuralNested

end CausalInference
