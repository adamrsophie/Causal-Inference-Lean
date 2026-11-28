/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Survival curves in continuous time

**Time scale: continuous.** Time is `s : ℝ`, and a survival curve is a function `S : ℝ → ℝ`
read on `[0, ∞)`: `S s` is the probability of surviving beyond `s`. The discrete time layer is
`CausalInference.Survival` (`Survival.survival`, `Survival.rmst`); the objects here carry their
own names so that both layers can be opened together.

A curve of the form `S = exp (-Λ)` with a cumulative hazard `Λ` has the hazard
`-S' / S = Λ'` wherever `Λ` is differentiable (`curveHazard_expSurvival`); for a continuous
hazard `h`, `Λ = ∫₀ˢ h` (`cumHazard`) gives back `h` (`curveHazard_expSurvival_cumHazard`).
The hazard of a curve is defined with Mathlib's `deriv`, which is `0` where the curve is not
differentiable; every result about it here therefore carries a derivative hypothesis and a
positive curve, so no value comes from that convention or from a division by zero.

## Main definitions

* `IsSurvivalCurve S`, `IsSurvivalFamily S`: measurable, with values in `[0, 1]` on `[0, ∞)`;
  for a family `S : 𝒳 → ℝ → ℝ` of conditional curves, jointly measurable.
* `expSurvival Λ = exp (-Λ)`, `cumHazard h s = ∫₀ˢ h`, `curveHazard S = -S' / S`.
* `restrictedMean S τ = ∫₀^τ S`, the restricted mean survival time up to the horizon `τ`.
* `stepSurvival m`: the curve of an event at the time `m`.
* `popSurvival ν S s = ∫ S x s dν(x)`, the population curve of a mixture of the conditional
  curves `S x` over a covariate law `ν`, its hazard `popHazard ν S` and its cumulative hazard
  `popCumHazard ν S = -log (popSurvival ν S)`.

## Main results

* `curveHazard_expSurvival`, `curveHazard_expSurvival_cumHazard`.
* `restrictedMean_nonneg`, `restrictedMean_le`: `0 ≤ restrictedMean S τ ≤ τ` for `τ ≥ 0`.
* `restrictedMean_exp_mul`: a constant hazard `c ≠ 0` has restricted mean
  `(1 - exp (-(c τ))) / c`; `restrictedMean_exp_zero`: a null hazard has restricted mean `τ`.
* `constHazard_instance`: the constant hazard `c` through `cumHazard`, `curveHazard`.
* `restrictedMean_stepSurvival`: an event at `m ≥ 0` has restricted mean `min m τ`.
* `isSurvivalCurve_popSurvival`, `popSurvival_dirac`, `popHazard_dirac`, `popSurvival_map`,
  `popHazard_map`.

## References

* P. Royston and M. K. B. Parmar, *Restricted mean survival time: an alternative to the hazard
  ratio for the design and analysis of randomized trials with a time-to-event outcome*, BMC
  Medical Research Methodology 13 (2013).
-/

@[expose] public section

namespace CausalInference

namespace Survival

namespace ContinuousTime

open MeasureTheory Set

/-! ### Survival curves and families of curves -/

/-- A **survival curve** on `[0, ∞)`: a measurable function with values in `[0, 1]` at every
nonnegative time. Nothing is required at negative times. -/
structure IsSurvivalCurve (S : ℝ → ℝ) : Prop where
  measurable : Measurable S
  nonneg : ∀ s, 0 ≤ s → 0 ≤ S s
  le_one : ∀ s, 0 ≤ s → S s ≤ 1

/-- A **family of conditional survival curves** `S x` indexed by a covariate value `x`: jointly
measurable in `(x, s)`, with values in `[0, 1]` at every nonnegative time. -/
structure IsSurvivalFamily {𝒳 : Type*} [MeasurableSpace 𝒳] (S : 𝒳 → ℝ → ℝ) : Prop where
  measurable : Measurable (Function.uncurry S)
  nonneg : ∀ x s, 0 ≤ s → 0 ≤ S x s
  le_one : ∀ x s, 0 ≤ s → S x s ≤ 1

theorem IsSurvivalFamily.isSurvivalCurve {𝒳 : Type*} [MeasurableSpace 𝒳] {S : 𝒳 → ℝ → ℝ}
    (hS : IsSurvivalFamily S) (x : 𝒳) : IsSurvivalCurve (S x) :=
  ⟨hS.measurable.comp (measurable_const.prodMk measurable_id), hS.nonneg x, hS.le_one x⟩

/-- A survival curve is integrable on every bounded interval of nonnegative times. -/
theorem IsSurvivalCurve.intervalIntegrable {S : ℝ → ℝ} (hS : IsSurvivalCurve S) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable S volume a b := by
  have key : ∀ {u v : ℝ}, 0 ≤ u → IntegrableOn S (Ioc u v) volume := fun {u v} hu =>
    Integrable.of_bound hS.measurable.aestronglyMeasurable 1
      ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hS.nonneg s (hu.trans hs.1.le))]
        exact hS.le_one s (hu.trans hs.1.le))
  exact ⟨key ha, key hb⟩

/-! ### Hazard and cumulative hazard -/

/-- The survival curve `exp (-Λ)` of a cumulative hazard `Λ`. -/
noncomputable def expSurvival (Λ : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (-Λ s)

/-- The cumulative hazard `∫₀ˢ h` of a hazard `h`. -/
noncomputable def cumHazard (h : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, h u

/-- The **hazard of a survival curve**, `-S'(s) / S(s)`. It is a genuine hazard where `S` is
differentiable and positive; the results below say so. -/
noncomputable def curveHazard (S : ℝ → ℝ) (s : ℝ) : ℝ := -deriv S s / S s

theorem expSurvival_pos (Λ : ℝ → ℝ) (s : ℝ) : 0 < expSurvival Λ s := Real.exp_pos _

/-- `(exp (-Λ))' = -Λ' exp (-Λ)`. -/
theorem hasDerivAt_expSurvival {Λ : ℝ → ℝ} {h s : ℝ} (hΛ : HasDerivAt Λ h s) :
    HasDerivAt (expSurvival Λ) (-(h * expSurvival Λ s)) s := by
  have := hΛ.neg.exp
  unfold expSurvival
  convert this using 1
  simp only [Pi.neg_apply]
  ring

/-- **The hazard of `exp (-Λ)` is `Λ'`**: where `Λ` has derivative `h` at `s`, the curve
`exp (-Λ)` has hazard `h` at `s`. -/
theorem curveHazard_expSurvival {Λ : ℝ → ℝ} {h s : ℝ} (hΛ : HasDerivAt Λ h s) :
    curveHazard (expSurvival Λ) s = h := by
  rw [curveHazard, (hasDerivAt_expSurvival hΛ).deriv, neg_neg,
    mul_div_assoc, div_self (expSurvival_pos Λ s).ne', mul_one]

/-- The cumulative hazard of a continuous hazard has derivative the hazard. -/
theorem hasDerivAt_cumHazard {h : ℝ → ℝ} (hh : Continuous h) (s : ℝ) :
    HasDerivAt (cumHazard h) (h s) s :=
  intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable _ _)
    (hh.stronglyMeasurableAtFilter _ _) hh.continuousAt

/-- **The curve of a continuous hazard has that hazard**: `exp (-∫₀ˢ h)` has hazard `h s` at
every time `s`. -/
theorem curveHazard_expSurvival_cumHazard {h : ℝ → ℝ} (hh : Continuous h) (s : ℝ) :
    curveHazard (expSurvival (cumHazard h)) s = h s :=
  curveHazard_expSurvival (hasDerivAt_cumHazard hh s)

/-- A nonnegative hazard has a nonnegative cumulative hazard at nonnegative times. -/
theorem cumHazard_nonneg {h : ℝ → ℝ} (hh : ∀ u, 0 ≤ u → 0 ≤ h u) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ cumHazard h s :=
  intervalIntegral.integral_nonneg hs fun u hu => hh u hu.1

/-- A measurable cumulative hazard, nonnegative on `[0, ∞)`, gives a survival curve. -/
theorem isSurvivalCurve_expSurvival {Λ : ℝ → ℝ} (hm : Measurable Λ)
    (h0 : ∀ s, 0 ≤ s → 0 ≤ Λ s) : IsSurvivalCurve (expSurvival Λ) :=
  ⟨hm.neg.exp, fun s _ => (expSurvival_pos Λ s).le,
    fun s hs => Real.exp_le_one_iff.2 (neg_nonpos.2 (h0 s hs))⟩

/-! ### The restricted mean survival time -/

/-- The **restricted mean survival time** `∫₀^τ S` of a survival curve `S` up to the horizon
`τ`. -/
noncomputable def restrictedMean (S : ℝ → ℝ) (τ : ℝ) : ℝ := ∫ s in (0 : ℝ)..τ, S s

/-- The restricted mean of a curve that is nonnegative on `[0, ∞)` is nonnegative for
`τ ≥ 0`. -/
theorem restrictedMean_nonneg {S : ℝ → ℝ} (hS : ∀ s, 0 ≤ s → 0 ≤ S s) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ restrictedMean S τ :=
  intervalIntegral.integral_nonneg hτ fun s hs => hS s hs.1

/-- **The restricted mean is at most the horizon**: `restrictedMean S τ ≤ τ` for a survival
curve and `τ ≥ 0`. -/
theorem restrictedMean_le {S : ℝ → ℝ} (hS : IsSurvivalCurve S) {τ : ℝ} (hτ : 0 ≤ τ) :
    restrictedMean S τ ≤ τ := by
  have h := intervalIntegral.integral_mono_on hτ (hS.intervalIntegrable le_rfl hτ)
    (intervalIntegrable_const (c := (1 : ℝ))) fun s hs => hS.le_one s hs.1
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h
  exact h

/-- **The restricted mean of a constant hazard**: for a hazard `c ≠ 0`, the curve
`exp (-(c s))` has restricted mean `(1 - exp (-(c τ))) / c` up to `τ`. -/
theorem restrictedMean_exp_mul {c : ℝ} (hc : c ≠ 0) (τ : ℝ) :
    restrictedMean (fun s => Real.exp (-(c * s))) τ = (1 - Real.exp (-(c * τ))) / c := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) τ,
      HasDerivAt (fun s => Real.exp (-(c * s)) * (-1 / c)) (Real.exp (-(c * s))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(c * s)) (-c) s := by
      have := (hasDerivAt_id s).const_mul (-c)
      simp only [id, mul_one, neg_mul] at this
      exact this
    convert h1.exp.mul_const (-1 / c) using 1
    field_simp
  rw [restrictedMean, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s => Real.exp (-(c * s))).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- A null hazard: the curve `1` has restricted mean `τ`. -/
theorem restrictedMean_exp_zero (τ : ℝ) :
    restrictedMean (fun s => Real.exp (-(0 * s))) τ = τ := by
  simp [restrictedMean]

/-- **The constant hazard as an instance.** The cumulative hazard of the constant hazard `c` is
`c s`; the curve `exp (-(c s))` has hazard `c` at every time, is a survival curve for `c ≥ 0`,
and for `c ≠ 0` has restricted mean `(1 - exp (-(c τ))) / c`. -/
theorem constHazard_instance {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≠ 0) (s τ : ℝ) :
    cumHazard (fun _ => c) = (fun u => c * u) ∧
      curveHazard (expSurvival (cumHazard fun _ => c)) s = c ∧
      IsSurvivalCurve (expSurvival (cumHazard fun _ => c)) ∧
      restrictedMean (expSurvival (cumHazard fun _ => c)) τ = (1 - Real.exp (-(c * τ))) / c := by
  have hΛ : cumHazard (fun _ => c) = fun u => c * u := by
    funext u; simp [cumHazard, mul_comm]
  refine ⟨hΛ, curveHazard_expSurvival_cumHazard continuous_const s, ?_, ?_⟩
  · exact isSurvivalCurve_expSurvival (by rw [hΛ]; fun_prop)
      fun u hu => cumHazard_nonneg (fun _ _ => hc0) hu
  · rw [hΛ]
    exact restrictedMean_exp_mul hc τ

/-- The curve of an event at the time `m`: `1` before `m` and `0` from `m` on. -/
noncomputable def stepSurvival (m : ℝ) (s : ℝ) : ℝ := if s < m then 1 else 0

theorem isSurvivalCurve_stepSurvival (m : ℝ) : IsSurvivalCurve (stepSurvival m) := by
  refine ⟨Measurable.ite measurableSet_Iio measurable_const measurable_const, fun s _ => ?_,
    fun s _ => ?_⟩ <;>
  · unfold stepSurvival; split_ifs <;> norm_num

/-- **The restricted mean of an event at `m ≥ 0` is `min m τ`** for `τ ≥ 0`. -/
theorem restrictedMean_stepSurvival {m τ : ℝ} (hm : 0 ≤ m) (hτ : 0 ≤ τ) :
    restrictedMean (stepSurvival m) τ = min m τ := by
  have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ m := by
    rw [ae_iff]
    simp
  have hint : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable (stepSurvival m) volume a b :=
    fun a b ha hb => (isSurvivalCurve_stepSurvival m).intervalIntegrable ha hb
  rcases le_total m τ with hmτ | hτm
  · rw [min_eq_left hmτ, restrictedMean,
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 m le_rfl hm) (hint m τ hm hτ)]
    have h1 : ∫ s in (0 : ℝ)..m, stepSurvival m s = ∫ s in (0 : ℝ)..m, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (hne.mono fun s hs hsI => ?_)
      rw [uIoc_of_le hm] at hsI
      simp [stepSurvival, lt_of_le_of_ne hsI.2 hs]
    have h2 : ∫ s in m..τ, stepSurvival m s = ∫ s in m..τ, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hsI => ?_)
      rw [uIoc_of_le hmτ] at hsI
      simp [stepSurvival, not_lt.2 hsI.1.le]
    rw [h1, h2]
    simp
  · rw [min_eq_right hτm, restrictedMean]
    have h1 : ∫ s in (0 : ℝ)..τ, stepSurvival m s = ∫ s in (0 : ℝ)..τ, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (hne.mono fun s hs hsI => ?_)
      rw [uIoc_of_le hτ] at hsI
      simp [stepSurvival, lt_of_le_of_ne (hsI.2.trans hτm) hs]
    rw [h1]
    simp

/-! ### The population curve of a mixture over a covariate law -/

section Population

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **population survival curve** of the conditional curves `S x` under the covariate law
`ν`: `s ↦ ∫ S x s dν(x)`. -/
noncomputable def popSurvival (ν : Measure 𝒳) (S : 𝒳 → ℝ → ℝ) (s : ℝ) : ℝ := ∫ x, S x s ∂ν

/-- The **population hazard**: the hazard of the population curve. -/
noncomputable def popHazard (ν : Measure 𝒳) (S : 𝒳 → ℝ → ℝ) (s : ℝ) : ℝ :=
  curveHazard (popSurvival ν S) s

/-- The **population cumulative hazard** `-log` of the population curve. -/
noncomputable def popCumHazard (ν : Measure 𝒳) (S : 𝒳 → ℝ → ℝ) (s : ℝ) : ℝ :=
  -Real.log (popSurvival ν S s)

/-- At a fixed time the conditional curves of a family are integrable in the covariate under a
finite law: they are measurable with values in `[0, 1]`. -/
theorem IsSurvivalFamily.integrable {S : 𝒳 → ℝ → ℝ} (hS : IsSurvivalFamily S) (ν : Measure 𝒳)
    [IsFiniteMeasure ν] {s : ℝ} (hs : 0 ≤ s) : Integrable (fun x => S x s) ν := by
  have hm : Measurable fun x => S x s :=
    hS.measurable.comp (measurable_id.prodMk measurable_const)
  exact Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hS.nonneg x s hs)]
    exact hS.le_one x s hs)

/-- The population curve is measurable. -/
theorem measurable_popSurvival {S : 𝒳 → ℝ → ℝ} (hS : Measurable (Function.uncurry S))
    (ν : Measure 𝒳) [SFinite ν] : Measurable (popSurvival ν S) :=
  (hS.stronglyMeasurable.integral_prod_left (μ := ν)).measurable

/-- **The population curve of a family of survival curves is a survival curve.** -/
theorem isSurvivalCurve_popSurvival {S : 𝒳 → ℝ → ℝ} (hS : IsSurvivalFamily S) (ν : Measure 𝒳)
    [IsProbabilityMeasure ν] : IsSurvivalCurve (popSurvival ν S) := by
  refine ⟨measurable_popSurvival hS.measurable ν, fun s hs => ?_, fun s hs => ?_⟩
  · exact integral_nonneg fun x => hS.nonneg x s hs
  · calc popSurvival ν S s ≤ ∫ _x, (1 : ℝ) ∂ν :=
          integral_mono (hS.integrable ν hs) (integrable_const (1 : ℝ)) fun x => hS.le_one x s hs
      _ = 1 := by simp

/-- Under a point mass the population curve is the conditional curve. -/
theorem popSurvival_dirac [MeasurableSingletonClass 𝒳] (S : 𝒳 → ℝ → ℝ) (x₀ : 𝒳) :
    popSurvival (Measure.dirac x₀) S = S x₀ :=
  funext fun s => integral_dirac (fun x => S x s) x₀

/-- Under a point mass the population hazard is the conditional hazard. -/
theorem popHazard_dirac [MeasurableSingletonClass 𝒳] (S : 𝒳 → ℝ → ℝ) (x₀ : 𝒳) (s : ℝ) :
    popHazard (Measure.dirac x₀) S s = curveHazard (S x₀) s := by
  rw [popHazard, popSurvival_dirac]

/-- The population curve under an image law `ν.map f` is the population curve under `ν` of the
curves `S (f y)`. -/
theorem popSurvival_map {𝒴 : Type*} [MeasurableSpace 𝒴] {S : 𝒳 → ℝ → ℝ}
    (hS : Measurable (Function.uncurry S)) {f : 𝒴 → 𝒳} (hf : Measurable f) (ν : Measure 𝒴) :
    popSurvival (ν.map f) S = popSurvival ν (fun y => S (f y)) := by
  funext s
  exact integral_map hf.aemeasurable
    (hS.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable

/-- The population hazard under an image law `ν.map f`. -/
theorem popHazard_map {𝒴 : Type*} [MeasurableSpace 𝒴] {S : 𝒳 → ℝ → ℝ}
    (hS : Measurable (Function.uncurry S)) {f : 𝒴 → 𝒳} (hf : Measurable f) (ν : Measure 𝒴)
    (s : ℝ) : popHazard (ν.map f) S s = popHazard ν (fun y => S (f y)) s := by
  rw [popHazard, popHazard, popSurvival_map hS hf]

end Population

end ContinuousTime

end Survival

end CausalInference
