/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.IPE
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Iterative parameter estimation: other contrasts

The population update of iterative parameter estimation
(`CausalInference.StructuralNested.SwitchingTrial.ipeMap`) compares the observed experimental arm
with the transformed control arm `U(ψ) = T^c + exp ψ T^e` by the ratio of arm means, the target
of an exponential accelerated failure time fit. This file treats two other parametric fits whose
population targets have a closed form for uncensored data, the same fixed point and convergence
questions for them, and two further concrete trials.

## Main definitions

* `SwitchingTrial.logMap ψ = E[log U(ψ) | R = 0] - E[log T | R = 1]`: the difference of mean log
  times, the target of a log-normal fit (least squares on log time) with the arm as covariate.
* `SwitchingTrial.weibullMap k ψ = log (E[U(ψ)^k | R = 0] / E[T^k | R = 1]) / k`: the log ratio of
  power means, the target of a Weibull fit with known common shape `k > 0`, whose scale estimate
  in each arm is `E[T^k]^{1/k}`. `weibullMap_one`: shape one is `ipeMap`.

## Main results

* `fixedPt_unique_and_tendsto_of_slope_lt`: a nondecreasing map of `ℝ` with
  `f y - f x < y - x` for `x < y` has at most one fixed point, and when it has one its iterates
  converge to it monotonically from every start. This replaces the contraction argument, which
  is not available for these maps on all of `ℝ`.
* `isFixedPt_logMap_trueParam`, `isFixedPt_weibullMap_trueParam`: under randomization, the common
  treatment effect and a fully treated experimental arm (with `0 ≤ T^e ≤ T`, `T > 0` and the
  stated integrability) the true parameter is a fixed point of both updates.
* `monotone_logMap`, `logMap_sub_lt`, `monotone_weibullMap`, `weibullMap_sub_lt`: both updates are
  nondecreasing with slope at most one, and strictly below one when the control patients with
  positive time off the experimental treatment, `T^c > 0`, have positive probability.
  `logMap_eq_add_of_noTimeOff`: if no control patient has time off the experimental treatment,
  `logMap ψ = ψ + logMap 0`, so either every `ψ` or no `ψ` is a fixed point.
* `tendsto_iterate_logMap`, `tendsto_iterate_weibullMap` and their `_trueParam` versions: under
  that condition a fixed point is unique and the iteration converges to it from every start;
  under the model it converges to `ψ₀`.
* `isFixedPt_logMap_iff_isFixedPt_ipeMap`: under the model the ratio of means and the log-time
  updates have the same fixed points. `IPECounterexample.Scaled.same_fixedPt_different_maps`:
  they are different maps (at the ITT start, `log (7/12)` against `(log 3 - log 8) / 2`).
* `IPECounterexample.Discontinued.logMap_fixedPt`: in the trial with experimental
  discontinuation of `CausalInference.StructuralNested.IPECounterexample.Discontinued`, the
  log-time update has the unique fixed point with time ratio `(2 + √22) / 9 ≈ 0.743`, the ratio of
  means update the time ratio `5/7 ≈ 0.714`, and the truth is `1/2`: without the scale relation in
  the experimental arm the two contrasts disagree with each other and with the truth.
* `IPECounterexample.Diverging.not_tendsto`: explicit data with
  `E[T | R = 1] ≤ E[T^e | R = 0]` on which the ratio of means iteration converges from no start;
  `Diverging.not_randomized_of_commonEffect`: with these data and a fully treated experimental
  arm, any untreated time satisfying the common effect is not independent of the arm, so in the
  trial (where the common effect holds) randomization is what fails.

## Setting and limitations

Counterfactual variables on a general probability space, real and positive times, arm means as
in `CausalInference.StructuralNested.FailureTime`; concrete trials on the eight point space of
`CausalInference.StructuralNested.RPSFTMCounterexample`. Censoring is not modeled: with
administrative censoring the closed forms above are not the targets of the fits, and
recensoring within the iteration (TSD 24, Section 4.2.1.1) is left out here; it belongs to the
treatment of recensoring. The Weibull fit with an estimated shape, and other parametric
families fitted by maximum likelihood (for example the log-logistic), have no closed form target
and are not formalized; the statements here do not formalize maximum likelihood itself, only
the closed form of its population target.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16* (2014): Section 3.2.3,
  Appendix A ("IPE Algorithm").
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24* (2024):
  Section 4.2.1.
* M. Branson, J. Whitehead, *Estimating a treatment effect in survival studies in which patients
  switch treatment*, Statistics in Medicine 21 (2002), 2449 to 2463.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology

namespace CausalInference

namespace StructuralNested

/-! ### Iteration of a monotone map with slope below one -/

/-- **Iteration of a nondecreasing map with slope below one.** If `f : ℝ → ℝ` is monotone,
`f y - f x < y - x` whenever `x < y`, and `p` is a fixed point, then `p` is the only fixed point
and the iterates of `f` converge to `p` from every starting value (monotonically). -/
theorem fixedPt_unique_and_tendsto_of_slope_lt {f : ℝ → ℝ} (hmono : Monotone f)
    (hslope : ∀ x y, x < y → f y - f x < y - x) {p : ℝ} (hp : IsFixedPt f p) :
    (∀ q, IsFixedPt f q → q = p) ∧ ∀ x, Tendsto (fun n ↦ f^[n] x) atTop (𝓝 p) := by
  have huniq : ∀ q, IsFixedPt f q → q = p := by
    intro q hq
    rcases lt_trichotomy q p with h | h | h
    · have := hslope q p h; rw [hp.eq, hq.eq] at this; exact absurd this (lt_irrefl _)
    · exact h
    · have := hslope p q h; rw [hp.eq, hq.eq] at this; exact absurd this (lt_irrefl _)
  have hcont : Continuous f := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    rcases lt_trichotomy x y with h | h | h
    · have h1 := hslope x y h; have h2 := hmono h.le
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h2), abs_sub_comm,
        abs_of_pos (sub_pos.2 h)]
      exact h1.le
    · simp [h]
    · have h1 := hslope y x h; have h2 := hmono h.le
      rw [abs_of_nonneg (sub_nonneg.2 h2), abs_of_pos (sub_pos.2 h)]
      exact h1.le
  have hstep_down : ∀ y, p ≤ y → f y ≤ y := fun y hy ↦ by
    rcases hy.eq_or_lt with h | h
    · rw [← h, hp.eq]
    · have := hslope p y h; rw [hp.eq] at this; linarith
  have hstep_up : ∀ y, y ≤ p → y ≤ f y := fun y hy ↦ by
    rcases hy.eq_or_lt with h | h
    · rw [h, hp.eq]
    · have := hslope y p h; rw [hp.eq] at this; linarith
  refine ⟨huniq, fun x ↦ ?_⟩
  have hfix : ∀ L, Tendsto (fun n ↦ f^[n] x) atTop (𝓝 L) → L = p := fun L hL ↦
    huniq L (isFixedPt_of_tendsto_iterate hL hcont.continuousAt)
  rcases le_total p x with hx | hx
  · have hlow : ∀ n, p ≤ f^[n] x := fun n ↦ by
      have := (hmono.iterate n) hx; rwa [(hp.iterate n).eq] at this
    have hanti : Antitone fun n ↦ f^[n] x := antitone_nat_of_succ_le fun n ↦ by
      rw [iterate_succ_apply']; exact hstep_down _ (hlow n)
    have hlim := tendsto_atTop_ciInf hanti ⟨p, by rintro _ ⟨n, rfl⟩; exact hlow n⟩
    rwa [hfix _ hlim] at hlim
  · have hup : ∀ n, f^[n] x ≤ p := fun n ↦ by
      have := (hmono.iterate n) hx; rwa [(hp.iterate n).eq] at this
    have hmon : Monotone fun n ↦ f^[n] x := monotone_nat_of_le_succ fun n ↦ by
      rw [iterate_succ_apply']; exact hstep_up _ (hup n)
    have hlim := tendsto_atTop_ciSup hmon ⟨p, by rintro _ ⟨n, rfl⟩; exact hup n⟩
    rwa [hfix _ hlim] at hlim

namespace SwitchingTrial

variable {Ω : Type*} {M : SwitchingTrial Ω}

/-! ### Pointwise facts about the candidate untreated time -/

/-- With `0 ≤ T^e ≤ T` and `T > 0`, every candidate untreated time is positive. -/
theorem counterfactual_pos (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) (ψ : ℝ) (ω : Ω) :
    0 < M.counterfactual ψ ω := by
  have h1 := hwf.te_nonneg ω
  have h2 := hwf.te_le ω
  have h3 := hTpos ω
  simp only [counterfactual, Tc]
  rcases h1.eq_or_lt with h | h
  · rw [← h]; linarith
  · nlinarith [Real.exp_pos ψ]

/-- With `T^e ≥ 0`, the candidate untreated time is nondecreasing in `ψ`. -/
theorem counterfactual_mono (hte : ∀ ω, 0 ≤ M.Te ω) {ψ ψ' : ℝ} (h : ψ ≤ ψ') (ω : Ω) :
    M.counterfactual ψ ω ≤ M.counterfactual ψ' ω := by
  simp only [counterfactual]
  have := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h) (hte ω)
  linarith

/-- With `T^c, T^e ≥ 0` and `ψ ≤ ψ'`, `U(ψ') ≤ exp (ψ' - ψ) U(ψ)`. -/
theorem counterfactual_le_exp_mul (hwf : M.WellFormed) {ψ ψ' : ℝ} (h : ψ ≤ ψ') (ω : Ω) :
    M.counterfactual ψ' ω ≤ Real.exp (ψ' - ψ) * M.counterfactual ψ ω := by
  have hc : 0 ≤ M.Tc ω := sub_nonneg.2 (hwf.te_le ω)
  have he : 1 ≤ Real.exp (ψ' - ψ) := Real.one_le_exp (sub_nonneg.2 h)
  have hmul : Real.exp (ψ' - ψ) * Real.exp ψ = Real.exp ψ' := by
    rw [← Real.exp_add]; ring_nf
  have e : Real.exp (ψ' - ψ) * (M.Tc ω + Real.exp ψ * M.Te ω) =
      Real.exp (ψ' - ψ) * M.Tc ω + Real.exp ψ' * M.Te ω := by rw [mul_add, ← mul_assoc, hmul]
  simp only [counterfactual]
  rw [e]
  linarith [le_mul_of_one_le_left hc he]

/-- The inequality of `counterfactual_le_exp_mul` is strict when `ψ < ψ'` and `T^c > 0`. -/
theorem counterfactual_lt_exp_mul {ψ ψ' : ℝ} (h : ψ < ψ') {ω : Ω} (hc : 0 < M.Tc ω) :
    M.counterfactual ψ' ω < Real.exp (ψ' - ψ) * M.counterfactual ψ ω := by
  have he : 1 < Real.exp (ψ' - ψ) := by simpa using Real.exp_lt_exp.2 (sub_pos.2 h)
  have hmul : Real.exp (ψ' - ψ) * Real.exp ψ = Real.exp ψ' := by
    rw [← Real.exp_add]; ring_nf
  have e : Real.exp (ψ' - ψ) * (M.Tc ω + Real.exp ψ * M.Te ω) =
      Real.exp (ψ' - ψ) * M.Tc ω + Real.exp ψ' * M.Te ω := by rw [mul_add, ← mul_assoc, hmul]
  simp only [counterfactual]
  rw [e]
  linarith [lt_mul_of_one_lt_left hc he]

/-- `U(ψ) ≤ exp |ψ| T`. -/
theorem counterfactual_le_exp_abs (hwf : M.WellFormed) (ψ : ℝ) (ω : Ω) :
    M.counterfactual ψ ω ≤ Real.exp |ψ| * M.T ω := by
  have hT : 0 ≤ M.T ω := (hwf.te_nonneg ω).trans (hwf.te_le ω)
  have h0 : M.counterfactual 0 ω = M.T ω := by rw [counterfactual_zero]
  rcases le_total 0 ψ with h | h
  · have := counterfactual_le_exp_mul hwf h ω
    rw [sub_zero, h0] at this
    rwa [abs_of_nonneg h]
  · have := counterfactual_mono hwf.te_nonneg h ω
    rw [h0] at this
    exact this.trans (le_mul_of_one_le_left hT (Real.one_le_exp (abs_nonneg ψ)))

/-- `|log U(ψ) - log T| ≤ |ψ|` for positive times. -/
theorem abs_log_counterfactual_sub_le (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) (ψ : ℝ)
    (ω : Ω) : |Real.log (M.counterfactual ψ ω) - Real.log (M.T ω)| ≤ |ψ| := by
  have hU := counterfactual_pos hwf hTpos ψ ω
  have hT := hTpos ω
  have h0 : M.counterfactual 0 ω = M.T ω := by rw [counterfactual_zero]
  rw [abs_le]
  rcases le_total 0 ψ with h | h
  · have a1 := counterfactual_mono hwf.te_nonneg h ω
    have a2 := counterfactual_le_exp_mul hwf h ω
    simp only [h0, sub_zero] at a1 a2
    have l1 := Real.log_le_log hT a1
    have l2 := Real.log_le_log hU a2
    rw [Real.log_mul (Real.exp_pos _).ne' hT.ne', Real.log_exp] at l2
    rw [abs_of_nonneg h]; constructor <;> linarith
  · have a1 := counterfactual_mono hwf.te_nonneg h ω
    have a2 := counterfactual_le_exp_mul hwf h ω
    rw [h0] at a1 a2
    have l1 := Real.log_le_log hU a1
    have l2 := Real.log_le_log hT a2
    rw [Real.log_mul (Real.exp_pos _).ne' hU.ne', Real.log_exp] at l2
    rw [abs_of_nonpos h]; constructor <;> linarith

/-! ### Integrals on an arm -/

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- An integral over an arm is strictly smaller when the integrand is pointwise smaller and
strictly smaller on a set of positive conditional measure. -/
theorem integral_lt_of_le_of_lt {ν : Measure Ω} {f g : Ω → ℝ} (hf : Integrable f ν)
    (hg : Integrable g ν) (hle : ∀ ω, f ω ≤ g ω) {S : Set Ω} (hS : ν S ≠ 0)
    (hlt : ∀ ω ∈ S, f ω < g ω) : ∫ ω, f ω ∂ν < ∫ ω, g ω ∂ν := by
  have hpos : 0 < ∫ ω, (g ω - f ω) ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun ω ↦ sub_nonneg.2 (hle ω)) (hg.sub hf)]
    refine pos_iff_ne_zero.2 fun h ↦ hS (measure_mono_null (fun ω hω ↦ ?_) h)
    exact (sub_pos.2 (hlt ω hω)).ne'
  rw [integral_sub hg hf] at hpos
  linarith

/-- The control patients with positive time off the experimental treatment have positive
conditional probability in the control arm when they have positive probability. -/
theorem cond_Tc_pos_ne_zero [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) :
    μ[|M.arm false] {ω | 0 < M.Tc ω} ≠ 0 := by
  rw [cond_apply (M.measurableSet_arm hR false)]
  exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) hpos

/-- The arm mean of a positive integrable function is positive. -/
theorem armMean_pos [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : ∀ ω, 0 < f ω)
    (hfi : Integrable f μ) {r : Bool} (hr : μ (M.arm r) ≠ 0) : 0 < M.armMean μ f r := by
  have := cond_isProbabilityMeasure (μ := μ) hr
  rw [armMean, integral_pos_iff_support_of_nonneg (fun ω ↦ (hf ω).le)
    (Mediation.integrable_cond_of_integrable hfi hr)]
  have : Function.support f = univ := eq_univ_of_forall fun ω ↦ (hf ω).ne'
  rw [this, measure_univ]
  exact one_pos

/-- The arm mean of `c + f` is `c + E[f | R = r]` for integrable `f`. -/
theorem armMean_const_add [IsFiniteMeasure μ] {f : Ω → ℝ} (hfi : Integrable f μ) {r : Bool}
    (hr : μ (M.arm r) ≠ 0) (c : ℝ) :
    M.armMean μ (fun ω ↦ c + f ω) r = c + M.armMean μ f r := by
  have := cond_isProbabilityMeasure (μ := μ) hr
  rw [armMean, integral_add (integrable_const c) (Mediation.integrable_cond_of_integrable hfi hr)]
  simp [armMean]

/-! ### The difference of mean log times -/

variable (M μ) in
/-- **The log-time update.** The control arm is transformed to `U(ψ)`, the experimental arm is
kept as observed, and the arms are compared by the difference of mean log times:
`logMap ψ = E[log U(ψ) | R = 0] - E[log T | R = 1]`. For uncensored data this is the population
target of a log-location accelerated failure time fit with the arm as covariate (log-normal, or
any model `log T = β₀ + β R + σ ε` with errors of mean zero fitted by least squares on log time):
the next value `ψ'` has time ratio `exp (-ψ') = exp (E[log T | R = 1] - E[log U(ψ) | R = 0])`. -/
noncomputable def logMap (ψ : ℝ) : ℝ :=
  M.armMean μ (fun ω ↦ Real.log (M.counterfactual ψ ω)) false -
    M.armMean μ (fun ω ↦ Real.log (M.T ω)) true

/-- With positive times and integrable `log T`, every `log U(ψ)` is integrable. -/
theorem integrable_log_counterfactual [IsFiniteMeasure μ] (hTm : Measurable M.T)
    (hTem : Measurable M.Te) (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω)
    (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ) (ψ : ℝ) :
    Integrable (fun ω ↦ Real.log (M.counterfactual ψ ω)) μ := by
  refine Integrable.mono' (hlogT.abs.add (integrable_const |ψ|))
    (Real.measurable_log.comp (measurable_counterfactual hTm hTem ψ)).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_log_counterfactual_sub_le hwf hTpos ψ ω
  have h2 := abs_sub_abs_le_abs_sub (Real.log (M.counterfactual ψ ω)) (Real.log (M.T ω))
  change _ ≤ |Real.log (M.T ω)| + |ψ|
  linarith

/-- **The true parameter is a fixed point of the log-time update.** Under the common treatment
effect `ψ₀`, randomization, a fully treated experimental arm, `0 ≤ T^e ≤ T`, `T > 0`, measurable
`R`, `T`, `T^e`, integrable `log T`, and both arms of positive probability, `logMap ψ₀ = ψ₀`. -/
theorem isFixedPt_logMap_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) : IsFixedPt (M.logMap μ) ψ₀ := by
  have hU : M.U = M.counterfactual ψ₀ := (M.commonEffect_iff ψ₀).1 h
  have hLi : Integrable (fun ω ↦ Real.log (M.U ω)) μ := by
    rw [hU]; exact integrable_log_counterfactual hTm hTem hwf hTpos hlogT ψ₀
  have hind : IndepFun (fun ω ↦ Real.log (M.U ω)) M.R μ :=
    (hrand.comp measurable_id Real.measurable_log).symm
  have hmean : ∀ r, μ (M.arm r) ≠ 0 →
      M.armMean μ (fun ω ↦ Real.log (M.U ω)) r = ∫ ω, Real.log (M.U ω) ∂μ := fun r hr ↦
    Mediation.condMean_preimage_singleton_of_indepFun hind hR hLi hr
  have e1 : M.armMean μ (fun ω ↦ Real.log (M.T ω)) true =
      M.armMean μ (fun ω ↦ -ψ₀ + Real.log (M.U ω)) true := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem (M.measurableSet_arm hR true)] with ω hω
    have hte := hfull ω hω
    have hUω : M.U ω = Real.exp ψ₀ * M.T ω := by rw [h ω, Tc, hte]; ring
    rw [hUω, Real.log_mul (Real.exp_pos _).ne' (hTpos ω).ne', Real.log_exp]; ring
  rw [IsFixedPt, logMap, ← hU, e1, armMean_const_add hLi h1, hmean true h1, hmean false h0]
  ring

variable (M μ) in
/-- The control arm part of the log-time update, `ψ ↦ E[log U(ψ) | R = 0]`. -/
noncomputable def logControl (ψ : ℝ) : ℝ :=
  M.armMean μ (fun ω ↦ Real.log (M.counterfactual ψ ω)) false

theorem logMap_eq (ψ : ℝ) :
    M.logMap μ ψ = M.logControl μ ψ - M.armMean μ (fun ω ↦ Real.log (M.T ω)) true := rfl

/-- **The log-time update is nondecreasing.** -/
theorem monotone_logMap [IsFiniteMeasure μ] (hTm : Measurable M.T) (hTem : Measurable M.Te)
    (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω)
    (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ) (h0 : μ (M.arm false) ≠ 0) :
    Monotone (M.logMap μ) := by
  intro ψ ψ' h
  have hi := fun x ↦ Mediation.integrable_cond_of_integrable
    (integrable_log_counterfactual hTm hTem hwf hTpos hlogT x) h0
  have : M.logControl μ ψ ≤ M.logControl μ ψ' :=
    integral_mono (hi ψ) (hi ψ') fun ω ↦ Real.log_le_log (counterfactual_pos hwf hTpos ψ ω)
      (counterfactual_mono hwf.te_nonneg h ω)
  rw [logMap_eq, logMap_eq]; linarith

/-- **The log-time update has slope below one.** If moreover the control patients with positive
time off the experimental treatment have positive probability, then
`logMap ψ' - logMap ψ < ψ' - ψ` whenever `ψ < ψ'`. Without that condition the slope can be one:
see `logMap_eq_add_of_noTimeOff`. -/
theorem logMap_sub_lt [IsFiniteMeasure μ] (hR : Measurable M.R) (hTm : Measurable M.T)
    (hTem : Measurable M.Te) (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω)
    (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ) (h0 : μ (M.arm false) ≠ 0)
    (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) {ψ ψ' : ℝ} (h : ψ < ψ') :
    M.logMap μ ψ' - M.logMap μ ψ < ψ' - ψ := by
  have hint := fun x ↦ integrable_log_counterfactual hTm hTem hwf hTpos hlogT x
  have hi := fun x ↦ Mediation.integrable_cond_of_integrable (hint x) h0
  have key : M.logControl μ ψ' <
      M.armMean μ (fun ω ↦ (ψ' - ψ) + Real.log (M.counterfactual ψ ω)) false := by
    refine integral_lt_of_le_of_lt (hi ψ') ((integrable_const _).add (hi ψ)) (fun ω ↦ ?_)
      (cond_Tc_pos_ne_zero hR hpos) fun ω hω ↦ ?_
    · have := Real.log_le_log (counterfactual_pos hwf hTpos ψ' ω)
        (counterfactual_le_exp_mul hwf h.le ω)
      rwa [Real.log_mul (Real.exp_pos _).ne' (counterfactual_pos hwf hTpos ψ ω).ne',
        Real.log_exp] at this
    · have := Real.log_lt_log (counterfactual_pos hwf hTpos ψ' ω)
        (counterfactual_lt_exp_mul h hω)
      rwa [Real.log_mul (Real.exp_pos _).ne' (counterfactual_pos hwf hTpos ψ ω).ne',
        Real.log_exp] at this
  rw [armMean_const_add (hint ψ) h0] at key
  rw [logMap_eq, logMap_eq]
  have : M.logControl μ ψ = M.armMean μ (fun ω ↦ Real.log (M.counterfactual ψ ω)) false := rfl
  linarith

/-- **Uniqueness and convergence of the log-time iteration.** With `0 ≤ T^e ≤ T`, `T > 0`,
measurable `R`, `T`, `T^e`, integrable `log T`, and control patients with positive time off the
experimental treatment of positive probability, a fixed point `p` of `logMap` is unique and the
iteration converges to it from every starting value. -/
theorem tendsto_iterate_logMap [IsFiniteMeasure μ] (hR : Measurable M.R) (hTm : Measurable M.T)
    (hTem : Measurable M.Te) (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω)
    (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ) (h0 : μ (M.arm false) ≠ 0)
    (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) {p : ℝ} (hp : IsFixedPt (M.logMap μ) p) :
    (∀ q, IsFixedPt (M.logMap μ) q → q = p) ∧
      ∀ ψ, Tendsto (fun k ↦ (M.logMap μ)^[k] ψ) atTop (𝓝 p) :=
  fixedPt_unique_and_tendsto_of_slope_lt (monotone_logMap hTm hTem hwf hTpos hlogT h0)
    (fun _ _ h ↦ logMap_sub_lt hR hTm hTem hwf hTpos hlogT h0 hpos h) hp

/-- **Convergence of the log-time iteration to the true parameter.** Under the hypotheses of
`isFixedPt_logMap_trueParam` and positive probability of control patients with positive time
off the experimental treatment, `ψ₀` is the only fixed point of `logMap` and the iteration
converges to it from every starting value. -/
theorem tendsto_iterate_logMap_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0)
    (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) :
    (∀ q, IsFixedPt (M.logMap μ) q → q = ψ₀) ∧
      ∀ ψ, Tendsto (fun k ↦ (M.logMap μ)^[k] ψ) atTop (𝓝 ψ₀) :=
  tendsto_iterate_logMap hR hTm hTem hwf hTpos hlogT h0 hpos
    (isFixedPt_logMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hlogT h1 h0)

/-- **Slope one without time off treatment in the control arm.** If every control patient is on
the experimental treatment throughout (`T^c = 0` on `R = 0`), then
`logMap ψ = ψ + logMap 0`: either every `ψ` is a fixed point (when `logMap 0 = 0`) or none is. -/
theorem logMap_eq_add_of_noTimeOff [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTpos : ∀ ω, 0 < M.T ω) (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ)
    (h0 : μ (M.arm false) ≠ 0) (hno : ∀ ω, M.R ω = false → M.Tc ω = 0) (ψ : ℝ) :
    M.logMap μ ψ = ψ + M.logMap μ 0 := by
  have e : M.logControl μ ψ = M.armMean μ (fun ω ↦ ψ + Real.log (M.T ω)) false := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem (M.measurableSet_arm hR false)] with ω hω
    have hc := hno ω hω
    have hUω : M.counterfactual ψ ω = Real.exp ψ * M.T ω := by
      simp only [counterfactual]; rw [hc]; simp only [Tc] at hc; rw [show M.Te ω = M.T ω by
        linarith]; ring
    rw [hUω, Real.log_mul (Real.exp_pos _).ne' (hTpos ω).ne', Real.log_exp]
  rw [logMap_eq, logMap_eq, e, armMean_const_add hlogT h0, logControl, counterfactual_zero]
  ring

/-- **Same fixed point as the ratio of means update under the model.** Under the common treatment
effect, randomization, a fully treated experimental arm, `0 ≤ T^e ≤ T`, `T > 0`, measurable and
integrable `T`, `T^e`, integrable `log T`, both arms of positive probability and control
patients with positive time off the experimental treatment of positive probability, `ipeMap` and
`logMap` have the same fixed points (both exactly `ψ₀`). The maps differ elsewhere
(`IPECounterexample.Scaled.ipeMap_ne_logMap`). -/
theorem isFixedPt_logMap_iff_isFixedPt_ipeMap [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (hlogT : Integrable (fun ω ↦ Real.log (M.T ω)) μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) (ψ : ℝ) :
    IsFixedPt (M.logMap μ) ψ ↔ IsFixedPt (M.ipeMap μ) ψ := by
  have ha : 0 < M.armMean μ M.Tc false := by
    have := integral_lt_of_le_of_lt (ν := μ[|M.arm false]) (f := fun _ ↦ (0 : ℝ)) (g := M.Tc)
      (integrable_const _) (Mediation.integrable_cond_of_integrable (integrable_Tc hT hTe) h0)
      (fun ω ↦ sub_nonneg.2 (hwf.te_le ω)) (cond_Tc_pos_ne_zero hR hpos) fun ω hω ↦ hω
    rw [integral_zero] at this
    exact this
  rw [isFixedPt_ipeMap_iff_trueParam hR h hrand hfull hwf.te_nonneg hT hTe h1 h0 ha]
  have := tendsto_iterate_logMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hlogT h1 h0 hpos
  exact ⟨this.1 ψ, fun e ↦ e ▸
    isFixedPt_logMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hlogT h1 h0⟩

/-! ### The Weibull update with known shape -/

variable (M μ) in
/-- **The Weibull update with known shape `k`.** For uncensored data, the maximum likelihood
estimate of the scale of a Weibull distribution with known shape `k > 0`, survival
`exp (-(t / λ)^k)`, is `λ = E[T^k]^{1/k}` (the likelihood equation in `λ` is
`n k / λ = k Σ t_i^k / λ^{k + 1}`). A Weibull accelerated failure time fit with the arm as
covariate and a common known shape fits each arm's scale separately, so its time ratio is the
ratio of the power means `E[T^k | R = 1]^{1/k} / E[U(ψ)^k | R = 0]^{1/k}`. That closed form is
taken as the definition of the population update:
`weibullMap k ψ = log (E[U(ψ)^k | R = 0] / E[T^k | R = 1]) / k`. The shape is assumed known;
when it is estimated jointly the population target has no closed form and is not formalized. -/
noncomputable def weibullMap (k ψ : ℝ) : ℝ :=
  Real.log (M.armMean μ (fun ω ↦ M.counterfactual ψ ω ^ k) false /
    M.armMean μ (fun ω ↦ M.T ω ^ k) true) / k

/-- **Shape one is the exponential fit**: `weibullMap 1 = ipeMap`. -/
theorem weibullMap_one : M.weibullMap μ 1 = M.ipeMap μ := by
  funext ψ; simp [weibullMap, ipeMap, Real.rpow_one]

/-- With positive times, `k ≥ 0` and integrable `T^k`, every `U(ψ)^k` is integrable. -/
theorem integrable_rpow_counterfactual [IsFiniteMeasure μ] (hTm : Measurable M.T)
    (hTem : Measurable M.Te) (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ}
    (hk : 0 ≤ k) (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ) (ψ : ℝ) :
    Integrable (fun ω ↦ M.counterfactual ψ ω ^ k) μ := by
  refine Integrable.mono' (hTk.const_mul (Real.exp |ψ| ^ k))
    ((measurable_counterfactual hTm hTem ψ).pow_const k).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hU := (counterfactual_pos hwf hTpos ψ ω).le
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hU k), ← Real.mul_rpow
    (Real.exp_pos _).le (hTpos ω).le]
  exact Real.rpow_le_rpow hU (counterfactual_le_exp_abs hwf ψ ω) hk

/-- **The true parameter is a fixed point of the Weibull update.** Under the common treatment
effect `ψ₀`, randomization, a fully treated experimental arm, `0 ≤ T^e ≤ T`, `T > 0`, measurable
`R`, `T`, `T^e`, a shape `k > 0` with `T^k` integrable, and both arms of positive probability,
`weibullMap k ψ₀ = ψ₀`. -/
theorem isFixedPt_weibullMap_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 < k) (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) :
    IsFixedPt (M.weibullMap μ k) ψ₀ := by
  have hU : M.U = M.counterfactual ψ₀ := (M.commonEffect_iff ψ₀).1 h
  have hVi : Integrable (fun ω ↦ M.U ω ^ k) μ := by
    rw [hU]; exact integrable_rpow_counterfactual hTm hTem hwf hTpos hk.le hTk ψ₀
  have hind : IndepFun (fun ω ↦ M.U ω ^ k) M.R μ :=
    (hrand.comp measurable_id (measurable_id.pow_const k)).symm
  have hmean : ∀ r, μ (M.arm r) ≠ 0 →
      M.armMean μ (fun ω ↦ M.U ω ^ k) r = ∫ ω, M.U ω ^ k ∂μ := fun r hr ↦
    Mediation.condMean_preimage_singleton_of_indepFun hind hR hVi hr
  have e1 : M.armMean μ (fun ω ↦ M.U ω ^ k) true =
      Real.exp (ψ₀ * k) * M.armMean μ (fun ω ↦ M.T ω ^ k) true := by
    rw [armMean, armMean, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem (M.measurableSet_arm hR true)] with ω hω
    have hUω : M.U ω = Real.exp ψ₀ * M.T ω := by rw [h ω, Tc, hfull ω hω]; ring
    rw [hUω, Real.mul_rpow (Real.exp_pos _).le (hTpos ω).le, ← Real.exp_mul]
  have hC : 0 < M.armMean μ (fun ω ↦ M.T ω ^ k) true :=
    armMean_pos (fun ω ↦ Real.rpow_pos_of_pos (hTpos ω) k) hTk h1
  rw [IsFixedPt, weibullMap, ← hU, hmean false h0, ← hmean true h1, e1,
    mul_div_cancel_right₀ _ hC.ne', Real.log_exp, mul_div_cancel_right₀ _ hk.ne']

variable (M μ) in
/-- The control arm power mean part of the Weibull update, `E[U(ψ)^k | R = 0]`. -/
noncomputable def powControl (k ψ : ℝ) : ℝ :=
  M.armMean μ (fun ω ↦ M.counterfactual ψ ω ^ k) false

theorem powControl_pos [IsFiniteMeasure μ] (hTm : Measurable M.T) (hTem : Measurable M.Te)
    (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 ≤ k)
    (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ) (h0 : μ (M.arm false) ≠ 0) (ψ : ℝ) :
    0 < M.powControl μ k ψ :=
  armMean_pos (fun ω ↦ Real.rpow_pos_of_pos (counterfactual_pos hwf hTpos ψ ω) k)
    (integrable_rpow_counterfactual hTm hTem hwf hTpos hk hTk ψ) h0

theorem weibullMap_eq [IsFiniteMeasure μ] (hTm : Measurable M.T) (hTem : Measurable M.Te)
    (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 ≤ k)
    (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (ψ : ℝ) :
    M.weibullMap μ k ψ = (Real.log (M.powControl μ k ψ) -
      Real.log (M.armMean μ (fun ω ↦ M.T ω ^ k) true)) / k := by
  change Real.log (M.powControl μ k ψ / M.armMean μ (fun ω ↦ M.T ω ^ k) true) / k = _
  rw [Real.log_div (powControl_pos hTm hTem hwf hTpos hk hTk h0 ψ).ne'
    (armMean_pos (fun ω ↦ Real.rpow_pos_of_pos (hTpos ω) k) hTk h1).ne']

/-- **The Weibull update is nondecreasing** for a shape `k > 0`. -/
theorem monotone_weibullMap [IsFiniteMeasure μ] (hTm : Measurable M.T) (hTem : Measurable M.Te)
    (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 < k)
    (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) : Monotone (M.weibullMap μ k) := by
  intro ψ ψ' h
  have hi := fun x ↦ Mediation.integrable_cond_of_integrable
    (integrable_rpow_counterfactual hTm hTem hwf hTpos hk.le hTk x) h0
  have hA : M.powControl μ k ψ ≤ M.powControl μ k ψ' :=
    integral_mono (hi ψ) (hi ψ') fun ω ↦ Real.rpow_le_rpow
      (counterfactual_pos hwf hTpos ψ ω).le (counterfactual_mono hwf.te_nonneg h ω) hk.le
  rw [weibullMap_eq hTm hTem hwf hTpos hk.le hTk h1 h0,
    weibullMap_eq hTm hTem hwf hTpos hk.le hTk h1 h0]
  exact div_le_div_of_nonneg_right (sub_le_sub_right
    (Real.log_le_log (powControl_pos hTm hTem hwf hTpos hk.le hTk h0 ψ) hA) _) hk.le

/-- **The Weibull update has slope below one** when the control patients with positive time off
the experimental treatment have positive probability: `weibullMap k ψ' - weibullMap k ψ < ψ' - ψ`
for `ψ < ψ'`. -/
theorem weibullMap_sub_lt [IsFiniteMeasure μ] (hR : Measurable M.R) (hTm : Measurable M.T)
    (hTem : Measurable M.Te) (hwf : M.WellFormed) (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ}
    (hk : 0 < k) (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) {ψ ψ' : ℝ}
    (h : ψ < ψ') : M.weibullMap μ k ψ' - M.weibullMap μ k ψ < ψ' - ψ := by
  have hint := fun x ↦ integrable_rpow_counterfactual hTm hTem hwf hTpos hk.le hTk x
  have hi := fun x ↦ Mediation.integrable_cond_of_integrable (hint x) h0
  have hpt : ∀ ω, Real.exp (ψ' - ψ) ^ k * M.counterfactual ψ ω ^ k =
      (Real.exp (ψ' - ψ) * M.counterfactual ψ ω) ^ k := fun ω ↦
    (Real.mul_rpow (Real.exp_pos _).le (counterfactual_pos hwf hTpos ψ ω).le).symm
  have key : M.powControl μ k ψ' <
      M.armMean μ (fun ω ↦ Real.exp (ψ' - ψ) ^ k * M.counterfactual ψ ω ^ k) false := by
    refine integral_lt_of_le_of_lt (hi ψ') ((hi ψ).const_mul _) (fun ω ↦ ?_)
      (cond_Tc_pos_ne_zero hR hpos) fun ω hω ↦ ?_
    · rw [hpt]
      exact Real.rpow_le_rpow (counterfactual_pos hwf hTpos ψ' ω).le
        (counterfactual_le_exp_mul hwf h.le ω) hk.le
    · rw [hpt]
      exact Real.rpow_lt_rpow (counterfactual_pos hwf hTpos ψ' ω).le
        (counterfactual_lt_exp_mul h hω) hk
  rw [armMean, integral_const_mul, ← Real.exp_mul] at key
  have key' : M.powControl μ k ψ' < Real.exp ((ψ' - ψ) * k) * M.powControl μ k ψ := key
  have hA := powControl_pos hTm hTem hwf hTpos hk.le hTk h0 ψ
  have hlog := Real.log_lt_log (powControl_pos hTm hTem hwf hTpos hk.le hTk h0 ψ') key'
  rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp] at hlog
  rw [weibullMap_eq hTm hTem hwf hTpos hk.le hTk h1 h0,
    weibullMap_eq hTm hTem hwf hTpos hk.le hTk h1 h0, ← sub_div, div_lt_iff₀ hk]
  linarith

/-- **Uniqueness and convergence of the Weibull iteration.** For a shape `k > 0`, with
`0 ≤ T^e ≤ T`, `T > 0`, measurable `R`, `T`, `T^e`, integrable `T^k`, both arms of positive
probability and control patients with positive time off the experimental treatment of positive
probability, a fixed point `p` of `weibullMap k` is unique and the iteration converges to it
from every starting value. -/
theorem tendsto_iterate_weibullMap [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 < k) (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0)
    (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) {p : ℝ}
    (hp : IsFixedPt (M.weibullMap μ k) p) :
    (∀ q, IsFixedPt (M.weibullMap μ k) q → q = p) ∧
      ∀ ψ, Tendsto (fun n ↦ (M.weibullMap μ k)^[n] ψ) atTop (𝓝 p) :=
  fixedPt_unique_and_tendsto_of_slope_lt (monotone_weibullMap hTm hTem hwf hTpos hk hTk h1 h0)
    (fun _ _ h ↦ weibullMap_sub_lt hR hTm hTem hwf hTpos hk hTk h1 h0 hpos h) hp

/-- **Convergence of the Weibull iteration to the true parameter.** Under the hypotheses of
`isFixedPt_weibullMap_trueParam` and positive probability of control patients with positive
time off the experimental treatment, `ψ₀` is the only fixed point of `weibullMap k` and the
iteration converges to it from every starting value. -/
theorem tendsto_iterate_weibullMap_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R)
    (hTm : Measurable M.T) (hTem : Measurable M.Te) {ψ₀ : ℝ} (h : M.CommonEffect ψ₀)
    (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated) (hwf : M.WellFormed)
    (hTpos : ∀ ω, 0 < M.T ω) {k : ℝ} (hk : 0 < k) (hTk : Integrable (fun ω ↦ M.T ω ^ k) μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0)
    (hpos : μ (M.arm false ∩ {ω | 0 < M.Tc ω}) ≠ 0) :
    (∀ q, IsFixedPt (M.weibullMap μ k) q → q = ψ₀) ∧
      ∀ ψ, Tendsto (fun n ↦ (M.weibullMap μ k)^[n] ψ) atTop (𝓝 ψ₀) :=
  tendsto_iterate_weibullMap hR hTm hTem hwf hTpos hk hTk h1 h0 hpos
    (isFixedPt_weibullMap_trueParam hR hTm hTem h hrand hfull hwf hTpos hk hTk h1 h0)

end SwitchingTrial

/-! ### Counterexamples -/

namespace IPECounterexample

open SwitchingTrial RPSFTMCounterexample CausalInference.Mediation.Counterexample

/-! #### The two contrasts differ away from the common fixed point -/

namespace Scaled

/-- The time ratio is `1/2` for everyone and the untreated time is `2 s`. Experimental patients
are on treatment throughout (observed `4 s`). Control patients of the good type never switch
(observed `4`); those of the poor type switch at time `1` and survive to `3`. -/
noncomputable def trial : SwitchingTrial Ω₀ where
  R ω := ω.1
  T ω := if ω.1 then 4 * scale ω else if ω.2.1 then 4 else 3
  Te ω := if ω.1 then 4 * scale ω else if ω.2.1 then 0 else 2
  U ω := 2 * scale ω

theorem commonEffect : trial.CommonEffect (Real.log (1 / 2)) := by
  intro ω
  obtain ⟨a, u, v⟩ := ω
  rw [Real.exp_log (by norm_num)]
  cases a <;> cases u <;> norm_num [trial, scale, Tc]

theorem randomized : trial.Randomized μ₀ :=
  randomized_of_eq trial (fun _ ↦ rfl) (fun x ↦ 2 * if x.1 then 2 else 1) fun _ ↦ rfl

theorem fullyTreated : trial.ExpFullyTreated := fun ω hω ↦ by
  have : ω.1 = true := hω
  simp [trial, this]

theorem wellFormed : trial.WellFormed where
  te_nonneg ω := by obtain ⟨a, u, v⟩ := ω; cases a <;> cases u <;> norm_num [trial, scale]
  te_le ω := by obtain ⟨a, u, v⟩ := ω; cases a <;> cases u <;> norm_num [trial, scale]

theorem T_pos (ω : Ω₀) : 0 < trial.T ω := by
  obtain ⟨a, u, v⟩ := ω; cases a <;> cases u <;> norm_num [trial, scale]

theorem timeOff_ne_zero : μ₀ (trial.arm false ∩ {ω | 0 < trial.Tc ω}) ≠ 0 :=
  μ₀_ne_zero_of_mem (ω := (false, false, false)) (by norm_num [SwitchingTrial.arm, trial, Tc])

/-- **Counterexample: the two updates are different maps.** At `ψ = 0` (the ITT fit) the ratio
of means update is `log (7/12)` and the log-time update is `(log 3 - log 8) / 2`; they differ.
Both have `log (1/2)` as their only fixed point. -/
theorem same_fixedPt_different_maps :
    trial.ipeMap μ₀ 0 = Real.log (7 / 12) ∧
      trial.logMap μ₀ 0 = (Real.log 3 - Real.log 8) / 2 ∧
      trial.ipeMap μ₀ 0 ≠ trial.logMap μ₀ 0 ∧
      (∀ ψ, IsFixedPt (trial.ipeMap μ₀) ψ ↔ ψ = Real.log (1 / 2)) ∧
      ∀ ψ, IsFixedPt (trial.logMap μ₀) ψ ↔ ψ = Real.log (1 / 2) := by
  have hR : Measurable trial.R := measurable_of_countable _
  have h1 := arm_ne_zero trial (fun _ ↦ rfl) true
  have h0 := arm_ne_zero trial (fun _ ↦ rfl) false
  have e1 : trial.ipeMap μ₀ 0 = Real.log (7 / 12) := by
    rw [ipeMap_zero, armMean_μ₀ trial (fun _ ↦ rfl), armMean_μ₀ trial (fun _ ↦ rfl)]
    norm_num [trial, scale]
  have e2 : trial.logMap μ₀ 0 = (Real.log 3 - Real.log 8) / 2 := by
    rw [logMap, counterfactual_zero, armMean_μ₀ trial (fun _ ↦ rfl),
      armMean_μ₀ trial (fun _ ↦ rfl)]
    norm_num [trial, scale]
    ring
  refine ⟨e1, e2, ?_, fun ψ ↦ ?_, fun ψ ↦ ?_⟩
  · rw [e1, e2]
    intro h
    have hl : Real.log ((7 / 12) ^ 2) = Real.log (3 / 8) := by
      rw [Real.log_pow, h, Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)]
      push_cast; ring
    have := Real.log_injOn_pos (by norm_num : ((7 : ℝ) / 12) ^ 2 ∈ Ioi 0)
      (by norm_num : (3 / 8 : ℝ) ∈ Ioi 0) hl
    norm_num at this
  · exact isFixedPt_ipeMap_iff_trueParam hR commonEffect randomized fullyTreated
      wellFormed.te_nonneg Integrable.of_finite Integrable.of_finite h1 h0
      (by rw [armMean_μ₀ trial (fun _ ↦ rfl)]; norm_num [trial, scale, Tc]) ψ
  · have := tendsto_iterate_logMap_trueParam hR (measurable_of_countable _)
      (measurable_of_countable _) commonEffect randomized fullyTreated wellFormed T_pos
      Integrable.of_finite h1 h0 timeOff_ne_zero
    exact ⟨this.1 ψ, fun e ↦ e ▸ isFixedPt_logMap_trueParam hR (measurable_of_countable _)
      (measurable_of_countable _) commonEffect randomized fullyTreated wellFormed T_pos
      Integrable.of_finite h1 h0⟩

end Scaled

/-! #### Without the scale relation the two contrasts disagree -/

namespace Discontinued

theorem wellFormed : trial.WellFormed where
  te_nonneg ω := by obtain ⟨a, u, v⟩ := ω; cases a <;> cases u <;> norm_num [trial, scale]
  te_le ω := by obtain ⟨a, u, v⟩ := ω; cases a <;> cases u <;> norm_num [trial, scale]

theorem T_pos (ω : Ω₀) : 0 < trial.T ω := by
  obtain ⟨a, u, v⟩ := ω; cases a <;> cases u <;> norm_num [trial, scale]

theorem timeOff_ne_zero : μ₀ (trial.arm false ∩ {ω | 0 < trial.Tc ω}) ≠ 0 :=
  μ₀_ne_zero_of_mem (ω := (false, false, false)) (by norm_num [SwitchingTrial.arm, trial, Tc])

/-- The log-time update is `ψ ↦ (log (1 + 2 exp ψ) + log 4 - log 3 - log 6) / 2`. -/
theorem logMap_eq (ψ : ℝ) :
    trial.logMap μ₀ ψ =
      (Real.log (1 + 2 * Real.exp ψ) + Real.log 4 - Real.log 3 - Real.log 6) / 2 := by
  rw [logMap, armMean_μ₀ trial (fun _ ↦ rfl), armMean_μ₀ trial (fun _ ↦ rfl)]
  norm_num [trial, scale, counterfactual, Tc]
  ring_nf

/-- The fixed points of the log-time update are the `ψ` with `9 x ^ 2 - 4 x - 2 = 0`,
`x = exp ψ`. -/
theorem isFixedPt_logMap_iff (ψ : ℝ) :
    IsFixedPt (trial.logMap μ₀) ψ ↔ 9 * Real.exp ψ ^ 2 - 4 * Real.exp ψ - 2 = 0 := by
  have hx := Real.exp_pos ψ
  have hP : Real.log (4 * (1 + 2 * Real.exp ψ)) = Real.log 4 + Real.log (1 + 2 * Real.exp ψ) :=
    Real.log_mul (by norm_num) (by positivity)
  have hQ : Real.log (18 * Real.exp ψ ^ 2) = Real.log 3 + Real.log 6 + 2 * ψ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_exp,
      show (18 : ℝ) = 3 * 6 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    push_cast; ring
  rw [IsFixedPt, logMap_eq]
  constructor
  · intro h
    have hl : Real.log (4 * (1 + 2 * Real.exp ψ)) = Real.log (18 * Real.exp ψ ^ 2) := by
      rw [hP, hQ]; linarith
    have := Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
      (by simp only [mem_Ioi]; positivity) hl
    linarith
  · intro h
    have hl : Real.log (4 * (1 + 2 * Real.exp ψ)) = Real.log (18 * Real.exp ψ ^ 2) := by
      congr 1; linarith
    rw [hP, hQ] at hl
    linarith

/-- **Counterexample: without the scale relation the contrasts disagree.** In the trial with
experimental discontinuation (randomization and the common effect with time ratio `1/2` hold),
the log-time update has the unique fixed point `log x₀` with `x₀ = (2 + √22) / 9`, the root of
`9 x ^ 2 - 4 x - 2 = 0`, and converges to it from every start. Its time ratio is neither the
ratio of means fixed point `5/7` nor the truth `1/2`. -/
theorem logMap_fixedPt :
    IsFixedPt (trial.logMap μ₀) (Real.log ((2 + Real.sqrt 22) / 9)) ∧
      (∀ q, IsFixedPt (trial.logMap μ₀) q → q = Real.log ((2 + Real.sqrt 22) / 9)) ∧
      (∀ ψ, Tendsto (fun k ↦ (trial.logMap μ₀)^[k] ψ) atTop
        (𝓝 (Real.log ((2 + Real.sqrt 22) / 9)))) ∧
      ∀ ψ, IsFixedPt (trial.logMap μ₀) ψ → Real.exp ψ ≠ 5 / 7 ∧ Real.exp ψ ≠ 1 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22)
  have hx0 : 0 < (2 + Real.sqrt 22) / 9 := by positivity
  have hp : IsFixedPt (trial.logMap μ₀) (Real.log ((2 + Real.sqrt 22) / 9)) := by
    rw [isFixedPt_logMap_iff, Real.exp_log hx0]
    linear_combination hs / 9
  have hconv := tendsto_iterate_logMap (measurable_of_countable _) (measurable_of_countable _)
    (measurable_of_countable _) wellFormed T_pos Integrable.of_finite
    (arm_ne_zero trial (fun _ ↦ rfl) false) timeOff_ne_zero hp
  refine ⟨hp, hconv.1, hconv.2, fun ψ hψ ↦ ?_⟩
  rw [isFixedPt_logMap_iff] at hψ
  constructor <;> intro h <;> rw [h] at hψ <;> norm_num at hψ

end Discontinued

/-! #### A trial in which the iteration does not converge -/

namespace Diverging

/-- Experimental patients are on treatment throughout and survive `s`; control patients are off
treatment for `s`, then on the experimental treatment for `2 s` (observed `3 s`). The latent
untreated time is the one of the common effect with time ratio `1/2`. -/
noncomputable def trial : SwitchingTrial Ω₀ where
  R ω := ω.1
  T ω := if ω.1 then scale ω else 3 * scale ω
  Te ω := if ω.1 then scale ω else 2 * scale ω
  U ω := if ω.1 then scale ω / 2 else 2 * scale ω

theorem commonEffect : trial.CommonEffect (Real.log (1 / 2)) := by
  intro ω
  obtain ⟨a, u, v⟩ := ω
  rw [Real.exp_log (by norm_num)]
  cases a <;> cases u <;> norm_num [trial, scale, Tc]

theorem fullyTreated : trial.ExpFullyTreated := fun ω hω ↦ by
  have : ω.1 = true := hω
  simp [trial, this]

/-- `E[T^c | R = 0] = 3/2`, `E[T | R = 1] = 3/2` and `E[T^e | R = 0] = 3`, so
`E[T | R = 1] ≤ E[T^e | R = 0]`. -/
theorem armMeans :
    trial.armMean μ₀ trial.Tc false = 3 / 2 ∧ trial.armMean μ₀ trial.T true = 3 / 2 ∧
      trial.armMean μ₀ trial.Te false = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [armMean_μ₀ trial (fun _ ↦ rfl)] <;> norm_num [trial, scale, Tc]

/-- **Counterexample: the iteration converges from no starting value.** The update has no fixed
point. -/
theorem not_tendsto (ψ L : ℝ) :
    ¬ Tendsto (fun k ↦ (trial.ipeMap μ₀)^[k] ψ) atTop (𝓝 L) := by
  obtain ⟨ha, hc, hb⟩ := armMeans
  exact not_tendsto_iterate_ipeMap Integrable.of_finite Integrable.of_finite
    (arm_ne_zero trial (fun _ ↦ rfl) false) (by rw [ha]; norm_num) (by rw [hc]; norm_num)
    (by rw [hc, hb]; norm_num) ψ L

/-- **The data contradict the model with randomization.** For any latent untreated time `U'`
attached to these observed data (the experimental arm is fully treated), if the common effect
holds with some `ψ` then randomization fails. -/
theorem not_randomized_of_commonEffect (U' : Ω₀ → ℝ) (ψ : ℝ)
    (h : ({ trial with U := U' } : SwitchingTrial Ω₀).CommonEffect ψ) :
    ¬ ({ trial with U := U' } : SwitchingTrial Ω₀).Randomized μ₀ := by
  intro hr
  have := armMean_Te_false_lt (M := { trial with U := U' }) (μ := μ₀)
    (measurable_of_countable _) h hr fullyTreated Integrable.of_finite Integrable.of_finite
    (arm_ne_zero _ (fun _ ↦ rfl) true) (arm_ne_zero _ (fun _ ↦ rfl) false)
    (by rw [armMean_μ₀ _ (fun _ ↦ rfl)]; norm_num [trial, scale, Tc])
  rw [armMean_μ₀ _ (fun _ ↦ rfl), armMean_μ₀ _ (fun _ ↦ rfl)] at this
  norm_num [trial, scale] at this

/-- In particular the trial's own untreated time, which satisfies the common effect, is not
independent of the arm: randomization is the hypothesis that fails. -/
theorem not_randomized : ¬ trial.Randomized μ₀ :=
  not_randomized_of_commonEffect trial.U _ commonEffect

end Diverging

end IPECounterexample

end StructuralNested

end CausalInference
