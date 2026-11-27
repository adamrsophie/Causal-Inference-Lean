/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageAssumptions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Two-stage estimation: the parametric (Weibull) stage one

TSD 16 (Section 3.2.4) and TSD 24 (Section 4.2.3) fit a parametric accelerated failure time
model, usually Weibull, to the time after the secondary baseline in the control arm, with the
switch indicator as covariate, and use the fitted acceleration factor as the time ratio of
switching. This file states that fit at the population level on a finite law and proves what it
returns. The model has no covariate besides the switch indicator; the fit adjusts for covariates
at the secondary baseline only through the choice of the population `P`. Stratum intercepts
for covariates are in `TwoStageWeibullStrata`.

## Main results

* `TwoStageTrial.weibullLogLik`, `TwoStageTrial.hasDerivAt_weibullLogLik`: the log-likelihood
  of the Weibull model with shape `k` and scale `exp (b₀ + b₁ X)`, and its scores
  `weibullScore₀`, `weibullScore₁` as derivatives.
* `TwoStageTrial.weibullScores_eq_zero_iff`, `TwoStageTrial.weibull_coef_eq`: for a given shape,
  the fitted scales are the `k`-th power means of each switch group, and the fitted coefficient
  is `b₁ = log (E[(T - S)^k | X = 1] / E[(T - S)^k | X = 0]) / k`.
* `TwoStageTrial.weibull_coef_eq_neg`: under the structural model in the baseline form, no
  unmeasured confounding for the `k`-th power of the untreated time after the secondary
  baseline, positivity and `T > S`, the fitted acceleration factor is the true time ratio:
  `b₁ = -ψ`, for every shape `k > 0`. The distributional form of no unmeasured confounding gives
  the hypothesis for every `k` (`TwoStageTrial.weibull_nuc_of_condIndep`).
* `TwoStageTrial.weibull_one_iff_stageOne`, `TwoStageTrial.weibull_and_stageOne_root`: with
  shape `1` (the exponential model) the fit and the mean-balancing `stageOne` with a single
  stratum have the same root, with no assumption beyond positivity and `T > S`; under the
  assumptions above both are the truth; for every shape `k > 0`, under the distributional
  form of no unmeasured confounding, the fit and `stageOne` both return the truth
  (`TwoStageTrial.weibull_and_stageOne_root_of_condIndep`).

A Weibull law of the untreated time is not needed for `weibull_coef_eq_neg`: at the population
level the fit recovers the time ratio at every fixed shape, so at whatever shape is fitted. A
Weibull law matters for the fitted shape itself (and for the fit with censored data). The fit
with the shape estimated is in `TwoStageWeibullShape`; `SwitchingTrial.fittedShape` treats the
fitted shape in the two-arm setting. `TwoStageWeibullBridge` identifies this fit with
`SwitchingCounterexamples.TimeDependent.weibullFactor` on that countermodel.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageTrial

variable {Ω : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω]

/-- The switch indicator as a real covariate: `1` for adjusted switchers, `0` otherwise. -/
def switchCov (ω : Ω) : ℝ := if M.X ω then 1 else 0

/-- The linear predictor of the log scale, `b₀ + b₁ X`. -/
noncomputable def weibullPredictor (b₀ b₁ : ℝ) (ω : Ω) : ℝ := b₀ + b₁ * M.switchCov ω

/-- **The population log-likelihood of the Weibull accelerated failure time model** for the
time after the secondary baseline, `t = T - S`, with the switch indicator as covariate, shape
`k` and scale `exp (b₀ + b₁ X)`: the log-density
`log k - k η + (k - 1) log t - t^k exp (-k η)`, with `η = b₀ + b₁ X` (here `(t / exp η)^k` is
written `t^k exp (-k η)`), averaged over `P` under `p`. The acceleration factor of switching
(time ratio of switchers against non-switchers) is `exp b₁`. -/
noncomputable def weibullLogLik (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) : ℝ :=
  wsum p P fun ω =>
    Real.log k - k * M.weibullPredictor b₀ b₁ ω + (k - 1) * Real.log (M.T ω - M.S ω) -
      (M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω))

/-- The score of the intercept `b₀`. -/
noncomputable def weibullScore₀ (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) : ℝ :=
  wsum p P fun ω =>
    k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1)

/-- The score of the coefficient `b₁` of the switch indicator. -/
noncomputable def weibullScore₁ (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) : ℝ :=
  wsum p P fun ω =>
    k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1) *
      M.switchCov ω

omit [Fintype Ω] [DecidableEq Ω] in
/-- The derivative of one log-density term along a linear predictor `η` with `η' = x`. -/
theorem hasDerivAt_weibullTerm {η : ℝ → ℝ} {x b : ℝ} (hη : HasDerivAt η x b) (c k a : ℝ) :
    HasDerivAt (fun b => c - k * η b - a * Real.exp (-(k * η b)))
      (k * (a * Real.exp (-(k * η b)) - 1) * x) b := by
  have h1 := (hη.const_mul k).neg.exp.const_mul a
  have h2 := ((hη.const_mul k).const_sub c).sub h1
  convert h2 using 1
  simp only [Pi.neg_apply]
  ring

omit [DecidableEq Ω] in
/-- **The scores are the derivatives of the log-likelihood.** -/
theorem hasDerivAt_weibullLogLik (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) :
    HasDerivAt (fun b => M.weibullLogLik p P k b b₁) (M.weibullScore₀ p P k b₀ b₁) b₀ ∧
      HasDerivAt (M.weibullLogLik p P k b₀) (M.weibullScore₁ p P k b₀ b₁) b₁ := by
  constructor
  · unfold weibullLogLik weibullScore₀ wsum
    refine HasDerivAt.fun_sum fun ω _ => ?_
    have hη : HasDerivAt (fun b => M.weibullPredictor b b₁ ω) 1 b₀ := by
      simpa [weibullPredictor] using (hasDerivAt_id b₀).add_const (b₁ * M.switchCov ω)
    have := (hasDerivAt_weibullTerm hη (Real.log k + (k - 1) * Real.log (M.T ω - M.S ω)) k
      ((M.T ω - M.S ω) ^ k)).const_mul (p ω)
    convert this using 1
    · funext b; ring
    · ring
  · unfold weibullLogLik weibullScore₁ wsum
    refine HasDerivAt.fun_sum fun ω _ => ?_
    have hη : HasDerivAt (fun b => M.weibullPredictor b₀ b ω) (M.switchCov ω) b₁ := by
      simpa [weibullPredictor] using ((hasDerivAt_id b₁).mul_const (M.switchCov ω)).const_add b₀
    have := (hasDerivAt_weibullTerm hη (Real.log k + (k - 1) * Real.log (M.T ω - M.S ω)) k
      ((M.T ω - M.S ω) ^ k)).const_mul (p ω)
    convert this using 1
    funext b; ring

/-- The `k`-th power mean of the time after the secondary baseline in the switch group `x`
of `P`, `E[(T - S)^k | P, X = x]`. -/
noncomputable def powerMean (p : FiniteDist Ω) (P : Finset Ω) (k : ℝ) (x : Bool) : ℝ :=
  condMean p (P ∩ ev M.X x) fun ω => (M.T ω - M.S ω) ^ k

/-- The score restricted to a switch group. -/
theorem wsum_group (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) (x : Bool) :
    wsum p (P ∩ ev M.X x) (fun ω =>
        k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1)) =
      k * (Real.exp (-(k * (b₀ + b₁ * if x then 1 else 0))) *
        wsum p (P ∩ ev M.X x) (fun ω => (M.T ω - M.S ω) ^ k) - wmass p (P ∩ ev M.X x)) := by
  have e : ∀ ω ∈ P ∩ ev M.X x,
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1) =
        k * Real.exp (-(k * (b₀ + b₁ * if x then 1 else 0))) * (M.T ω - M.S ω) ^ k +
          (-k) * 1 := fun ω hω => by
    have hx : M.X ω = x := mem_ev.1 (mem_inter.1 hω).2
    simp only [weibullPredictor, switchCov, hx]
    ring
  rw [wsum_congr e]
  simp only [wsum, wmass, mul_sub, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- The scores split over the switch groups. -/
theorem weibullScores_eq (p : FiniteDist Ω) (P : Finset Ω) (k b₀ b₁ : ℝ) :
    M.weibullScore₁ p P k b₀ b₁ =
        k * (Real.exp (-(k * (b₀ + b₁))) *
          wsum p (P ∩ ev M.X true) (fun ω => (M.T ω - M.S ω) ^ k) -
            wmass p (P ∩ ev M.X true)) ∧
      M.weibullScore₀ p P k b₀ b₁ - M.weibullScore₁ p P k b₀ b₁ =
        k * (Real.exp (-(k * b₀)) *
          wsum p (P ∩ ev M.X false) (fun ω => (M.T ω - M.S ω) ^ k) -
            wmass p (P ∩ ev M.X false)) := by
  have g1 := M.wsum_group p P k b₀ b₁ true
  have g0 := M.wsum_group p P k b₀ b₁ false
  simp only [ite_true, mul_one, Bool.false_eq_true, ite_false, mul_zero, add_zero] at g1 g0
  have s1 := wsum_eq_sum_ev (m := p) P M.X (fun ω =>
    k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1) *
      M.switchCov ω)
  have s0 := wsum_eq_sum_ev (m := p) P M.X (fun ω =>
    k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1))
  simp only [Fintype.sum_bool] at s1 s0
  have c1 : wsum p (P ∩ ev M.X true) (fun ω =>
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1) *
        M.switchCov ω) = wsum p (P ∩ ev M.X true) (fun ω =>
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1)) :=
    wsum_congr fun ω hω => by
      have hx : M.X ω = true := mem_ev.1 (mem_inter.1 hω).2
      simp [switchCov, hx]
  have c0 : wsum p (P ∩ ev M.X false) (fun ω =>
      k * ((M.T ω - M.S ω) ^ k * Real.exp (-(k * M.weibullPredictor b₀ b₁ ω)) - 1) *
        M.switchCov ω) = 0 := by
    rw [wsum_congr (g := fun _ => 0) fun ω hω => by
      have hx : M.X ω = false := mem_ev.1 (mem_inter.1 hω).2
      simp [switchCov, hx]]
    simp [wsum]
  refine ⟨?_, ?_⟩
  · rw [weibullScore₁, s1, c1, c0, g1, add_zero]
  · rw [weibullScore₀, weibullScore₁, s0, s1, c1, c0, g1, g0]
    ring

/-- **The Weibull fit.** For a shape `k ≠ 0` and both switch groups of positive mass, the
scores vanish exactly when `exp (k b₀)` is the power mean of the non-switchers and
`exp (k (b₀ + b₁))` the power mean of the switchers: the maximum likelihood scales are the
`k`-th power means of each group. -/
theorem weibullScores_eq_zero_iff (p : FiniteDist Ω) (P : Finset Ω) {k : ℝ} (hk : k ≠ 0)
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false)) (b₀ b₁ : ℝ) :
    M.weibullScore₀ p P k b₀ b₁ = 0 ∧ M.weibullScore₁ p P k b₀ b₁ = 0 ↔
      Real.exp (k * b₀) = M.powerMean p P k false ∧
        Real.exp (k * (b₀ + b₁)) = M.powerMean p P k true := by
  obtain ⟨e1, e0⟩ := M.weibullScores_eq p P k b₀ b₁
  have key : ∀ (a w m : ℝ), 0 < m →
      (k * (Real.exp (-a) * w - m) = 0 ↔ Real.exp a = w / m) := fun a w m hm => by
    rw [mul_eq_zero, or_iff_right hk, sub_eq_zero, eq_div_iff hm.ne', Real.exp_neg]
    have := Real.exp_pos a
    constructor
    · intro h; field_simp at h; linarith
    · intro h; field_simp; linarith
  rw [powerMean, powerMean, condMean, condMean, ← key _ _ _ h0, ← key _ _ _ h1, ← e1, ← e0]
  constructor
  · rintro ⟨a, b⟩; exact ⟨by rw [a, b, sub_zero], b⟩
  · rintro ⟨a, b⟩; exact ⟨by linarith, b⟩

/-- **The fitted acceleration factor**: at the maximum likelihood fit, the coefficient of the
switch indicator is `log (E[(T - S)^k | switchers] / E[(T - S)^k | non-switchers]) / k`. -/
theorem weibull_coef_eq (p : FiniteDist Ω) (P : Finset Ω) {k : ℝ} (hk : k ≠ 0)
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false)) {b₀ b₁ : ℝ}
    (hfit : M.weibullScore₀ p P k b₀ b₁ = 0 ∧ M.weibullScore₁ p P k b₀ b₁ = 0) :
    b₁ = Real.log (M.powerMean p P k true / M.powerMean p P k false) / k := by
  obtain ⟨a, b⟩ := (M.weibullScores_eq_zero_iff p P hk h1 h0 b₀ b₁).1 hfit
  rw [← a, ← b, ← Real.exp_sub, Real.log_exp]
  field_simp
  ring

omit [DecidableEq Ω] in
/-- A weighted sum of a positive function over an event of positive mass is positive. -/
theorem wsum_pos_of_pos {p : FiniteDist Ω} {s : Finset Ω} {f : Ω → ℝ}
    (hf : ∀ ω ∈ s, 0 < f ω) (hm : 0 < wmass p s) : 0 < wsum p s f := by
  have : ∃ ω ∈ s, 0 < p ω := by
    by_contra hc
    push Not at hc
    have := sum_nonpos hc
    rw [wmass] at hm
    linarith
  obtain ⟨ω, hω, hp⟩ := this
  exact sum_pos' (fun ω hω => mul_nonneg (p.nonneg ω) (hf ω hω).le) ⟨ω, hω, mul_pos hp (hf ω hω)⟩

/-- **The Weibull fit recovers the true time ratio.** Suppose the structural model holds on `P`
in the baseline form (`ModelOn P S ψ`: switchers have `U - S = exp ψ (T - S)`), the
`k`-th power of the untreated time after the secondary baseline is mean independent of the
switch in `P` (no unmeasured confounding; it follows from the distributional form,
`weibull_nuc_of_condIndep`), both switch groups have positive mass, and `T > S` on `P`. Then
for every shape `k > 0`, at the maximum likelihood fit of the Weibull accelerated failure time
model the coefficient of the switch indicator is `-ψ`: the fitted acceleration factor
`exp b₁` is the true time ratio `exp (-ψ)`. No Weibull law of the untreated time is needed;
it holds at whatever shape is fitted. -/
theorem weibull_coef_eq_neg {p : FiniteDist Ω} {P : Finset Ω} {ψ k : ℝ} (hk : 0 < k)
    (hmodel : M.ModelOn P M.S ψ)
    (hnuc : MeanIndepOn p P (ev M.X true) fun ω => (M.U ω - M.S ω) ^ k)
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) {b₀ b₁ : ℝ}
    (hfit : M.weibullScore₀ p P k b₀ b₁ = 0 ∧ M.weibullScore₁ p P k b₀ b₁ = 0) :
    b₁ = -ψ := by
  rw [M.weibull_coef_eq p P hk.ne' h1 h0 hfit]
  have hU : ∀ x, ∀ ω ∈ P ∩ ev M.X x,
      (M.U ω - M.S ω) ^ k = (if x then Real.exp (ψ * k) else 1) * (M.T ω - M.S ω) ^ k := by
    intro x ω hω
    have hP := (mem_inter.1 hω).1
    have hx : M.X ω = x := mem_ev.1 (mem_inter.1 hω).2
    rw [hmodel ω hP]
    cases x
    · rw [M.adjusted_of_not_switch _ _ hx]; simp
    · rw [M.adjusted_of_switch _ _ hx, add_sub_cancel_left,
        Real.mul_rpow (Real.exp_pos _).le (sub_pos.2 (htime ω hP)).le, ← Real.exp_mul]
      simp
  have e1 : condMean p (P ∩ ev M.X true) (fun ω => (M.U ω - M.S ω) ^ k) =
      Real.exp (ψ * k) * M.powerMean p P k true := by
    rw [powerMean, condMean, condMean, wsum_congr (hU true), mul_div_assoc', wsum, wsum,
      mul_sum]
    simp only [ite_true]
    congr 1
    exact sum_congr rfl fun _ _ => by ring
  have e0 : condMean p (P ∩ ev M.X false) (fun ω => (M.U ω - M.S ω) ^ k) =
      M.powerMean p P k false := by
    rw [powerMean, condMean, condMean, wsum_congr (hU false)]
    simp
  have hpos : 0 < M.powerMean p P k false := by
    rw [powerMean, condMean]
    exact div_pos (wsum_pos_of_pos (fun ω hω => Real.rpow_pos_of_pos
      (sub_pos.2 (htime ω (mem_inter.1 hω).1)) k) h0) h0
  have heq := M.condMean_switch_eq (show MeanIndepOn p (P ∩ ev M.X true ∪ P) (ev M.X true)
    (fun ω => (M.U ω - M.S ω) ^ k) by rwa [union_eq_right.2 inter_subset_left]) (by
      rwa [union_eq_right.2 inter_subset_left]) (by rwa [union_eq_right.2 inter_subset_left])
  rw [union_eq_right.2 inter_subset_left, e1, e0] at heq
  rw [show M.powerMean p P k true = Real.exp (-(ψ * k)) * M.powerMean p P k false by
    rw [← heq, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul],
    mul_div_cancel_right₀ _ hpos.ne', Real.log_exp]
  field_simp

/-- No unmeasured confounding in distributional form (with no covariate besides the switch)
gives the mean independence of every power of the untreated time after the secondary
baseline. -/
theorem weibull_nuc_of_condIndep {p : FiniteDist Ω} {P : Finset Ω}
    (h : M.BaselineCondIndep p P fun _ => ()) (k : ℝ) :
    MeanIndepOn p P (ev M.X true) fun ω => (M.U ω - M.S ω) ^ k := by
  have e : P = ev (fun ω => (decide (ω ∈ P), ())) (true, ()) := by
    ext ω; simp
  rw [e]
  exact meanIndepOn_of_condIndepFun h (fun t => t ^ k) true (true, ())

/-- **The exponential fit is the mean-balancing stage one.** With shape `1`, a single stratum
and the baseline form, the maximum likelihood coefficient `b₁` of the switch indicator is `-ψ`
exactly when `ψ` is a root of the mean-balancing stage-one equation `stageOne`. -/
theorem weibull_one_iff_stageOne {p : FiniteDist Ω} {P : Finset Ω}
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) {b₀ b₁ : ℝ}
    (hfit : M.weibullScore₀ p P 1 b₀ b₁ = 0 ∧ M.weibullScore₁ p P 1 b₀ b₁ = 0) (ψ : ℝ) :
    b₁ = -ψ ↔ M.stageOne p P (fun _ => ()) (fun _ => 1) M.S ψ = 0 := by
  rw [M.weibull_coef_eq p P one_ne_zero h1 h0 hfit, div_one]
  have hc : ∀ x, M.cell P (fun _ => ()) x () = P ∩ ev M.X x := fun x => by
    ext ω; simp [cell, ev]
  have hr : ∀ x, ∀ ω ∈ P ∩ ev M.X x, M.resid M.S ψ ω =
      (if x then Real.exp ψ else 1) * (M.T ω - M.S ω) ^ (1 : ℝ) := fun x ω hω => by
    have hx : M.X ω = x := mem_ev.1 (mem_inter.1 hω).2
    rw [Real.rpow_one, resid]
    cases x
    · rw [M.adjusted_of_not_switch _ _ hx]; simp
    · rw [M.adjusted_of_switch _ _ hx]; simp
  have m1 : condMean p (P ∩ ev M.X true) (M.resid M.S ψ) =
      Real.exp ψ * M.powerMean p P 1 true := by
    rw [powerMean, condMean, condMean, wsum_congr (hr true), mul_div_assoc', wsum, wsum,
      mul_sum]
    simp only [ite_true]
    congr 1
    exact sum_congr rfl fun _ _ => by ring
  have m0 : condMean p (P ∩ ev M.X false) (M.resid M.S ψ) = M.powerMean p P 1 false := by
    rw [powerMean, condMean, condMean, wsum_congr (hr false)]
    simp
  have hpos : ∀ x, 0 < wmass p (P ∩ ev M.X x) → 0 < M.powerMean p P 1 x := fun x hm => by
    rw [powerMean, condMean]
    exact div_pos (wsum_pos_of_pos (fun ω hω => Real.rpow_pos_of_pos
      (sub_pos.2 (htime ω (mem_inter.1 hω).1)) 1) hm) hm
  have p1 := hpos true h1
  have p0 := hpos false h0
  rw [stageOne, Fintype.sum_unique, one_mul, show (default : Unit) = () from rfl, hc, hc, m1, m0,
    sub_eq_zero, Real.log_div p1.ne' p0.ne']
  constructor
  · intro h
    have : ψ = Real.log (M.powerMean p P 1 false) - Real.log (M.powerMean p P 1 true) := by
      linarith
    rw [this, Real.exp_sub, Real.exp_log p0, Real.exp_log p1]
    field_simp
  · intro h
    have : Real.exp ψ = M.powerMean p P 1 false / M.powerMean p P 1 true := by
      rw [eq_div_iff p1.ne']; exact h
    rw [← Real.log_exp ψ, this, Real.log_div p0.ne' p1.ne']
    ring

/-- **The parametric and the mean-balancing stage one have the same root.** Under the
assumptions of `weibull_coef_eq_neg` with shape `1`, stage one has the root `ψ` and the
exponential fit has the coefficient `-ψ`. -/
theorem weibull_and_stageOne_root {p : FiniteDist Ω} {P : Finset Ω} {ψ : ℝ}
    (hmodel : M.ModelOn P M.S ψ)
    (hnuc : MeanIndepOn p P (ev M.X true) fun ω => M.U ω - M.S ω)
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) {b₀ b₁ : ℝ}
    (hfit : M.weibullScore₀ p P 1 b₀ b₁ = 0 ∧ M.weibullScore₁ p P 1 b₀ b₁ = 0) :
    b₁ = -ψ ∧ M.stageOne p P (fun _ => ()) (fun _ => 1) M.S ψ = 0 := by
  have hb : b₁ = -ψ := M.weibull_coef_eq_neg one_pos hmodel
    (by simpa only [Real.rpow_one] using hnuc) h1 h0 htime hfit
  exact ⟨hb, (M.weibull_one_iff_stageOne h1 h0 htime hfit ψ).1 hb⟩

/-- **The Weibull fit at any shape and the mean-balancing stage one have the same root.** Under
the structural model in the baseline form, no unmeasured confounding in distributional form
with no covariate besides the switch, positivity and `T > S`, for every shape `k > 0` the fitted
coefficient of the switch indicator is `-ψ`, and `ψ` is the root of `stageOne` with a single
stratum. -/
theorem weibull_and_stageOne_root_of_condIndep {p : FiniteDist Ω} {P : Finset Ω} {ψ k : ℝ}
    (hk : 0 < k) (hmodel : M.ModelOn P M.S ψ) (hci : M.BaselineCondIndep p P fun _ => ())
    (h1 : 0 < wmass p (P ∩ ev M.X true)) (h0 : 0 < wmass p (P ∩ ev M.X false))
    (htime : ∀ ω ∈ P, M.S ω < M.T ω) {b₀ b₁ : ℝ}
    (hfit : M.weibullScore₀ p P k b₀ b₁ = 0 ∧ M.weibullScore₁ p P k b₀ b₁ = 0) :
    b₁ = -ψ ∧ M.stageOne p P (fun _ => ()) (fun _ => 1) M.S ψ = 0 := by
  have hc : ∀ x, M.cell P (fun _ => ()) x () = P ∩ ev M.X x := fun x => by
    ext ω; simp [cell, ev]
  refine ⟨M.weibull_coef_eq_neg hk hmodel (M.weibull_nuc_of_condIndep hci k) h1 h0 htime hfit,
    M.stageOne_eq_zero hmodel hci.baselineNUC fun _ _ => ?_⟩
  rw [hc, hc]; exact ⟨h1, h0⟩

end TwoStageTrial

end StructuralNested

end CausalInference
