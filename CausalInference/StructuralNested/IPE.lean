/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.RPSFTMCounterexamples
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Dynamics.FixedPoints.Topology

/-!
# Iterative parameter estimation

The iterative parameter estimation (IPE) procedure of Branson and Whitehead for the structural
failure time model of `CausalInference.StructuralNested.SwitchingTrial`, in the population: its
update map, the fixed point at the true parameter, uniqueness, convergence, and its relation to
the rank preserving g-estimation of `CausalInference.StructuralNested.RPSFTM`.

## The procedure and the contrast formalized

The documents (TSD 16, Section 3.2.3 and Appendix A, "IPE Algorithm"; TSD 24, Section 4.2.1)
describe the procedure as follows. A parametric failure time model fitted to the unadjusted ITT
data gives an initial `ψ`; the observed times of switching patients are re-estimated with
`exp ψ` and Equation A2; the treatment groups are compared again with the parametric model,
giving an updated `ψ`; the step is repeated until successive values of `exp ψ` agree. So only
the control arm is transformed, and the experimental arm is compared as observed. The RPSFTM
instead transforms both arms to their untreated times and asks for equality.

The comparison formalized is the time ratio of an accelerated failure time model between the
observed experimental arm and the transformed control arm, measured by the ratio of arm means:
`ipeMap ψ = log (E[U(ψ) | R = 0] / E[T | R = 1])`. This is the population target of the maximum
likelihood fit of an exponential accelerated failure time model with the arm as covariate to
uncensored data, and it equals the time ratio whenever the two arms differ by a change of time
scale. At the true parameter the transformed control arm and the experimental arm differ
exactly by such a change of scale, the situation in which accelerated failure time fits
estimate the time ratio; away from it other parametric fits (Weibull, log-normal) give other
maps, which are not formalized. Censoring is not modeled.

## Main definitions

* `SwitchingTrial.ipeMap`: the update map; `ipeMap 0` is the ITT fit (`ipeMap_zero`).
* `SwitchingTrial.ipeRatio`: the same update on the scale `x = exp ψ` of the stopping rule,
  `x ↦ (E[T^c | R = 0] + x E[T^e | R = 0]) / E[T | R = 1]`, an affine map
  (`ipeMap_eq`: `ipeMap = log ∘ ipeRatio ∘ exp`).
* `SwitchingTrial.ExpFullyTreated`: the experimental arm is on treatment throughout follow-up.

## Main results

* `isFixedPt_ipeRatio_exp_iff_gMean`: **relation to the RPSFTM.** `exp ψ` is a fixed point of the
  update exactly when `gMean ψ = (1 - exp ψ) E[T^c | R = 1]`, where `gMean` is the mean-form
  g-estimating function. So the two population targets agree when the experimental arm is fully
  treated (`isFixedPt_ipeMap_iff_gMean_eq_zero`), and in general differ by the time the
  experimental arm spends off treatment.
* `isFixedPt_ipeMap_trueParam`: **the true parameter is a fixed point** under randomization, the
  common treatment effect and a fully treated experimental arm. The last hypothesis is the
  additional assumption of the procedure: the observed experimental times must be the untreated
  times rescaled by the time ratio, which is the accelerated failure time model for the
  experimental arm. It cannot be dropped (`IPECounterexample.Discontinued`).
* `isFixedPt_ipeMap_unique`, `isFixedPt_ipeMap_iff_trueParam`: **at most one fixed point** when
  the control arm has positive mean time off the experimental treatment, `E[T^c | R = 0] > 0`;
  under the model the fixed point is `ψ₀`.
* `contractingWith_ipeRatio`, `tendsto_iterate_ipeMap`: **convergence.** If `E[T^c | R = 0] > 0`
  and `0 ≤ E[T^e | R = 0] < E[T | R = 1]`, the time ratio update is a contraction (Mathlib
  `ContractingWith`) with constant `E[T^e | R = 0] / E[T | R = 1]`, and the iteration converges
  from every starting value. The map in `ψ` itself is not a contraction on all of `ℝ` when
  `E[T^e | R = 0] > 0`; the transfer is through `exp_iterate_ipeMap`.
* `tendsto_iterate_ipeMap_trueParam`: under the model and `E[T^c | R = 0] > 0` the contraction
  condition holds automatically and the iteration converges to `ψ₀` from every start.
* `isFixedPt_of_tendsto_iterate_ipeMap`, `not_tendsto_iterate_ipeMap`: a limit of the iteration is
  a fixed point; if `E[T | R = 1] ≤ E[T^e | R = 0]` there is no fixed point and the iteration
  converges from no start (such data contradict the model).
* `IPECounterexample.Discontinued.fixedPoint_ne_truth`: **the rank preserving root is the truth
  and the iterative fixed point is not.** Randomization and the common effect with time ratio
  `1/2` hold, experimental patients stop treatment before death; the g-estimating root is
  `log (1/2)`, the update has the unique fixed point `log (5/7)` and converges to it.
* `IPECounterexample.NoFirstStage.every_fixedPt`: the claim of TSD 24, Section 4.2.1 that IPE
  "has the advantage of ensuring that multiple solutions will not be identified for ψ" is a
  statement about the output. With no time off treatment in either arm every `ψ` is a fixed
  point; the iteration returns its starting value (the ITT fit `0`), not the truth `log (1/2)`.
  For the ratio of means contrast there is at most one fixed point as soon as
  `E[T^c | R = 0] > 0`, `E[T^e | R = 0] ≥ 0` and `E[T | R = 1] > 0` (`isFixedPt_ipeMap_unique`),
  so a second fixed point needs a control arm with no time off the experimental treatment.

## Setting

Counterfactual variables on a general probability space; real times; no censoring; arm means
as in `CausalInference.StructuralNested.FailureTime`. The counterexamples use the eight point
space of `CausalInference.StructuralNested.RPSFTMCounterexample`. The speed of convergence
claimed in TSD 16, Section 3.2.3, the bootstrap, and recensoring (TSD 24, Section 4.2.1.1) are
not formalized.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014): Section 3.2.3, Appendix A
  ("IPE Algorithm", Equation A2).
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to TSD 16*
  (2024): Section 4.2.1.
* M. Branson, J. Whitehead, *Estimating a treatment effect in survival studies in which
  patients switch treatment*, Statistics in Medicine 21 (2002), 2449 to 2463.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal

namespace CausalInference

namespace StructuralNested

namespace SwitchingTrial

variable {Ω : Type*} [MeasurableSpace Ω] {M : SwitchingTrial Ω} {μ : Measure Ω}

/-! ### The update map -/

variable (M) in
/-- **The experimental arm is on treatment throughout follow-up**: every patient randomized to
the experimental arm has time on the experimental treatment equal to the observed survival
time, `T^e = T`, so `T^c = 0`. -/
def ExpFullyTreated : Prop := ∀ ω, M.R ω = true → M.Te ω = M.T ω

variable (M μ) in
/-- **The population update of iterative parameter estimation** (TSD 16, Section 3.2.3 and
Appendix A, "IPE Algorithm"; TSD 24, Section 4.2.1). Given the current value `ψ`, the times of
the control arm are transformed to their untreated values `U(ψ) = T^c + exp ψ T^e` (only
switchers change, since `T^e = 0` for the others), the experimental arm is kept as observed, and
the two arms are compared by the time ratio of an accelerated failure time model, here the ratio
of arm means. The next value `ψ'` has time ratio `exp (-ψ') = E[T | R = 1] / E[U(ψ) | R = 0]`
(a fully treated patient has `T = exp (-ψ) U`): `ipeMap ψ = log (E[U(ψ) | R = 0] / E[T | R = 1])`.
-/
noncomputable def ipeMap (ψ : ℝ) : ℝ :=
  Real.log (M.armMean μ (M.counterfactual ψ) false / M.armMean μ M.T true)

variable (M μ) in
/-- The update on the scale of the time ratio `x = exp ψ`, the scale of the stopping rule of the
documents: `x ↦ (E[T^c | R = 0] + x E[T^e | R = 0]) / E[T | R = 1]`. It is affine in `x`. -/
noncomputable def ipeRatio (x : ℝ) : ℝ :=
  (M.armMean μ M.Tc false + x * M.armMean μ M.Te false) / M.armMean μ M.T true

/-- **The first step is the ITT fit.** Since `U(0) = T`, the update at `ψ = 0` compares the
observed arms: `ipeMap 0 = log (E[T | R = 0] / E[T | R = 1])`, the accelerated failure time
estimate from the unadjusted intention-to-treat data that starts the iteration. -/
theorem ipeMap_zero : M.ipeMap μ 0 = Real.log (M.armMean μ M.T false / M.armMean μ M.T true) := by
  rw [ipeMap, counterfactual_zero]

/-- Arm means of `T^c`: `E[T^c | R = r] = E[T | R = r] - E[T^e | R = r]`. -/
theorem armMean_Tc (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) {r : Bool}
    (hpos : μ (M.arm r) ≠ 0) : M.armMean μ M.Tc r = M.armMean μ M.T r - M.armMean μ M.Te r :=
  integral_sub (Mediation.integrable_cond_of_integrable hT hpos)
    (Mediation.integrable_cond_of_integrable hTe hpos)

/-- The control arm mean of the candidate untreated time is affine in `exp ψ`. -/
theorem armMean_counterfactual_false (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) (ψ : ℝ) :
    M.armMean μ (M.counterfactual ψ) false =
      M.armMean μ M.Tc false + Real.exp ψ * M.armMean μ M.Te false := by
  rw [armMean_counterfactual hT hTe h0, armMean_Tc hT hTe h0]

/-- `ipeMap = log ∘ ipeRatio ∘ exp`. -/
theorem ipeMap_eq (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h0 : μ (M.arm false) ≠ 0)
    (ψ : ℝ) : M.ipeMap μ ψ = Real.log (M.ipeRatio μ (Real.exp ψ)) := by
  rw [ipeMap, armMean_counterfactual_false hT hTe h0, ipeRatio]

/-! ### Fixed points -/

/-- With `E[T^c | R = 0] > 0`, `E[T^e | R = 0] ≥ 0` and `E[T | R = 1] > 0`, the time ratio
update maps nonnegative values to positive ones. -/
theorem ipeRatio_pos (ha : 0 < M.armMean μ M.Tc false) (hb : 0 ≤ M.armMean μ M.Te false)
    (hc : 0 < M.armMean μ M.T true) {x : ℝ} (hx : 0 ≤ x) : 0 < M.ipeRatio μ x :=
  div_pos (by positivity) hc

/-- **Fixed points of the time ratio update.** With `E[T | R = 1] ≠ 0`, `x` is a fixed point
exactly when `x (E[T | R = 1] - E[T^e | R = 0]) = E[T^c | R = 0]`. -/
theorem isFixedPt_ipeRatio_iff (hc : M.armMean μ M.T true ≠ 0) (x : ℝ) :
    IsFixedPt (M.ipeRatio μ) x ↔
      x * (M.armMean μ M.T true - M.armMean μ M.Te false) = M.armMean μ M.Tc false := by
  rw [IsFixedPt, ipeRatio, div_eq_iff hc]
  constructor <;> intro h <;> linarith

/-- A fixed point of the time ratio update gives a fixed point of `ipeMap`. -/
theorem isFixedPt_ipeMap_of_ipeRatio (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) {ψ : ℝ} (h : IsFixedPt (M.ipeRatio μ) (Real.exp ψ)) :
    IsFixedPt (M.ipeMap μ) ψ := by
  rw [IsFixedPt, ipeMap_eq hT hTe h0, h.eq, Real.log_exp]

/-- **Fixed points of `ipeMap` are fixed points of the time ratio update**, under
`E[T^c | R = 0] > 0`, `E[T^e | R = 0] ≥ 0` and `E[T | R = 1] > 0` (so that the logarithm is
taken of a positive number). -/
theorem isFixedPt_ipeMap_iff (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (hb : 0 ≤ M.armMean μ M.Te false) (hc : 0 < M.armMean μ M.T true) (ψ : ℝ) :
    IsFixedPt (M.ipeMap μ) ψ ↔ IsFixedPt (M.ipeRatio μ) (Real.exp ψ) := by
  refine ⟨fun h ↦ ?_, isFixedPt_ipeMap_of_ipeRatio hT hTe h0⟩
  have hpos := ipeRatio_pos ha hb hc (Real.exp_pos ψ).le
  have h' : Real.log (M.ipeRatio μ (Real.exp ψ)) = ψ := by rw [← ipeMap_eq hT hTe h0]; exact h
  calc M.ipeRatio μ (Real.exp ψ) = Real.exp (Real.log (M.ipeRatio μ (Real.exp ψ))) :=
        (Real.exp_log hpos).symm
    _ = Real.exp ψ := by rw [h']

/-- **At most one fixed point.** If `E[T^c | R = 0] > 0`, `E[T^e | R = 0] ≥ 0` and
`E[T | R = 1] > 0`, the update has at most one fixed point, whatever the data. -/
theorem isFixedPt_ipeMap_unique (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (hb : 0 ≤ M.armMean μ M.Te false) (hc : 0 < M.armMean μ M.T true) {ψ ψ' : ℝ}
    (h : IsFixedPt (M.ipeMap μ) ψ) (h' : IsFixedPt (M.ipeMap μ) ψ') : ψ = ψ' := by
  rw [isFixedPt_ipeMap_iff hT hTe h0 ha hb hc, isFixedPt_ipeRatio_iff hc.ne'] at h h'
  have hne : M.armMean μ M.T true - M.armMean μ M.Te false ≠ 0 := by
    intro hz; rw [hz, mul_zero] at h; linarith
  exact Real.exp_injective (mul_right_cancel₀ hne (h.trans h'.symm))

/-- **Relation to the rank preserving estimating equation.** With integrable `T`, `T^e`, both arms
of positive probability and `E[T | R = 1] ≠ 0`, `exp ψ` is a fixed point of the time ratio update
exactly when the mean-form g-estimating function satisfies
`gMean ψ = (1 - exp ψ) E[T^c | R = 1]`. The two targets differ by the time spent off the
experimental treatment in the experimental arm. -/
theorem isFixedPt_ipeRatio_exp_iff_gMean (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (hc : M.armMean μ M.T true ≠ 0)
    (ψ : ℝ) :
    IsFixedPt (M.ipeRatio μ) (Real.exp ψ) ↔
      M.gMean μ ψ = (1 - Real.exp ψ) * M.armMean μ M.Tc true := by
  rw [isFixedPt_ipeRatio_iff hc, gMean, meanContrast, armMean_counterfactual_false hT hTe h0,
    armMean_counterfactual hT hTe h1, armMean_Tc hT hTe h1, armMean_Tc hT hTe h0]
  constructor <;> intro h <;> linarith

/-- In a fully treated experimental arm the mean time off the experimental treatment is zero. -/
theorem armMean_Tc_true_of_fullyTreated (hR : Measurable M.R) (hfull : M.ExpFullyTreated) :
    M.armMean μ M.Tc true = 0 := by
  have : M.armMean μ M.Tc true = ∫ _ω, (0 : ℝ) ∂μ[|M.arm true] := by
    refine integral_congr_ae ?_
    filter_upwards [ae_cond_mem (M.measurableSet_arm hR true)] with ω hω
    simp [Tc, hfull ω hω]
  rw [this, integral_zero]

/-- **The two targets agree in a fully treated experimental arm.** If the experimental arm is on
treatment throughout follow-up, `exp ψ` is a fixed point of the time ratio update exactly when
`ψ` is a root of the mean-form g-estimating function of the RPSFTM. No randomization or common
effect is used: this is an identity between the two population criteria. -/
theorem isFixedPt_ipeRatio_exp_iff_gMean_eq_zero (hR : Measurable M.R)
    (hfull : M.ExpFullyTreated) (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (hc : M.armMean μ M.T true ≠ 0)
    (ψ : ℝ) : IsFixedPt (M.ipeRatio μ) (Real.exp ψ) ↔ M.gMean μ ψ = 0 := by
  rw [isFixedPt_ipeRatio_exp_iff_gMean hT hTe h1 h0 hc, armMean_Tc_true_of_fullyTreated hR hfull,
    mul_zero]

/-- **Fixed points of the update are the rank preserving roots** in a fully treated experimental
arm, when `E[T^c | R = 0] > 0`, `E[T^e | R = 0] ≥ 0` and `E[T | R = 1] > 0`. -/
theorem isFixedPt_ipeMap_iff_gMean_eq_zero (hR : Measurable M.R) (hfull : M.ExpFullyTreated)
    (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (hb : 0 ≤ M.armMean μ M.Te false) (hc : 0 < M.armMean μ M.T true) (ψ : ℝ) :
    IsFixedPt (M.ipeMap μ) ψ ↔ M.gMean μ ψ = 0 := by
  rw [isFixedPt_ipeMap_iff hT hTe h0 ha hb hc,
    isFixedPt_ipeRatio_exp_iff_gMean_eq_zero hR hfull hT hTe h1 h0 hc.ne']

/-! ### The true parameter -/

/-- **The true time ratio solves the fixed point equation.** Under the common treatment effect
`ψ₀`, randomization, a fully treated experimental arm, integrable `T`, `T^e` and both arms of
positive probability, `exp ψ₀ (E[T | R = 1] - E[T^e | R = 0]) = E[T^c | R = 0]`. -/
theorem exp_trueParam_mul [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated)
    (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) :
    Real.exp ψ₀ * (M.armMean μ M.T true - M.armMean μ M.Te false) = M.armMean μ M.Tc false := by
  have hg := gMean_trueParam hR h hrand hT hTe h1 h0
  rw [gMean, meanContrast, armMean_counterfactual_false hT hTe h0,
    armMean_counterfactual hT hTe h1] at hg
  have hz := armMean_Tc_true_of_fullyTreated (μ := μ) hR hfull
  rw [armMean_Tc hT hTe h1] at hz
  linear_combination hg + (Real.exp ψ₀ - 1) * hz

/-- **The true parameter is a fixed point** (TSD 16, Section 3.2.3: the IPE procedure makes the
randomization and common treatment effect assumptions). Under the common treatment effect `ψ₀`,
randomization, a fully treated experimental arm, integrable `T`, `T^e`, both arms of positive
probability and `E[T | R = 1] ≠ 0`, `ipeMap ψ₀ = ψ₀`. The hypothesis on the experimental arm is
needed (`CausalInference.StructuralNested.IPECounterexample.Discontinued`). -/
theorem isFixedPt_ipeMap_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated)
    (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (hc : M.armMean μ M.T true ≠ 0) :
    IsFixedPt (M.ipeMap μ) ψ₀ :=
  isFixedPt_ipeMap_of_ipeRatio hT hTe h0
    ((isFixedPt_ipeRatio_exp_iff_gMean_eq_zero hR hfull hT hTe h1 h0 hc ψ₀).2
      (gMean_trueParam hR h hrand hT hTe h1 h0))

/-- Under the model and `E[T^c | R = 0] > 0`, `E[T^e | R = 0] < E[T | R = 1]`. -/
theorem armMean_Te_false_lt [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated)
    (hT : Integrable M.T μ) (hTe : Integrable M.Te μ) (h1 : μ (M.arm true) ≠ 0)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false) :
    M.armMean μ M.Te false < M.armMean μ M.T true := by
  have e := exp_trueParam_mul hR h hrand hfull hT hTe h1 h0
  by_contra hn
  nlinarith [Real.exp_pos ψ₀]

/-- The arm mean of `T^e` is nonnegative when `T^e ≥ 0`. -/
theorem armMean_Te_nonneg (hte : ∀ ω, 0 ≤ M.Te ω) (r : Bool) : 0 ≤ M.armMean μ M.Te r :=
  integral_nonneg hte

/-- **Uniqueness of the fixed point under the model.** Under the common treatment effect `ψ₀`,
randomization, a fully treated experimental arm, `T^e ≥ 0`, integrable `T`, `T^e`, both arms of
positive probability and positive mean time off the experimental treatment in the control arm
(`E[T^c | R = 0] > 0`), `ψ₀` is the only fixed point of the update. -/
theorem isFixedPt_ipeMap_iff_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated)
    (hte : ∀ ω, 0 ≤ M.Te ω) (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (ψ : ℝ) : IsFixedPt (M.ipeMap μ) ψ ↔ ψ = ψ₀ := by
  have hb := armMean_Te_nonneg (μ := μ) hte false
  have hc : 0 < M.armMean μ M.T true :=
    hb.trans_lt (armMean_Te_false_lt hR h hrand hfull hT hTe h1 h0 ha)
  have h₀ := isFixedPt_ipeMap_trueParam hR h hrand hfull hT hTe h1 h0 hc.ne'
  exact ⟨fun hψ ↦ isFixedPt_ipeMap_unique hT hTe h0 ha hb hc hψ h₀, fun e ↦ e ▸ h₀⟩

/-! ### Convergence -/

/-- **The time ratio update is a contraction** with constant `E[T^e | R = 0] / E[T | R = 1]`
when `0 ≤ E[T^e | R = 0] < E[T | R = 1]`. -/
theorem contractingWith_ipeRatio (hb : 0 ≤ M.armMean μ M.Te false)
    (hbc : M.armMean μ M.Te false < M.armMean μ M.T true) :
    ContractingWith (M.armMean μ M.Te false / M.armMean μ M.T true).toNNReal
      (M.ipeRatio μ) := by
  have hc : 0 < M.armMean μ M.T true := hb.trans_lt hbc
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  · exact Real.toNNReal_lt_one.2 ((div_lt_one hc).2 hbc)
  · rw [Real.coe_toNNReal _ (div_nonneg hb hc.le), Real.dist_eq, Real.dist_eq, ipeRatio,
      ipeRatio, ← sub_div,
      show M.armMean μ M.Tc false + x * M.armMean μ M.Te false -
          (M.armMean μ M.Tc false + y * M.armMean μ M.Te false) =
        (x - y) * M.armMean μ M.Te false by ring,
      abs_div, abs_mul, abs_of_nonneg hb, abs_of_pos hc]
    exact le_of_eq (by ring)

/-- The fixed point of the contraction is `E[T^c | R = 0] / (E[T | R = 1] - E[T^e | R = 0])`. -/
theorem fixedPoint_ipeRatio (hb : 0 ≤ M.armMean μ M.Te false)
    (hbc : M.armMean μ M.Te false < M.armMean μ M.T true) :
    ContractingWith.fixedPoint (M.ipeRatio μ) (contractingWith_ipeRatio hb hbc) =
      M.armMean μ M.Tc false / (M.armMean μ M.T true - M.armMean μ M.Te false) := by
  refine ((contractingWith_ipeRatio hb hbc).fixedPoint_unique ?_).symm
  rw [isFixedPt_ipeRatio_iff (hb.trans_lt hbc).ne', div_mul_cancel₀ _ (sub_pos.2 hbc).ne']

/-- **The iteration on the two scales.** With `E[T^c | R = 0] > 0`, `E[T^e | R = 0] ≥ 0` and
`E[T | R = 1] > 0`, the `k`-th iterate of `ipeMap` is the logarithm of the `k`-th iterate of the
time ratio update started at `exp ψ`. -/
theorem exp_iterate_ipeMap (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (hb : 0 ≤ M.armMean μ M.Te false) (hc : 0 < M.armMean μ M.T true) (ψ : ℝ) (k : ℕ) :
    Real.exp ((M.ipeMap μ)^[k] ψ) = (M.ipeRatio μ)^[k] (Real.exp ψ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ipeMap_eq hT hTe h0, ih,
      Real.exp_log (ipeRatio_pos ha hb hc (ih ▸ Real.exp_pos _).le)]

/-- **Convergence from every start** (TSD 16, Appendix A: the iteration "is continued until the
new estimate for exp(ψ) is very close to the previous estimate"). If `E[T^c | R = 0] > 0` and
`0 ≤ E[T^e | R = 0] < E[T | R = 1]`, the iterates of `ipeMap` from any starting value converge to
`log (E[T^c | R = 0] / (E[T | R = 1] - E[T^e | R = 0]))`, the unique fixed point. This uses only
the observed data. -/
theorem tendsto_iterate_ipeMap (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (hb : 0 ≤ M.armMean μ M.Te false) (hbc : M.armMean μ M.Te false < M.armMean μ M.T true)
    (ψ : ℝ) :
    Tendsto (fun k ↦ (M.ipeMap μ)^[k] ψ) atTop
      (𝓝 (Real.log (M.armMean μ M.Tc false /
        (M.armMean μ M.T true - M.armMean μ M.Te false)))) := by
  have hc : 0 < M.armMean μ M.T true := hb.trans_lt hbc
  have e : (fun k ↦ (M.ipeMap μ)^[k] ψ) =
      fun k ↦ Real.log ((M.ipeRatio μ)^[k] (Real.exp ψ)) := by
    funext k; rw [← exp_iterate_ipeMap hT hTe h0 ha hb hc, Real.log_exp]
  have hlim := (contractingWith_ipeRatio hb hbc).tendsto_iterate_fixedPoint (Real.exp ψ)
  rw [fixedPoint_ipeRatio hb hbc] at hlim
  rw [e]
  exact (Real.continuousAt_log (div_pos ha (sub_pos.2 hbc)).ne').tendsto.comp hlim

/-- **Convergence to the true parameter.** Under the common treatment effect `ψ₀`, randomization,
a fully treated experimental arm, `T^e ≥ 0`, integrable `T`, `T^e`, both arms of positive
probability and `E[T^c | R = 0] > 0`, the iteration converges to `ψ₀` from every starting value,
in particular from the ITT fit `ipeMap 0`. The contraction condition
`E[T^e | R = 0] < E[T | R = 1]` is a consequence of the model. -/
theorem tendsto_iterate_ipeMap_trueParam [IsFiniteMeasure μ] (hR : Measurable M.R) {ψ₀ : ℝ}
    (h : M.CommonEffect ψ₀) (hrand : M.Randomized μ) (hfull : M.ExpFullyTreated)
    (hte : ∀ ω, 0 ≤ M.Te ω) (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h1 : μ (M.arm true) ≠ 0) (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (ψ : ℝ) : Tendsto (fun k ↦ (M.ipeMap μ)^[k] ψ) atTop (𝓝 ψ₀) := by
  have hbc := armMean_Te_false_lt hR h hrand hfull hT hTe h1 h0 ha
  have hlim := tendsto_iterate_ipeMap hT hTe h0 ha (armMean_Te_nonneg hte false) hbc ψ
  rwa [← exp_trueParam_mul hR h hrand hfull hT hTe h1 h0,
    mul_div_cancel_right₀ _ (sub_pos.2 hbc).ne', Real.log_exp] at hlim

/-- **A limit of the iteration is a fixed point.** With `E[T^c | R = 0] > 0`,
`E[T^e | R = 0] ≥ 0` and `E[T | R = 1] > 0`, the update is continuous, so any limit of its
iterates is a fixed point. -/
theorem isFixedPt_of_tendsto_iterate_ipeMap (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (hb : 0 ≤ M.armMean μ M.Te false) (hc : 0 < M.armMean μ M.T true) {ψ L : ℝ}
    (hlim : Tendsto (fun k ↦ (M.ipeMap μ)^[k] ψ) atTop (𝓝 L)) : IsFixedPt (M.ipeMap μ) L := by
  refine isFixedPt_of_tendsto_iterate hlim ?_
  have e : M.ipeMap μ = fun ψ ↦ Real.log (M.ipeRatio μ (Real.exp ψ)) :=
    funext (ipeMap_eq hT hTe h0)
  have hG : Continuous (M.ipeRatio μ) := by unfold ipeRatio; fun_prop
  rw [e]
  exact (hG.comp Real.continuous_exp).continuousAt.log
    (ipeRatio_pos ha hb hc (Real.exp_pos L).le).ne'

/-- **Failure of convergence.** If `E[T^c | R = 0] > 0`, `E[T | R = 1] > 0` and
`E[T | R = 1] ≤ E[T^e | R = 0]`, the update has no fixed point, so the iterates converge from no
starting value. Such data are incompatible with the model of `tendsto_iterate_ipeMap_trueParam`
(`armMean_Te_false_lt`). -/
theorem not_tendsto_iterate_ipeMap (hT : Integrable M.T μ) (hTe : Integrable M.Te μ)
    (h0 : μ (M.arm false) ≠ 0) (ha : 0 < M.armMean μ M.Tc false)
    (hc : 0 < M.armMean μ M.T true) (hcb : M.armMean μ M.T true ≤ M.armMean μ M.Te false)
    (ψ L : ℝ) : ¬ Tendsto (fun k ↦ (M.ipeMap μ)^[k] ψ) atTop (𝓝 L) := by
  intro hlim
  have hb : 0 ≤ M.armMean μ M.Te false := hc.le.trans hcb
  have hfix := isFixedPt_of_tendsto_iterate_ipeMap hT hTe h0 ha hb hc hlim
  rw [isFixedPt_ipeMap_iff hT hTe h0 ha hb hc, isFixedPt_ipeRatio_iff hc.ne'] at hfix
  nlinarith [Real.exp_pos L]

end SwitchingTrial

/-! ### Counterexamples -/

namespace IPECounterexample

open SwitchingTrial RPSFTMCounterexample CausalInference.Mediation.Counterexample

/-! #### An experimental arm with time off treatment -/

namespace Discontinued

/-- The time ratio is `1/2` for everyone and the untreated time is `2 s`. Experimental patients
take the experimental treatment for `2 s` and then stop, surviving `s` more (observed `3 s`).
Control patients of the good type never switch (observed `4`); those of the poor type switch at
time `1` and survive to `3`. -/
noncomputable def trial : SwitchingTrial Ω₀ where
  R ω := ω.1
  T ω := if ω.1 then 3 * scale ω else if ω.2.1 then 4 else 3
  Te ω := if ω.1 then 2 * scale ω else if ω.2.1 then 0 else 2
  U ω := 2 * scale ω

theorem commonEffect : trial.CommonEffect (Real.log (1 / 2)) := by
  intro ω
  obtain ⟨a, u, v⟩ := ω
  rw [Real.exp_log (by norm_num)]
  cases a <;> cases u <;> norm_num [trial, scale, Tc]

theorem randomized : trial.Randomized μ₀ :=
  randomized_of_eq trial (fun _ ↦ rfl) (fun x ↦ 2 * if x.1 then 2 else 1) fun _ ↦ rfl

/-- The experimental arm is not fully treated. -/
theorem not_fullyTreated : ¬ trial.ExpFullyTreated := by
  intro h
  have := h (true, true, true) rfl
  norm_num [trial, scale] at this

theorem armMean_T_true : trial.armMean μ₀ trial.T true = 9 / 2 := by
  rw [armMean_μ₀ trial (fun _ ↦ rfl)]; norm_num [trial, scale]

theorem armMean_Te_false : trial.armMean μ₀ trial.Te false = 1 := by
  rw [armMean_μ₀ trial (fun _ ↦ rfl)]; norm_num [trial, scale]

theorem armMean_Tc_false : trial.armMean μ₀ trial.Tc false = 5 / 2 := by
  rw [armMean_μ₀ trial (fun _ ↦ rfl)]; norm_num [trial, scale, Tc]

/-- **The rank preserving root is the truth**: the mean-form g-estimating function is
`2 exp ψ - 1`, with the unique root `ψ = log (1/2)`. -/
theorem gMean_eq_zero_iff (ψ : ℝ) : trial.gMean μ₀ ψ = 0 ↔ ψ = Real.log (1 / 2) := by
  have e : trial.gMean μ₀ ψ = 2 * Real.exp ψ - 1 := by
    simp only [gMean, meanContrast, armMean_μ₀ trial (fun _ ↦ rfl)]
    simp only [counterfactual, Tc, trial, scale]
    norm_num
    ring
  rw [e]
  constructor
  · intro h
    rw [← Real.log_exp ψ]
    exact congrArg Real.log (by linarith)
  · rintro rfl; rw [Real.exp_log (by norm_num)]; norm_num

/-- The update is `ψ ↦ log ((5 + 2 exp ψ) / 9)`. -/
theorem ipeMap_eq (ψ : ℝ) : trial.ipeMap μ₀ ψ = Real.log ((5 + 2 * Real.exp ψ) / 9) := by
  rw [SwitchingTrial.ipeMap_eq Integrable.of_finite Integrable.of_finite
    (arm_ne_zero trial (fun _ ↦ rfl) false), ipeRatio, armMean_T_true, armMean_Te_false,
    armMean_Tc_false]
  congr 1; ring

/-- **Counterexample: the iterative fixed point is not the truth.** Randomization and the common
treatment effect hold, the rank preserving root is `log (1/2)`, but `log (1/2)` is not a fixed
point of the update (`ipeMap (log (1/2)) = log (2/3)`), the only fixed point has time ratio
`5/7`, and the iteration converges to `log (5/7)` from every starting value. -/
theorem fixedPoint_ne_truth :
    trial.ipeMap μ₀ (Real.log (1 / 2)) = Real.log (2 / 3) ∧
      Real.log (2 / 3) ≠ Real.log (1 / 2) ∧
      (∀ ψ, IsFixedPt (trial.ipeMap μ₀) ψ ↔ Real.exp ψ = 5 / 7) ∧
      ∀ ψ, Tendsto (fun k ↦ (trial.ipeMap μ₀)^[k] ψ) atTop (𝓝 (Real.log (5 / 7))) := by
  have hT : Integrable trial.T μ₀ := Integrable.of_finite
  have hTe : Integrable trial.Te μ₀ := Integrable.of_finite
  have h0 := arm_ne_zero trial (fun _ ↦ rfl) false
  have ha : 0 < trial.armMean μ₀ trial.Tc false := by rw [armMean_Tc_false]; norm_num
  have hb : 0 ≤ trial.armMean μ₀ trial.Te false := by rw [armMean_Te_false]; norm_num
  have hc : 0 < trial.armMean μ₀ trial.T true := by rw [armMean_T_true]; norm_num
  refine ⟨?_, ?_, fun ψ ↦ ?_, fun ψ ↦ ?_⟩
  · rw [ipeMap_eq, Real.exp_log (by norm_num)]; norm_num
  · intro h
    have := Real.log_injOn_pos (by norm_num : (2 / 3 : ℝ) ∈ Ioi 0)
      (by norm_num : (1 / 2 : ℝ) ∈ Ioi 0) h
    norm_num at this
  · rw [isFixedPt_ipeMap_iff hT hTe h0 ha hb hc, isFixedPt_ipeRatio_iff hc.ne', armMean_T_true,
      armMean_Te_false, armMean_Tc_false]
    constructor <;> intro h <;> linarith
  · have := tendsto_iterate_ipeMap hT hTe h0 ha hb
      (by rw [armMean_T_true, armMean_Te_false]; norm_num) ψ
    rw [armMean_T_true, armMean_Te_false, armMean_Tc_false] at this
    convert this using 3; norm_num

end Discontinued

/-! #### No first stage: every value is a fixed point -/

namespace NoFirstStage

/-- Everybody is on the experimental treatment from time `0`, in both arms, with time ratio
`1/2`: untreated `2 s`, observed `4 s`. -/
noncomputable def trial : SwitchingTrial Ω₀ where
  R ω := ω.1
  T ω := 4 * scale ω
  Te ω := 4 * scale ω
  U ω := 2 * scale ω

theorem commonEffect : trial.CommonEffect (Real.log (1 / 2)) := by
  intro ω
  rw [Real.exp_log (by norm_num)]
  simp only [trial, Tc]; ring

theorem randomized : trial.Randomized μ₀ :=
  randomized_of_eq trial (fun _ ↦ rfl) (fun x ↦ 2 * if x.1 then 2 else 1) fun _ ↦ rfl

theorem fullyTreated : trial.ExpFullyTreated := fun _ _ ↦ rfl

/-- The update is the identity. -/
theorem ipeMap_eq (ψ : ℝ) : trial.ipeMap μ₀ ψ = ψ := by
  rw [SwitchingTrial.ipeMap_eq Integrable.of_finite Integrable.of_finite
    (arm_ne_zero trial (fun _ ↦ rfl) false), ipeRatio]
  simp only [armMean_μ₀ trial (fun _ ↦ rfl)]
  simp only [Tc, trial, scale]
  norm_num

/-- **Counterexample: the iteration returns one value, not a unique solution.** Randomization,
the common treatment effect `log (1/2)` and a fully treated experimental arm hold, but every `ψ`
is a fixed point of the update and a root of the mean-form g-estimating function. The iteration
started at the ITT fit `ipeMap 0 = 0` stays at `0`, which is returned although the truth is
`log (1/2)`; started elsewhere it returns its start. The control arm has no time off the
experimental treatment, `E[T^c | R = 0] = 0`, which `isFixedPt_ipeMap_iff_trueParam` excludes. -/
theorem every_fixedPt :
    (∀ ψ, IsFixedPt (trial.ipeMap μ₀) ψ) ∧ (∀ ψ, trial.gMean μ₀ ψ = 0) ∧
      (∀ ψ k, (trial.ipeMap μ₀)^[k] ψ = ψ) ∧ trial.ipeMap μ₀ 0 = 0 ∧
      (0 : ℝ) ≠ Real.log (1 / 2) ∧ trial.armMean μ₀ trial.Tc false = 0 := by
  have hfix : ∀ ψ, IsFixedPt (trial.ipeMap μ₀) ψ := ipeMap_eq
  refine ⟨hfix, fun ψ ↦ ?_, fun ψ k ↦ (hfix ψ).iterate k, ipeMap_eq 0, ?_, ?_⟩
  · simp only [gMean, meanContrast, armMean_μ₀ trial (fun _ ↦ rfl)]
    simp only [counterfactual, Tc, trial, scale]
    norm_num
  · rw [one_div, Real.log_inv]
    exact (neg_ne_zero.2 (Real.log_pos one_lt_two).ne').symm
  · rw [armMean_μ₀ trial (fun _ ↦ rfl)]; norm_num [trial, Tc]

end NoFirstStage

end IPECounterexample

end StructuralNested

end CausalInference
