/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredSurvivalTarget
public import CausalInference.NetworkMetaRegression.AggregationIdentity
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The median survival time of an unanchored survival comparison

**Time scale: continuous.** The median of a survival curve `S` is a time `m ≥ 0` with
`S(m) = 1/2`. A continuous curve with `S(0) = 1` that reaches `1/2` has a median (intermediate
value theorem), and a strictly decreasing curve has at most one. A survival curve need not reach
`1/2`: `(1 + e^{-t}) / 2` stays above it (`not_exists_median_of_cure`), so the existence of a
median is a genuine hypothesis, which a population with a cured fraction of one half violates.

For a family `M(ξ, t)` of curves, continuously differentiable in `(ξ, t)` with a nonzero time
derivative at the median, the median `m(ξ)` is continuously differentiable in `ξ` as soon as each
curve near `ξ₀` is injective in `t` (`contDiffAt_median`): the implicit function theorem gives a
continuously differentiable solution of `M(ξ, t) = 1/2`, and injectivity identifies it with the
median. No uniqueness or existence of medians near `ξ₀` is assumed beyond `M(ξ, m(ξ)) = 1/2`.

## Main results

* `exists_median`, `median_unique`, `not_exists_median_of_cure`.
* `contDiffAt_median`: the median of a continuously differentiable family is continuously
  differentiable.
* `median_instance`: the target survival `(e^{-t} + e^{-2t}) / 2` of a two valued covariate with
  relative hazards `1` and `2` has the unique median `log((1 + √5) / 2)`.
* `contDiff_median_instance`: the median `log 2 · e^{-ξ}` of `exp(-e^ξ t)` with every hypothesis of
  `contDiffAt_median` discharged.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology Set
open Survival.ContinuousTime

/-! ### Existence and uniqueness -/

/-- **A median exists** for a curve continuous on `[0, T]` with `S(0) = 1` and `S(T) ≤ 1/2`. -/
theorem exists_median {S : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn S (Icc 0 T))
    (h0 : S 0 = 1) (hT2 : S T ≤ 1 / 2) : ∃ m ∈ Icc 0 T, S m = 1 / 2 := by
  have h := intermediate_value_Icc' hT hc
  exact h ⟨hT2, by rw [h0]; norm_num⟩

/-- **The median is unique** for a curve strictly decreasing on `[0, ∞)`. -/
theorem median_unique {S : ℝ → ℝ} (hS : StrictAntiOn S (Ici 0)) {m m' : ℝ} (hm : 0 ≤ m)
    (hm' : 0 ≤ m') (h : S m = 1 / 2) (h' : S m' = 1 / 2) : m = m' :=
  hS.injOn hm hm' (h.trans h'.symm)

/-- **A survival curve need not have a median.** The curve `(1 + e^{-t}) / 2`, a population of
which one half is never at risk of the event, is continuous, antitone, equal to `1` at `0`, with
values in `[0, 1]` at nonnegative times, and never equal to `1/2` at a nonnegative time. -/
theorem not_exists_median_of_cure :
    Continuous (fun t : ℝ => (1 + Real.exp (-t)) / 2) ∧
      Antitone (fun t : ℝ => (1 + Real.exp (-t)) / 2) ∧
      (1 + Real.exp (-0)) / 2 = 1 ∧
      (∀ t, 0 ≤ t → (1 + Real.exp (-t)) / 2 ∈ Icc (0 : ℝ) 1) ∧
      ∀ t, 0 ≤ t → (1 + Real.exp (-t)) / 2 ≠ 1 / 2 := by
  refine ⟨by fun_prop, fun a b hab => ?_, by simp, fun t ht => ⟨?_, ?_⟩, fun t _ h => ?_⟩
  · have := Real.exp_le_exp.2 (neg_le_neg hab)
    simp only
    linarith
  · positivity
  · have := Real.exp_le_one_iff.2 (neg_nonpos.2 ht)
    linarith
  · have := Real.exp_pos (-t)
    linarith

/-! ### Differentiability of the median -/

/-- A continuous linear map `ℝ → ℝ` with a nonzero value at `1` is invertible. -/
theorem isInvertible_of_ne_zero_at_one {L : ℝ →L[ℝ] ℝ} (h : L 1 ≠ 0) :
    L.IsInvertible :=
  ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ h),
    ContinuousLinearMap.ext_ring (by simp)⟩

/-- **The median of a continuously differentiable family is continuously differentiable.** Let
`M(ξ, t)` be continuously differentiable at `(ξ₀, m(ξ₀))`, with time derivative `d ≠ 0` at
`m(ξ₀)` (for a survival curve, minus a positive density at the median), let `M(ξ, m(ξ)) = 1/2`
and let `t ↦ M(ξ, t)` be injective for every `ξ` near `ξ₀`. Then `m` is continuously
differentiable at `ξ₀`. -/
theorem contDiffAt_median {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M : E × ℝ → ℝ} {med : E → ℝ} {ξ₀ : E} {d : ℝ} (hM : ContDiffAt ℝ 1 M (ξ₀, med ξ₀))
    (hd : HasDerivAt (fun t => M (ξ₀, t)) d (med ξ₀)) (hd0 : d ≠ 0)
    (hmed : ∀ᶠ ξ in 𝓝 ξ₀, M (ξ, med ξ) = 1 / 2)
    (hinj : ∀ᶠ ξ in 𝓝 ξ₀, Function.Injective fun t => M (ξ, t)) :
    ContDiffAt ℝ 1 med ξ₀ := by
  have hMd : HasFDerivAt M (fderiv ℝ M (ξ₀, med ξ₀)) (ξ₀, med ξ₀) :=
    (hM.differentiableAt one_ne_zero).hasFDerivAt
  have hpart : HasDerivAt (fun t => M (ξ₀, t)) (fderiv ℝ M (ξ₀, med ξ₀) (0, 1)) (med ξ₀) :=
    hMd.comp_hasDerivAt (med ξ₀) ((hasDerivAt_const (med ξ₀) ξ₀).prodMk (hasDerivAt_id' _))
  have h1 : (fderiv ℝ M (ξ₀, med ξ₀) ∘L ContinuousLinearMap.inr ℝ E ℝ) 1 ≠ 0 := by
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
    rw [hpart.unique hd]
    exact hd0
  have hinv := isInvertible_of_ne_zero_at_one h1
  have hself : M (ξ₀, med ξ₀) = 1 / 2 := hmed.self_of_nhds
  have hsol := hM.eventually_apply_implicitFunction one_ne_zero hinv
  have heq : med =ᶠ[𝓝 ξ₀] hM.implicitFunction one_ne_zero hinv := by
    filter_upwards [hsol, hmed, hinj] with ξ hξ hm hi
    exact hi (hm.trans (hξ.trans hself).symm)
  exact (hM.contDiffAt_implicitFunction one_ne_zero hinv).congr_of_eventuallyEq heq

/-! ### Instances -/

/-- The curve `(e^{-t} + e^{-2t}) / 2` is strictly decreasing. -/
theorem strictAnti_exp_neg_add_exp_neg_two :
    StrictAnti fun t : ℝ => (Real.exp (-t) + Real.exp (-(2 * t))) / 2 := by
  intro a b hab
  have h1 := Real.exp_lt_exp.2 (neg_lt_neg hab)
  have h2 := Real.exp_lt_exp.2 (neg_lt_neg (mul_lt_mul_of_pos_left hab two_pos))
  simp only
  linarith

/-- **Instance: the median of a target survival.** Under a unit baseline hazard, a covariate with
values `0` and `1` of probability `1/2` and log hazard ratio `log 2`, the target survival is
`S(t) = (e^{-t} + e^{-2t}) / 2`, and `S(t) = 1/2` exactly at `t = log((1 + √5) / 2)`. -/
theorem median_instance :
    (∀ t, popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
        (phSurvival id (linearRelativeHazard 0 ![Real.log 2])) t =
      (Real.exp (-t) + Real.exp (-(2 * t))) / 2) ∧
    ∀ t, popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
        (phSurvival id (linearRelativeHazard 0 ![Real.log 2])) t = 1 / 2 ↔
      t = Real.log ((1 + √5) / 2) := by
  have hS : ∀ t, popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
      (phSurvival id (linearRelativeHazard 0 ![Real.log 2])) t =
      (Real.exp (-t) + Real.exp (-(2 * t))) / 2 := fun t => by
    rw [popSurvival, integral_twoAtomLaw (by norm_num) (by norm_num)]
    simp only [phSurvival, linearRelativeHazard, dotProduct, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one, Finset.sum_singleton, zero_mul,
      add_zero, Real.exp_zero, one_mul, zero_add, id, Real.exp_log two_pos]
    ring
  refine ⟨hS, fun t => ?_⟩
  have h5 : (0 : ℝ) < √5 := by positivity
  have hpos : (0 : ℝ) < (1 + √5) / 2 := by positivity
  have hm : (Real.exp (-Real.log ((1 + √5) / 2)) +
      Real.exp (-(2 * Real.log ((1 + √5) / 2)))) / 2 = 1 / 2 := by
    have hsq : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
    rw [Real.exp_neg, Real.exp_log hpos, show -(2 * Real.log ((1 + √5) / 2)) =
      -Real.log ((1 + √5) / 2) * 2 by ring, Real.exp_mul, Real.exp_neg, Real.exp_log hpos]
    rw [show ((((1 + √5) / 2)⁻¹) ^ (2 : ℝ)) = (((1 + √5) / 2)⁻¹) ^ (2 : ℕ) by norm_cast]
    field_simp
    nlinarith
  rw [hS]
  constructor
  · intro h
    exact strictAnti_exp_neg_add_exp_neg_two.injective (h.trans hm.symm)
  · rintro rfl
    exact hm

/-- **Instance: a differentiable median.** For the family `M(ξ, t) = exp(-e^ξ t)` (a unit
baseline hazard with log relative hazard `ξ`), the median `m(ξ) = log 2 · e^{-ξ}` satisfies every
hypothesis of `contDiffAt_median` at every `ξ₀`, with time derivative `-e^{ξ₀} / 2`. -/
theorem contDiff_median_instance (ξ₀ : ℝ) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Real.exp (-(Real.exp q.1 * q.2)))
        (ξ₀, Real.log 2 * Real.exp (-ξ₀)) ∧
      HasDerivAt (fun t => Real.exp (-(Real.exp ξ₀ * t))) (-(Real.exp ξ₀ / 2))
        (Real.log 2 * Real.exp (-ξ₀)) ∧
      (∀ ξ, Real.exp (-(Real.exp ξ * (Real.log 2 * Real.exp (-ξ)))) = 1 / 2) ∧
      (∀ ξ, Function.Injective fun t => Real.exp (-(Real.exp ξ * t))) ∧
      ContDiffAt ℝ 1 (fun ξ => Real.log 2 * Real.exp (-ξ)) ξ₀ := by
  have hhalf : ∀ ξ, Real.exp (-(Real.exp ξ * (Real.log 2 * Real.exp (-ξ)))) = 1 / 2 := fun ξ => by
    rw [show Real.exp ξ * (Real.log 2 * Real.exp (-ξ)) = Real.log 2 * (Real.exp ξ * Real.exp (-ξ))
      by ring, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, Real.exp_neg,
      Real.exp_log two_pos, one_div]
  have hC : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Real.exp (-(Real.exp q.1 * q.2)))
      (ξ₀, Real.log 2 * Real.exp (-ξ₀)) := by fun_prop
  have hD : HasDerivAt (fun t => Real.exp (-(Real.exp ξ₀ * t))) (-(Real.exp ξ₀ / 2))
      (Real.log 2 * Real.exp (-ξ₀)) := by
    have h0 : HasDerivAt (fun t => -(Real.exp ξ₀ * t)) (-(Real.exp ξ₀))
        (Real.log 2 * Real.exp (-ξ₀)) := by
      have := ((hasDerivAt_id (Real.log 2 * Real.exp (-ξ₀))).const_mul (Real.exp ξ₀)).neg
      simp only [id, mul_one] at this
      exact this
    convert h0.exp using 1
    rw [hhalf]
    ring
  have hI : ∀ ξ, Function.Injective fun t => Real.exp (-(Real.exp ξ * t)) := fun ξ a b h => by
    have := Real.exp_injective h
    have hξ := (Real.exp_pos ξ).ne'
    simp only [neg_inj] at this
    exact mul_left_cancel₀ hξ this
  refine ⟨hC, hD, hhalf, hI, ?_⟩
  exact contDiffAt_median (M := fun q : ℝ × ℝ => Real.exp (-(Real.exp q.1 * q.2))) hC hD
    (neg_ne_zero.2 (div_pos (Real.exp_pos ξ₀) two_pos).ne')
    (Eventually.of_forall hhalf) (Eventually.of_forall hI)

end NetworkMetaRegression

end CausalInference
