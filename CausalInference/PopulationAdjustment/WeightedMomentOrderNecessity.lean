/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderSetting
public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralExamples
public import Mathlib.Probability.Distributions.Exponential

/-!
# The order of the exponential moment on the exponential law

The consistency theorem of the weighted arm mean under one exponential moment
(`sampleBalancedArmMean_isConsistent_of_isMinOn`) asks for `E[exp(κ ‖φ(X) - t‖)] < ∞` with
`κ > 2 p ‖β*‖`. This file computes everything for one law of a scalar feature, the standard
exponential law (`expMeasure 1`) with the feature `φ(x) = x` (`p = 1`) and a target `t > 0`.

* **The dual objective in closed form**: `E[exp(β(X - t))] = exp(-βt) / (1 - β)` for `β < 1` and
  `∞` for `β ≥ 1` (`sharpDualObjective_expMeasure_of_lt`, `sharpDualObjective_expMeasure_of_le`).
  Its minimizer is `β* = 1 - 1/t` (`isMinOn_sharpDualObjective_expMeasure`), by
  `exp(u - 1) ≥ u` at `u = (1 - β) t`.
* **The moments**: `E[exp(κ |X - t|)] < ∞` exactly when `κ < κ₀ = 1`
  (`integrable_exp_norm_expMeasure_iff`).
* **Comparison**: `|β*| < κ₀` exactly when `t > 1/2` (`norm_tiltMinimizer_expMeasure_lt_one_iff`),
  and an order `κ` with a finite moment and `κ > 2|β*|` exists exactly when `2/3 < t < 2`
  (`exists_order_expMeasure_iff`).
* **The second moment of the population weight** `w*(x) = exp(β*(x - t))`: in general
  `E[w*²] = E[exp(2β*ᵀ(φ - t))]`, the objective at `2β*`, in `[0, ∞]`
  (`lintegral_sq_tilt_eq_sharpDualObjective`, `integrable_sq_tilt_iff`); for the exponential law
  `E[w*²] < ∞` exactly when `t < 2` (`integrable_sq_tilt_expMeasure_iff`).

So for `2 ≤ t` the population weight has an infinite second moment and no order satisfies the
hypothesis of the theorem, while for `t ≤ 2/3` the weight has a finite second moment (it is bounded,
`β* < 0` and `X ≥ 0`) but again no order satisfies the hypothesis: the norm condition
`κ > 2 p ‖β*‖` measures both tails, the weight only the tail in the direction of `β*`.

## Main results

* `lintegral_exp_mul_expMeasure_of_lt`, `lintegral_exp_mul_expMeasure_of_le`,
  `integrable_exp_mul_expMeasure_iff`.
* `isMinOn_sharpDualObjective_expMeasure`, `integrable_exp_norm_expMeasure_iff`,
  `exists_order_expMeasure_iff`, `norm_tiltMinimizer_expMeasure_lt_one_iff`.
* `lintegral_sq_tilt_eq_sharpDualObjective`, `integrable_sq_tilt_iff`,
  `integrable_sq_tilt_expMeasure_iff`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

/-! ### The second moment of the population weight -/

section Weight

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {p : ℕ} {ν : Measure 𝒪} {f : 𝒪 → Fin p → ℝ}
  {t : Fin p → ℝ}

/-- **The second moment of the tilt weight is the dual objective at twice the parameter**:
`E[exp(βᵀ(f - t))²] = E[exp((2β)ᵀ(f - t))]`, in `[0, ∞]`. -/
theorem lintegral_sq_tilt_eq_sharpDualObjective (β : Fin p → ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (β ⬝ᵥ (f z - t)) ^ 2) ∂ν =
      sharpDualObjective ν f t ((2 : ℝ) • β) := by
  refine lintegral_congr fun z => ?_
  rw [← Real.exp_nat_mul, smul_dotProduct, smul_eq_mul]
  norm_num

/-- **The weight is square integrable exactly when the tilt of twice the parameter is
integrable**: `E[w²] < ∞ ↔ E[exp(2βᵀ(f - t))] < ∞` for `w = exp(βᵀ(f - t))`. -/
theorem integrable_sq_tilt_iff (β : Fin p → ℝ) :
    Integrable (fun z => Real.exp (β ⬝ᵥ (f z - t)) ^ 2) ν ↔
      Integrable (fun z => Real.exp (((2 : ℝ) • β) ⬝ᵥ (f z - t))) ν := by
  have e : (fun z => Real.exp (β ⬝ᵥ (f z - t)) ^ 2) =
      fun z => Real.exp (((2 : ℝ) • β) ⬝ᵥ (f z - t)) := funext fun z => by
    rw [← Real.exp_nat_mul, smul_dotProduct, smul_eq_mul]; norm_num
  rw [e]

end Weight

/-! ### The standard exponential law -/

section ExpLaw

instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

/-- Integration against the standard exponential law: the density `exp(-x)` on `[0, ∞)`. -/
theorem lintegral_expMeasure_one {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂expMeasure 1 = ∫⁻ x in Ici 0, ENNReal.ofReal (Real.exp (-x)) * g x := by
  have hd : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ hd hg,
    ← lintegral_indicator measurableSet_Ici]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (mem_Ici.2 hx)]
    change exponentialPDF 1 x * g x = _
    rw [exponentialPDF_of_nonneg hx, one_mul, one_mul]
  · rw [indicator_of_notMem (fun h => hx (mem_Ici.1 h))]
    change exponentialPDF 1 x * g x = _
    rw [exponentialPDF_of_neg (not_le.1 hx), zero_mul]

theorem lintegral_exp_mul_expMeasure_eq (c : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂expMeasure 1 =
      ∫⁻ x in Ici 0, ENNReal.ofReal (Real.exp ((c - 1) * x)) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (c * x)) := by fun_prop
  rw [lintegral_expMeasure_one hm]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- `E[exp(cX)] = 1 / (1 - c)` for `c < 1` under the standard exponential law. -/
theorem lintegral_exp_mul_expMeasure_of_lt {c : ℝ} (hc : c < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂expMeasure 1 = ENNReal.ofReal (1 / (1 - c)) := by
  rw [lintegral_exp_mul_expMeasure_eq]
  have hc' : c - 1 < 0 := by linarith
  have hi : IntegrableOn (fun x => Real.exp ((c - 1) * x)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 (integrableOn_exp_mul_Ioi hc' 0)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le),
    integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hc' 0, mul_zero, Real.exp_zero]
  congr 1
  rw [neg_div, ← div_neg, neg_sub]

/-- `E[exp(cX)] = ∞` for `c ≥ 1` under the standard exponential law. -/
theorem lintegral_exp_mul_expMeasure_of_le {c : ℝ} (hc : 1 ≤ c) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x)) ∂expMeasure 1 = ⊤ := by
  rw [lintegral_exp_mul_expMeasure_eq]
  refine top_unique ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ _ in Ici (0 : ℝ), 1 := by
        rw [lintegral_one, Measure.restrict_apply_univ, Real.volume_Ici]
    _ ≤ _ := setLIntegral_mono (by fun_prop)
        fun x hx => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal
            (Real.one_le_exp (mul_nonneg (by linarith) (mem_Ici.1 hx)))

/-- `exp(cX)` is integrable under the standard exponential law exactly when `c < 1`. -/
theorem integrable_exp_mul_expMeasure_iff {c : ℝ} :
    Integrable (fun x => Real.exp (c * x)) (expMeasure 1) ↔ c < 1 := by
  have hm : AEStronglyMeasurable (fun x => Real.exp (c * x)) (expMeasure 1) :=
    (by fun_prop : Measurable fun x : ℝ => Real.exp (c * x)).aestronglyMeasurable
  rw [Integrable, and_iff_right hm,
    hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  constructor
  · intro h
    by_contra hc
    rw [lintegral_exp_mul_expMeasure_of_le (not_lt.1 hc)] at h
    exact lt_irrefl _ h
  · intro hc
    rw [lintegral_exp_mul_expMeasure_of_lt hc]
    exact ENNReal.ofReal_lt_top

theorem dotProduct_featureLineVec_sub (β : Fin 1 → ℝ) (x t : ℝ) :
    β ⬝ᵥ (featureLineVec x - featureLineVec t) = β 0 * (x - t) := by
  simp [featureLineVec, dotProduct]

theorem norm_featureLineVec (r : ℝ) : ‖featureLineVec r‖ = |r| := by
  rw [show featureLineVec r = fun _ : Fin 1 => r from rfl, pi_norm_const, Real.norm_eq_abs]

theorem sharpDualObjective_expMeasure (t : ℝ) (β : Fin 1 → ℝ) :
    sharpDualObjective (expMeasure 1) featureLineVec (featureLineVec t) β =
      ENNReal.ofReal (Real.exp (-(β 0 * t))) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (β 0 * x)) ∂expMeasure 1 := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (β 0 * x)) := by fun_prop
  rw [sharpDualObjective, ← lintegral_const_mul _ hm]
  refine lintegral_congr fun x => ?_
  rw [dotProduct_featureLineVec_sub, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  ring_nf

/-- **The dual objective of the exponential law in closed form**:
`E[exp(β(X - t))] = exp(-βt) / (1 - β)` for `β < 1`. -/
theorem sharpDualObjective_expMeasure_of_lt (t : ℝ) {β : Fin 1 → ℝ} (hβ : β 0 < 1) :
    sharpDualObjective (expMeasure 1) featureLineVec (featureLineVec t) β =
      ENNReal.ofReal (Real.exp (-(β 0 * t)) / (1 - β 0)) := by
  rw [sharpDualObjective_expMeasure, lintegral_exp_mul_expMeasure_of_lt hβ,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_one_div]

/-- The dual objective of the exponential law is infinite for `β ≥ 1`. -/
theorem sharpDualObjective_expMeasure_of_le (t : ℝ) {β : Fin 1 → ℝ} (hβ : 1 ≤ β 0) :
    sharpDualObjective (expMeasure 1) featureLineVec (featureLineVec t) β = ⊤ := by
  rw [sharpDualObjective_expMeasure, lintegral_exp_mul_expMeasure_of_le hβ]
  exact ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

/-- **The population dual minimizer of the exponential law is `β* = 1 - 1/t`.** For `t > 0` and
`β < 1`, `exp(-βt) / (1 - β) ≥ t exp(1 - t)`, the value at `β*`, by `exp(u - 1) ≥ u` at
`u = (1 - β) t`; for `β ≥ 1` the objective is infinite. -/
theorem isMinOn_sharpDualObjective_expMeasure {t : ℝ} (ht : 0 < t) :
    IsMinOn (sharpDualObjective (expMeasure 1) featureLineVec (featureLineVec t)) univ
      (featureLineVec (1 - 1 / t)) := by
  refine isMinOn_iff.2 fun γ _ => ?_
  have hs : (featureLineVec (1 - 1 / t)) 0 < 1 := by
    simp only [featureLineVec]; have := one_div_pos.2 ht; linarith
  rw [sharpDualObjective_expMeasure_of_lt t hs]
  rcases lt_or_ge (γ 0) 1 with hγ | hγ
  · rw [sharpDualObjective_expMeasure_of_lt t hγ]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [featureLineVec]
    have h1 : 1 - (1 - 1 / t) = 1 / t := by ring
    have h2 : -((1 - 1 / t) * t) = 1 - t := by field_simp; ring
    rw [h1, h2, div_div_eq_mul_div, div_one, le_div_iff₀ (by linarith)]
    have h3 := Real.add_one_le_exp ((1 - γ 0) * t - 1)
    have h4 : Real.exp (-(γ 0 * t)) = Real.exp (1 - t) * Real.exp ((1 - γ 0) * t - 1) := by
      rw [← Real.exp_add]; ring_nf
    rw [h4]
    have h5 := Real.exp_pos (1 - t)
    nlinarith
  · rw [sharpDualObjective_expMeasure_of_le t hγ]
    exact le_top

/-- **The exponential moments of the exponential law**: `E[exp(κ |X - t|)] < ∞` exactly when
`κ < 1`. -/
theorem integrable_exp_norm_expMeasure_iff (t κ : ℝ) :
    Integrable (fun x => Real.exp (κ * ‖featureLineVec x - featureLineVec t‖)) (expMeasure 1) ↔
      κ < 1 := by
  have hn : ∀ x, ‖featureLineVec x - featureLineVec t‖ = |x - t| := fun x => by
    rw [show featureLineVec x - featureLineVec t = featureLineVec (x - t) from
      funext fun _ => rfl, norm_featureLineVec]
  simp only [hn]
  have hm : ∀ c : ℝ, Measurable fun x : ℝ => Real.exp (c * x) := fun c => by fun_prop
  constructor
  · intro h
    by_contra hκ
    have h1 : Integrable (fun x => Real.exp (1 * x)) (expMeasure 1) := by
      refine (h.const_mul (Real.exp t)).mono' (hm 1).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : x - t ≤ κ * |x - t| :=
        (le_abs_self _).trans (le_mul_of_one_le_left (abs_nonneg _) (not_lt.1 hκ))
      linarith
    exact lt_irrefl _ (integrable_exp_mul_expMeasure_iff.1 h1)
  · intro hκ
    have hmeas : AEStronglyMeasurable (fun x => Real.exp (κ * |x - t|)) (expMeasure 1) :=
      (by fun_prop : Measurable fun x : ℝ => Real.exp (κ * |x - t|)).aestronglyMeasurable
    rcases le_or_gt κ 0 with h0 | h0
    · refine (integrable_const (1 : ℝ)).mono' hmeas (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg h0 (abs_nonneg _)
    · have i1 := (integrable_exp_mul_expMeasure_iff (c := κ)).2 hκ
      have i2 := (integrable_exp_mul_expMeasure_iff (c := -κ)).2 (by linarith)
      refine ((i1.const_mul (Real.exp (-(κ * t)))).add
        (i2.const_mul (Real.exp (κ * t)))).mono' hmeas (ae_of_all _ fun x => ?_)
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, ← Real.exp_add]
      rcases abs_cases (x - t) with ⟨hx, -⟩ | ⟨hx, -⟩
      · rw [hx]
        have := (Real.exp_pos (κ * t + -κ * x))
        have e : κ * (x - t) = -(κ * t) + κ * x := by ring
        rw [e]; linarith
      · rw [hx]
        have := (Real.exp_pos (-(κ * t) + κ * x))
        have e : κ * -(x - t) = κ * t + -κ * x := by ring
        rw [e]; linarith

/-- `|β*| < 1` exactly when `t > 1/2`, for `β* = 1 - 1/t` and `t > 0`. -/
theorem norm_tiltMinimizer_expMeasure_lt_one_iff {t : ℝ} (ht : 0 < t) :
    ‖featureLineVec (1 - 1 / t)‖ < 1 ↔ 1 / 2 < t := by
  rw [norm_featureLineVec, abs_lt]
  have h1 : (1 : ℝ) / t < 2 ↔ 1 / 2 < t := one_div_lt ht two_pos
  have h2 : (0 : ℝ) < 1 / t := one_div_pos.2 ht
  constructor
  · rintro ⟨h, -⟩; exact h1.1 (by linarith)
  · intro h; exact ⟨by linarith [h1.2 h], by linarith⟩

/-- **When the hypothesis of one exponential moment can be met for the exponential law.** With
`β* = 1 - 1/t`, there is an order `κ` with `E[exp(κ |X - t|)] < ∞` and `κ > 2|β*|` exactly when
`2/3 < t < 2`. -/
theorem exists_order_expMeasure_iff {t : ℝ} (ht : 0 < t) :
    (∃ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖featureLineVec x - featureLineVec t‖))
        (expMeasure 1) ∧ 2 * (1 : ℕ) * ‖featureLineVec (1 - 1 / t)‖ < κ) ↔
      2 / 3 < t ∧ t < 2 := by
  simp only [integrable_exp_norm_expMeasure_iff, Nat.cast_one, mul_one, norm_featureLineVec]
  have hlt : (∃ κ : ℝ, κ < 1 ∧ 2 * |1 - 1 / t| < κ) ↔ 2 * |1 - 1 / t| < 1 :=
    ⟨fun ⟨κ, h1, h2⟩ => h2.trans h1, fun h => ⟨(2 * |1 - 1 / t| + 1) / 2, by linarith,
      by linarith⟩⟩
  rw [hlt, ← lt_div_iff₀' two_pos, abs_lt]
  have h1 : (1 : ℝ) / t < 3 / 2 ↔ 1 / (3 / 2) < t := one_div_lt ht (by norm_num)
  have h2 : (1 : ℝ) / 2 < 1 / t ↔ t < 1 / (1 / 2) := lt_one_div (by norm_num) ht
  rw [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] at h1
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num] at h2
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨h1.1 (by linarith), h2.1 (by linarith)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by linarith [h1.2 ha], by linarith [h2.2 hb]⟩

/-- **The population weight of the exponential law has a finite second moment exactly when
`t < 2`**: for `β* = 1 - 1/t`, `E[exp(β*(X - t))²] < ∞` exactly when `2β* < 1`. -/
theorem integrable_sq_tilt_expMeasure_iff {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => Real.exp (featureLineVec (1 - 1 / t) ⬝ᵥ
      (featureLineVec x - featureLineVec t)) ^ 2) (expMeasure 1) ↔ t < 2 := by
  rw [integrable_sq_tilt_iff]
  simp only [dotProduct_featureLineVec_sub, Pi.smul_apply, smul_eq_mul]
  have e : (fun x => Real.exp (2 * featureLineVec (1 - 1 / t) 0 * (x - t))) =
      fun x => Real.exp (-(2 * (1 - 1 / t) * t)) * Real.exp ((2 * (1 - 1 / t)) * x) :=
    funext fun x => by rw [← Real.exp_add]; simp only [featureLineVec]; ring_nf
  rw [e, integrable_const_mul_iff (isUnit_iff_ne_zero.2 (Real.exp_pos _).ne'),
    integrable_exp_mul_expMeasure_iff]
  have h2 : (1 : ℝ) / 2 < 1 / t ↔ t < 1 / (1 / 2) := lt_one_div (by norm_num) ht
  rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num] at h2
  constructor
  · intro h; exact h2.1 (by linarith)
  · intro h; linarith [h2.2 h]

end ExpLaw

end PopulationAdjustment

end CausalInference
