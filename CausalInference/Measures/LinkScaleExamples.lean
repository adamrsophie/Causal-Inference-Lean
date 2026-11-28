/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Measures.OddsRatioLink
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.Complex.Exponential

/-!
# Concrete models on a link scale: noncollapsibility and scale dependence

All models have a binary covariate with both levels of probability `1/2` (`halfLaw`).

## Main definitions

* `logisticRef`, `logisticAct`: the risks of a logistic model in the two strata.
* `scaleRef`, `scaleAct`, `commonOrRef`, `commonOrAct`: two pairs of stratum risks.

## Main results

* `logisticExample_contrast`, `logisticExample_linkMarginal`, `logisticExample_value`: in the
  logistic model with reference risks `expit (∓1)` and active risks `expit (1/2)`,
  `expit (5/2)`, the conditional log odds ratio is `3/2` in both strata, the marginal reference
  risk is `1/2`, and the marginal log odds ratio is
  `log ((r + r⁵ + 2 r⁶) / (2 + r + r⁵))` with `r = e^{1/2}`, a number in `(1.22704, 1.22705)`,
  strictly between `0` and `3/2` as `logit_linkMarginal_attenuation` predicts.
* `not_linkCollapsible_logit`: the odds ratio is not collapsible.
* `effectModifier_scale_dependence`: risks `(1/10, 1/2)` and `(1/5, 3/5)` have the constant risk
  difference `1/10` and the conditional odds ratios `9/4` and `3/2`: the covariate is an effect
  modifier on the logit scale and not on the identity scale.
* `effectModifier_collapsibility_independent`: effect modification and noncollapsibility are
  independent; all four combinations occur.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Section 4.1 and Fine
  Point 4.3.
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace EffectMeasure

/-! ### The inverse of the logit -/

/-- `expit t = exp t / (1 + exp t)`. -/
theorem sigmoid_eq_exp_div (t : ℝ) : Real.sigmoid t = Real.exp t / (1 + Real.exp t) := by
  rw [Real.sigmoid_def, Real.exp_neg]
  field_simp
  ring

/-- The odds of `expit t` are `exp t`. -/
theorem odds_sigmoid (t : ℝ) : odds (Real.sigmoid t) = Real.exp t := by
  rw [odds, sigmoid_eq_exp_div]
  have h := Real.exp_pos t
  field_simp
  ring

/-- `logit ∘ expit = id`. -/
theorem logit_sigmoid (t : ℝ) : logit (Real.sigmoid t) = t := by
  rw [logit, odds_sigmoid, Real.log_exp]

/-- `expit ∘ logit = id` on `(0, 1)`. -/
theorem sigmoid_logit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : Real.sigmoid (logit p) = p := by
  have h1 : (0 : ℝ) < 1 - p := by linarith
  rw [sigmoid_eq_exp_div, logit, Real.exp_log (odds_pos hp0 hp1), odds]
  field_simp
  ring

theorem sigmoid_mem_Ioo (t : ℝ) : Real.sigmoid t ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨Real.sigmoid_pos t, Real.sigmoid_lt_one t⟩

/-! ### A logistic model -/

/-- The reference risks of the logistic model: `expit 1` in stratum `true`, `expit (-1)` in
stratum `false`. -/
noncomputable def logisticRef (v : Bool) : ℝ := Real.sigmoid (if v then 1 else -1)

/-- The active risks of the logistic model: `expit (5/2)` and `expit (1/2)`. -/
noncomputable def logisticAct (v : Bool) : ℝ := Real.sigmoid (if v then 5 / 2 else 1 / 2)

/-- The conditional log odds ratio of the logistic model is `3/2` in both strata. -/
theorem logisticExample_contrast (v : Bool) :
    linkContrast logit logisticRef logisticAct v = 3 / 2 := by
  cases v <;> norm_num [linkContrast, logisticRef, logisticAct, logit_sigmoid]

/-- The marginal reference risk of the logistic model is `1/2`. -/
theorem logisticExample_integral_ref : ∫ v, logisticRef v ∂halfLaw = 1 / 2 := by
  rw [integral_halfLaw]
  have := Real.sigmoid_neg 1
  simp only [logisticRef, ite_true, Bool.false_eq_true, ite_false]
  linarith

/-- **The marginal log odds ratio of the logistic model in closed form**:
`log ((r + r⁵ + 2 r⁶) / (2 + r + r⁵))` with `r = e^{1/2}`. -/
theorem logisticExample_linkMarginal :
    linkMarginal logit halfLaw logisticRef logisticAct =
      Real.log ((Real.exp (1 / 2) + Real.exp (1 / 2) ^ 5 + 2 * Real.exp (1 / 2) ^ 6) /
        (2 + Real.exp (1 / 2) + Real.exp (1 / 2) ^ 5)) := by
  set r := Real.exp (1 / 2) with hr
  have r0 : 0 < r := Real.exp_pos _
  have e5 : Real.exp (5 / 2) = r ^ 5 := by
    rw [hr, ← Real.exp_nat_mul]
    norm_num
  have hA : ∫ v, logisticAct v ∂halfLaw = (r ^ 5 / (1 + r ^ 5) + r / (1 + r)) / 2 := by
    rw [integral_halfLaw]
    simp only [logisticAct, ite_true, Bool.false_eq_true, ite_false, sigmoid_eq_exp_div, e5]
    rfl
  have hodds : odds ((r ^ 5 / (1 + r ^ 5) + r / (1 + r)) / 2) =
      (r + r ^ 5 + 2 * r ^ 6) / (2 + r + r ^ 5) := by
    rw [odds]
    have h1 : 0 < 1 + r := by linarith
    have h5 : 0 < 1 + r ^ 5 := by positivity
    have h2 : 0 < 2 + r + r ^ 5 := by positivity
    rw [div_eq_div_iff (by field_simp; ring_nf; positivity) h2.ne']
    field_simp
    ring
  rw [linkMarginal, hA, logisticExample_integral_ref, logit, logit, hodds, odds]
  norm_num

/-- **The odds ratio is not collapsible**: in the logistic model the conditional log odds ratio
is `3/2` in both strata, and the marginal log odds ratio lies strictly between `0` and `3/2`.
The bounds are an instance of the attenuation theorem `logit_linkMarginal_attenuation`. -/
theorem logisticExample_bounds :
    0 < linkMarginal logit halfLaw logisticRef logisticAct ∧
      linkMarginal logit halfLaw logisticRef logisticAct < 3 / 2 := by
  have hW : IsPrognostic halfLaw logisticRef := by
    rw [isPrognostic_stratumLaw_iff (fun _ => by norm_num)]
    refine ⟨true, false, fun h => ?_⟩
    have := Real.sigmoid_neg 1
    have hlt : Real.sigmoid (-1) < Real.sigmoid 1 := Real.sigmoid_strictMono (by norm_num)
    simp only [logisticRef, ite_true, Bool.false_eq_true, ite_false] at h
    linarith
  obtain ⟨-, h2, h3⟩ := logit_linkMarginal_attenuation (ν := halfLaw) (a := logisticRef)
    (b := logisticAct)
    (integrable_stratumLaw _ _) (integrable_stratumLaw _ _)
    (ae_halfLaw_iff.2 fun v => ⟨sigmoid_mem_Ioo _, sigmoid_mem_Ioo _⟩) (c := 3 / 2)
    (by norm_num) (ae_halfLaw_iff.2 logisticExample_contrast) hW
  have hpos : 0 < linkMarginal logit halfLaw logisticRef logisticAct := by nlinarith
  rw [abs_of_pos hpos, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at h2
  exact ⟨hpos, h2⟩

/-- **The odds ratio is not collapsible on the logit scale**: the logistic model is a
counterexample to `LinkCollapsible (Set.Ioo 0 1) logit`. -/
theorem not_linkCollapsible_logit : ¬ LinkCollapsible (Set.Ioo 0 1) logit := by
  intro h
  have := h Bool halfLaw logisticRef logisticAct (integrable_stratumLaw _ _)
    (integrable_stratumLaw _ _) (ae_halfLaw_iff.2 fun v => ⟨sigmoid_mem_Ioo _, sigmoid_mem_Ioo _⟩)
    (3 / 2) (ae_halfLaw_iff.2 logisticExample_contrast)
  linarith [logisticExample_bounds.2]

/-- Taylor bounds for `exp` on `[0, 1]` with ten terms. -/
theorem abs_exp_sub_taylor_ten_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    |Real.exp x - ∑ m ∈ Finset.range 10, x ^ m / m.factorial| ≤
      x ^ 10 * (11 / (3628800 * 10)) := by
  have := Real.exp_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1) (n := 10) (by norm_num)
  rw [abs_of_nonneg h0] at this
  simpa [Nat.factorial] using this

/-- **The value of the marginal log odds ratio of the logistic model**:
`1.22704 < log ((r + r⁵ + 2 r⁶) / (2 + r + r⁵)) < 1.22705`, against the conditional `1.5`. -/
theorem logisticExample_value :
    1.22704 < linkMarginal logit halfLaw logisticRef logisticAct ∧
      linkMarginal logit halfLaw logisticRef logisticAct < 1.22705 := by
  rw [logisticExample_linkMarginal]
  set r := Real.exp (1 / 2)
  have hr := abs_exp_sub_taylor_ten_le (x := 1 / 2) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hr
  rw [abs_le] at hr
  norm_num at hr
  have rl : (1.6487212 : ℝ) < r := by linarith [hr.1]
  have ru : r < (1.6487213 : ℝ) := by linarith [hr.2]
  have r0 : 0 < r := by linarith
  have ha := abs_exp_sub_taylor_ten_le (x := 0.61352) (by norm_num) (by norm_num)
  have hb := abs_exp_sub_taylor_ten_le (x := 0.613525) (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ha hb
  rw [abs_le] at ha hb
  norm_num at ha hb
  have eau : Real.exp 0.61352 < (1.8469212 : ℝ) := by linarith [ha.2]
  have ebl : (1.8469303 : ℝ) < Real.exp 0.613525 := by linarith [hb.1]
  have hD : 0 < 2 + r + r ^ 5 := by positivity
  have hRpos : 0 < (r + r ^ 5 + 2 * r ^ 6) / (2 + r + r ^ 5) := by positivity
  have N_lo : (1.6487212 : ℝ) + 1.6487212 ^ 5 + 2 * 1.6487212 ^ 6 < r + r ^ 5 + 2 * r ^ 6 := by
    have h5 := pow_lt_pow_left₀ rl (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)
    have h6 := pow_lt_pow_left₀ rl (by norm_num) (by norm_num : (6 : ℕ) ≠ 0)
    linarith
  have N_hi : r + r ^ 5 + 2 * r ^ 6 < (1.6487213 : ℝ) + 1.6487213 ^ 5 + 2 * 1.6487213 ^ 6 := by
    have h5 := pow_lt_pow_left₀ ru r0.le (by norm_num : (5 : ℕ) ≠ 0)
    have h6 := pow_lt_pow_left₀ ru r0.le (by norm_num : (6 : ℕ) ≠ 0)
    linarith
  have D_lo : (2 : ℝ) + 1.6487212 + 1.6487212 ^ 5 < 2 + r + r ^ 5 := by
    have h5 := pow_lt_pow_left₀ rl (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)
    linarith
  have D_hi : 2 + r + r ^ 5 < (2 : ℝ) + 1.6487213 + 1.6487213 ^ 5 := by
    have h5 := pow_lt_pow_left₀ ru r0.le (by norm_num : (5 : ℕ) ≠ 0)
    linarith
  constructor
  · rw [Real.lt_log_iff_exp_lt hRpos, lt_div_iff₀ hD]
    have e2 : Real.exp 1.22704 = Real.exp 0.61352 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e2]
    have hsq : Real.exp 0.61352 ^ 2 < (1.8469212 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ eau (Real.exp_pos _).le (by norm_num)
    have : (1.8469212 : ℝ) ^ 2 * ((2 : ℝ) + 1.6487213 + 1.6487213 ^ 5) <
        (1.6487212 : ℝ) + 1.6487212 ^ 5 + 2 * 1.6487212 ^ 6 := by norm_num
    nlinarith
  · rw [Real.log_lt_iff_lt_exp hRpos, div_lt_iff₀ hD]
    have e2 : Real.exp 1.22705 = Real.exp 0.613525 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e2]
    have hsq : (1.8469303 : ℝ) ^ 2 < Real.exp 0.613525 ^ 2 :=
      pow_lt_pow_left₀ ebl (by norm_num) (by norm_num)
    have : (1.6487213 : ℝ) + 1.6487213 ^ 5 + 2 * 1.6487213 ^ 6 <
        (1.8469303 : ℝ) ^ 2 * ((2 : ℝ) + 1.6487212 + 1.6487212 ^ 5) := by norm_num
    nlinarith

/-! ### Scale dependence and independence of the two notions -/

/-- Reference risks `1/2` and `1/10`. -/
noncomputable def scaleRef (v : Bool) : ℝ := if v then 1 / 2 else 1 / 10

/-- Active risks `3/5` and `1/5`. -/
noncomputable def scaleAct (v : Bool) : ℝ := if v then 3 / 5 else 1 / 5

/-- Reference risks `2/5` and `1/10`. -/
noncomputable def commonOrRef (v : Bool) : ℝ := if v then 2 / 5 else 1 / 10

/-- Active risks `4/5` and `2/5`. -/
noncomputable def commonOrAct (v : Bool) : ℝ := if v then 4 / 5 else 2 / 5

theorem scale_contrast_id (v : Bool) : linkContrast id scaleRef scaleAct v = 1 / 10 := by
  cases v <;> norm_num [linkContrast, scaleRef, scaleAct]

theorem scale_contrast_logit :
    linkContrast logit scaleRef scaleAct true = Real.log (3 / 2) ∧
      linkContrast logit scaleRef scaleAct false = Real.log (9 / 4) := by
  constructor <;>
  · simp only [linkContrast, scaleRef, scaleAct, ite_true, Bool.false_eq_true, ite_false]
    rw [logit_sub_logit (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [oddsRatio, odds]

theorem commonOr_contrast_logit (v : Bool) :
    linkContrast logit commonOrRef commonOrAct v = Real.log 6 := by
  cases v <;>
  · simp only [linkContrast, commonOrRef, commonOrAct, ite_true, Bool.false_eq_true, ite_false]
    rw [logit_sub_logit (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [oddsRatio, odds]

theorem log_ne_log_of_ne {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ≠ y) :
    Real.log x ≠ Real.log y :=
  fun e => h (Real.log_injOn_pos hx hy e)

/-- **Effect modification depends on the scale.** With reference risks `1/2`, `1/10` and active
risks `3/5`, `1/5`, the risk difference is `1/10` in both strata, while the odds ratios are
`3/2` and `9/4`: the covariate is not an effect modifier on the identity scale and is one on the
logit scale. -/
theorem effectModifier_scale_dependence :
    ¬ IsEffectModifier halfLaw id scaleRef scaleAct ∧
      IsEffectModifier halfLaw logit scaleRef scaleAct := by
  have hπ : ∀ v : Bool, 0 < (fun _ => (1 / 2 : ℝ)) v := fun _ => by norm_num
  refine ⟨fun h => h ⟨1 / 10, Filter.Eventually.of_forall scale_contrast_id⟩,
    (isEffectModifier_stratumLaw_iff hπ).2 ⟨true, false, ?_⟩⟩
  rw [scale_contrast_logit.1, scale_contrast_logit.2]
  exact log_ne_log_of_ne (by norm_num) (by norm_num) (by norm_num)

/-- **Effect modification and noncollapsibility are independent**: all four combinations
occur, on a binary covariate with both levels of probability `1/2`.
1. Risks `(1/2, 1/10)` and `(3/5, 1/5)`: no effect modification on the identity scale, and the
   marginal risk difference is the average conditional one.
2. Risks `(2/5, 1/10)` and `(4/5, 2/5)`: effect modification on the identity scale (risk
   differences `2/5` and `3/10`), and the marginal risk difference is still the average.
3. The same risks have the conditional odds ratio `6` in both strata (no effect modification on
   the logit scale), and the marginal log odds ratio `log (9/2)` is below `log 6`, toward the
   null as `logit_linkMarginal_attenuation` predicts.
4. The risks of item 1 are effect modifiers on the logit scale (odds ratios `3/2` and `9/4`), and
   the marginal log odds ratio `log (14/9)` is not the average `(log (3/2) + log (9/4)) / 2`. -/
theorem effectModifier_collapsibility_independent :
    (¬ IsEffectModifier halfLaw id scaleRef scaleAct ∧
      linkMarginal id halfLaw scaleRef scaleAct = linkConditional id halfLaw scaleRef scaleAct) ∧
    (IsEffectModifier halfLaw id commonOrRef commonOrAct ∧
      linkMarginal id halfLaw commonOrRef commonOrAct =
        linkConditional id halfLaw commonOrRef commonOrAct) ∧
    (¬ IsEffectModifier halfLaw logit commonOrRef commonOrAct ∧
      linkMarginal logit halfLaw commonOrRef commonOrAct = Real.log (9 / 2) ∧
      linkConditional logit halfLaw commonOrRef commonOrAct = Real.log 6 ∧
      Real.log (9 / 2) < Real.log 6) ∧
    (IsEffectModifier halfLaw logit scaleRef scaleAct ∧
      linkMarginal logit halfLaw scaleRef scaleAct = Real.log (14 / 9) ∧
      linkConditional logit halfLaw scaleRef scaleAct = (Real.log (3 / 2) + Real.log (9 / 4)) / 2 ∧
      Real.log (14 / 9) ≠ (Real.log (3 / 2) + Real.log (9 / 4)) / 2) := by
  have hπ : ∀ v : Bool, 0 < (fun _ => (1 / 2 : ℝ)) v := fun _ => by norm_num
  have hrd : ∀ a b : Bool → ℝ, linkMarginal id halfLaw a b = linkConditional id halfLaw a b :=
    fun a b => linkDirectlyCollapsible_id Bool halfLaw a b (integrable_stratumLaw _ _)
      (integrable_stratumLaw _ _) (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩)
      (integrable_stratumLaw _ _)
  refine ⟨⟨effectModifier_scale_dependence.1, hrd _ _⟩, ⟨?_, hrd _ _⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨effectModifier_scale_dependence.2, ?_, ?_, ?_⟩⟩
  · refine (isEffectModifier_stratumLaw_iff hπ).2 ⟨true, false, ?_⟩
    norm_num [linkContrast, commonOrRef, commonOrAct]
  · exact fun h => h ⟨Real.log 6, Filter.Eventually.of_forall commonOr_contrast_logit⟩
  · rw [linkMarginal, integral_halfLaw, integral_halfLaw]
    simp only [commonOrRef, commonOrAct, ite_true, Bool.false_eq_true, ite_false]
    rw [logit_sub_logit (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [oddsRatio, odds]
  · rw [linkConditional, integral_halfLaw, commonOr_contrast_logit, commonOr_contrast_logit]
    ring
  · exact Real.log_lt_log (by norm_num) (by norm_num)
  · rw [linkMarginal, integral_halfLaw, integral_halfLaw]
    simp only [scaleRef, scaleAct, ite_true, Bool.false_eq_true, ite_false]
    rw [logit_sub_logit (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num [oddsRatio, odds]
  · rw [linkConditional, integral_halfLaw, scale_contrast_logit.1, scale_contrast_logit.2]
  · have e : 2 * Real.log (14 / 9) = Real.log ((14 / 9) ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [← Real.log_mul (by norm_num) (by norm_num), ne_eq, eq_div_iff (by norm_num),
      mul_comm, e]
    exact log_ne_log_of_ne (by norm_num) (by norm_num) (by norm_num)

end EffectMeasure

end CausalInference
