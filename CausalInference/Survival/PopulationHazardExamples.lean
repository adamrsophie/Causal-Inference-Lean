/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.PopulationHazard
public import CausalInference.IndirectComparison.SurvivalTransportContinuous
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The population hazard of a mixture: instances

**Time scale: continuous.** Three instances of the survivor weighted hazard formula of
`Survival.PopulationHazard`, each with every hypothesis verified.

* **A model that is not proportional hazards** (`nonPHHazard`): two equally likely strata with
  the conditional hazards `1` and `2 u`. The conditional hazard ratio is `1` at the time `1/2`
  and `2` at the time `1` (`curveHazard_nonPH_ratio`), and the population hazard at the time `1`
  is exactly `3/2` (`popHazard_nonPH_one`): both curves equal `exp (-1)` there, so the survivors
  are still equally split between the strata. At the time `2` the survivors lean to the stratum
  of hazard `1` and the population hazard lies in `(4/3, 11/8)`, below the unweighted mean `5/2`
  (`popHazard_nonPH_two`).
* **The proportional hazards example of `IndirectComparison.SurvivalTransportContinuous`.** In
  the model `phModel` under the law
  `strataLaw` at the time `log 2`, the survivor weighted formula `popHazard_phSurvival_eq_div`
  gives the numerators `1/2`, `3/8` and the denominators `3/8`, `5/32` for the control and the
  treated arm, hence the population hazards `4/3` and `12/5`
  (`popHazard_phModel_strataLaw_eq_div`), in agreement with `popHazard_phModel_strataLaw`.
* **A gamma frailty over a continuous covariate law.** With the frailty `x` distributed as
  Mathlib's `gammaMeasure a r` and the conditional hazards `x g₀(u)`, the population hazard at a
  time `s` with `∫₀ˢ g₀ > 0` is `g₀(s) a / (r + ∫₀ˢ g₀)` and the frailty of the survivors is
  `gammaMeasure a (r + ∫₀ˢ g₀)` (`popHazard_gammaFrailty`);
  with an exponential frailty of rate `1` and the unit baseline the population hazard at the
  time `1` is `1/2` (`popHazard_gammaFrailty_one`).

## Main definitions

* `nonPHHazard`.

## Main results

* `isEnvelopedHazardAt_nonPH`, `curveHazard_nonPH_ratio`, `popHazard_nonPH_one`,
  `popHazard_nonPH_one_mem_Icc`, `popHazard_nonPH_two`.
* `popHazard_phModel_strataLaw_eq_div`.
* `popHazard_gammaFrailty`, `popHazard_gammaFrailty_one`.

## References

* M. A. Hernán, *The hazards of hazard ratios*, Epidemiology 21 (2010).
* O. O. Aalen, R. J. Cook and K. Røysland, *Does Cox analysis of a randomized survival study
  yield a causal treatment effect?*, Lifetime Data Analysis 21 (2015).
-/

@[expose] public section

namespace CausalInference

namespace Survival

namespace ContinuousTime

open MeasureTheory Set Metric EffectMeasure

/-! ### A model that is not proportional hazards -/

/-- The conditional hazards of two strata: `2 u` in the stratum `true` and `1` in the stratum
`false`. -/
noncomputable def nonPHHazard (b : Bool) (u : ℝ) : ℝ := if b then 2 * u else 1

theorem continuous_nonPHHazard (b : Bool) : Continuous (nonPHHazard b) := by
  cases b
  · exact continuous_const
  · exact continuous_const.mul continuous_id

theorem cumHazard_nonPHHazard (b : Bool) (u : ℝ) :
    cumHazard (nonPHHazard b) u = if b then u ^ 2 else u := by
  cases b
  · simp [cumHazard, nonPHHazard]
  · simp only [cumHazard, nonPHHazard, ite_true]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring

/-- **The model is not proportional hazards**: the conditional hazard ratio of the stratum
`true` against the stratum `false` is `1` at the time `1/2` and `2` at the time `1`. -/
theorem curveHazard_nonPH_ratio :
    curveHazard (hazardCurves nonPHHazard true) (1 / 2) /
        curveHazard (hazardCurves nonPHHazard false) (1 / 2) = 1 ∧
      curveHazard (hazardCurves nonPHHazard true) 1 /
        curveHazard (hazardCurves nonPHHazard false) 1 = 2 := by
  simp only [hazardCurves, curveHazard_expSurvival_cumHazard (continuous_nonPHHazard _)]
  norm_num [nonPHHazard]

/-- **The regularity holds at every time `s > 0`**: with the radius `s` the hazards are
continuous and at most `4 s + 1` on `(0, 2 s)`. -/
theorem isEnvelopedHazardAt_nonPH {s : ℝ} (hs : 0 < s) :
    IsEnvelopedHazardAt halfLaw nonPHHazard s := by
  refine IsEnvelopedHazardAt.of_hazard_le (g := fun _ => 4 * s + 1)
    (measurable_from_prod_countable_right fun b => (continuous_nonPHHazard b).measurable)
    (Filter.Eventually.of_forall fun b u hu => ?_)
    (Filter.Eventually.of_forall fun b u _ => (continuous_nonPHHazard b).intervalIntegrable _ _)
    hs le_rfl (integrable_const _)
    (Filter.Eventually.of_forall fun b => ⟨(continuous_nonPHHazard b).continuousOn,
      fun u hu => ?_⟩)
  · cases b
    · simp [nonPHHazard]
    · simp only [nonPHHazard, ite_true]
      linarith
  · rw [mem_ball, Real.dist_eq, abs_lt] at hu
    cases b
    · simp only [nonPHHazard, Bool.false_eq_true, ite_false]
      linarith
    · simp only [nonPHHazard, ite_true]
      linarith

/-- **The population hazard at the time `1` is `3/2`.** Both conditional curves equal
`exp (-1)` at the time `1`, so the survivors are equally split and the population hazard is the
mean `(2 + 1) / 2` of the conditional hazards. -/
theorem popHazard_nonPH_one :
    popHazard halfLaw (hazardCurves nonPHHazard) 1 = 3 / 2 := by
  rw [(popHazard_hazardCurves (isEnvelopedHazardAt_nonPH one_pos)).2, integral_halfLaw,
    integral_halfLaw]
  simp only [hazardCurves_apply, cumHazard_nonPHHazard, nonPHHazard]
  have : 0 < Real.exp (-1) := Real.exp_pos _
  norm_num
  field_simp
  ring

/-- The bounds of `popHazard_hazardCurves_mem_Icc` at the time `1`: the conditional hazards are
`2` and `1` there, so the population hazard lies in `[1, 2]`. -/
theorem popHazard_nonPH_one_mem_Icc : popHazard halfLaw (hazardCurves nonPHHazard) 1 ∈ Icc 1 2 :=
  popHazard_hazardCurves_mem_Icc (isEnvelopedHazardAt_nonPH one_pos)
    (Filter.Eventually.of_forall fun b => by cases b <;> norm_num [nonPHHazard])

/-- **The population hazard at the time `2`: the weighting matters.** At the time `2` the
conditional hazards are `4` and `1` and the conditional curves are `exp (-4)` and `exp (-2)`,
so the survivors lean to the stratum of hazard `1`. With `x = exp (-2)` the population hazard
is `(4 x + 1) / (x + 1)`, and `7 < exp 2 < 8` gives `4/3 < popHazard < 11/8`, well below the
unweighted mean `5/2` of the conditional hazards. -/
theorem popHazard_nonPH_two :
    popHazard halfLaw (hazardCurves nonPHHazard) 2 =
        (4 * Real.exp (-2) + 1) / (Real.exp (-2) + 1) ∧
      4 / 3 < popHazard halfLaw (hazardCurves nonPHHazard) 2 ∧
      popHazard halfLaw (hazardCurves nonPHHazard) 2 < 11 / 8 := by
  set x := Real.exp (-2) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hx4 : Real.exp (-(2 : ℝ) ^ 2) = x * x := by
    rw [hxdef, ← Real.exp_add]
    norm_num
  have hE : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have hxE : x * Real.exp 2 = 1 := by
    rw [hxdef, ← Real.exp_add]
    norm_num
  have hlo := Real.exp_one_gt_d9
  have hhi := Real.exp_one_lt_d9
  have hE7 : 7 < Real.exp 2 := by rw [hE]; nlinarith
  have hE8 : Real.exp 2 < 8 := by rw [hE]; nlinarith
  have hform : popHazard halfLaw (hazardCurves nonPHHazard) 2 = (4 * x + 1) / (x + 1) := by
    rw [(popHazard_hazardCurves (isEnvelopedHazardAt_nonPH two_pos)).2, integral_halfLaw,
      integral_halfLaw]
    simp only [hazardCurves_apply, cumHazard_nonPHHazard, nonPHHazard, ite_true,
      Bool.false_eq_true, ite_false]
    rw [hx4]
    field_simp
    ring
  refine ⟨hform, ?_, ?_⟩
  · rw [hform, lt_div_iff₀ (by linarith)]
    nlinarith
  · rw [hform, div_lt_iff₀ (by linarith)]
    nlinarith

/-! ### The proportional hazards example `phModel` -/

section PHModel

open IndirectComparison

/-- Integrals against `strataLaw` are averages over the strata `0` and `1`. -/
theorem integral_strataLaw_eq {f : (Fin 1 → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂strataLaw = (f (strataCov true) + f (strataCov false)) / 2 := by
  rw [strataLaw, integral_map (measurable_of_finite strataCov).aemeasurable
    hf.aestronglyMeasurable, integral_halfLaw]

/-- **The survivor weighted formula on `phModel`.** Under `strataLaw` at the time `log 2` with
the unit baseline, `popHazard_phSurvival_eq_div` writes the population hazard of the arm `a` as
a numerator `∫ ρ x S x dν` over a denominator `∫ S x dν`; these are `1/2` and `3/8` for the
control arm (`a = false`) and `3/8` and `5/32` for the treated arm (`a = true`), so the
population hazards are `4/3` and `12/5`. -/
theorem popHazard_phModel_strataLaw_eq_div (a : Bool) :
    popHazard strataLaw (phCurve phModel id a) (Real.log 2) =
        (∫ x, Real.exp (phModel.predictor a x) * 1 * phCurve phModel id a x (Real.log 2)
          ∂strataLaw) / ∫ x, phCurve phModel id a x (Real.log 2) ∂strataLaw ∧
      (∫ x, Real.exp (phModel.predictor a x) * 1 * phCurve phModel id a x (Real.log 2)
          ∂strataLaw) = (if a then 3 / 8 else 1 / 2) ∧
      (∫ x, phCurve phModel id a x (Real.log 2) ∂strataLaw) = (if a then 5 / 32 else 3 / 8) ∧
      popHazard strataLaw (phCurve phModel id a) (Real.log 2) = (if a then 12 / 5 else 4 / 3) := by
  have hρ : Measurable fun x => Real.exp (phModel.predictor a x) :=
    (measurable_predictor phModel a).exp
  have hS : Measurable fun x => phCurve phModel id a x (Real.log 2) :=
    (hρ.mul_const _).neg.exp
  have hform : popHazard strataLaw (phCurve phModel id a) (Real.log 2) =
      (∫ x, Real.exp (phModel.predictor a x) * 1 * phCurve phModel id a x (Real.log 2)
        ∂strataLaw) / ∫ x, phCurve phModel id a x (Real.log 2) ∂strataLaw :=
    popHazard_phSurvival_eq_div hρ (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      (hasDerivAt_id (Real.log 2)) log_two_pos'
  have hnum : (∫ x, Real.exp (phModel.predictor a x) * 1 * phCurve phModel id a x (Real.log 2)
      ∂strataLaw) = (if a then 3 / 8 else 1 / 2) := by
    have hm : Measurable fun x =>
        Real.exp (phModel.predictor a x) * 1 * phCurve phModel id a x (Real.log 2) :=
      (hρ.mul_const 1).mul hS
    rw [integral_strataLaw_eq hm]
    simp only [phCurve, phSurvival, exp_phModel_predictor, id, exp_neg_mul_log_two]
    cases a <;> norm_num [phRate]
  have hden : (∫ x, phCurve phModel id a x (Real.log 2) ∂strataLaw) =
      (if a then 5 / 32 else 3 / 8) := by
    rw [integral_strataLaw_eq hS]
    simp only [phCurve, phSurvival, exp_phModel_predictor, id, exp_neg_mul_log_two]
    cases a <;> norm_num [phRate]
  refine ⟨hform, hnum, hden, ?_⟩
  rw [hform, hnum, hden]
  cases a <;> norm_num

end PHModel

/-! ### A gamma frailty over a continuous covariate law -/

section GammaFrailty

open ProbabilityTheory Bias.HazardMixtureGeneral

/-- **Gamma frailty: the population hazard and the survivors.** Let the frailty `x` follow
`gammaMeasure a r` (`a, r > 0`) and the conditional hazards be `x g₀(u)`, with a measurable
baseline `g₀ ≥ 0` on `[0, ∞)`, integrable on every `[0, u]` and continuous on `(s - ε₀, s + ε₀)`
with `0 < ε₀ ≤ s`, and `∫₀ˢ g₀ > 0`. Then the family is regular at `s`, the population hazard at
`s` is `g₀(s) a / (r + ∫₀ˢ g₀)`, and the frailty of the survivors at `s` follows
`gammaMeasure a (r + ∫₀ˢ g₀)`. -/
theorem popHazard_gammaFrailty {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {g₀ : ℝ → ℝ}
    (hm₀ : Measurable g₀) (hn₀ : ∀ u, 0 ≤ u → 0 ≤ g₀ u)
    (hi₀ : ∀ u, 0 ≤ u → IntervalIntegrable g₀ volume 0 u) {s ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀s : ε₀ ≤ s) (hc₀ : ContinuousOn g₀ (ball s ε₀)) (hΛ : 0 < cumHazard g₀ s) :
    IsEnvelopedHazardAt (gammaMeasure a r) (fun x u => x * g₀ u) s ∧
      popHazard (gammaMeasure a r) (hazardCurves fun x u => x * g₀ u) s =
        g₀ s * (a / (r + cumHazard g₀ s)) ∧
      covSurvivorLaw (gammaMeasure a r) (hazardCurves fun x u => x * g₀ u) s =
        gammaMeasure a (r + cumHazard g₀ s) := by
  have := isProbabilityMeasure_gammaMeasure ha hr
  refine ⟨isEnvelopedHazardAt_mul (ρ := fun x => x) measurable_id ae_nonneg_gammaMeasure hm₀ hn₀
    hi₀ hε₀ hε₀s hc₀ hΛ, ?_, ?_⟩
  · rw [hazardCurves_mul, popHazard_phSurvival_cumHazard_genHazard (ρ := fun x => x)
      measurable_id ae_nonneg_gammaMeasure hm₀ hn₀ hi₀ hε₀ hε₀s hc₀ hΛ, Measure.map_id',
      genHazard_gamma ha hr hΛ.le]
  · have h := map_covSurvivorLaw_phSurvival (ν := gammaMeasure a r) (ρ := fun x => x)
      measurable_id (cumHazard g₀) s
    rw [Measure.map_id', Measure.map_id', survivorLaw_gamma ha hr hΛ.le] at h
    rw [hazardCurves_mul, h]

/-- **Exponential frailty: numbers.** With the frailty of law `gammaMeasure 1 1` (exponential
of rate `1`) and the unit baseline, the population hazard at the time `1` is `1/2`, and the
frailty of the survivors at the time `1` follows `gammaMeasure 1 2`. -/
theorem popHazard_gammaFrailty_one :
    popHazard (gammaMeasure 1 1) (hazardCurves fun x _ => x * 1) 1 = 1 / 2 ∧
      covSurvivorLaw (gammaMeasure 1 1) (hazardCurves fun x _ => x * 1) 1 = gammaMeasure 1 2 := by
  have hΛ : cumHazard (fun _ => (1 : ℝ)) 1 = 1 := by simp [cumHazard]
  obtain ⟨-, h1, h2⟩ := popHazard_gammaFrailty one_pos one_pos (g₀ := fun _ => 1)
    measurable_const (fun _ _ => zero_le_one) (fun _ _ => intervalIntegrable_const) one_pos le_rfl
    continuousOn_const (by rw [hΛ]; exact one_pos)
  rw [hΛ] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [h1]
    norm_num
  · rw [h2]
    norm_num

end GammaFrailty

end ContinuousTime

end Survival

end CausalInference
