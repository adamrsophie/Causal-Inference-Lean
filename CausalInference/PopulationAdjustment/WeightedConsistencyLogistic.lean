/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.DensityRatio
public import CausalInference.PointTreatment.OverlapVarianceExample
public import CausalInference.PointTreatment.Randomized
public import CausalInference.Measures.LinkScale

/-!
# Logistic membership with a nonzero slope: the density ratio in numbers

`map_cond_eq_withDensity_tiltWeight` turns a logistic membership model
`P(S = true | X = x) = σ(α̃ + β̃ᵀx)` into a log linear density ratio between the target and the
trial covariate laws. This file gives an instance with slope `β̃ = log 3 ≠ 0`.

**The model.** The covariate `X ∈ {0, 1}` (a vector of length one) is a fair coin. Membership of
the trial is `S = 1{V < σ(log 3 · X)}` for an independent uniform `V` on `(0, 1)`, so that
`P(S = true | X) = σ(log 3 · X)`: `1/2` at `X = 0` and `3/4` at `X = 1`
(`isPropensityScore_logisticMembership`, the conditional expectation of the assignment by a
uniform draw). Then `P(S = true) = 5/8` and `P(S = false) = 3/8`
(`logisticLaw_real_true`, `logisticLaw_real_false`), so `k = 5/3`, and the target covariate law
has density `exp(log(5/3) - log 3 · x)` with respect to the trial covariate law: the tilt weights
are `5/3` at `x = 0` and `5/9` at `x = 1` (`logistic_density_ratio_example`). Directly,
`P(X = 0 | S = false) / P(X = 0 | S = true) = (2/3) / (2/5) = 5/3` and
`P(X = 1 | S = false) / P(X = 1 | S = true) = (1/3) / (3/5) = 5/9`.

## Main definitions

* `logisticFeature`, `logisticCovLaw`, `logisticSlope`, `logisticScore`, `logisticLaw`,
  `logisticMembership`.

## Main results

* `isPropensityScore_logisticMembership`.
* `logistic_density_ratio_example`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace CausalInference

namespace PopulationAdjustment

open MissingData PointTreatment EffectMeasure

/-- The covariate value `1{x}` as a vector of length one. -/
def logisticFeature (x : Bool) : Fin 1 → ℝ := fun _ => if x then 1 else 0

/-- The covariate law: a fair coin on `{0, 1}`. -/
noncomputable def logisticCovLaw : Measure (Fin 1 → ℝ) := halfLaw.map logisticFeature

instance : IsProbabilityMeasure logisticCovLaw := by
  unfold logisticCovLaw; infer_instance

/-- The slope `β̃ = log 3` of the membership model. -/
noncomputable def logisticSlope : Fin 1 → ℝ := fun _ => Real.log 3

theorem logisticSlope_ne_zero : logisticSlope ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [logisticSlope, Pi.zero_apply] at h0
  have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  linarith

/-- The membership propensity `σ(0 + β̃ᵀx)`. -/
noncomputable def logisticScore (x : Fin 1 → ℝ) : ℝ := Real.sigmoid (0 + logisticSlope ⬝ᵥ x)

theorem measurable_logisticScore : Measurable logisticScore := by
  unfold logisticScore
  exact continuous_sigmoid.measurable.comp
    (continuous_const.add (continuous_const.dotProduct continuous_id)).measurable

/-- The pooled law of the covariate and the uniform draw. -/
noncomputable def logisticLaw : Measure ((Fin 1 → ℝ) × ℝ) := logisticCovLaw.prod unitUniform

instance : IsProbabilityMeasure logisticLaw := by
  unfold logisticLaw; infer_instance

/-- Membership of the trial: `S = 1{V < σ(β̃ᵀX)}`. -/
noncomputable def logisticMembership : (Fin 1 → ℝ) × ℝ → Bool := drawAssign logisticScore

theorem measurable_logisticMembership : Measurable logisticMembership :=
  measurable_drawAssign measurable_logisticScore

/-- **The membership propensity is logistic with slope `log 3`.** -/
theorem isPropensityScore_logisticMembership :
    IsPropensityScore logisticLaw logisticMembership Prod.fst
      fun x => Real.sigmoid (0 + logisticSlope ⬝ᵥ x) :=
  isPropensityScore_drawAssign logisticCovLaw measurable_logisticScore fun _ =>
    ⟨(Real.sigmoid_pos _).le, (Real.sigmoid_lt_one _).le⟩

theorem logisticScore_feature_false : logisticScore (logisticFeature false) = 1 / 2 := by
  simp only [logisticScore, logisticFeature, dotProduct, Fin.sum_univ_one, Bool.false_eq_true,
    ↓reduceIte, mul_zero, add_zero, Real.sigmoid_def, neg_zero, Real.exp_zero]
  norm_num

theorem logisticScore_feature_true : logisticScore (logisticFeature true) = 3 / 4 := by
  simp only [logisticScore, logisticFeature, dotProduct, Fin.sum_univ_one, logisticSlope,
    ↓reduceIte, mul_one, zero_add, Real.sigmoid_def, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  norm_num

/-- `P(S = true) = 5/8`: the mean of the propensity `(1/2 + 3/4) / 2`. -/
theorem logisticLaw_real_true : logisticLaw.real (logisticMembership ⁻¹' {true}) = 5 / 8 := by
  rw [← integral_respInd measurable_logisticMembership,
    ← integral_condExp measurable_fst.comap_le,
    integral_congr_ae isPropensityScore_logisticMembership.2]
  change ∫ ω, logisticScore ω.1 ∂logisticCovLaw.prod unitUniform = 5 / 8
  rw [integral_fun_fst, probReal_univ, one_smul, logisticCovLaw,
    integral_map (measurable_of_countable _).aemeasurable
      measurable_logisticScore.aestronglyMeasurable, integral_halfLaw,
    logisticScore_feature_true, logisticScore_feature_false]
  norm_num

/-- `P(S = false) = 3/8`. -/
theorem logisticLaw_real_false : logisticLaw.real (logisticMembership ⁻¹' {false}) = 3 / 8 := by
  have hc : logisticMembership ⁻¹' {false} = (logisticMembership ⁻¹' {true})ᶜ := by
    ext ω; simp
  rw [hc, probReal_compl_eq_one_sub (measurable_logisticMembership (measurableSet_singleton _)),
    logisticLaw_real_true]
  norm_num

/-- **The density ratio with a nonzero slope, in numbers.** For the logistic membership model
with slope `log 3`, the target covariate law has density
`tiltWeight id 0 (log (5/3)) (-log 3)` with respect to the trial covariate law, and the tilt
weights are `5/3` at `x = 0` and `5/9` at `x = 1`. -/
theorem logistic_density_ratio_example :
    (logisticLaw[|logisticMembership ⁻¹' {false}]).map Prod.fst =
        ((logisticLaw[|logisticMembership ⁻¹' {true}]).map Prod.fst).withDensity (fun x =>
          ENNReal.ofReal (tiltWeight id 0 (Real.log (5 / 3)) (-logisticSlope) x)) ∧
      logisticSlope ≠ 0 ∧
      tiltWeight id 0 (Real.log (5 / 3)) (-logisticSlope) (logisticFeature false) = 5 / 3 ∧
      tiltWeight id 0 (Real.log (5 / 3)) (-logisticSlope) (logisticFeature true) = 5 / 9 := by
  have hpos : ∀ b : Bool, logisticLaw (logisticMembership ⁻¹' {b}) ≠ 0 := fun b h => by
    have h' : logisticLaw.real (logisticMembership ⁻¹' {b}) = 0 := by
      rw [measureReal_def, h, ENNReal.toReal_zero]
    cases b
    · rw [logisticLaw_real_false] at h'; norm_num at h'
    · rw [logisticLaw_real_true] at h'; norm_num at h'
  have h := map_cond_eq_withDensity_tiltWeight measurable_logisticMembership measurable_fst
    isPropensityScore_logisticMembership (hpos true) (hpos false)
  rw [logisticLaw_real_true, logisticLaw_real_false,
    show (5 / 8 : ℝ) / (3 / 8) = 5 / 3 by norm_num, sub_zero] at h
  refine ⟨h, logisticSlope_ne_zero, ?_, ?_⟩
  · simp only [tiltWeight, id, sub_zero, logisticFeature, Bool.false_eq_true, ↓reduceIte,
      dotProduct, Fin.sum_univ_one, mul_zero, add_zero]
    exact Real.exp_log (by norm_num)
  · simp only [tiltWeight, id, sub_zero, logisticFeature, ↓reduceIte, dotProduct,
      Fin.sum_univ_one, mul_one, Pi.neg_apply, logisticSlope]
    rw [← sub_eq_add_neg, Real.exp_sub, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
    norm_num

end PopulationAdjustment

end CausalInference
