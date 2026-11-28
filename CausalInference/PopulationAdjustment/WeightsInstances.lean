/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightsInstancesTransport
public import CausalInference.PopulationAdjustment.Examples

/-!
# Population adjustment: instances of the sample weighting results

Concrete instances, with every hypothesis verified and the values computed, of the results on
weighted arm means, tilted laws, the empirical law and inverse odds weights.

* **A four unit data set** (`fourUnitArm`, `fourUnitZ` of the examples file, outcomes
  `(1, 3, 0, 2)`, weights `w(z) = 1 + z`, that is `(1, 3, 1, 3)`). The weighted arm means are
  `5/2` and `3/2` (`weightedArmMean_fourUnit`), the values at the empirical law
  (`lawWeightedArmMean_ipdEmpirical_fourUnit`), and the treated one is the ratio `(5/2) / 1` of
  two sample means (`weightedArmMean_eq_div_sampleMean_fourUnit`). With the fitted score
  `1 / (2 + z)` (`1/2` and `1/4`, never `0` or `1`) the Hájek estimator of the treated arm is the
  weighted arm mean with weights `(2, 4)`, equal to `7/3` (`sampleHajekArmMean_fourUnit`).
* **The tilted law of the example of non trivial tilt** has feature mean `3/4`
  (`integral_feature_tilted_tiltExample`, from `integral_feature_tilted_iff`).
* **A three unit sample** with covariates `(-1, 1, 1)` and outcomes `(2, 0, 8)`: its integral
  against the empirical law (`integral_ipdEmpirical_threeUnit`, mean `10/3`), the tilting
  weights of slope `-(log 2) / 2` balance it at `0` in the population sense
  (`populationBalanced_ipdEmpirical_threeUnit`), the tilted empirical law is a probability law
  with feature mean `0` (`integral_feature_tilted_ipdEmpirical_threeUnit`) and outcome mean
  `1/2 · 2 + 1/4 · 0 + 1/4 · 8 = 3` (`integral_tilted_ipdEmpirical_threeUnit`).
* **Inverse odds under a two point law.** The law `δ₀ + δ₁` on `ℝ¹` is not carried by any
  hyperplane (`not_ae_dotProduct_eq_twoPoint`), so `inverseOdds_proportional_ae_iff` applies:
  the inverse odds of the logistic membership `σ(x)` is almost everywhere proportional to the
  tilting weight of slope `β` exactly when `β = -1` (`inverseOdds_proportional_ae_twoPoint`).

## Main results

* `weightedArmMean_fourUnit`, `lawWeightedArmMean_ipdEmpirical_fourUnit`,
  `weightedArmMean_eq_div_sampleMean_fourUnit`, `sampleHajekArmMean_fourUnit`.
* `integral_feature_tilted_tiltExample`.
* `integral_ipdEmpirical_threeUnit`, `populationBalanced_ipdEmpirical_threeUnit`,
  `integral_feature_tilted_ipdEmpirical_threeUnit`, `integral_tilted_ipdEmpirical_threeUnit`.
* `not_ae_dotProduct_eq_twoPoint`, `inverseOdds_proportional_ae_twoPoint`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory PointTreatment IndirectComparison EffectMeasure

/-! ### A four unit data set -/

/-- The outcomes `(1, 3, 0, 2)` of the four unit data set. -/
def fourUnitOutcome : Fin 4 → ℝ := ![1, 3, 0, 2]

/-- The weight function `w(z) = 1 + z`, giving the weights `(1, 3, 1, 3)`. -/
def fourUnitWeight (z : Fin 1 → ℝ) : ℝ := 1 + z 0

/-- **The weighted arm means of the four unit data set**: the arm totals are `4 ≠ 0`, the
treated mean is `(1 · 1 + 3 · 3) / 4 = 5/2` and the untreated mean `(1 · 0 + 3 · 2) / 4 = 3/2`. -/
theorem weightedArmMean_fourUnit :
    (∀ t, ∑ i, armWeights (fun i => fourUnitWeight (fourUnitZ i)) fourUnitArm t i = 4) ∧
      weightedArmMean (fun i => fourUnitWeight (fourUnitZ i)) fourUnitArm fourUnitOutcome true =
        5 / 2 ∧
      weightedArmMean (fun i => fourUnitWeight (fourUnitZ i)) fourUnitArm fourUnitOutcome false =
        3 / 2 := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · cases t <;> simp [armWeights, fourUnitWeight, fourUnitArm, fourUnitZ, Fin.sum_univ_four] <;>
      norm_num
  all_goals
    simp [weightedArmMean, weightedMean, armWeights, fourUnitWeight, fourUnitArm, fourUnitZ,
      fourUnitOutcome, Fin.sum_univ_four]
    norm_num

/-- **The empirical law of the four unit data set** gives the population weighted arm means
`5/2` and `3/2` (`lawWeightedArmMean_ipdEmpirical`). -/
theorem lawWeightedArmMean_ipdEmpirical_fourUnit :
    lawWeightedArmMean (Trial.ipdEmpirical fourUnitZ fourUnitArm fourUnitOutcome) fourUnitWeight
        true = 5 / 2 ∧
      lawWeightedArmMean (Trial.ipdEmpirical fourUnitZ fourUnitArm fourUnitOutcome)
        fourUnitWeight false = 3 / 2 := by
  rw [lawWeightedArmMean_ipdEmpirical (by norm_num), lawWeightedArmMean_ipdEmpirical (by norm_num)]
  exact weightedArmMean_fourUnit.2

/-- The four unit data set as a sequence of observations `(Zᵢ, Aᵢ, Yᵢ)` (fixed data). -/
noncomputable def fourUnitObs (i : ℕ) (_ : Unit) : (Fin 1 → ℝ) × Bool × ℝ :=
  if h : i < 4 then (fourUnitZ ⟨i, h⟩, fourUnitArm ⟨i, h⟩, fourUnitOutcome ⟨i, h⟩)
  else (0, false, 0)

theorem fourUnitObs_fin (i : Fin 4) :
    fourUnitObs i () = (fourUnitZ i, fourUnitArm i, fourUnitOutcome i) := by
  simp [fourUnitObs]

/-- **The weighted arm mean as a ratio of sample means**: for the four observations, the
sample mean of `1{A = true} w(Z) Y` is `5/2` and that of `1{A = true} w(Z)` is `1`, and the
weighted arm mean is their ratio `5/2` (`weightedArmMean_eq_div_sampleMean`). -/
theorem weightedArmMean_eq_div_sampleMean_fourUnit :
    sampleMean (fun z => armIndObs true z * fourUnitWeight z.1 * z.2.2) fourUnitObs 4 () =
        5 / 2 ∧
      sampleMean (fun z => armIndObs true z * fourUnitWeight z.1) fourUnitObs 4 () = 1 ∧
      weightedArmMean (fun i : Fin 4 => fourUnitWeight (fourUnitObs i ()).1)
        (fun i => (fourUnitObs i ()).2.1) (fun i => (fourUnitObs i ()).2.2) true = 5 / 2 := by
  have h1 : sampleMean (fun z => armIndObs true z * fourUnitWeight z.1 * z.2.2) fourUnitObs 4 () =
      5 / 2 := by
    simp [sampleMean, Finset.sum_range_succ, fourUnitObs, armIndObs, fourUnitWeight, fourUnitArm,
      fourUnitZ, fourUnitOutcome]
    norm_num
  have h2 : sampleMean (fun z => armIndObs true z * fourUnitWeight z.1) fourUnitObs 4 () = 1 := by
    simp [sampleMean, Finset.sum_range_succ, fourUnitObs, armIndObs, fourUnitWeight, fourUnitArm,
      fourUnitZ]
    norm_num
  refine ⟨h1, h2, ?_⟩
  rw [weightedArmMean_eq_div_sampleMean, h1, h2, div_one]

/-- The fitted score `ê(z) = 1 / (2 + z)`: `1/2` at `z = 0` and `1/4` at `z = 2`. -/
noncomputable def fourUnitScore (_ : ℕ) (_ : Unit) (z : Fin 1 → ℝ) : ℝ := 1 / (2 + z 0)

/-- **The Hájek estimator of the four unit data set**: the fitted probabilities of both arms are
in `(0, 1)` at every observation, so the weights `1 / π̂_a(Zᵢ)` are finite; for the treated
arm they are `2` and `4`, and the Hájek estimator is the weighted arm mean
`(2 · 1 + 4 · 3) / 6 = 7/3` (`sampleHajekArmMean_eq_weightedArmMean`). -/
theorem sampleHajekArmMean_fourUnit :
    (∀ (i : Fin 4) (t : Bool), 0 < armProb (fourUnitScore 4 ()) t (fourUnitObs i ()).1 ∧
      armProb (fourUnitScore 4 ()) t (fourUnitObs i ()).1 < 1) ∧
      sampleHajekArmMean fourUnitScore true fourUnitObs 4 () = 7 / 3 := by
  refine ⟨fun i t => ?_, ?_⟩
  · rw [fourUnitObs_fin]
    fin_cases i <;> cases t <;>
      norm_num [armProb, fourUnitScore, fourUnitZ]
  · rw [sampleHajekArmMean_eq_weightedArmMean]
    simp only [fourUnitObs_fin]
    simp [weightedArmMean, weightedMean, armWeights, armProb, fourUnitScore, fourUnitArm,
      fourUnitZ, fourUnitOutcome, Fin.sum_univ_four]
    norm_num

/-! ### The tilted law of the example of non trivial tilt -/

/-- **The tilted law has the target feature mean**: the fair coin tilted by `log 3 · 1{x}` gives
`true` the mean `3/4` (`integral_feature_tilted_iff`, from the population balance of the tilting
weights at `3/4`). -/
theorem integral_feature_tilted_tiltExample :
    ∀ j, ∫ x, tiltFeature x j ∂(halfLaw.tilted fun x => tiltBeta ⬝ᵥ (tiltFeature x - 0)) =
      3 / 4 := by
  have hbal := tiltExample_densityRatio.2.2.1
  rw [map_snd_uniformPairLaw] at hbal
  exact (integral_feature_tilted_iff tiltFeature 0 tiltAlpha tiltBeta halfLaw (fun _ => 3 / 4)
    Integrable.of_finite fun _ => Integrable.of_finite).2 hbal

/-! ### A three unit sample -/

/-- The outcomes `(2, 0, 8)` of the three unit sample. -/
def threeUnitOutcome : Fin 3 → ℝ := ![2, 0, 8]

/-- All three units are in the same arm. -/
def threeUnitArm : Fin 3 → Bool := fun _ => true

/-- The mean of the outcomes under the empirical law of the three unit sample is `10/3`
(`integral_ipdEmpirical`). -/
theorem integral_ipdEmpirical_threeUnit :
    ∫ z, z.2.2 ∂(Trial.ipdEmpirical threeUnitDelta threeUnitArm threeUnitOutcome) = 10 / 3 := by
  rw [integral_ipdEmpirical]
  simp [threeUnitOutcome, Fin.sum_univ_three]
  norm_num

theorem tiltWeight_threeUnit (i : Fin 3) :
    tiltWeight id 0 0 threeUnitBeta (threeUnitDelta i) =
      Real.exp (threeUnitBeta ⬝ᵥ threeUnitDelta i) := by
  simp [tiltWeight]

theorem momentBalanced_tiltWeight_threeUnit :
    MomentBalanced (fun i => tiltWeight id 0 0 threeUnitBeta (threeUnitDelta i))
      (fun i => id (threeUnitDelta i)) 0 := by
  simp only [tiltWeight_threeUnit, id]
  exact (isMinOn_logPartition_iff threeUnitBeta).1 isMinOn_logPartition_threeUnitDelta

/-- **Population balance at the empirical law**: the tilting weights `exp(βᵀz)` with
`β = -(log 2) / 2` balance the covariates `(-1, 1, 1)` at `0` under the empirical law
(`populationBalanced_ipdEmpirical_iff`). -/
theorem populationBalanced_ipdEmpirical_threeUnit :
    PopulationBalanced (Trial.ipdEmpirical threeUnitDelta threeUnitArm threeUnitOutcome)
      (fun z => tiltWeight id 0 0 threeUnitBeta z.1) (fun z => id z.1) 0 :=
  (populationBalanced_ipdEmpirical_iff (by norm_num) threeUnitDelta threeUnitArm threeUnitOutcome
    (tiltWeight id 0 0 threeUnitBeta) id 0).2 momentBalanced_tiltWeight_threeUnit

/-- **The tilted empirical law is a probability law with feature mean `0`**
(`isProbabilityMeasure_tilted_ipdEmpirical`, `integral_feature_tilted_ipdEmpirical_iff`). -/
theorem integral_feature_tilted_ipdEmpirical_threeUnit :
    IsProbabilityMeasure ((Trial.ipdEmpirical threeUnitDelta threeUnitArm threeUnitOutcome).tilted
        fun z => threeUnitBeta ⬝ᵥ (id z.1 - 0)) ∧
      ∀ j, ∫ z, id z.1 j ∂((Trial.ipdEmpirical threeUnitDelta threeUnitArm threeUnitOutcome).tilted
        fun z => threeUnitBeta ⬝ᵥ (id z.1 - 0)) = (0 : Fin 1 → ℝ) j := by
  obtain ⟨hP, hiff⟩ := integral_feature_tilted_ipdEmpirical_iff (by norm_num) threeUnitDelta
    threeUnitArm threeUnitOutcome id 0 0 threeUnitBeta 0
  exact ⟨isProbabilityMeasure_tilted_ipdEmpirical (by norm_num) _ _ _ _,
    hiff.2 momentBalanced_tiltWeight_threeUnit⟩

/-- **The reweighted outcome mean of the three unit sample**: the tilted empirical law gives the
units the normalized weights `(1/2, 1/4, 1/4)` (`integral_tilted_ipdEmpirical`), so the outcome
mean is `1/2 · 2 + 1/4 · 0 + 1/4 · 8 = 3`, against the unweighted mean `10/3`. -/
theorem integral_tilted_ipdEmpirical_threeUnit :
    ∫ z, z.2.2 ∂((Trial.ipdEmpirical threeUnitDelta threeUnitArm threeUnitOutcome).tilted
      fun z => threeUnitBeta ⬝ᵥ (z.1 - 0)) = 3 := by
  rw [integral_tilted_ipdEmpirical (by norm_num)]
  have hw : normalizedWeights (fun i => Real.exp (threeUnitBeta ⬝ᵥ (threeUnitDelta i - 0))) =
      ![1 / 2, 1 / 4, 1 / 4] := by
    simp only [sub_zero]
    rw [← entropyWeights_eq_normalizedWeights, ← dualMinimizer_threeUnitDelta]
    exact balancingWeights_threeUnitDelta.1
  rw [hw]
  simp [threeUnitOutcome, Fin.sum_univ_three]
  norm_num

/-! ### Inverse odds under a two point law -/

/-- The two point law `δ₀ + δ₁` on `ℝ¹`, of total mass `2` (the theorem on inverse odds does not
need a probability law). -/
noncomputable def twoPointLaw : Measure (Fin 1 → ℝ) :=
  Measure.dirac 0 + Measure.dirac fun _ => 1

/-- **The two point law is not carried by a hyperplane**: for `v ≠ 0`, `vᵀx = r` cannot hold at
both `x = 0` and `x = 1`. -/
theorem not_ae_dotProduct_eq_twoPoint :
    ∀ v : Fin 1 → ℝ, v ≠ 0 → ∀ r : ℝ, ¬ ∀ᵐ x ∂twoPointLaw, v ⬝ᵥ x = r := by
  intro v hv r h
  rw [twoPointLaw, ae_add_measure_iff, ae_dirac_eq, ae_dirac_eq, Filter.eventually_pure,
    Filter.eventually_pure] at h
  obtain ⟨h0, h1⟩ := h
  simp [dotProduct] at h0 h1
  apply hv
  funext j
  rw [Subsingleton.elim j 0]
  simp only [Pi.zero_apply]
  linarith

/-- **The almost everywhere proportionality under the two point law**: for the logistic
membership `σ(0 + 1 · x)` and `k = 1`, the inverse odds `exp(-x)` is almost everywhere a positive
multiple of the tilting weight `exp(βx)` exactly when `β = -1`
(`inverseOdds_proportional_ae_iff`); so it is for `β = -1` and it is not for `β = 1`. -/
theorem inverseOdds_proportional_ae_twoPoint :
    (∀ β : Fin 1 → ℝ, (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂twoPointLaw,
        inverseOdds 1 (fun x => Real.sigmoid (0 + (fun _ => (1 : ℝ)) ⬝ᵥ x)) x =
          C * tiltWeight id 0 0 β x) ↔ β = fun _ => -1) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂twoPointLaw,
        inverseOdds 1 (fun x => Real.sigmoid (0 + (fun _ => (1 : ℝ)) ⬝ᵥ x)) x =
          C * tiltWeight id 0 0 (fun _ => -1) x) ∧
      ¬ (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂twoPointLaw,
        inverseOdds 1 (fun x => Real.sigmoid (0 + (fun _ => (1 : ℝ)) ⬝ᵥ x)) x =
          C * tiltWeight id 0 0 (fun _ => 1) x) := by
  have h : ∀ β : Fin 1 → ℝ, (∃ C : ℝ, 0 < C ∧ ∀ᵐ x ∂twoPointLaw,
      inverseOdds 1 (fun x => Real.sigmoid (0 + (fun _ => (1 : ℝ)) ⬝ᵥ x)) x =
        C * tiltWeight id 0 0 β x) ↔ β = fun _ => -1 := fun β => by
    rw [inverseOdds_proportional_ae_iff not_ae_dotProduct_eq_twoPoint 1 0 0 _ β 0 one_pos]
    constructor <;> intro hβ <;> rw [hβ] <;> rfl
  refine ⟨h, (h _).2 rfl, fun h1 => ?_⟩
  have := congrFun ((h _).1 h1) 0
  norm_num at this

end PopulationAdjustment

end CausalInference
