/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityVarianceCompare
public import CausalInference.PopulationAdjustment.WeightedConsistencyExamples

/-!
# Without an affine regression the sandwich variance can exceed the naive variance

Under randomization and an arm regression affine in the features, the sandwich variance of the
weighted arm mean is at most the naive variance (`weightedArmVariance_le_weightedNaiveVariance`).
The affinity cannot be dropped. In the model below the arm is a fair coin independent of the
covariate, the outcome is a function of the covariate, every hypothesis of the general comparison
holds, but the regression is not affine in the feature and `σ² = 219/10 > 528/25 = σ_naive²`.

The model: a covariate `X ∈ {0, 1, 2}` with probabilities `2/3, 1/6, 1/6`, the feature
`φ(x) = x`, the target mean `t = 1`, an independent fair coin `A` and `Y = μ(X)` with
`μ = (-2, 6, -1)`. The population tilt is `β₀ = log 2`, with weights `w₀ = (1/2, 1, 2)`; in the
treated arm `q = 5/12`, `m₀ = 0`, `M = 2/3` and `c = 1/6`.

## Main definitions

* `nonaffineRecordLaw`: the law of the records `(X, A, μ(X))`.

## Main results

* `nonaffine_indep`, `nonaffine_condExp`, `nonaffine_margin`, `nonaffine_bound`,
  `nonaffine_prob_arm`, `nonaffine_memLp_outcome`: the hypotheses of the comparison.
* `nonaffine_not_affine`: the regression is not affine in the feature.
* `nonaffine_tiltMinimizer`: the population tilt is `log 2`.
* `nonaffine_weightedArmVariance`: `σ² = 219/10`.
* `nonaffine_weightedNaiveVariance`: `σ_naive² = 528/25`.
* `nonaffine_weightedNaiveVariance_lt_weightedArmVariance`: the strict reverse inequality.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
* Stefanski, Boos, *The calculus of M-estimation* (2002).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

/-! ### The model -/

/-- The covariate probabilities `2/3, 1/6, 1/6`. -/
noncomputable def nonaffineProb : Fin 3 → ℝ := ![2 / 3, 1 / 6, 1 / 6]

/-- The covariate values `0, 1, 2`. -/
def nonaffineVal : Fin 3 → ℝ := ![0, 1, 2]

/-- The regression `μ = (-2, 6, -1)`, the same in both arms. -/
def nonaffineRegression : Fin 3 → ℝ := ![-2, 6, -1]

/-- The feature `φ(x) = x`. -/
def nonaffineFeature (x : Fin 3) : Fin 1 → ℝ := fun _ => nonaffineVal x

/-- The target mean `t = 1`. -/
def nonaffineTarget : Fin 1 → ℝ := fun _ => 1

/-- The law of the covariate. -/
noncomputable def nonaffineCovLaw : Measure (Fin 3) := stratumLaw nonaffineProb

theorem nonaffineProb_nonneg (x : Fin 3) : 0 ≤ nonaffineProb x := by
  fin_cases x <;> norm_num [nonaffineProb]

instance : IsProbabilityMeasure nonaffineCovLaw :=
  isProbabilityMeasure_stratumLaw ⟨nonaffineProb_nonneg, by
    simp [nonaffineProb, Fin.sum_univ_three]; norm_num⟩

/-- The record `(X, A, μ(X))`. -/
def nonaffineRecord (q : Fin 3 × Bool) : Fin 3 × Bool × ℝ := (q.1, q.2, nonaffineRegression q.1)

theorem measurable_nonaffineRecord : Measurable nonaffineRecord := measurable_of_countable _

/-- The law of the records: `X`, an independent fair coin `A` and `Y = μ(X)`. -/
noncomputable def nonaffineRecordLaw : Measure (Fin 3 × Bool × ℝ) :=
  (nonaffineCovLaw.prod halfLaw).map nonaffineRecord

instance : IsProbabilityMeasure nonaffineRecordLaw :=
  (Measure.isProbabilityMeasure_map_iff measurable_nonaffineRecord.aemeasurable).2
    inferInstance

theorem integral_nonaffinePairLaw (f : Fin 3 × Bool → ℝ) :
    ∫ q, f q ∂(nonaffineCovLaw.prod halfLaw) =
      ∑ x, nonaffineProb x * ((f (x, true) + f (x, false)) / 2) := by
  rw [integral_prod f Integrable.of_finite, nonaffineCovLaw,
    integral_stratumLaw nonaffineProb_nonneg, standardizedRisk]
  simp only [integral_halfLaw]

/-- Almost every record satisfies `Y = μ(X)`. -/
theorem ae_nonaffineRecordLaw_outcome :
    ∀ᵐ z ∂nonaffineRecordLaw, z.2.2 = nonaffineRegression z.1 := by
  have hm : Measurable fun z : Fin 3 × Bool × ℝ => nonaffineRegression z.1 :=
    (measurable_of_countable _).comp measurable_fst
  rw [nonaffineRecordLaw, ae_map_iff measurable_nonaffineRecord.aemeasurable
    (measurableSet_eq_fun measurable_snd.snd hm)]
  exact ae_of_all _ fun q => rfl

/-- **Integrals under the record law** are weighted sums over the six values of `(X, A)`. -/
theorem integral_nonaffineRecordLaw (f : Fin 3 × Bool × ℝ → ℝ) :
    ∫ z, f z ∂nonaffineRecordLaw =
      ∑ x, nonaffineProb x * ((f (nonaffineRecord (x, true)) +
        f (nonaffineRecord (x, false))) / 2) := by
  set g : Fin 3 × Bool → ℝ := fun q => f (nonaffineRecord q)
  have hg : Measurable fun z : Fin 3 × Bool × ℝ => g (z.1, z.2.1) :=
    (measurable_of_countable g).comp (measurable_fst.prodMk measurable_snd.fst)
  have h1 : ∫ z, f z ∂nonaffineRecordLaw = ∫ z, g (z.1, z.2.1) ∂nonaffineRecordLaw := by
    refine integral_congr_ae (ae_nonaffineRecordLaw_outcome.mono fun z hz => ?_)
    obtain ⟨x, s, y⟩ := z
    simp only at hz
    subst hz
    rfl
  rw [h1, nonaffineRecordLaw, integral_map measurable_nonaffineRecord.aemeasurable
    hg.aestronglyMeasurable]
  exact integral_nonaffinePairLaw g

theorem nonaffineRecordLaw_real {S : Set (Fin 3 × Bool × ℝ)} (hS : MeasurableSet S) :
    nonaffineRecordLaw.real S = ∑ x, nonaffineProb x *
      ((S.indicator 1 (nonaffineRecord (x, true)) +
        S.indicator 1 (nonaffineRecord (x, false))) / 2) := by
  rw [← integral_indicator_one hS, integral_nonaffineRecordLaw]

/-! ### The hypotheses -/

theorem abs_nonaffineRegression_le (x : Fin 3) : |nonaffineRegression x| ≤ 6 := by
  fin_cases x <;> norm_num [nonaffineRegression, abs_le]

theorem measurable_nonaffineFeature : Measurable nonaffineFeature := measurable_of_countable _

theorem nonaffine_indep :
    IndepFun (fun z : Fin 3 × Bool × ℝ => z.1) (fun z => z.2.1) nonaffineRecordLaw := by
  have h1 : Measurable fun z : Fin 3 × Bool × ℝ => z.1 := measurable_fst
  have h2 : Measurable fun z : Fin 3 × Bool × ℝ => z.2.1 := measurable_snd.fst
  rw [indepFun_iff_map_prod_eq_prod_map_map h1.aemeasurable h2.aemeasurable, nonaffineRecordLaw,
    Measure.map_map (h1.prodMk h2) measurable_nonaffineRecord,
    Measure.map_map h1 measurable_nonaffineRecord, Measure.map_map h2 measurable_nonaffineRecord]
  have hid : ((fun z : Fin 3 × Bool × ℝ => (z.1, z.2.1)) ∘ nonaffineRecord) = id := by
    funext q; rfl
  have hfst : ((fun z : Fin 3 × Bool × ℝ => z.1) ∘ nonaffineRecord) = Prod.fst := by
    funext q; rfl
  have hsnd : ((fun z : Fin 3 × Bool × ℝ => z.2.1) ∘ nonaffineRecord) = Prod.snd := by
    funext q; rfl
  rw [hid, hfst, hsnd, Measure.map_id, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ,
    measure_univ, one_smul, one_smul]

/-- **The arm regression**: `E[Y | X, A] = μ(X)`, in both arms. -/
theorem nonaffine_condExp :
    nonaffineRecordLaw[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : Fin 3 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[nonaffineRecordLaw]
      fun z => (fun (_ : Bool) (x : Fin 3) => nonaffineRegression x) z.2.1 z.1 := by
  have hpair : Measurable fun z : Fin 3 × Bool × ℝ => (z.1, z.2.1) :=
    measurable_fst.prodMk measurable_snd.fst
  have hm : MeasurableSpace.comap (fun z : Fin 3 × Bool × ℝ => (z.1, z.2.1)) inferInstance ≤
      (inferInstance : MeasurableSpace (Fin 3 × Bool × ℝ)) := hpair.comap_le
  have hsm : StronglyMeasurable[MeasurableSpace.comap
      (fun z : Fin 3 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
      (fun z : Fin 3 × Bool × ℝ => nonaffineRegression z.1) :=
    (((measurable_of_countable fun q : Fin 3 × Bool => nonaffineRegression q.1).comp
      (Measurable.of_comap_le le_rfl))).stronglyMeasurable
  have hint : Integrable (fun z : Fin 3 × Bool × ℝ => nonaffineRegression z.1)
      nonaffineRecordLaw :=
    integrable_of_abs_le (C := 6) ((measurable_of_countable _).comp measurable_fst) fun z =>
      abs_nonaffineRegression_le z.1
  exact (condExp_congr_ae ae_nonaffineRecordLaw_outcome).trans
    (condExp_of_stronglyMeasurable hm hsm hint).eventuallyEq

theorem nonaffine_bound (x : Fin 3) : ‖nonaffineFeature x - nonaffineTarget‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => ?_
  fin_cases x <;> norm_num [nonaffineFeature, nonaffineTarget, nonaffineVal]

theorem nonaffine_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 6 : ℝ) ≤
    nonaffineRecordLaw.real {z | 1 / 6 ≤ v ⬝ᵥ (nonaffineFeature z.1 - nonaffineTarget)} := by
  intro v hv
  have hv0 : |v 0| = 1 := by
    rw [← Real.norm_eq_abs, ← hv]
    refine le_antisymm (norm_le_pi_norm v 0) ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      fun i => by rw [Subsingleton.elim i 0])
  have hS : MeasurableSet {z : Fin 3 × Bool × ℝ |
      1 / 6 ≤ v ⬝ᵥ (nonaffineFeature z.1 - nonaffineTarget)} :=
    measurableSet_le measurable_const
      ((measurable_of_countable fun x : Fin 3 =>
        v ⬝ᵥ (nonaffineFeature x - nonaffineTarget)).comp measurable_fst)
  rw [nonaffineRecordLaw_real hS]
  rcases (abs_eq zero_le_one).1 hv0 with h | h <;>
    simp [Fin.sum_univ_three, Set.indicator, nonaffineRecord, dotProduct, h, nonaffineFeature,
      nonaffineTarget, nonaffineVal, nonaffineProb] <;> norm_num

theorem nonaffine_prob_arm (a : Bool) : nonaffineRecordLaw.real {z | z.2.1 = a} = 1 / 2 := by
  rw [nonaffineRecordLaw_real (measurableSet_eq_fun measurable_snd.fst measurable_const)]
  cases a <;> simp [Fin.sum_univ_three, Set.indicator, nonaffineRecord, nonaffineProb] <;>
    norm_num

theorem nonaffine_memLp_outcome :
    MemLp (fun z : Fin 3 × Bool × ℝ => z.2.2) 2 nonaffineRecordLaw :=
  MemLp.of_bound measurable_snd.snd.aestronglyMeasurable 6
    (ae_nonaffineRecordLaw_outcome.mono fun z hz => by
      rw [hz, Real.norm_eq_abs]
      exact abs_nonaffineRegression_le z.1)

/-- **The regression is not affine in the feature**: no `a₀`, `γ` give
`μ(x) = a₀ + γᵀ φ(x)` for every `x`. -/
theorem nonaffine_not_affine (a0 : ℝ) (γ : Fin 1 → ℝ) :
    ¬ ∀ x, nonaffineRegression x = a0 + γ ⬝ᵥ nonaffineFeature x := by
  intro h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [nonaffineRegression, nonaffineFeature, nonaffineVal, dotProduct] at h0 h1 h2
  linarith

/-! ### The population quantities -/

/-- The population tilt `β₀ = log 2`. -/
noncomputable def nonaffineTilt : Fin 1 → ℝ := fun _ => Real.log 2

/-- The tilt weights `w₀ = (1/2, 1, 2)`. -/
noncomputable def nonaffineWeight : Fin 3 → ℝ := ![1 / 2, 1, 2]

theorem nonaffine_tiltWeight (x : Fin 3) :
    tiltWeight nonaffineFeature nonaffineTarget 0 nonaffineTilt x = nonaffineWeight x := by
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  fin_cases x <;> simp [tiltWeight, nonaffineTilt, nonaffineFeature, nonaffineTarget,
    nonaffineVal, nonaffineWeight, dotProduct, h2, Real.exp_neg]
  norm_num [h2]

/-- **The population tilt is `log 2`**: the weights `(1/2, 1, 2)` balance the feature,
`(2/3)(1/2)(0 - 1) + (1/6)(2)(2 - 1) = 0`. -/
theorem nonaffine_tiltMinimizer :
    tiltMinimizer nonaffineRecordLaw nonaffineFeature nonaffineTarget = nonaffineTilt := by
  refine tiltMinimizer_eq_of_balance measurable_nonaffineFeature nonaffine_bound
    (by norm_num : (0 : ℝ) < 1 / 6) nonaffine_margin fun j => ?_
  simp only [nonaffine_tiltWeight]
  rw [integral_nonaffineRecordLaw]
  simp [Fin.sum_univ_three, nonaffineRecord, nonaffineWeight, nonaffineProb, nonaffineFeature,
    nonaffineTarget, nonaffineVal]
  norm_num

/-- The tilted mass of the treated arm is `q = 5/12`. -/
theorem nonaffine_weightedArmMass :
    weightedArmMass nonaffineRecordLaw nonaffineFeature nonaffineTarget true = 5 / 12 := by
  rw [weightedArmMass, nonaffine_tiltMinimizer]
  simp only [nonaffine_tiltWeight]
  rw [integral_nonaffineRecordLaw]
  simp [Fin.sum_univ_three, nonaffineRecord, nonaffineWeight, nonaffineProb, armIndObs]
  norm_num

/-- The weighted mean of the treated arm is `m₀ = 0`. -/
theorem nonaffine_tiltArmMean :
    tiltArmMean nonaffineRecordLaw nonaffineFeature nonaffineTarget true nonaffineTilt = 0 := by
  rw [tiltArmMean]
  simp only [nonaffine_tiltWeight]
  rw [integral_nonaffineRecordLaw]
  simp [Fin.sum_univ_three, nonaffineRecord, nonaffineWeight, nonaffineProb, armIndObs,
    nonaffineRegression]
  norm_num

/-- The tilted second moment is `M = 2/3`. -/
theorem nonaffine_tiltedSecondMoment :
    tiltedSecondMoment nonaffineRecordLaw nonaffineFeature nonaffineTarget nonaffineTilt =
      Matrix.of fun _ _ => 2 / 3 := by
  ext j k
  simp only [tiltedSecondMoment, Matrix.of_apply, nonaffine_tiltWeight]
  rw [integral_nonaffineRecordLaw]
  simp [Fin.sum_univ_three, nonaffineRecord, nonaffineWeight, nonaffineProb, nonaffineFeature,
    nonaffineTarget, nonaffineVal]
  norm_num

theorem nonaffine_tiltedSecondMoment_inv :
    (tiltedSecondMoment nonaffineRecordLaw nonaffineFeature nonaffineTarget nonaffineTilt)⁻¹ =
      Matrix.of fun _ _ => 3 / 2 := by
  rw [nonaffine_tiltedSecondMoment]
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul_apply]

/-- The coupling vector of the treated arm is `c = 1/6`. -/
theorem nonaffine_weightedCoupling :
    weightedCoupling nonaffineRecordLaw nonaffineFeature nonaffineTarget true = fun _ => 1 / 6 := by
  funext k
  rw [weightedCoupling, nonaffine_tiltMinimizer, nonaffine_tiltArmMean]
  simp only [nonaffine_tiltWeight]
  rw [integral_nonaffineRecordLaw]
  simp [Fin.sum_univ_three, nonaffineRecord, nonaffineWeight, nonaffineProb, armIndObs,
    nonaffineRegression, nonaffineFeature, nonaffineTarget, nonaffineVal]
  norm_num

/-- The influence function of the treated arm:
`IF = (1{A = a} w₀(X) Y - (1/4) w₀(X) (X - 1)) / (5/12)`. -/
theorem nonaffine_weightedArmInfluence :
    weightedArmInfluence nonaffineRecordLaw nonaffineFeature nonaffineTarget true = fun z =>
      (armIndObs true z * nonaffineWeight z.1 * z.2.2 -
        1 / 4 * (nonaffineWeight z.1 * (nonaffineVal z.1 - 1))) / (5 / 12) := by
  funext z
  rw [weightedArmInfluence, nonaffine_weightedCoupling, nonaffine_weightedArmMass,
    nonaffine_tiltMinimizer, nonaffine_tiltArmMean, nonaffine_tiltedSecondMoment_inv]
  simp only [nonaffine_tiltWeight, Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.of_apply,
    nonaffineFeature, nonaffineTarget]
  ring

/-- **The sandwich variance of the treated arm is `σ² = 219/10`.** -/
theorem nonaffine_weightedArmVariance :
    weightedArmVariance nonaffineRecordLaw nonaffineFeature nonaffineTarget true = 219 / 10 := by
  rw [weightedArmVariance, nonaffine_weightedArmInfluence, integral_nonaffineRecordLaw]
  simp [Fin.sum_univ_three, nonaffineRecord, nonaffineWeight, nonaffineProb, armIndObs,
    nonaffineRegression, nonaffineVal]
  norm_num

/-- **The naive variance of the treated arm is `σ_naive² = 528/25`.** -/
theorem nonaffine_weightedNaiveVariance :
    weightedNaiveVariance nonaffineRecordLaw nonaffineFeature nonaffineTarget true = 528 / 25 := by
  rw [weightedNaiveVariance, nonaffine_weightedArmMass]
  simp only [weightedArmResidual, nonaffine_tiltMinimizer, nonaffine_tiltArmMean,
    nonaffine_tiltWeight]
  rw [integral_nonaffineRecordLaw]
  simp [Fin.sum_univ_three, nonaffineRecord, nonaffineWeight, nonaffineProb, armIndObs,
    nonaffineRegression]
  norm_num

/-- **Without an affine regression the comparison reverses.** The arm is independent of the
covariate, `E[Y | X, A] = μ(X)`, the features are bounded and satisfy the margin condition with
`δ = 1/6`, `P(A = true) = 1/2` and `E[Y²] < ∞`, but `μ` is not affine in the feature, and the
sandwich variance strictly exceeds the naive variance: `528/25 < 219/10`. -/
theorem nonaffine_weightedNaiveVariance_lt_weightedArmVariance :
    weightedNaiveVariance nonaffineRecordLaw nonaffineFeature nonaffineTarget true <
      weightedArmVariance nonaffineRecordLaw nonaffineFeature nonaffineTarget true := by
  rw [nonaffine_weightedNaiveVariance, nonaffine_weightedArmVariance]
  norm_num

end PopulationAdjustment

end CausalInference
