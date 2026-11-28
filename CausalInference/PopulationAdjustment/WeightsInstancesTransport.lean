/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.DensityRatio
public import CausalInference.PointTreatment.Randomized
public import CausalInference.IndirectComparison.CommonComparator

/-!
# Population adjustment: a concrete transport model for the weighting results

A concrete instance of the population results on weighting with every hypothesis verified.

**The model** (`tiltModel`). The trial has a fair coin treatment `A` and an independent fair
coin covariate `X₁ ∈ {false, true}` (`IndirectComparison.uniformPairLaw`, `A` the first
coordinate). The target covariate law gives `true` the probability `3/4` and `false` the
probability `1/4` (`tiltTargetLaw`). In both populations the potential outcomes are
`Y(b) = 2 · 1{x} + 1{b}` (`tiltOutcome`): `3, 1` in the treated arm and `2, 0` in the
untreated arm for `x = true, false`.

* **The density ratio is a non trivial tilt.** With the feature `φ(x) = 1{x}`, centering `0`,
  intercept `log (1/2)` and slope `log 3 ≠ 0`, the target law has the tilting weight density
  with respect to the trial covariate law (`tiltTargetLaw_eq_withDensity`); the weights are
  `1/2` at `false` and `3/2` at `true` (`tiltWeight_tiltExample`). Fed through
  `densityRatio_ae_eq_tiltWeight`, `integral_tiltWeight_eq_one`, `populationBalanced_tiltWeight`
  and `map_eq_tilted` (`tiltExample_densityRatio`).
* **Conditional transportability** of both arms (`isConditionallyTransportable_tiltModel`), with
  the constant propensity `1/2` (`isPropensityScore_tiltModel`) and the common regressions
  `tiltOutcome b` (`isCommonRegression_tiltModel`).
* **The weighted arm means.** The population weighted arm mean of the treated arm with any
  weights `w` is `(3 w(true) + w(false)) / (w(true) + w(false))`
  (`lawWeightedArmMean_tiltModel_true`), so `2` without weights and `5/2` with the tilting
  weights; the target means are `5/2` and `3/2` (`targetMean_tiltModel`). The four results of
  the target mean (`lawWeightedArmMean_sourceLaw_eq_targetMean`,
  `lawWeightedArmMean_tiltWeight_eq_targetMean`, `lawWeightedContrast_eq_targetMean_sub`,
  `lawWeightedContrast_sub_eq_anchoredEstimand`) give `5/2`, `5/2`, `-1` and `-7/4`
  (`tiltModel_weighted_results`).
* **Logistic membership.** Two independent fair coins `(S, Z)` with covariate `φ(Z)` have
  logistic membership `σ(0 + 0ᵀx)`; `map_cond_eq_withDensity_tiltWeight` gives the log linear
  density ratio with intercept `log 1 = 0` and slope `0`, whose weight is `1`, and the results
  of the log linear section apply (`logisticExample_results`).

## Main definitions

* `tiltFeature`, `tiltOutcome`, `tiltTargetLaw`, `tiltModel`.

## Main results

* `tiltTargetLaw_eq_withDensity`, `tiltWeight_tiltExample`, `tiltExample_densityRatio`.
* `isPropensityScore_tiltModel`, `isCommonRegression_tiltModel`,
  `isConditionallyTransportable_tiltModel`.
* `targetMean_tiltModel`, `lawWeightedArmMean_tiltModel_true`,
  `lawWeightedArmMean_tiltModel_false`, `tiltModel_weighted_results`.
* `logisticExample_results`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory MissingData PointTreatment Transport IndirectComparison
  EffectMeasure
open scoped ENNReal

/-! ### The laws and the tilt -/

/-- The feature `φ(x) = 1{x}` of a binary covariate. -/
def tiltFeature (x : Bool) : Fin 1 → ℝ := fun _ => if x then 1 else 0

/-- The intercept `log (1/2)` of the example. -/
noncomputable def tiltAlpha : ℝ := Real.log (1 / 2)

/-- The slope `log 3` of the example. -/
noncomputable def tiltBeta : Fin 1 → ℝ := fun _ => Real.log 3

/-- The slope of the example is not zero. -/
theorem tiltBeta_ne_zero : tiltBeta ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [tiltBeta, Pi.zero_apply] at this
  have h3 : (1 : ℝ) < 3 := by norm_num
  exact (Real.log_pos h3).ne' this

/-- The probabilities `1/4` of `false` and `3/4` of `true` in the target. -/
noncomputable def tiltTargetProb (x : Bool) : ℝ := if x then 3 / 4 else 1 / 4

/-- The target covariate law: `P*(true) = 3/4`, `P*(false) = 1/4`. -/
noncomputable def tiltTargetLaw : Measure Bool := stratumLaw tiltTargetProb

theorem isWeights_tiltTargetProb : IsWeights tiltTargetProb :=
  ⟨fun x => by cases x <;> norm_num [tiltTargetProb], by
    simp [tiltTargetProb]; norm_num⟩

instance : IsProbabilityMeasure tiltTargetLaw :=
  isProbabilityMeasure_stratumLaw isWeights_tiltTargetProb

theorem integral_tiltTargetLaw (f : Bool → ℝ) :
    ∫ x, f x ∂tiltTargetLaw = 3 / 4 * f true + 1 / 4 * f false := by
  rw [tiltTargetLaw, integral_stratumLaw isWeights_tiltTargetProb.1, standardizedRisk,
    Fintype.sum_bool]
  simp [tiltTargetProb]

/-- **The tilting weights of the example**: `exp(log (1/2) + log 3 · 1{x})` is `1/2` at `false`
and `3/2` at `true`. -/
theorem tiltWeight_tiltExample (x : Bool) :
    tiltWeight tiltFeature 0 tiltAlpha tiltBeta x = if x then 3 / 2 else 1 / 2 := by
  cases x <;> simp only [tiltWeight, tiltFeature, tiltAlpha, tiltBeta, dotProduct,
    Fin.sum_univ_one, Pi.sub_apply, Pi.zero_apply, sub_zero, Bool.false_eq_true, ↓reduceIte,
    mul_one, mul_zero, add_zero]
  · rw [Real.exp_log (by norm_num)]
  · rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
    norm_num

/-- The trial covariate law is the fair coin. -/
theorem map_snd_uniformPairLaw : uniformPairLaw.map Prod.snd = halfLaw := by
  rw [uniformPairLaw, Measure.map_snd_prod, measure_univ, one_smul]

theorem stratumLaw_singleton (π : Bool → ℝ) (x : Bool) :
    stratumLaw π {x} = ENNReal.ofReal (π x) := by
  cases x <;> simp [stratumLaw]

/-- **The target law has the tilting weight density** with respect to the trial covariate
law. -/
theorem tiltTargetLaw_eq_withDensity :
    tiltTargetLaw = (uniformPairLaw.map Prod.snd).withDensity fun x =>
      ENNReal.ofReal (tiltWeight tiltFeature 0 tiltAlpha tiltBeta x) := by
  rw [map_snd_uniformPairLaw]
  refine Measure.ext_of_singleton fun x => ?_
  rw [withDensity_apply _ (measurableSet_singleton x), Measure.restrict_singleton,
    lintegral_smul_measure, lintegral_dirac, tiltTargetLaw, stratumLaw_singleton,
    stratumLaw_singleton, tiltWeight_tiltExample, smul_eq_mul, ← ENNReal.ofReal_mul (by norm_num)]
  cases x <;> norm_num [tiltTargetProb]

theorem measurable_tiltFeature : Measurable tiltFeature := Measurable.of_discrete

/-- **The log linear results on the example, with the non trivial slope `log 3`**: the target
law is absolutely continuous with respect to the trial covariate law, the density ratio is
`1/2` at `false` and `3/2` at `true`, the tilting weights have mean one under the trial law,
they balance the feature at its target mean `3/4`, and the target law is the trial law
exponentially tilted by `log 3 · 1{x}`. -/
theorem tiltExample_densityRatio :
    (tiltTargetLaw.map id ≪ uniformPairLaw.map Prod.snd ∧
      densityRatio uniformPairLaw Prod.snd tiltTargetLaw id =ᵐ[uniformPairLaw.map Prod.snd]
        fun x => if x then 3 / 2 else 1 / 2) ∧
      ∫ x, tiltWeight tiltFeature 0 tiltAlpha tiltBeta x ∂(uniformPairLaw.map Prod.snd) = 1 ∧
      PopulationBalanced (uniformPairLaw.map Prod.snd) (tiltWeight tiltFeature 0 tiltAlpha tiltBeta)
        tiltFeature (fun _ => 3 / 4) ∧
      tiltTargetLaw.map id = (uniformPairLaw.map Prod.snd).tilted
        fun x => tiltBeta ⬝ᵥ (tiltFeature x - 0) := by
  have htilt : tiltTargetLaw.map id = (uniformPairLaw.map Prod.snd).withDensity fun x =>
      ENNReal.ofReal (tiltWeight tiltFeature 0 tiltAlpha tiltBeta x) := by
    rw [Measure.map_id]; exact tiltTargetLaw_eq_withDensity
  obtain ⟨hac, hae⟩ := densityRatio_ae_eq_tiltWeight measurable_tiltFeature htilt
  have hmean : (fun _ : Fin 1 => ∫ x, tiltFeature x 0 ∂(tiltTargetLaw.map id)) =
      fun _ => 3 / 4 := by
    funext j
    rw [Measure.map_id, integral_tiltTargetLaw]
    simp [tiltFeature]
  have hbal := populationBalanced_tiltWeight measurable_tiltFeature htilt
    fun _ => Integrable.of_finite
  have hj : (fun j : Fin 1 => ∫ x, tiltFeature x j ∂(tiltTargetLaw.map id)) = fun _ => 3 / 4 := by
    funext j; rw [Subsingleton.elim j 0]; exact congrFun hmean 0
  rw [hj] at hbal
  refine ⟨⟨hac, ?_⟩, integral_tiltWeight_eq_one measurable_tiltFeature htilt, hbal,
    map_eq_tilted measurable_tiltFeature htilt⟩
  filter_upwards [hae] with x hx
  rw [hx, tiltWeight_tiltExample]

/-! ### The transport model -/

/-- The potential outcomes `Y(b) = 2 · 1{x} + 1{b}` of the example, in both populations. -/
def tiltOutcome (b x : Bool) : ℝ := (if x then 2 else 0) + (if b then 1 else 0)

/-- **The transport model of the example**: a trial with a fair coin treatment (first
coordinate) and an independent fair coin covariate (second coordinate), a target with
`P*(true) = 3/4`, and the potential outcomes `tiltOutcome` in both populations. -/
noncomputable def tiltModel : TransportModel (Bool × Bool) Bool Bool where
  μ₁ := uniformPairLaw
  X₁ := Prod.snd
  A := Prod.fst
  Y₁ := fun b ω => tiltOutcome b ω.2
  μ₂ := tiltTargetLaw
  X₂ := id
  Y₂ := tiltOutcome

instance : IsProbabilityMeasure tiltModel.μ₁ := by
  change IsProbabilityMeasure uniformPairLaw; infer_instance

instance : IsProbabilityMeasure tiltModel.μ₂ := by
  change IsProbabilityMeasure tiltTargetLaw; infer_instance

theorem indepFun_fst_snd_uniformPairLaw : IndepFun Prod.fst Prod.snd uniformPairLaw :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem real_fst_uniformPairLaw (b : Bool) : uniformPairLaw.real (Prod.fst ⁻¹' {b}) = 1 / 2 := by
  rw [← integral_indicator_one (measurable_fst (measurableSet_singleton b)),
    integral_uniformPairLaw]
  cases b <;> simp [Set.indicator] <;> norm_num

/-- **The trial is randomized with probability `1/2`.** -/
theorem isPropensityScore_tiltModel :
    IsPropensityScore tiltModel.μ₁ tiltModel.A tiltModel.X₁ fun _ => 1 / 2 := by
  have h := isPropensityScore_const_of_indepFun measurable_snd measurable_fst
    indepFun_fst_snd_uniformPairLaw
  rw [real_fst_uniformPairLaw] at h
  exact h

/-- **Common regressions**: `tiltOutcome b` is the conditional mean of `Y(b)` given the
covariate in the trial and in the target. -/
theorem isCommonRegression_tiltModel (b : Bool) :
    IsCommonRegression tiltModel.μ₁ tiltModel.X₁ (tiltModel.Y₁ b) tiltModel.μ₂ tiltModel.X₂
      (tiltModel.Y₂ b) (tiltOutcome b) := by
  refine ⟨Measurable.of_discrete, ?_, ?_⟩
  · have hsm : StronglyMeasurable[MeasurableSpace.comap Prod.snd inferInstance]
        fun ω : Bool × Bool => tiltOutcome b ω.2 :=
      ((Measurable.of_discrete (f := tiltOutcome b)).comp
        (comap_measurable (Prod.snd : Bool × Bool → Bool))).stronglyMeasurable
    change (fun ω : Bool × Bool => tiltOutcome b ω.2) =ᵐ[uniformPairLaw]
      uniformPairLaw[fun ω => tiltOutcome b ω.2 | MeasurableSpace.comap Prod.snd inferInstance]
    rw [condExp_of_stronglyMeasurable measurable_snd.comap_le hsm Integrable.of_finite]
  · have hsm : StronglyMeasurable[MeasurableSpace.comap id inferInstance] (tiltOutcome b) :=
      ((Measurable.of_discrete (f := tiltOutcome b)).comp
        (comap_measurable (id : Bool → Bool))).stronglyMeasurable
    change (fun x => tiltOutcome b (id x)) =ᵐ[tiltTargetLaw]
      tiltTargetLaw[tiltOutcome b | MeasurableSpace.comap id inferInstance]
    rw [condExp_of_stronglyMeasurable measurable_id.comap_le hsm Integrable.of_finite]
    rfl

theorem tiltModel_targetCovLaw_eq_withDensity :
    tiltModel.μ₂.map tiltModel.X₂ = (tiltModel.μ₁.map tiltModel.X₁).withDensity fun x =>
      ENNReal.ofReal (tiltWeight tiltFeature 0 tiltAlpha tiltBeta x) := by
  change tiltTargetLaw.map id = _
  rw [Measure.map_id]
  exact tiltTargetLaw_eq_withDensity

/-- **Both arms of the example are conditionally transportable**: probability laws,
measurability and integrability (finite spaces), exchangeability (the treatment is independent
of the covariate and the outcomes are functions of the covariate), positivity (the propensity is
`1/2`), common regressions, overlap (the target law has a density) and integrability of the
reweighted outcome. -/
theorem isConditionallyTransportable_tiltModel (a : Bool) :
    tiltModel.IsConditionallyTransportable a := by
  have hY : Measurable (tiltModel.Y₁ a) :=
    (Measurable.of_discrete (f := tiltOutcome a)).comp measurable_snd
  have hmcar : MCAR tiltModel.μ₁ tiltModel.X₁ (tiltModel.Y₁ a) (arm tiltModel.A a) :=
    indepFun_fst_snd_uniformPairLaw.comp (φ := fun b : Bool => b == a)
      (ψ := fun x : Bool => (x, tiltOutcome a x)) Measurable.of_discrete Measurable.of_discrete
  refine ⟨inferInstance, inferInstance, measurable_snd, measurable_fst,
    fun b => (Measurable.of_discrete (f := tiltOutcome b)).comp measurable_snd, measurable_id,
    Integrable.of_finite, Integrable.of_finite,
    hmcar.marMean measurable_snd hY (measurable_arm measurable_fst a), ?_,
    ⟨_, isCommonRegression_tiltModel a⟩,
    (densityRatio_ae_eq_tiltWeight measurable_tiltFeature
      tiltModel_targetCovLaw_eq_withDensity).1, Integrable.of_finite⟩
  filter_upwards [isPropensityScore_tiltModel.condExp_arm measurable_snd measurable_fst a]
    with ω hω
  change 0 < tiltModel.μ₁[respInd (arm Prod.fst a) | MeasurableSpace.comap Prod.snd inferInstance] ω
  rw [hω]
  cases a <;> norm_num [armProb]

/-! ### The weighted arm means and the target means -/

/-- **The target means of the example**: `E*[Y(true)] = 3/4 · 3 + 1/4 · 1 = 5/2` and
`E*[Y(false)] = 3/4 · 2 + 1/4 · 0 = 3/2`. -/
theorem targetMean_tiltModel :
    tiltModel.targetMean true = 5 / 2 ∧ tiltModel.targetMean false = 3 / 2 := by
  simp only [TransportModel.targetMean]
  change ∫ x, tiltOutcome true x ∂tiltTargetLaw = 5 / 2 ∧
    ∫ x, tiltOutcome false x ∂tiltTargetLaw = 3 / 2
  rw [integral_tiltTargetLaw, integral_tiltTargetLaw]
  norm_num [tiltOutcome]

theorem integral_sourceLaw_tiltModel {f : Bool × Bool × ℝ → ℝ} (hf : Measurable f) :
    ∫ z, f z ∂tiltModel.sourceLaw =
      (f (true, true, 3) + f (false, true, 1) + f (true, false, 2) + f (false, false, 0)) / 4 := by
  rw [TransportModel.sourceLaw, integral_map (Measurable.of_discrete).aemeasurable
    hf.aestronglyMeasurable]
  change ∫ x, f (x.2, x.1, tiltOutcome x.1 x.2) ∂uniformPairLaw = _
  rw [integral_uniformPairLaw]
  norm_num [tiltOutcome]

theorem measurable_armWeight_mul (w : Bool → ℝ) (t : Bool) :
    Measurable fun z : Bool × Bool × ℝ => (if z.2.1 = t then w z.1 else 0) * z.2.2 :=
  (Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton t))
    ((Measurable.of_discrete (f := w)).comp measurable_fst) measurable_const).mul
    (measurable_snd.comp measurable_snd)

theorem measurable_armWeight (w : Bool → ℝ) (t : Bool) :
    Measurable fun z : Bool × Bool × ℝ => if z.2.1 = t then w z.1 else 0 :=
  Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton t))
    ((Measurable.of_discrete (f := w)).comp measurable_fst) measurable_const

/-- **The weighted arm means of the example with any weights** of nonzero total
`w(true) + w(false)`: the treated arm gives `(3 w(true) + w(false)) / (w(true) + w(false))`. -/
theorem lawWeightedArmMean_tiltModel_true {w : Bool → ℝ} (hw : w true + w false ≠ 0) :
    lawWeightedArmMean tiltModel.sourceLaw w true =
      (3 * w true + w false) / (w true + w false) := by
  rw [lawWeightedArmMean, integral_sourceLaw_tiltModel (measurable_armWeight_mul w true),
    integral_sourceLaw_tiltModel (measurable_armWeight w true)]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [div_eq_div_iff (fun h => hw (by linarith)) hw]
  ring

/-- For weights of nonzero total the untreated arm gives `2 w(true) / (w(true) + w(false))`. -/
theorem lawWeightedArmMean_tiltModel_false {w : Bool → ℝ} (hw : w true + w false ≠ 0) :
    lawWeightedArmMean tiltModel.sourceLaw w false = 2 * w true / (w true + w false) := by
  rw [lawWeightedArmMean, integral_sourceLaw_tiltModel (measurable_armWeight_mul w false),
    integral_sourceLaw_tiltModel (measurable_armWeight w false)]
  simp only [↓reduceIte, Bool.true_eq_false]
  rw [div_eq_div_iff (fun h => hw (by linarith)) hw]
  ring

/-- **The four target mean results on the example.** With the tilting weights `(1/2, 3/2)`,
`lawWeightedArmMean_sourceLaw_eq_targetMean` gives the target mean `5/2` of the treated arm
(the unweighted trial mean is `2`); `lawWeightedArmMean_tiltWeight_eq_targetMean` with the
intercept `0` (weights `(1, 3)`) gives the target mean `3/2` of the untreated arm;
`lawWeightedContrast_eq_targetMean_sub` gives the contrast `3/2 - 5/2 = -1`; and with the
common regressions `tiltOutcome` and the effect `τ_bc(x) = 1{x}` of the aggregate data trial,
`lawWeightedContrast_sub_eq_anchoredEstimand` gives `-1 - 3/4 = -7/4`. The direct
computations `lawWeightedArmMean_tiltModel_true` and `lawWeightedArmMean_tiltModel_false` agree. -/
theorem tiltModel_weighted_results :
    lawWeightedArmMean tiltModel.sourceLaw (tiltWeight tiltFeature 0 tiltAlpha tiltBeta) true =
        5 / 2 ∧
      lawWeightedArmMean tiltModel.sourceLaw (fun _ => 1) true = 2 ∧
      lawWeightedArmMean tiltModel.sourceLaw (tiltWeight tiltFeature 0 0 tiltBeta) false = 3 / 2 ∧
      lawWeightedContrast id tiltModel.sourceLaw (tiltWeight tiltFeature 0 tiltAlpha tiltBeta)
        true false = -1 ∧
      lawWeightedContrast id tiltModel.sourceLaw (tiltWeight tiltFeature 0 tiltAlpha tiltBeta)
          true false - ∫ x, (if x then (1 : ℝ) else 0) ∂tiltModel.targetCovLaw =
        anchoredEstimand tiltModel.targetCovLaw
          (fun x => tiltOutcome false x - tiltOutcome true x) (fun x => if x then 1 else 0) ∧
      anchoredEstimand tiltModel.targetCovLaw
          (fun x => tiltOutcome false x - tiltOutcome true x) (fun x => if x then 1 else 0) =
        -7 / 4 := by
  obtain ⟨hmt, hmf⟩ := targetMean_tiltModel
  have hq0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hq1 : (1 : ℝ) / 2 < 1 := by norm_num
  obtain ⟨-, hae⟩ := densityRatio_ae_eq_tiltWeight measurable_tiltFeature
    tiltModel_targetCovLaw_eq_withDensity
  have hw : tiltWeight tiltFeature 0 tiltAlpha tiltBeta =ᵐ[tiltModel.μ₁.map tiltModel.X₁]
      fun x => 1 * densityRatio tiltModel.μ₁ tiltModel.X₁ tiltModel.μ₂ tiltModel.X₂ x := by
    filter_upwards [hae] with x hx
    rw [hx, one_mul]
  have hwm := measurable_tiltWeight tiltFeature 0 tiltAlpha tiltBeta measurable_tiltFeature
  have h1 := lawWeightedArmMean_sourceLaw_eq_targetMean
    (isConditionallyTransportable_tiltModel true) hq0 hq1 isPropensityScore_tiltModel one_ne_zero
    hwm hw
  have h2 := lawWeightedArmMean_tiltWeight_eq_targetMean
    (isConditionallyTransportable_tiltModel false) hq0 hq1 isPropensityScore_tiltModel
    measurable_tiltFeature tiltModel_targetCovLaw_eq_withDensity 0
  have h3 := lawWeightedContrast_eq_targetMean_sub (isConditionallyTransportable_tiltModel true)
    (isConditionallyTransportable_tiltModel false) hq0 hq1 isPropensityScore_tiltModel
    one_ne_zero hwm hw id
  have h4 := lawWeightedContrast_sub_eq_anchoredEstimand
    (isConditionallyTransportable_tiltModel true) (isConditionallyTransportable_tiltModel false)
    hq0 hq1 isPropensityScore_tiltModel one_ne_zero hwm hw (m := tiltOutcome)
    isCommonRegression_tiltModel (fun x => if x then 1 else 0)
  have h5 : anchoredEstimand tiltModel.targetCovLaw
      (fun x => tiltOutcome false x - tiltOutcome true x) (fun x => if x then 1 else 0) =
      -7 / 4 := by
    rw [anchoredEstimand]
    change ∫ x, (tiltOutcome false x - tiltOutcome true x) ∂(tiltTargetLaw.map id) -
      ∫ x, (if x then (1 : ℝ) else 0) ∂(tiltTargetLaw.map id) = -7 / 4
    rw [Measure.map_id, integral_tiltTargetLaw, integral_tiltTargetLaw]
    norm_num [tiltOutcome]
  refine ⟨h1.trans hmt, ?_, h2.trans hmf, by rw [h3, hmt, hmf]; norm_num, h4, h5⟩
  rw [lawWeightedArmMean_tiltModel_true (by norm_num)]
  norm_num

/-! ### Logistic membership -/

/-- The covariate `φ(Z)` of two independent fair coins `(S, Z)`. -/
def logisticCov (ω : Bool × Bool) : Fin 1 → ℝ := tiltFeature ω.2

theorem measurable_logisticCov : Measurable logisticCov :=
  measurable_tiltFeature.comp measurable_snd

/-- Membership `S` independent of the covariate is logistic with `α̃ = 0`, `β̃ = 0`. -/
theorem isPropensityScore_logisticCov :
    IsPropensityScore uniformPairLaw Prod.fst logisticCov
      fun x => Real.sigmoid (0 + (0 : Fin 1 → ℝ) ⬝ᵥ x) := by
  have h := isPropensityScore_const_of_indepFun measurable_logisticCov measurable_fst
    (indepFun_fst_snd_uniformPairLaw.comp measurable_id measurable_tiltFeature)
  rw [real_fst_uniformPairLaw] at h
  have he : (fun x : Fin 1 → ℝ => Real.sigmoid (0 + (0 : Fin 1 → ℝ) ⬝ᵥ x)) = fun _ => 1 / 2 := by
    funext x
    simp [Real.sigmoid_def]
    norm_num
  rw [he]
  exact h

theorem uniformPairLaw_fst_ne_zero (b : Bool) : uniformPairLaw (Prod.fst ⁻¹' {b}) ≠ 0 := by
  intro h
  have := real_fst_uniformPairLaw b
  rw [measureReal_def, h] at this
  norm_num at this

/-- The tilting weight with intercept `0` and slope `0` is `1`. -/
theorem tiltWeight_zero_zero {𝒳 : Type*} {p : ℕ} (φ : 𝒳 → Fin p → ℝ) (c : Fin p → ℝ) (x : 𝒳) :
    tiltWeight φ c 0 0 x = 1 := by
  simp [tiltWeight]

/-- **Logistic membership fed through the log linear results.** For two independent fair coins
`(S, Z)` with covariate `X = φ(Z)`, membership is logistic with `α̃ = 0` and `β̃ = 0`, so
`map_cond_eq_withDensity_tiltWeight` gives the target covariate law (`S = false`) the density
`exp(log 1 - 0 + 0ᵀx) = 1` with respect to the trial covariate law (`S = true`). Then the
target law is absolutely continuous with respect to the trial law with density ratio `1`
(`densityRatio_ae_eq_tiltWeight`), the weight has mean one (`integral_tiltWeight_eq_one`), it
balances the covariate at its target mean (`populationBalanced_tiltWeight`), and the target law
is the trial law tilted by `0` (`map_eq_tilted`). -/
theorem logisticExample_results :
    (uniformPairLaw[|Prod.fst ⁻¹' {false}]).map logisticCov =
        ((uniformPairLaw[|Prod.fst ⁻¹' {true}]).map logisticCov).withDensity (fun x =>
          ENNReal.ofReal (tiltWeight id 0 0 0 x)) ∧
      ((uniformPairLaw[|Prod.fst ⁻¹' {false}]).map logisticCov ≪
          (uniformPairLaw[|Prod.fst ⁻¹' {true}]).map logisticCov ∧
        densityRatio (uniformPairLaw[|Prod.fst ⁻¹' {true}]) logisticCov
            (uniformPairLaw[|Prod.fst ⁻¹' {false}]) logisticCov
          =ᵐ[(uniformPairLaw[|Prod.fst ⁻¹' {true}]).map logisticCov] fun _ => 1) ∧
      ∫ x, tiltWeight id 0 0 0 x ∂((uniformPairLaw[|Prod.fst ⁻¹' {true}]).map logisticCov) = 1 ∧
      PopulationBalanced ((uniformPairLaw[|Prod.fst ⁻¹' {true}]).map logisticCov)
        (tiltWeight id 0 0 0) id
        (fun j => ∫ x, x j ∂((uniformPairLaw[|Prod.fst ⁻¹' {false}]).map logisticCov)) ∧
      (uniformPairLaw[|Prod.fst ⁻¹' {false}]).map logisticCov =
        ((uniformPairLaw[|Prod.fst ⁻¹' {true}]).map logisticCov).tilted
          fun x => (0 : Fin 1 → ℝ) ⬝ᵥ (id x - 0) := by
  have h0 := uniformPairLaw_fst_ne_zero false
  have h1 := uniformPairLaw_fst_ne_zero true
  have := cond_isProbabilityMeasure h0
  have := cond_isProbabilityMeasure h1
  have hcond := map_cond_eq_withDensity_tiltWeight measurable_fst measurable_logisticCov
    isPropensityScore_logisticCov h1 h0
  rw [real_fst_uniformPairLaw, real_fst_uniformPairLaw, div_self (by norm_num), Real.log_one,
    sub_zero, neg_zero] at hcond
  obtain ⟨hac, hae⟩ := densityRatio_ae_eq_tiltWeight measurable_id hcond
  refine ⟨hcond, ⟨hac, ?_⟩, integral_tiltWeight_eq_one measurable_id hcond,
    populationBalanced_tiltWeight measurable_id hcond fun j => ?_,
    map_eq_tilted measurable_id hcond⟩
  · filter_upwards [hae] with x hx
    rw [hx, tiltWeight_zero_zero]
  · exact (integrable_map_measure (measurable_pi_apply j).aestronglyMeasurable
      measurable_logisticCov.aemeasurable).2 Integrable.of_finite

end PopulationAdjustment

end CausalInference
