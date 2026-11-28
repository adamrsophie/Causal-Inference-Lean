/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralTrial
public import CausalInference.PopulationAdjustment.WeightedConsistencyLogistic

/-!
# Instances for the weighted estimator: conditional covariate laws and feature laws

**The logistic membership model in numbers.** In the model of `WeightedConsistencyLogistic`
(a fair coin covariate `X ∈ {0, 1}`, membership of the trial with `P(S = true | X) = σ(log 3 · X)`),
the joint masses are `P(X = x, S = true) = σ(log 3 · x) / 2` and
`P(X = x, S = false) = (1 - σ(log 3 · x)) / 2`, computed from the propensity of the uniform draw
(`logisticLaw_real_inter_true`, `logisticLaw_real_inter_false`). Hence the two conditional
covariate laws: `P(X = 0 | S = true) = 2/5`, `P(X = 1 | S = true) = 3/5`,
`P(X = 0 | S = false) = 2/3`, `P(X = 1 | S = false) = 1/3`, and the density ratios
`(2/3) / (2/5) = 5/3` and `(1/3) / (3/5) = 5/9` (`logistic_condCovLaw_ratios`), which agree with
the tilt weights of `logistic_density_ratio_example`, here computed independently of it.

**Feature laws satisfying the interior condition and the moment condition.**
* A three point law on `{-1, 0, 1}` (`threePointLaw`): the target `0` lies in the interior of the
  closed convex hull of its support (`zero_mem_interior_threePointLaw`), which by
  `WeightedConsistencyGeneralInterior` is the margin condition; its features are bounded, so all
  exponential moments are finite (`integrable_exp_threePointLaw`).
* A converging deterministic target sequence `tₙ = 1 / (n + 1) → 0`
  (`tendstoInMeasure_threePointTarget`).
* The standard Gaussian law, an unbounded feature law: every target lies in the interior
  (`mem_interior_gaussian`) and all exponential moments of `|x - t|` are finite
  (`integrable_exp_gaussian`).

## Main results

* `logistic_condCovLaw_true`, `logistic_condCovLaw_false`, `logistic_condCovLaw_ratios`.
* `zero_mem_interior_threePointLaw`, `integrable_exp_threePointLaw`,
  `tendstoInMeasure_threePointTarget`, `mem_interior_gaussian`, `integrable_exp_gaussian`.
* `feature_hypotheses_of_map_eq`, `feature_hypotheses_threePoint`,
  `feature_hypotheses_gaussian`: the interior and moment hypotheses of the arm theorem for
  records whose features follow these laws.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press (1970).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open MissingData PointTreatment EffectMeasure

/-! ### The conditional covariate laws of the logistic membership model -/

section Logistic

theorem halfLaw_real_singleton_eq_half (x : Bool) : halfLaw.real {x} = 1 / 2 := by
  rw [← integral_indicator_one (measurableSet_singleton x), integral_halfLaw]
  cases x <;> simp [Set.indicator]

theorem logisticFeature_injective : Function.Injective logisticFeature := by
  intro x y h
  have h0 := congrFun h 0
  cases x <;> cases y <;> simp_all [logisticFeature]

theorem logisticLaw_real_fst (x : Bool) :
    logisticLaw.real (Prod.fst ⁻¹' {logisticFeature x}) = 1 / 2 := by
  have hs : MeasurableSet ({logisticFeature x} : Set (Fin 1 → ℝ)) := measurableSet_singleton _
  rw [← map_measureReal_apply measurable_fst hs, logisticLaw, Measure.map_fst_prod,
    measure_univ, one_smul, logisticCovLaw,
    map_measureReal_apply (measurable_of_countable _) hs,
    show logisticFeature ⁻¹' {logisticFeature x} = {x} from
      Set.ext fun y => by simp [logisticFeature_injective.eq_iff]]
  exact halfLaw_real_singleton_eq_half x

/-- `P(X = x, S = true) = σ(log 3 · x) / 2`, from the propensity of the uniform draw. -/
theorem logisticLaw_real_inter_true (x : Bool) :
    logisticLaw.real (logisticMembership ⁻¹' {true} ∩ Prod.fst ⁻¹' {logisticFeature x}) =
      logisticScore (logisticFeature x) / 2 := by
  have hs : MeasurableSet ({logisticFeature x} : Set (Fin 1 → ℝ)) := measurableSet_singleton _
  have hA : MeasurableSet (logisticMembership ⁻¹' {true}) :=
    measurable_logisticMembership (measurableSet_singleton _)
  have hm : MeasurableSpace.comap (Prod.fst : (Fin 1 → ℝ) × ℝ → Fin 1 → ℝ) inferInstance ≤
      (inferInstance : MeasurableSpace ((Fin 1 → ℝ) × ℝ)) := measurable_fst.comap_le
  have hB : MeasurableSet[MeasurableSpace.comap (Prod.fst : (Fin 1 → ℝ) × ℝ → Fin 1 → ℝ)
      inferInstance] (Prod.fst ⁻¹' {logisticFeature x}) := ⟨_, hs, rfl⟩
  have hi : Integrable (respInd logisticMembership) logisticLaw :=
    (integrable_const (1 : ℝ)).indicator hA
  calc logisticLaw.real (logisticMembership ⁻¹' {true} ∩ Prod.fst ⁻¹' {logisticFeature x})
      = ∫ ω in Prod.fst ⁻¹' {logisticFeature x}, respInd logisticMembership ω ∂logisticLaw := by
        rw [respInd, setIntegral_indicator hA, Set.inter_comm]
        simp
    _ = ∫ ω in Prod.fst ⁻¹' {logisticFeature x},
          logisticLaw[respInd logisticMembership | MeasurableSpace.comap Prod.fst inferInstance] ω
          ∂logisticLaw := (setIntegral_condExp hm hi hB).symm
    _ = ∫ ω in Prod.fst ⁻¹' {logisticFeature x}, logisticScore ω.1 ∂logisticLaw :=
        setIntegral_congr_ae (hm _ hB)
          (isPropensityScore_logisticMembership.2.mono fun ω h _ => h)
    _ = ∫ ω in Prod.fst ⁻¹' {logisticFeature x}, logisticScore (logisticFeature x)
          ∂logisticLaw :=
        setIntegral_congr_fun (hm _ hB) fun ω hω => by
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hω
          rw [hω]
    _ = logisticScore (logisticFeature x) / 2 := by
        rw [setIntegral_const, logisticLaw_real_fst, smul_eq_mul]; ring

/-- `P(X = x, S = false) = (1 - σ(log 3 · x)) / 2`. -/
theorem logisticLaw_real_inter_false (x : Bool) :
    logisticLaw.real (logisticMembership ⁻¹' {false} ∩ Prod.fst ⁻¹' {logisticFeature x}) =
      (1 - logisticScore (logisticFeature x)) / 2 := by
  have hA : MeasurableSet (logisticMembership ⁻¹' {true}) :=
    measurable_logisticMembership (measurableSet_singleton _)
  have hc : logisticMembership ⁻¹' {false} ∩ Prod.fst ⁻¹' {logisticFeature x} =
      Prod.fst ⁻¹' {logisticFeature x} \
        (logisticMembership ⁻¹' {true} ∩ Prod.fst ⁻¹' {logisticFeature x}) := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff]
    cases logisticMembership ω <;> simp
  rw [hc, measureReal_sdiff Set.inter_subset_right (hA.inter (measurable_fst
    (measurableSet_singleton _))), logisticLaw_real_fst, logisticLaw_real_inter_true]
  ring

/-- The conditional covariate law `P(X = x | S = s)` as a ratio of masses. -/
theorem logistic_condCovLaw_real (s x : Bool) :
    ((logisticLaw[|logisticMembership ⁻¹' {s}]).map Prod.fst).real {logisticFeature x} =
      logisticLaw.real (logisticMembership ⁻¹' {s} ∩ Prod.fst ⁻¹' {logisticFeature x}) /
        logisticLaw.real (logisticMembership ⁻¹' {s}) := by
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton _), measureReal_def,
    cond_apply (measurable_logisticMembership (measurableSet_singleton _)),
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, div_eq_inv_mul]

/-- **The trial covariate law** `P(X | S = true)`: `2/5` at `x = 0` and `3/5` at `x = 1`. -/
theorem logistic_condCovLaw_true :
    ((logisticLaw[|logisticMembership ⁻¹' {true}]).map Prod.fst).real
        {logisticFeature false} = 2 / 5 ∧
      ((logisticLaw[|logisticMembership ⁻¹' {true}]).map Prod.fst).real
        {logisticFeature true} = 3 / 5 := by
  refine ⟨?_, ?_⟩ <;>
  · rw [logistic_condCovLaw_real, logisticLaw_real_inter_true, logisticLaw_real_true]
    simp only [logisticScore_feature_false, logisticScore_feature_true]
    norm_num

/-- **The target covariate law** `P(X | S = false)`: `2/3` at `x = 0` and `1/3` at `x = 1`. -/
theorem logistic_condCovLaw_false :
    ((logisticLaw[|logisticMembership ⁻¹' {false}]).map Prod.fst).real
        {logisticFeature false} = 2 / 3 ∧
      ((logisticLaw[|logisticMembership ⁻¹' {false}]).map Prod.fst).real
        {logisticFeature true} = 1 / 3 := by
  refine ⟨?_, ?_⟩ <;>
  · rw [logistic_condCovLaw_real, logisticLaw_real_inter_false, logisticLaw_real_false]
    simp only [logisticScore_feature_false, logisticScore_feature_true]
    norm_num

/-- **The density ratios of the two conditional covariate laws**:
`P(X = 0 | S = false) / P(X = 0 | S = true) = (2/3) / (2/5) = 5/3` and
`P(X = 1 | S = false) / P(X = 1 | S = true) = (1/3) / (3/5) = 5/9`. -/
theorem logistic_condCovLaw_ratios :
    ((logisticLaw[|logisticMembership ⁻¹' {false}]).map Prod.fst).real {logisticFeature false} /
        ((logisticLaw[|logisticMembership ⁻¹' {true}]).map Prod.fst).real
          {logisticFeature false} = 5 / 3 ∧
      ((logisticLaw[|logisticMembership ⁻¹' {false}]).map Prod.fst).real
          {logisticFeature true} /
        ((logisticLaw[|logisticMembership ⁻¹' {true}]).map Prod.fst).real
          {logisticFeature true} = 5 / 9 := by
  rw [logistic_condCovLaw_true.1, logistic_condCovLaw_true.2, logistic_condCovLaw_false.1,
    logistic_condCovLaw_false.2]
  norm_num

end Logistic

/-! ### A three point feature law -/

section ThreePoint

/-- The constant vector of length one with entry `r`. -/
def featureLineVec (r : ℝ) : Fin 1 → ℝ := fun _ => r

/-- The uniform law on the three points `-1, 0, 1` of the line, as vectors of length one. -/
noncomputable def threePointLaw : Measure (Fin 1 → ℝ) :=
  (3 : ℝ≥0∞)⁻¹ • (Measure.dirac (featureLineVec (-1)) + Measure.dirac (featureLineVec 0) +
    Measure.dirac (featureLineVec 1))

instance : IsProbabilityMeasure threePointLaw := by
  constructor
  simp only [threePointLaw, smul_apply, add_apply, measure_univ, smul_eq_mul]
  rw [show (1 : ℝ≥0∞) + 1 + 1 = 3 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem threePointLaw_pos {S : Set (Fin 1 → ℝ)} {r : ℝ} (hr : r = -1 ∨ r = 0 ∨ r = 1)
    (hS : featureLineVec r ∈ S) : 0 < threePointLaw S := by
  have h : (3 : ℝ≥0∞)⁻¹ * Measure.dirac (featureLineVec r) S ≤ threePointLaw S := by
    simp only [threePointLaw, smul_apply, add_apply, smul_eq_mul]
    gcongr
    rcases hr with rfl | rfl | rfl
    · exact le_self_add.trans le_self_add
    · exact le_add_self.trans le_self_add
    · exact le_add_self
  refine lt_of_lt_of_le ?_ h
  rw [Measure.dirac_apply_of_mem hS, mul_one]
  exact ENNReal.inv_pos.2 (by norm_num)

theorem apply_zero_ne_zero_of_ne_zero_fin_one {v : Fin 1 → ℝ} (hv : v ≠ 0) : v 0 ≠ 0 := fun h =>
  hv (funext fun i => by rw [Fin.fin_one_eq_zero i, h]; rfl)

/-- **The interior condition for the three point law**, through the measure form of
`mem_interior_closedConvexHull_iff_measure_pos`: every open half line through `0` charges one of
the points `-1` and `1`. -/
theorem zero_mem_interior_threePointLaw :
    (0 : Fin 1 → ℝ) ∈ interior (closedConvexHull ℝ threePointLaw.support) := by
  refine mem_interior_closedConvexHull_iff_measure_pos.2 fun v hv => ?_
  have h0 := apply_zero_ne_zero_of_ne_zero_fin_one hv
  rcases h0.lt_or_gt with hneg | hpos
  · refine threePointLaw_pos (r := -1) (Or.inl rfl) ?_
    simp only [Set.mem_ofPred_eq, sub_zero, dotProduct, Fin.sum_univ_one, featureLineVec]
    linarith
  · refine threePointLaw_pos (r := 1) (Or.inr (Or.inr rfl)) ?_
    simp only [Set.mem_ofPred_eq, sub_zero, dotProduct, Fin.sum_univ_one, featureLineVec]
    linarith

/-- Every measurable function is integrable for the three point law; in particular all
exponential moments `E[exp(κ ‖y - t‖)]` are finite. -/
theorem integrable_threePointLaw {f : (Fin 1 → ℝ) → ℝ} (hf : Measurable f) :
    Integrable f threePointLaw := by
  have hd : ∀ r : ℝ, Integrable f (Measure.dirac (featureLineVec r)) := fun r =>
    integrable_dirac' hf.stronglyMeasurable eNorm_lt_top
  exact (((hd (-1)).add_measure (hd 0)).add_measure (hd 1)).smul_measure (by simp)

theorem integrable_exp_threePointLaw (κ : ℝ) (t : Fin 1 → ℝ) :
    Integrable (fun y => Real.exp (κ * ‖y - t‖)) threePointLaw :=
  integrable_threePointLaw (Real.measurable_exp.comp (measurable_const.mul
    (measurable_id.sub_const t).norm))

/-- **A converging deterministic target sequence**: `tₙ = 1 / (n + 1) → 0`, as constant random
variables on any probability space. -/
theorem tendstoInMeasure_threePointTarget {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    TendstoInMeasure P (fun (n : ℕ) (_ : Ω) => featureLineVec (1 / ((n : ℝ) + 1))) atTop
      (fun _ => 0) := by
  refine tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (ae_of_all _ fun _ => ?_)
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_pi_nhds.2 fun _ => h

end ThreePoint

/-! ### An unbounded feature law: the standard Gaussian -/

section Gaussian

/-- The standard Gaussian law on vectors of length one. -/
noncomputable def gaussianFeatureLaw : Measure (Fin 1 → ℝ) := (gaussianReal 0 1).map featureLineVec

theorem measurable_featureLineVec : Measurable featureLineVec :=
  Measurable.of_eval fun _ => measurable_id

instance : IsProbabilityMeasure gaussianFeatureLaw := by
  unfold gaussianFeatureLaw; infer_instance

/-- **The interior condition holds at every target** for the Gaussian feature law: every open
half line has positive Gaussian mass. -/
theorem mem_interior_gaussian (t : Fin 1 → ℝ) :
    t ∈ interior (closedConvexHull ℝ gaussianFeatureLaw.support) := by
  refine mem_interior_closedConvexHull_iff_measure_pos.2 fun v hv => ?_
  have h0 := apply_zero_ne_zero_of_ne_zero_fin_one hv
  have hset : MeasurableSet {y : Fin 1 → ℝ | 0 < v ⬝ᵥ (y - t)} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [gaussianFeatureLaw, Measure.map_apply measurable_featureLineVec hset, pos_iff_ne_zero]
  intro hz
  have hvol := gaussianReal_absolutelyContinuous' 0 one_ne_zero hz
  have hpre : featureLineVec ⁻¹' {y : Fin 1 → ℝ | 0 < v ⬝ᵥ (y - t)} =
      {r : ℝ | 0 < v 0 * (r - t 0)} := by
    ext r
    simp [featureLineVec, dotProduct]
  rw [hpre] at hvol
  rcases h0.lt_or_gt with hneg | hpos
  · have : Set.Iio (t 0) ⊆ {r : ℝ | 0 < v 0 * (r - t 0)} := fun r hr => by
      simp only [Set.mem_ofPred_eq]; nlinarith [Set.mem_Iio.1 hr]
    have := measure_mono_null this hvol
    simp at this
  · have : Set.Ioi (t 0) ⊆ {r : ℝ | 0 < v 0 * (r - t 0)} := fun r hr => by
      simp only [Set.mem_ofPred_eq]; nlinarith [Set.mem_Ioi.1 hr]
    have := measure_mono_null this hvol
    simp at this

/-- **All exponential moments are finite** for the Gaussian feature law:
`E[exp(κ ‖y - t‖)] < ∞` for every `κ` and `t`, although the features are unbounded. -/
theorem integrable_exp_gaussian (κ : ℝ) (t : Fin 1 → ℝ) :
    Integrable (fun y => Real.exp (κ * ‖y - t‖)) gaussianFeatureLaw := by
  have hm : Measurable fun y : Fin 1 → ℝ => Real.exp (κ * ‖y - t‖) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_id.sub_const t).norm)
  rw [gaussianFeatureLaw, integrable_map_measure hm.aestronglyMeasurable
    measurable_featureLineVec.aemeasurable]
  have hi : ∀ c : ℝ, Integrable (fun r : ℝ => Real.exp (c * (r - t 0))) (gaussianReal 0 1) :=
    fun c => by
      have := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) c).const_mul
        (Real.exp (-(c * t 0)))
      refine this.congr (ae_of_all _ fun r => ?_)
      simp only
      rw [← Real.exp_add]; ring_nf
  refine ((hi |κ|).add (hi (-|κ|))).mono' (hm.comp measurable_featureLineVec).aestronglyMeasurable
    (ae_of_all _ fun r => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hn : ‖featureLineVec r - t‖ = |r - t 0| := by
    have : featureLineVec r - t = fun _ : Fin 1 => r - t 0 := funext fun i => by
      rw [Fin.fin_one_eq_zero i]; rfl
    rw [this, pi_norm_const, Real.norm_eq_abs]
  rw [hn]
  have h1 : κ * |r - t 0| ≤ |κ| * |r - t 0| :=
    mul_le_mul_of_nonneg_right (le_abs_self κ) (abs_nonneg _)
  rcases le_total 0 (r - t 0) with h | h
  · rw [abs_of_nonneg h] at h1 ⊢
    exact (Real.exp_le_exp.2 h1).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [abs_of_nonpos h] at h1 ⊢
    refine (Real.exp_le_exp.2 h1).trans (le_add_of_nonneg_left (Real.exp_pos _).le |>.trans_eq' ?_)
    ring_nf

end Gaussian

/-! ### The feature hypotheses of the arm theorem from the feature law -/

section Records

variable {𝒟 : Type*} [MeasurableSpace 𝒟] {ν : Measure 𝒟} {p : ℕ}

/-- **The feature hypotheses from the feature law.** If the law of the features `f(z)` of a
record is `λ`, the target `t` lies in the interior of the closed convex hull of the support of
`λ` and `λ` has all exponential moments of `‖y - t‖`, then the record law satisfies the interior
and moment hypotheses of `sampleBalancedArmMean_isConsistent_of_interior_of_integrable_exp`. -/
theorem feature_hypotheses_of_map_eq {f : 𝒟 → Fin p → ℝ} (hf : Measurable f)
    {lam : Measure (Fin p → ℝ)} (hlam : ν.map f = lam) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ lam.support))
    (hexp : ∀ κ : ℝ, Integrable (fun y => Real.exp (κ * ‖y - t‖)) lam) :
    t ∈ interior (closedConvexHull ℝ (ν.map f).support) ∧
      ∀ κ : ℝ, Integrable (fun z => Real.exp (κ * ‖f z - t‖)) ν := by
  refine ⟨hlam ▸ hint, fun κ => ?_⟩
  have hm : Measurable fun y : Fin p → ℝ => Real.exp (κ * ‖y - t‖) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_id.sub_const t).norm)
  have h := hexp κ
  rw [← hlam, integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable] at h
  exact h

/-- Records whose features follow the three point law satisfy the feature hypotheses at the
target `0`. -/
theorem feature_hypotheses_threePoint {f : 𝒟 → Fin 1 → ℝ} (hf : Measurable f)
    (hlaw : ν.map f = threePointLaw) :
    (0 : Fin 1 → ℝ) ∈ interior (closedConvexHull ℝ (ν.map f).support) ∧
      ∀ κ : ℝ, Integrable (fun z => Real.exp (κ * ‖f z - 0‖)) ν :=
  feature_hypotheses_of_map_eq hf hlaw zero_mem_interior_threePointLaw fun κ =>
    integrable_exp_threePointLaw κ 0

/-- Records whose features follow the standard Gaussian law satisfy the feature hypotheses at
every target `t`, although the features are unbounded. -/
theorem feature_hypotheses_gaussian {f : 𝒟 → Fin 1 → ℝ} (hf : Measurable f)
    (hlaw : ν.map f = gaussianFeatureLaw) (t : Fin 1 → ℝ) :
    t ∈ interior (closedConvexHull ℝ (ν.map f).support) ∧
      ∀ κ : ℝ, Integrable (fun z => Real.exp (κ * ‖f z - t‖)) ν :=
  feature_hypotheses_of_map_eq hf hlaw (mem_interior_gaussian t) fun κ =>
    integrable_exp_gaussian κ t

end Records

end PopulationAdjustment

end CausalInference
