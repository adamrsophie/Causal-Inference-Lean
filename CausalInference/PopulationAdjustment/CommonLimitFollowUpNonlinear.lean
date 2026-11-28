/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitFollowUpGeneral

/-!
# Weighting and standardization with a regression nonlinear in a matched feature

A concrete model in which the regression of the treated arm is not affine in the matched feature,
so that the weighted limit, the standardized limit and the target mean are three different
numbers. Both limits are computed through `commonLimitFollowUp_interaction_limits`.

* The covariate `X ∈ {-1, 0, 1}` has law `(1/2, 1/4, 1/4)` in the trial; the arm is independent
  and equally likely. The matched feature is `φ(x) = x` with reported target mean `t = 0`.
* The outcome is `Y(true) = X²` and `Y(false) = 0`, with no noise.
* The design is the interaction design `(1, x, 1[a], 1[a]x)`.
* The target covariate law is uniform on `{-1, 0, 1}`; its feature mean is `0`.

The population tilt solves `-(1/2) e^{-β} + (1/4) e^{β} = 0`, so `e^{β} = √2`
(`commonLimitFollowUpNl_tiltMinimizer`); the tilted law is proportional to
`(1/2 · e^{-β}, 1/4, 1/4 · e^{β})` and the weighted limit is
`∫ x² dT_X^tilt = 4/(4 + √2)`. The projection coefficient of the treated arm is the least
squares line of `x²` on `(1, x)` under the trial law, `8/11 - x/11`
(`commonLimitFollowUpNl_trialProjectionCoef`), so the standardized limit is `8/11`. The target
mean of `x²` is `2/3`.

## Main definitions

* `commonLimitFollowUpNlTrial`, `commonLimitFollowUpNlTarget`, `commonLimitFollowUpNlSample`.

## Main results

* `commonLimitFollowUpNl_tiltMinimizer`, `commonLimitFollowUpNl_trialProjectionCoef`.
* `commonLimitFollowUpNl_limits`: the weighted estimator converges in probability to
  `4/(4 + √2)`, the standardized estimator to `8/11`, the target mean is `2/3`, and the three
  numbers are pairwise different.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The value `-1, 0, 1` of the covariate levels. -/
noncomputable def commonLimitFollowUpNlValue : Fin 3 → ℝ := ![-1, 0, 1]

/-- The trial covariate weights `(1/2, 1/4, 1/4)`. -/
noncomputable def commonLimitFollowUpNlWeights : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The trial covariate law. -/
noncomputable def commonLimitFollowUpNlCovLaw : Measure (Fin 3) :=
  stratumLaw commonLimitFollowUpNlWeights

theorem commonLimitFollowUpNl_weights_nonneg (x : Fin 3) : 0 ≤ commonLimitFollowUpNlWeights x := by
  fin_cases x <;> norm_num [commonLimitFollowUpNlWeights]

instance : IsProbabilityMeasure commonLimitFollowUpNlCovLaw :=
  isProbabilityMeasure_stratumLaw ⟨commonLimitFollowUpNl_weights_nonneg, by
    simp [commonLimitFollowUpNlWeights, Fin.sum_univ_three]; norm_num⟩

/-- The target covariate law: uniform on the three levels. -/
noncomputable def commonLimitFollowUpNlTargetLaw : Measure (Fin 3) :=
  stratumLaw fun _ => (1 / 3 : ℝ)

instance : IsProbabilityMeasure commonLimitFollowUpNlTargetLaw :=
  isProbabilityMeasure_stratumLaw ⟨fun _ => by norm_num, by simp⟩

/-- The matched feature `φ(x) = x`. -/
noncomputable def commonLimitFollowUpNlFeature (x : Fin 3) : Fin 1 → ℝ :=
  fun _ => commonLimitFollowUpNlValue x

/-- The potential outcomes `Y(true) = x²`, `Y(false) = 0`. -/
noncomputable def commonLimitFollowUpNlOutcome (a : Bool) (x : Fin 3) : ℝ :=
  if a then commonLimitFollowUpNlValue x ^ 2 else 0

/-- The trial: assignment `ω.1` and covariate `ω.2`, independent. -/
noncomputable def commonLimitFollowUpNlTrial : Trial (Bool × Fin 3) (Fin 3) Bool where
  μ := halfLaw.prod commonLimitFollowUpNlCovLaw
  X := Prod.snd
  Y a ω := commonLimitFollowUpNlOutcome a ω.2
  A := Prod.fst

instance : IsProbabilityMeasure commonLimitFollowUpNlTrial.μ := by
  unfold commonLimitFollowUpNlTrial; infer_instance

/-- The target population: uniform covariate, the same potential outcomes. -/
noncomputable def commonLimitFollowUpNlTarget : Population (Fin 3) (Fin 3) Bool :=
  ⟨commonLimitFollowUpNlTargetLaw, id, commonLimitFollowUpNlOutcome⟩

instance : IsProbabilityMeasure commonLimitFollowUpNlTarget.μ := by
  unfold commonLimitFollowUpNlTarget; infer_instance

theorem commonLimitFollowUpNl_integral_covLaw (f : Fin 3 → ℝ) :
    ∫ x, f x ∂commonLimitFollowUpNlCovLaw = f 0 / 2 + f 1 / 4 + f 2 / 4 := by
  rw [commonLimitFollowUpNlCovLaw, integral_stratumLaw commonLimitFollowUpNl_weights_nonneg]
  simp [standardizedRisk, Fin.sum_univ_three, commonLimitFollowUpNlWeights]
  ring

theorem commonLimitFollowUpNl_integral_targetLaw (f : Fin 3 → ℝ) :
    ∫ x, f x ∂commonLimitFollowUpNlTargetLaw = (f 0 + f 1 + f 2) / 3 := by
  rw [commonLimitFollowUpNlTargetLaw, integral_stratumLaw fun _ => by norm_num]
  simp [standardizedRisk, Fin.sum_univ_three]
  ring

theorem commonLimitFollowUpNl_integral_trial (F : Bool × Fin 3 → ℝ) :
    ∫ ω, F ω ∂commonLimitFollowUpNlTrial.μ =
      ((F (true, 0) + F (false, 0)) / 2 + (F (true, 1) + F (false, 1)) / 4 +
        (F (true, 2) + F (false, 2)) / 4) / 2 := by
  change ∫ ω, F ω ∂(halfLaw.prod commonLimitFollowUpNlCovLaw) = _
  rw [integral_prod _ Integrable.of_finite, integral_halfLaw, commonLimitFollowUpNl_integral_covLaw,
    commonLimitFollowUpNl_integral_covLaw]
  ring

theorem commonLimitFollowUpNl_covLaw : commonLimitFollowUpNlTrial.covLaw =
    commonLimitFollowUpNlCovLaw := by
  change (halfLaw.prod commonLimitFollowUpNlCovLaw).map Prod.snd = _
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- **The trial is randomized.** -/
theorem commonLimitFollowUpNl_isRandomizedTwoArm :
    commonLimitFollowUpNlTrial.IsRandomizedTwoArm where
  measurable_X := measurable_snd
  measurable_A := measurable_fst
  measurable_Y _ := measurable_of_finite _
  indepFun := by
    have h : IndepFun (Prod.fst : Bool × Fin 3 → Bool) Prod.snd
        (halfLaw.prod commonLimitFollowUpNlCovLaw) :=
      indepFun_prod (X := (id : Bool → Bool)) (Y := (id : Fin 3 → Fin 3)) measurable_id
        measurable_id
    exact h.comp measurable_id (measurable_of_finite (fun x : Fin 3 =>
      (x, potentialPair (fun a (y : Fin 3) => commonLimitFollowUpNlOutcome a y) x)))
  prob_pos := by
    change 0 < (halfLaw.prod commonLimitFollowUpNlCovLaw).real (Prod.fst ⁻¹' {true})
    rw [measureReal_def, ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    simp [halfLaw, stratumLaw]
  prob_lt_one := by
    change (halfLaw.prod commonLimitFollowUpNlCovLaw).real (Prod.fst ⁻¹' {true}) < 1
    rw [measureReal_def, ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    simp [halfLaw, stratumLaw]
    norm_num

/-- The potential outcomes have finite second moments. -/
theorem commonLimitFollowUpNl_memLp (a : Bool) : MemLp (commonLimitFollowUpNlTrial.Y a) 2
    commonLimitFollowUpNlTrial.μ :=
  MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
    rcases ω with ⟨_, x⟩
    cases a <;> fin_cases x <;>
      norm_num [commonLimitFollowUpNlTrial, commonLimitFollowUpNlOutcome,
        commonLimitFollowUpNlValue])

/-- **The regression** of the outcome on the covariate and the arm is the outcome itself. -/
theorem commonLimitFollowUpNl_regression :
    IsOutcomeRegression commonLimitFollowUpNlTrial.μ commonLimitFollowUpNlTrial.A
      commonLimitFollowUpNlTrial.X commonLimitFollowUpNlTrial.obsOutcome
      commonLimitFollowUpNlOutcome := by
  refine ⟨fun _ => measurable_of_finite _, ?_⟩
  have hm : Measurable[MeasurableSpace.comap
      (fun ω => (commonLimitFollowUpNlTrial.X ω, commonLimitFollowUpNlTrial.A ω)) inferInstance]
      commonLimitFollowUpNlTrial.obsOutcome :=
    (measurable_of_finite fun q : Fin 3 × Bool => commonLimitFollowUpNlOutcome q.2 q.1).comp
      (comap_measurable _)
  rw [condExp_of_stronglyMeasurable (commonLimitFollowUpNl_isRandomizedTwoArm.measurable_X.prodMk
    commonLimitFollowUpNl_isRandomizedTwoArm.measurable_A).comap_le hm.stronglyMeasurable
    Integrable.of_finite]
  rfl

/-- The law of the sample: infinitely many independent copies of the trial. -/
noncomputable def commonLimitFollowUpNlSampleLaw : Measure (ℕ → Bool × Fin 3) :=
  Measure.infinitePi fun _ => commonLimitFollowUpNlTrial.μ

instance : IsProbabilityMeasure commonLimitFollowUpNlSampleLaw := by
  unfold commonLimitFollowUpNlSampleLaw; infer_instance

/-- The record `(X, A, Y)` of a unit of the trial. -/
noncomputable def commonLimitFollowUpNlRecord (ω : Bool × Fin 3) : Fin 3 × Bool × ℝ :=
  (commonLimitFollowUpNlTrial.X ω, commonLimitFollowUpNlTrial.A ω,
    commonLimitFollowUpNlTrial.obsOutcome ω)

/-- The records of the sample. -/
noncomputable def commonLimitFollowUpNlSample (i : ℕ) (ω : ℕ → Bool × Fin 3) :
    Fin 3 × Bool × ℝ :=
  commonLimitFollowUpNlRecord (ω i)

theorem commonLimitFollowUpNl_map_sample (i : ℕ) :
    commonLimitFollowUpNlSampleLaw.map (commonLimitFollowUpNlSample i) =
      commonLimitFollowUpNlTrial.ipdLaw := by
  have : commonLimitFollowUpNlSample i =
      commonLimitFollowUpNlRecord ∘ fun x : ℕ → Bool × Fin 3 => x i := rfl
  rw [this, ← Measure.map_map (g := commonLimitFollowUpNlRecord) (measurable_of_finite _)
    (measurable_pi_apply i), commonLimitFollowUpNlSampleLaw, Measure.infinitePi_map_eval]
  rfl

/-- **The sample is i.i.d.** -/
theorem commonLimitFollowUpNl_isIIDSample :
    IsIIDSample commonLimitFollowUpNlSample commonLimitFollowUpNlSampleLaw where
  indep := iIndepFun_infinitePi (P := fun _ => commonLimitFollowUpNlTrial.μ) fun _ =>
    measurable_of_finite _
  ident i := ⟨((measurable_of_finite commonLimitFollowUpNlRecord).comp
      (measurable_pi_apply i)).aemeasurable,
    ((measurable_of_finite commonLimitFollowUpNlRecord).comp (measurable_pi_apply 0)).aemeasurable,
    (commonLimitFollowUpNl_map_sample i).trans (commonLimitFollowUpNl_map_sample 0).symm⟩

theorem commonLimitFollowUpNl_bound (x : Fin 3) : ‖commonLimitFollowUpNlFeature x - 0‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => ?_
  fin_cases x <;> norm_num [commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue]

theorem commonLimitFollowUpNl_real_singleton (x : Fin 3) :
    commonLimitFollowUpNlCovLaw.real {x} = commonLimitFollowUpNlWeights x := by
  rw [← integral_indicator_one (measurableSet_singleton x),
    commonLimitFollowUpNl_integral_covLaw]
  fin_cases x <;> simp [Set.indicator, commonLimitFollowUpNlWeights]

/-- **The margin condition** at `t = 0` with `δ = 1/4` for the trial covariate law. -/
theorem commonLimitFollowUpNl_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 4 : ℝ) ≤
    commonLimitFollowUpNlTrial.covLaw.real
      {x | 1 / 4 ≤ v ⬝ᵥ (commonLimitFollowUpNlFeature x - 0)} := by
  intro v hv
  have hv0 : |v 0| = 1 := by
    have h : ‖v‖ = ‖v 0‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
        (norm_le_pi_norm v 0)
      rw [Subsingleton.elim j 0]
    rw [← Real.norm_eq_abs, ← h, hv]
  rw [commonLimitFollowUpNl_covLaw]
  rcases abs_eq zero_le_one |>.1 hv0 with h | h
  · calc (1 / 4 : ℝ) ≤ commonLimitFollowUpNlCovLaw.real {2} := by
          rw [commonLimitFollowUpNl_real_singleton]; norm_num [commonLimitFollowUpNlWeights]
      _ ≤ _ := measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue]
    norm_num
  · calc (1 / 4 : ℝ) ≤ commonLimitFollowUpNlCovLaw.real {0} := by
          rw [commonLimitFollowUpNl_real_singleton]; norm_num [commonLimitFollowUpNlWeights]
      _ ≤ _ := measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue]
    norm_num

/-! ### The population tilt and the weighted limit -/

theorem commonLimitFollowUpNl_isProbabilityMeasure_ipdLaw :
    IsProbabilityMeasure commonLimitFollowUpNlTrial.ipdLaw := by
  rw [Trial.ipdLaw]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).2
    inferInstance

/-- The population tilt `β₀ = log √2`, that is `e^{β₀} = √2` and `e^{2β₀} = 2`. -/
noncomputable def commonLimitFollowUpNlTilt : Fin 1 → ℝ := fun _ => Real.log (Real.sqrt 2)

theorem commonLimitFollowUpNl_tiltWeight (x : Fin 3) :
    tiltWeight commonLimitFollowUpNlFeature 0 0 commonLimitFollowUpNlTilt x =
      ![(Real.sqrt 2)⁻¹, 1, Real.sqrt 2] x := by
  have h := Real.exp_log (Real.sqrt_pos.2 (two_pos : (0 : ℝ) < 2))
  fin_cases x <;>
    simp [tiltWeight, dotProduct, commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue,
      commonLimitFollowUpNlTilt, Real.exp_neg, h]

/-- **The population tilt of the trial** is `β₀ = log √2`: it solves the balance equation
`-(1/2) e^{-β} + (1/4) e^{β} = 0`. -/
theorem commonLimitFollowUpNl_tiltMinimizer :
    tiltMinimizer commonLimitFollowUpNlTrial.ipdLaw commonLimitFollowUpNlFeature 0 =
      commonLimitFollowUpNlTilt := by
  have := commonLimitFollowUpNl_isProbabilityMeasure_ipdLaw
  refine tiltMinimizer_eq_of_balance (measurable_of_finite _) commonLimitFollowUpNl_bound
    (by norm_num : (0 : ℝ) < 1 / 4) (commonLimitFollowUp_margin_ipdLaw
      commonLimitFollowUpNl_isRandomizedTwoArm (measurable_of_finite _)
      commonLimitFollowUpNl_margin) fun j => ?_
  rw [commonLimitFollowUp_integral_ipdLaw_fst commonLimitFollowUpNl_isRandomizedTwoArm
    (f := fun x => tiltWeight commonLimitFollowUpNlFeature 0 0 commonLimitFollowUpNlTilt x *
      (commonLimitFollowUpNlFeature x j - (0 : Fin 1 → ℝ) j)) (measurable_of_finite _),
    commonLimitFollowUpNl_covLaw, commonLimitFollowUpNl_integral_covLaw]
  simp only [commonLimitFollowUpNl_tiltWeight]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  simp [commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue]
  field_simp
  linarith

/-- **The weighted limit**: the treated regression `x²` averaged under the tilted covariate law
is `4/(4 + √2)`. -/
theorem commonLimitFollowUpNl_weighted_value :
    ∫ x, commonLimitFollowUpNlOutcome true x ∂commonLimitFollowUpTilted commonLimitFollowUpNlTrial
      commonLimitFollowUpNlFeature 0 = 4 / (4 + Real.sqrt 2) := by
  rw [commonLimitFollowUp_integral_tiltedCovLaw (measurable_of_finite _)]
  simp only [commonLimitFollowUpTilt, commonLimitFollowUpNl_tiltMinimizer,
    commonLimitFollowUpNl_covLaw, commonLimitFollowUpNl_integral_covLaw,
    commonLimitFollowUpNl_tiltWeight]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_zero,
    commonLimitFollowUpNlOutcome, ↓reduceIte, commonLimitFollowUpNlValue, even_two, Even.neg_pow,
    one_pow, mul_one, cons_val_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_div, add_zero, cons_val, one_div]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  nlinarith

/-! ### The projection coefficient and the standardized limit -/

/-- The projection coefficient of the example in the interaction design: `0` for the control
arm, and the line `8/11 - x/11` for the treated arm. -/
noncomputable def commonLimitFollowUpNlCoef : Option (Fin 1) ⊕ Option (Fin 1) → ℝ
  | .inl _ => 0
  | .inr none => 8 / 11
  | .inr (some _) => -1 / 11

/-- **The projection coefficient** of the interaction design is `commonLimitFollowUpNlCoef`: the
normal equations `G ξ = E[z Y]` hold at it, and `G` is positive definite. -/
theorem commonLimitFollowUpNl_trialProjectionCoef :
    commonLimitFollowUpCoef commonLimitFollowUpNlTrial
      (featureInteractionDesign commonLimitFollowUpNlFeature) = commonLimitFollowUpNlCoef := by
  have hG := posDef_featureInteractionDesign_gram commonLimitFollowUpNl_isRandomizedTwoArm
    (measurable_of_finite _) commonLimitFollowUpNl_bound (by norm_num : (0 : ℝ) < 1 / 4)
    commonLimitFollowUpNl_margin
  have hmul : (Matrix.of fun j k => ∫ ω,
      featureInteractionDesign commonLimitFollowUpNlFeature (commonLimitFollowUpNlTrial.A ω)
        (commonLimitFollowUpNlTrial.X ω) j *
      featureInteractionDesign commonLimitFollowUpNlFeature (commonLimitFollowUpNlTrial.A ω)
        (commonLimitFollowUpNlTrial.X ω) k ∂commonLimitFollowUpNlTrial.μ) *ᵥ
      commonLimitFollowUpNlCoef = fun j => ∫ ω,
        featureInteractionDesign commonLimitFollowUpNlFeature (commonLimitFollowUpNlTrial.A ω)
          (commonLimitFollowUpNlTrial.X ω) j * commonLimitFollowUpNlTrial.obsOutcome ω
        ∂commonLimitFollowUpNlTrial.μ := by
    funext j
    simp only [mulVec, dotProduct, Matrix.of_apply]
    simp only [commonLimitFollowUpNl_integral_trial]
    rcases j with (_ | j) | (_ | j) <;>
      simp [featureInteractionDesign, interactionDesign, Fintype.sum_sum_type,
        commonLimitFollowUpNlCoef, commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue,
        commonLimitFollowUpNlTrial, Trial.obsOutcome, commonLimitFollowUpNlOutcome] <;>
      norm_num
  rw [commonLimitFollowUpCoef, ← hmul, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG.det_pos.ne'), one_mulVec]

theorem commonLimitFollowUpNl_targetCovLaw :
    commonLimitFollowUpNlTarget.covLaw = commonLimitFollowUpNlTargetLaw := by
  change commonLimitFollowUpNlTargetLaw.map id = _
  rw [Measure.map_id]

/-- **The standardized limit**: the fitted treated surface at the projection coefficient,
`8/11 - x/11`, averaged under the uniform target law, is `8/11`. -/
theorem commonLimitFollowUpNl_standardized_value :
    ∫ x, featureInteractionDesign commonLimitFollowUpNlFeature true x ⬝ᵥ
      commonLimitFollowUpCoef commonLimitFollowUpNlTrial
        (featureInteractionDesign commonLimitFollowUpNlFeature)
      ∂commonLimitFollowUpNlTarget.covLaw = 8 / 11 := by
  rw [commonLimitFollowUpNl_trialProjectionCoef, commonLimitFollowUpNl_targetCovLaw,
    commonLimitFollowUpNl_integral_targetLaw]
  simp [featureInteractionDesign, interactionDesign, dotProduct, Fintype.sum_sum_type,
    commonLimitFollowUpNlCoef, commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue]
  norm_num

/-- **The target mean** of `Y(true) = x²` under the uniform target law is `2/3`. -/
theorem commonLimitFollowUpNl_target_value : commonLimitFollowUpNlTarget.armMean true = 2 / 3 := by
  change ∫ x, commonLimitFollowUpNlOutcome true x ∂commonLimitFollowUpNlTargetLaw = _
  rw [commonLimitFollowUpNl_integral_targetLaw]
  simp [commonLimitFollowUpNlOutcome, commonLimitFollowUpNlValue]
  norm_num

/-- The target feature mean is `0`. -/
theorem commonLimitFollowUpNl_featureMean (k : Fin 1) :
    ∫ x, commonLimitFollowUpNlFeature x k ∂commonLimitFollowUpNlTarget.covLaw =
      (0 : Fin 1 → ℝ) k := by
  rw [commonLimitFollowUpNl_targetCovLaw, commonLimitFollowUpNl_integral_targetLaw]
  simp [commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue]

/-- **Weighting, standardization and the target mean are three different numbers.** In the model
of this file every hypothesis of `commonLimitFollowUp_interaction_limits` holds; the treated
regression `x²` is not affine in the matched feature; the weighted estimator converges in
probability to `4/(4 + √2)`, the standardized least squares estimator to `8/11`, and their
difference to `4/(4 + √2) - 8/11`; the target mean is `2/3`; the three numbers are pairwise
different, and the weighted estimator is not consistent for the target mean. -/
theorem commonLimitFollowUpNl_limits :
    (¬ ∃ (α : ℝ) (β : Fin 1 → ℝ), ∀ x, commonLimitFollowUpNlOutcome true x =
      α + β ⬝ᵥ commonLimitFollowUpNlFeature x) ∧
    TendstoInMeasure commonLimitFollowUpNlSampleLaw
      (sampleBalancedArmMean commonLimitFollowUpNlFeature 0 commonLimitFollowUpNlSample true)
      atTop (fun _ => 4 / (4 + Real.sqrt 2)) ∧
    TendstoInMeasure commonLimitFollowUpNlSampleLaw (fun n ω => ∫ x,
      featureInteractionDesign commonLimitFollowUpNlFeature true x ⬝ᵥ
        leastSquaresFit (recordDesign (featureInteractionDesign commonLimitFollowUpNlFeature))
          recordResponse commonLimitFollowUpNlSample n ω ∂commonLimitFollowUpNlTarget.covLaw)
      atTop (fun _ => 8 / 11) ∧
    TendstoInMeasure commonLimitFollowUpNlSampleLaw (fun n ω =>
      sampleBalancedArmMean commonLimitFollowUpNlFeature 0 commonLimitFollowUpNlSample true n ω -
        ∫ x, featureInteractionDesign commonLimitFollowUpNlFeature true x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign commonLimitFollowUpNlFeature))
            recordResponse commonLimitFollowUpNlSample n ω ∂commonLimitFollowUpNlTarget.covLaw)
      atTop (fun _ => 4 / (4 + Real.sqrt 2) - 8 / 11) ∧
    commonLimitFollowUpNlTarget.armMean true = 2 / 3 ∧
    4 / (4 + Real.sqrt 2) ≠ 8 / 11 ∧ 4 / (4 + Real.sqrt 2) ≠ 2 / 3 ∧ (8 / 11 : ℝ) ≠ 2 / 3 ∧
    ¬ IsConsistent
      (sampleBalancedArmMean commonLimitFollowUpNlFeature 0 commonLimitFollowUpNlSample true)
      (commonLimitFollowUpNlTarget.armMean true) commonLimitFollowUpNlSampleLaw := by
  have : IsProbabilityMeasure commonLimitFollowUpNlTarget.covLaw := by
    rw [commonLimitFollowUpNl_targetCovLaw]; infer_instance
  obtain ⟨hW, hS, hD⟩ := commonLimitFollowUp_interaction_limits
    commonLimitFollowUpNl_isRandomizedTwoArm commonLimitFollowUpNl_memLp
    commonLimitFollowUpNl_regression commonLimitFollowUpNl_isIIDSample
    (commonLimitFollowUpNl_map_sample 0) (measurable_of_finite _) commonLimitFollowUpNl_bound
    (by norm_num : (0 : ℝ) < 1 / 4) commonLimitFollowUpNl_margin
    commonLimitFollowUpNlTarget.covLaw true
  rw [commonLimitFollowUpNl_weighted_value] at hW
  rw [commonLimitFollowUpNl_standardized_value] at hS
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne1 : 4 / (4 + Real.sqrt 2) ≠ 8 / 11 := by
    rw [Ne, div_eq_div_iff (by positivity) (by norm_num)]
    intro h
    have : Real.sqrt 2 = 3 / 2 := by linarith
    rw [this] at h2
    norm_num at h2
  have hne2 : 4 / (4 + Real.sqrt 2) ≠ 2 / 3 := by
    rw [Ne, div_eq_div_iff (by positivity) (by norm_num)]
    intro h
    have : Real.sqrt 2 = 2 := by linarith
    rw [this] at h2
    norm_num at h2
  refine ⟨?_, hW, hS, ?_, commonLimitFollowUpNl_target_value, hne1, hne2, by norm_num, ?_⟩
  · rintro ⟨α, β, h⟩
    have h0 := h 0
    have h1 := h 1
    have h2' := h 2
    simp [commonLimitFollowUpNlOutcome, commonLimitFollowUpNlFeature, commonLimitFollowUpNlValue,
      dotProduct] at h0 h1 h2'
    linarith
  · have h := hW.sub hS
    simp only [Pi.sub_def] at h
    exact h
  · intro hc
    rw [commonLimitFollowUpNl_target_value] at hc
    exact hne2 (tendstoInMeasure_const_unique hW hc)

end PopulationAdjustment

end CausalInference
