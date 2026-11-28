/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.CommonLimitLinear
public import CausalInference.PopulationAdjustment.WeightedNormalityLimit

/-!
# The two limits of weighting and standardization without an outcome model

The index trial `T` randomizes the arms `true` and `false`; an i.i.d. sample `O` of its records
`(X, A, Y)` is used by the weighted estimator (the entropy balancing weights at the reported
target feature means `t`, `sampleBalancedArmMean`) and by the standardized least squares
estimator `∫ z(a, x)ᵀξ̂ dQ_X` of a design `z`. No outcome model is assumed: the regression
`μ_a(x) = E[Y | X = x, A = a]` of the trial is arbitrary.

* **The weighted limit** is the arm regression averaged under the **tilted covariate law**
  `T_X^tilt`, the trial covariate law reweighted by the population tilt
  `w₀(x) = exp(β₀ᵀ(φ(x) - t))` (`commonLimitFollowUpTilted`):
  `μ̂_a → ∫ μ_a dT_X^tilt` (`commonLimitFollowUp_tendstoInMeasure_weighted`). The tilted law
  has feature means `t` (`commonLimitFollowUp_integral_feature_tiltedCovLaw`).
* **The standardized limit** is the fitted surface at the projection coefficient
  `ξ* = E[z zᵀ]⁻¹ E[z Y]` (`commonLimitFollowUpCoef`), averaged over the target covariate law:
  `∫ z(a, ·)ᵀξ̂ dQ_X → ∫ z(a, ·)ᵀξ* dQ_X`
  (`commonLimitFollowUp_tendstoInMeasure_standardized`).
* **The gap** (`commonLimitFollowUp_limits`): the difference of the two estimators converges in
  probability to
  `∫ (μ_a - z(a, ·)ᵀξ*) dT_X^tilt + (∫ z(a, ·)ᵀξ* dT_X^tilt - ∫ z(a, ·)ᵀξ* dQ_X)`,
  the tilted mean of the regression residual plus the difference of the tilted law and the target
  law on the fitted surface. The second term vanishes when the design functions of arm `a` are
  affine in the matched features and `Q_X` has feature means `t`
  (`commonLimitFollowUp_gap_of_affine_design`).
* **Zero gap** (`commonLimitFollowUp_zero_gap`): when the design is a correct model,
  `μ_a = z(a, ·)ᵀξ₀` for both arms, and the regression of arm `a` is affine in the features, both
  limits are `α + βᵀt`; with absolute constancy and overlap this is the target arm mean, as in
  `commonLimit_leastSquares_armMean`.
* **When the weighted limit is the target mean** (`commonLimitFollowUp_weighted_iff`): under
  absolute constancy and overlap, the weighted estimator is consistent for `E_Q[Y(s)]` exactly when
  `∫ μ_a dT_X^tilt = ∫ μ_a dQ_X`.
* For the interaction design `(1, φ(x), 1[a], 1[a]φ(x))` the design conditions follow from
  the margin condition (`commonLimitFollowUp_interaction_limits`).

## Main definitions

* `commonLimitFollowUpTilt`, `commonLimitFollowUpTilted`: the population tilt of a trial and the
  tilted covariate law.
* `commonLimitFollowUpCoef`: the projection coefficient of the design.

## Main results

* `commonLimitFollowUp_tiltArmMean_eq`, `commonLimitFollowUp_tendstoInMeasure_weighted`,
  `commonLimitFollowUp_tendstoInMeasure_standardized`, `commonLimitFollowUp_limits`.
* `commonLimitFollowUp_gap_of_affine_design`, `commonLimitFollowUp_zero_gap`,
  `commonLimitFollowUp_weighted_iff`, `commonLimitFollowUp_interaction_limits`.

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
open scoped ENNReal NNReal

/-! ### The tilted covariate law -/

section Tilt

variable {Ω₁ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] {p : ℕ}
  {T : Trial Ω₁ 𝒳 Bool} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}

/-- The **population tilt** `w₀(x) = exp(β₀ᵀ(φ(x) - t))` of a trial, with `β₀` the minimizer of
the population dual objective of entropy balancing on the records of the trial. -/
noncomputable def commonLimitFollowUpTilt (T : Trial Ω₁ 𝒳 Bool) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (x : 𝒳) : ℝ :=
  tiltWeight φ t 0 (tiltMinimizer T.ipdLaw φ t) x

/-- The **tilted covariate law** of a trial: the trial covariate law with density
`w₀ / ∫ w₀ dT_X`. -/
noncomputable def commonLimitFollowUpTilted (T : Trial Ω₁ 𝒳 Bool) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) : Measure 𝒳 :=
  T.covLaw.withDensity fun x =>
    ((commonLimitFollowUpTilt T φ t x / ∫ y, commonLimitFollowUpTilt T φ t y ∂T.covLaw).toNNReal :
      ℝ≥0∞)

omit [MeasurableSpace 𝒳] in
/-- A tilt is bounded above by `exp(p ‖β‖ B)` for features with `‖φ(x) - t‖ ≤ B`. -/
theorem commonLimitFollowUp_tiltWeight_le {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ)
    (x : 𝒳) : tiltWeight φ t 0 β x ≤ Real.exp (p * (‖β‖ * B)) :=
  (tiltWeight_mem_Icc (hB x) le_rfl).2

/-- A tilt is measurable for measurable features. -/
theorem commonLimitFollowUp_measurable_tiltWeight (hφ : Measurable φ) (β : Fin p → ℝ) :
    Measurable (tiltWeight φ t 0 β) :=
  (measurable_const.add ((continuous_const.dotProduct continuous_id).measurable.comp
    (hφ.sub_const t))).exp

/-- A tilt times a bounded measurable function is integrable under a finite measure. -/
theorem commonLimitFollowUp_integrable_tiltWeight_mul {ν : Measure 𝒳} [IsFiniteMeasure ν]
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ) {h : 𝒳 → ℝ}
    (hh : Integrable h ν) : Integrable (fun x => tiltWeight φ t 0 β x * h x) ν :=
  hh.bdd_mul (c := Real.exp (p * (‖β‖ * B)))
    (commonLimitFollowUp_measurable_tiltWeight hφ β).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (tiltWeight_pos _ _ _ _ _)]
      exact commonLimitFollowUp_tiltWeight_le hB β x)

/-- The population tilt is positive. -/
theorem commonLimitFollowUp_trialTilt_pos (x : 𝒳) : 0 < commonLimitFollowUpTilt T φ t x :=
  tiltWeight_pos _ _ _ _ _

/-- The population tilt is integrable under a finite measure, for bounded measurable features. -/
theorem commonLimitFollowUp_integrable_trialTilt {ν : Measure 𝒳} [IsFiniteMeasure ν]
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) :
    Integrable (commonLimitFollowUpTilt T φ t) ν := by
  have h := commonLimitFollowUp_integrable_tiltWeight_mul (ν := ν) hφ hB
    (tiltMinimizer T.ipdLaw φ t) (integrable_const (1 : ℝ))
  simp only [mul_one] at h
  exact h

/-- **The integral under the tilted covariate law** is the tilted ratio
`∫ g dT_X^tilt = (∫ w₀ g dT_X) / ∫ w₀ dT_X`, for every function `g`. -/
theorem commonLimitFollowUp_integral_tiltedCovLaw (hφ : Measurable φ) (g : 𝒳 → ℝ) :
    ∫ x, g x ∂commonLimitFollowUpTilted T φ t =
      (∫ x, commonLimitFollowUpTilt T φ t x * g x ∂T.covLaw) /
        ∫ x, commonLimitFollowUpTilt T φ t x ∂T.covLaw := by
  have hw : Measurable (commonLimitFollowUpTilt T φ t) :=
    commonLimitFollowUp_measurable_tiltWeight hφ _
  set Z := ∫ y, commonLimitFollowUpTilt T φ t y ∂T.covLaw with hZ
  have hZ0 : 0 ≤ Z := integral_nonneg fun y => (commonLimitFollowUp_trialTilt_pos y).le
  rw [commonLimitFollowUpTilted,
    integral_withDensity_eq_integral_smul (hw.div_const Z).real_toNNReal]
  have e : ∀ x, (commonLimitFollowUpTilt T φ t x / Z).toNNReal • g x =
      commonLimitFollowUpTilt T φ t x * g x / Z :=
    fun x => by
      rw [NNReal.smul_def, smul_eq_mul,
        Real.coe_toNNReal _ (div_nonneg (commonLimitFollowUp_trialTilt_pos x).le hZ0)]
      ring
  simp_rw [e]
  rw [integral_div]

/-- The law of the covariates of the records is the covariate law of the trial. -/
theorem commonLimitFollowUp_ipdLaw_map_fst (hT : T.IsRandomizedTwoArm) :
    T.ipdLaw.map Prod.fst = T.covLaw := by
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  rw [Trial.ipdLaw, Measure.map_map measurable_fst
    (hT.measurable_X.prodMk (hT.measurable_A.prodMk hYo))]
  rfl

/-- An integral of a function of the covariates of the records is an integral under the trial
covariate law. -/
theorem commonLimitFollowUp_integral_ipdLaw_fst (hT : T.IsRandomizedTwoArm) {f : 𝒳 → ℝ}
    (hf : Measurable f) : ∫ z, f z.1 ∂T.ipdLaw = ∫ x, f x ∂T.covLaw := by
  rw [← commonLimitFollowUp_ipdLaw_map_fst hT,
    integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]

/-- The margin condition for the trial covariate law is the margin condition for the law of the
records. -/
theorem commonLimitFollowUp_margin_ipdLaw (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ)
    {δ : ℝ} (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)}) :
    ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.ipdLaw.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)} := fun v hv => by
  have hset : MeasurableSet {x : 𝒳 | δ ≤ v ⬝ᵥ (φ x - t)} :=
    measurableSet_le measurable_const
      ((continuous_const.dotProduct continuous_id).measurable.comp (hφ.sub_const t))
  have h := hmargin v hv
  rwa [← commonLimitFollowUp_ipdLaw_map_fst hT, map_measureReal_apply measurable_fst hset] at h

variable [IsProbabilityMeasure T.μ]

/-- The normalizer `∫ w₀ dT_X` of the tilt is positive. -/
theorem commonLimitFollowUp_integral_trialTilt_pos (hT : T.IsRandomizedTwoArm)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) :
    0 < ∫ x, commonLimitFollowUpTilt T φ t x ∂T.covLaw := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  set β := tiltMinimizer T.ipdLaw φ t
  have hlow : ∀ x, Real.exp (-(p * (‖β‖ * B))) ≤ commonLimitFollowUpTilt T φ t x := fun x =>
    (tiltWeight_mem_Icc (hB x) le_rfl).1
  have hi : Integrable (commonLimitFollowUpTilt T φ t) T.covLaw :=
    commonLimitFollowUp_integrable_trialTilt hφ hB
  calc (0 : ℝ) < Real.exp (-(p * (‖β‖ * B))) := Real.exp_pos _
    _ = ∫ _ : 𝒳, Real.exp (-(p * (‖β‖ * B))) ∂T.covLaw := by simp
    _ ≤ _ := integral_mono (integrable_const _) hi hlow

/-- **The tilted covariate law balances the features**: `∫ φ_k dT_X^tilt = t_k`, by the
population balance equations of the tilt. -/
theorem commonLimitFollowUp_integral_feature_tiltedCovLaw (hT : T.IsRandomizedTwoArm)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (k : Fin p) : ∫ x, φ x k ∂commonLimitFollowUpTilted T φ t = t k := by
  have : IsProbabilityMeasure T.ipdLaw := by
    rw [Trial.ipdLaw]
    exact (Measure.isProbabilityMeasure_map_iff (hT.measurable_X.prodMk (hT.measurable_A.prodMk
      (measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A
        hT.measurable_Y))).aemeasurable).2 inferInstance
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  have hbal := integral_tiltWeight_tiltMinimizer_mul_sub hφ hB hδ
    (commonLimitFollowUp_margin_ipdLaw hT hφ hmargin) k
  have hw := commonLimitFollowUp_measurable_tiltWeight (t := t) hφ (tiltMinimizer T.ipdLaw φ t)
  have hφk : Measurable fun x => φ x k := (measurable_pi_apply k).comp hφ
  rw [commonLimitFollowUp_integral_ipdLaw_fst hT (f := fun x =>
    tiltWeight φ t 0 (tiltMinimizer T.ipdLaw φ t) x * (φ x k - t k))
    (hw.mul (hφk.sub_const _))] at hbal
  change ∫ x, commonLimitFollowUpTilt T φ t x * (φ x k - t k) ∂T.covLaw = 0 at hbal
  have hφi : Integrable (fun x => φ x k) T.covLaw :=
    (integrable_const (B + ‖t‖)).mono' hφk.aestronglyMeasurable (ae_of_all _ fun x => by
      calc ‖φ x k‖ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) k
        _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ B + ‖t‖ := (norm_add_le _ _).trans (by linarith [hB x]))
  have h1 : Integrable (fun x => commonLimitFollowUpTilt T φ t x * φ x k) T.covLaw :=
    commonLimitFollowUp_integrable_tiltWeight_mul (ν := T.covLaw) hφ hB
      (tiltMinimizer T.ipdLaw φ t) hφi
  have h2 : Integrable (commonLimitFollowUpTilt T φ t) T.covLaw :=
    commonLimitFollowUp_integrable_trialTilt hφ hB
  have e : ∀ x, commonLimitFollowUpTilt T φ t x * (φ x k - t k) =
      commonLimitFollowUpTilt T φ t x * φ x k - t k * commonLimitFollowUpTilt T φ t x := fun x => by
    ring
  simp_rw [e] at hbal
  rw [integral_sub h1 (h2.const_mul _), integral_const_mul, sub_eq_zero] at hbal
  rw [commonLimitFollowUp_integral_tiltedCovLaw hφ, hbal,
    mul_div_cancel_right₀ _ (commonLimitFollowUp_integral_trialTilt_pos hT hφ hB).ne']

/-- **The tilted law of an affine function of the features** is the affine function at `t`:
`∫ (c + bᵀφ) dT_X^tilt = c + bᵀt`. -/
theorem commonLimitFollowUp_integral_affine_tiltedCovLaw (hT : T.IsRandomizedTwoArm)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {f : 𝒳 → ℝ} {c : ℝ} {b : Fin p → ℝ} (haff : ∀ x, f x = c + b ⬝ᵥ φ x) :
    ∫ x, f x ∂commonLimitFollowUpTilted T φ t = c + b ⬝ᵥ t := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  set β := tiltMinimizer T.ipdLaw φ t
  set Z := ∫ x, commonLimitFollowUpTilt T φ t x ∂T.covLaw with hZ
  have hZ0 : Z ≠ 0 := (commonLimitFollowUp_integral_trialTilt_pos hT hφ hB).ne'
  have hφk : ∀ k, Measurable fun x => φ x k := fun k => (measurable_pi_apply k).comp hφ
  have hφi : ∀ k, Integrable (fun x => φ x k) T.covLaw := fun k =>
    (integrable_const (B + ‖t‖)).mono' (hφk k).aestronglyMeasurable (ae_of_all _ fun x => by
      calc ‖φ x k‖ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) k
        _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ B + ‖t‖ := (norm_add_le _ _).trans (by linarith [hB x]))
  have h1 : ∀ k, Integrable (fun x => commonLimitFollowUpTilt T φ t x * φ x k) T.covLaw := fun k =>
    commonLimitFollowUp_integrable_tiltWeight_mul hφ hB β (hφi k)
  have h2 : Integrable (commonLimitFollowUpTilt T φ t) T.covLaw :=
    commonLimitFollowUp_integrable_trialTilt hφ hB
  have hk : ∀ k, ∫ x, commonLimitFollowUpTilt T φ t x * φ x k ∂T.covLaw = t k * Z := fun k => by
    have h := commonLimitFollowUp_integral_feature_tiltedCovLaw hT hφ hB hδ hmargin k
    rw [commonLimitFollowUp_integral_tiltedCovLaw hφ, div_eq_iff hZ0] at h
    exact h
  have e : ∀ x, commonLimitFollowUpTilt T φ t x * f x =
      c * commonLimitFollowUpTilt T φ t x + ∑ k, b k * (commonLimitFollowUpTilt T φ t x * φ x k) :=
        fun x => by
    rw [haff, dotProduct, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun k _ => by ring
  rw [commonLimitFollowUp_integral_tiltedCovLaw hφ]
  simp_rw [e]
  rw [integral_add (h2.const_mul c) (integrable_finsetSum _ fun k _ => (h1 k).const_mul _),
    integral_const_mul, integral_finsetSum _ fun k _ => (h1 k).const_mul _]
  simp_rw [integral_const_mul, hk]
  rw [← hZ, dotProduct, add_div, mul_div_cancel_right₀ _ hZ0, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by field_simp

/-- A function integrable under the trial covariate law is integrable under the tilted law, for
bounded features. -/
theorem commonLimitFollowUp_integrable_tiltedCovLaw (hT : T.IsRandomizedTwoArm)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {g : 𝒳 → ℝ}
    (hg : Integrable g T.covLaw) : Integrable g (commonLimitFollowUpTilted T φ t) := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  have hw : Measurable (commonLimitFollowUpTilt T φ t) :=
    commonLimitFollowUp_measurable_tiltWeight hφ _
  set Z := ∫ y, commonLimitFollowUpTilt T φ t y ∂T.covLaw
  have hZ0 : 0 < Z := commonLimitFollowUp_integral_trialTilt_pos hT hφ hB
  rw [commonLimitFollowUpTilted,
    integrable_withDensity_iff_integrable_smul (hw.div_const Z).real_toNNReal]
  have h := (commonLimitFollowUp_integrable_tiltWeight_mul hφ hB
    (tiltMinimizer T.ipdLaw φ t) hg).div_const Z
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (div_nonneg (commonLimitFollowUp_trialTilt_pos x).le hZ0.le)]
  simp only [commonLimitFollowUpTilt]
  ring

end Tilt

/-! ### The weighted limit -/

section Weighted

variable {Ω₁ Ξ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳] {p : ℕ}
  {T : Trial Ω₁ 𝒳 Bool} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} [IsProbabilityMeasure T.μ]

/-- **The tilted arm mean of a randomized trial is the tilted mean of the arm regression.** For
any tilt `w_β` of bounded measurable features and any version `μ` of the regression
`E[Y | X, A]` with integrable potential outcomes, the weighted mean of arm `a` of the records
under the tilt is `∫ w_β μ_a dT_X / ∫ w_β dT_X`. The observed outcome is replaced by its
regression (tower property), and the arm indicator factors out by the independence of the
covariates and the assignment. -/
theorem commonLimitFollowUp_tiltArmMean_eq_ratio (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ a, Integrable (T.Y a) T.μ) {m : Bool → 𝒳 → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (a : Bool) (β : Fin p → ℝ) :
    tiltArmMean T.ipdLaw φ t a β =
      (∫ x, tiltWeight φ t 0 β x * m a x ∂T.covLaw) / ∫ x, tiltWeight φ t 0 β x ∂T.covLaw := by
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  have hYoi : Integrable T.obsOutcome T.μ :=
    PointTreatment.integrable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hYi
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) :=
    hT.measurable_X.prodMk (hT.measurable_A.prodMk hYo)
  have hw := commonLimitFollowUp_measurable_tiltWeight (t := t) hφ β
  set w := tiltWeight φ t 0 β
  set ind : Bool → ℝ := fun b => if b = a then 1 else 0
  have hind : Measurable ind := measurable_of_finite _
  -- the arm indicator factors out of a function of the covariates
  have hfac : ∀ h : 𝒳 → ℝ, Measurable h →
      ∫ ω, h (T.X ω) * ind (T.A ω) ∂T.μ =
        (∫ x, h x ∂T.covLaw) * T.μ.real (T.A ⁻¹' {a}) := fun h hh => by
    rw [hT.indepFun_X_A.integral_fun_comp_mul_comp hT.measurable_X.aemeasurable
      hT.measurable_A.aemeasurable hh.aestronglyMeasurable hind.aestronglyMeasurable]
    congr 1
    · rw [Population.covLaw, integral_map hT.measurable_X.aemeasurable hh.aestronglyMeasurable]
    · have e : (fun ω => ind (T.A ω)) = (T.A ⁻¹' {a}).indicator (1 : Ω₁ → ℝ) := by
        funext ω; simp [ind, Set.indicator]
      rw [e, integral_indicator_one (hT.measurable_A (measurableSet_singleton a))]
  have hq := hT.prob_arm_pos a
  -- the record integrals as integrals over the trial
  have hrec : ∀ F : 𝒳 × Bool × ℝ → ℝ, Measurable F →
      ∫ z, F z ∂T.ipdLaw = ∫ ω, F (T.X ω, T.A ω, T.obsOutcome ω) ∂T.μ := fun F hF => by
    rw [Trial.ipdLaw, integral_map hf.aemeasurable hF.aestronglyMeasurable]
  have hpt : ∀ z : 𝒳 × Bool × ℝ, armIndObs a z = ind z.2.1 := fun z => rfl
  have hnum : ∫ z, armIndObs a z * w z.1 * z.2.2 ∂T.ipdLaw =
      (∫ x, w x * m a x ∂T.covLaw) * T.μ.real (T.A ⁻¹' {a}) := by
    rw [hrec (fun z => armIndObs a z * w z.1 * z.2.2)
      (((measurable_armIndObs a).mul (hw.comp measurable_fst)).mul measurable_snd.snd)]
    simp only [hpt]
    -- the tower property on `σ(X, A)`
    set C : Ω₁ → 𝒳 × Bool := fun ω => (T.X ω, T.A ω)
    have hC : Measurable C := hT.measurable_X.prodMk hT.measurable_A
    set g : 𝒳 × Bool → ℝ := fun c => ind c.2 * w c.1
    have hg : Measurable g := (hind.comp measurable_snd).mul (hw.comp measurable_fst)
    have hgb : ∀ c, ‖g c‖ ≤ Real.exp (p * (‖β‖ * B)) := fun c => by
      simp only [g, ind, Real.norm_eq_abs]
      split_ifs
      · rw [one_mul, abs_of_pos (tiltWeight_pos _ _ _ _ _)]
        exact commonLimitFollowUp_tiltWeight_le hB β c.1
      · simp [(Real.exp_pos _).le]
    have hgY : Integrable (fun ω => g (C ω) * T.obsOutcome ω) T.μ :=
      hYoi.bdd_mul (hg.comp hC).aestronglyMeasurable (ae_of_all _ fun ω => hgb (C ω))
    have hle := hC.comap_le
    have hsm : StronglyMeasurable[MeasurableSpace.comap C inferInstance] fun ω => g (C ω) :=
      (hg.comp (comap_measurable C)).stronglyMeasurable
    have h1 := condExp_mul_of_stronglyMeasurable_left hsm hgY hYoi
    have e1 : ∫ ω, ind (T.A ω) * w (T.X ω) * T.obsOutcome ω ∂T.μ =
        ∫ ω, g (C ω) * T.obsOutcome ω ∂T.μ := rfl
    rw [e1, ← integral_condExp hle]
    change ∫ ω, T.μ[(fun ω => g (C ω)) * T.obsOutcome |
      MeasurableSpace.comap C inferInstance] ω ∂T.μ = _
    rw [integral_congr_ae (h1.trans (EventuallyEq.mul (ae_eq_refl _) hreg.2))]
    rw [← hfac (fun x => w x * m a x) (hw.mul (hreg.1 a))]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Pi.mul_apply, g, ind, C]
    by_cases h : T.A ω = a
    · simp [h]
    · simp [h]
  have hden : ∫ z, armIndObs a z * w z.1 ∂T.ipdLaw =
      (∫ x, w x ∂T.covLaw) * T.μ.real (T.A ⁻¹' {a}) := by
    rw [hrec (fun z => armIndObs a z * w z.1)
      ((measurable_armIndObs a).mul (hw.comp measurable_fst)), ← hfac _ hw]
    simp only [hpt]
    exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  rw [tiltArmMean, hnum, hden, mul_div_mul_right _ _ hq.ne']

/-- **The tilted arm mean at the population tilt is the arm regression averaged under the tilted
covariate law.** -/
theorem commonLimitFollowUp_tiltArmMean_eq (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ a, Integrable (T.Y a) T.μ) {m : Bool → 𝒳 → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) (a : Bool) :
    tiltArmMean T.ipdLaw φ t a (tiltMinimizer T.ipdLaw φ t) =
      ∫ x, m a x ∂commonLimitFollowUpTilted T φ t := by
  rw [commonLimitFollowUp_tiltArmMean_eq_ratio hT hYi hreg hφ hB,
    commonLimitFollowUp_integral_tiltedCovLaw hφ]
  rfl

variable {P : Measure Ξ} [IsProbabilityMeasure P] {O : ℕ → Ξ → 𝒳 × Bool × ℝ}

/-- **The weighted limit without an outcome model.** In a randomized trial with integrable
potential outcomes and any version `μ` of the regression `E[Y | X, A]`, for an i.i.d. sample of
its records, bounded measurable features and the margin condition at `t` for the trial covariate
law, the weighted arm mean converges in probability to `∫ μ_a dT_X^tilt`, the arm regression
averaged under the tilted covariate law. -/
theorem commonLimitFollowUp_tendstoInMeasure_weighted (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ a, Integrable (T.Y a) T.μ) {m : Bool → 𝒳 → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (a : Bool) :
    TendstoInMeasure P (sampleBalancedArmMean φ t O a) atTop
      (fun _ => ∫ x, m a x ∂commonLimitFollowUpTilted T φ t) := by
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) :=
    hT.measurable_X.prodMk (hT.measurable_A.prodMk hYo)
  have hq : 0 < (P.map (O 0)).real {z | z.2.1 = a} := by
    rw [hlaw, Trial.ipdLaw, map_measureReal_apply hf
      (measurableSet_eq_fun measurable_snd.fst measurable_const)]
    exact hT.prob_arm_pos a
  have hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) (P.map (O 0)) := by
    rw [hlaw, Trial.ipdLaw, integrable_map_measure measurable_snd.snd.aestronglyMeasurable
      hf.aemeasurable]
    exact PointTreatment.integrable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hYi
  have hm' : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)} := by
    rw [hlaw]; exact commonLimitFollowUp_margin_ipdLaw hT hφ hmargin
  have h := sampleBalancedArmMean_tendstoInMeasure hO hφ hB hδ hm' a hq hy
  rw [hlaw, commonLimitFollowUp_tiltArmMean_eq hT hYi hreg hφ hB a] at h
  exact h

end Weighted

/-! ### The standardized limit -/

section Standardized

variable {Ω₁ Ξ 𝒳 κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [Fintype κ] [DecidableEq κ] {T : Trial Ω₁ 𝒳 Bool}
  {P : Measure Ξ} [IsProbabilityMeasure P] {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {z : Bool → 𝒳 → κ → ℝ}

/-- The **projection coefficient** `ξ* = E[z zᵀ]⁻¹ E[z Y]` of the design `z(A, X)` and the
observed outcome of a trial: the coefficient of the best linear predictor of `Y` in the design. -/
noncomputable def commonLimitFollowUpCoef (T : Trial Ω₁ 𝒳 Bool) (z : Bool → 𝒳 → κ → ℝ) : κ → ℝ :=
  (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ)⁻¹ *ᵥ
    fun j => ∫ ω, z (T.A ω) (T.X ω) j * T.obsOutcome ω ∂T.μ

/-- **The least squares fit converges to the projection coefficient** with no outcome model, in
a randomized trial whose potential outcomes and design coordinates of each arm have finite second
moments and whose design second moment is positive definite. -/
theorem commonLimitFollowUp_tendstoInMeasure_fit (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hz : ∀ a j, Measurable fun x => z a x j)
    (hz2 : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ)
    (hG : (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ).PosDef)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) :
    TendstoInMeasure P (leastSquaresFit (recordDesign z) recordResponse O) atTop
      (fun _ => commonLimitFollowUpCoef T z) := by
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  have hD : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) :=
    hT.measurable_X.prodMk (hT.measurable_A.prodMk hYo)
  have hdm := measurable_recordDesign hz
  have hrm : Measurable (recordResponse (𝒲 := 𝒳)) := measurable_snd.comp measurable_snd
  have hzA : ∀ j, MemLp (fun ω => z (T.A ω) (T.X ω) j) 2 T.μ := fun j =>
    memLp_two_select (f := fun a ω => z a (T.X ω) j) hT.measurable_A
      (fun a => (hz a j).comp hT.measurable_X) fun a => hz2 a j
  have hd2 : ∀ j, MemLp (fun o => recordDesign z o j) 2 (P.map (O 0)) := fun j => by
    rw [hlaw, Trial.ipdLaw, memLp_map_measure_iff (hdm j).aestronglyMeasurable hD.aemeasurable]
    exact hzA j
  have hr2 : MemLp recordResponse 2 (P.map (O 0)) := by
    rw [hlaw, Trial.ipdLaw, memLp_map_measure_iff hrm.aestronglyMeasurable hD.aemeasurable]
    exact memLp_two_select hT.measurable_A hT.measurable_Y hY2
  have hGμ : ∀ j k, ∫ o, recordDesign z o j * recordDesign z o k ∂(P.map (O 0)) =
      ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ := fun j k => by
    rw [hlaw, Trial.ipdLaw, integral_map (f := fun o => recordDesign z o j * recordDesign z o k)
      hD.aemeasurable ((hdm j).mul (hdm k)).aestronglyMeasurable]
    rfl
  have hcμ : ∀ j, ∫ o, recordDesign z o j * recordResponse o ∂(P.map (O 0)) =
      ∫ ω, z (T.A ω) (T.X ω) j * T.obsOutcome ω ∂T.μ := fun j => by
    rw [hlaw, Trial.ipdLaw, integral_map (f := fun o => recordDesign z o j * recordResponse o)
      hD.aemeasurable ((hdm j).mul hrm).aestronglyMeasurable]
    rfl
  have hG' : (Matrix.of fun j k => ∫ o, recordDesign z o j * recordDesign z o k
      ∂(P.map (O 0))).PosDef := by
    simp only [hGμ]; exact hG
  have h := tendstoInMeasure_leastSquaresFit hO hdm hrm hd2 hr2 hG'
  simp only [hGμ, hcμ] at h
  exact h

/-- **The standardized limit without an outcome model**: under the conditions of
`commonLimitFollowUp_tendstoInMeasure_fit`, for a law `ν` under which the design coordinates of
arm `a` are integrable, `∫ z(a, x)ᵀξ̂ dν → ∫ z(a, x)ᵀξ* dν` in probability. -/
theorem commonLimitFollowUp_tendstoInMeasure_standardized (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hz : ∀ a j, Measurable fun x => z a x j)
    (hz2 : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ)
    (hG : (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ).PosDef)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) {ν : Measure 𝒳} (a : Bool)
    (hzν : ∀ j, Integrable (fun x => z a x j) ν) :
    TendstoInMeasure P (fun n ω => ∫ x, z a x ⬝ᵥ
        leastSquaresFit (recordDesign z) recordResponse O n ω ∂ν) atTop
      (fun _ => ∫ x, z a x ⬝ᵥ commonLimitFollowUpCoef T z ∂ν) := by
  obtain ⟨hm, hH, hdom, hcont⟩ := linearSurface_dominated (hz a) hzν (commonLimitFollowUpCoef T z)
  exact tendstoInMeasure_integral_of_dominated (h := fun ξ x => z a x ⬝ᵥ ξ)
    (Eventually.of_forall hm) hH hdom hcont
    (commonLimitFollowUp_tendstoInMeasure_fit hT hY2 hz hz2 hG hO hlaw)

end Standardized

/-! ### The gap between the two limits -/

section Gap

variable {Ω₁ Ω₂ Ξ 𝒳 κ ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ] [DecidableEq κ] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool}
  [IsProbabilityMeasure T.μ] {P : Measure Ξ} [IsProbabilityMeasure P]
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {z : Bool → 𝒳 → κ → ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {m : Bool → 𝒳 → ℝ}

omit [DecidableEq κ] in
/-- A linear surface of design coordinates with finite second moments is integrable under the
trial covariate law. -/
theorem commonLimitFollowUp_integrable_surface_covLaw (hT : T.IsRandomizedTwoArm)
    (hz : ∀ a j, Measurable fun x => z a x j)
    (hz2 : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ) (a : Bool) (ξ : κ → ℝ) :
    Integrable (fun x => z a x ⬝ᵥ ξ) T.covLaw := by
  have hj : ∀ j, Integrable (fun x => z a x j) T.covLaw := fun j =>
    (integrable_map_measure (hz a j).aestronglyMeasurable hT.measurable_X.aemeasurable).2
      ((hz2 a j).integrable one_le_two)
  simp only [dotProduct]
  exact integrable_finsetSum _ fun j _ => (hj j).mul_const _

/-- **The two limits and their gap, with no outcome model.** Let `T` be a randomized trial with
potential outcomes of finite second moments, `μ` any version of its regression `E[Y | X, A]`,
`z` a design whose coordinates are measurable with finite second moments in each arm and whose
second moment `E[z zᵀ]` is positive definite, `O` an i.i.d. sample of the records, `φ` bounded
measurable features with the margin condition at `t` for the trial covariate law, and `ν` a law
under which the design coordinates of arm `a` are integrable. Then

* the weighted arm mean converges in probability to `∫ μ_a dT_X^tilt`;
* the standardized least squares mean `∫ z(a, ·)ᵀξ̂ dν` converges in probability to
  `∫ z(a, ·)ᵀξ* dν`;
* their difference converges in probability to
  `∫ (μ_a - z(a, ·)ᵀξ*) dT_X^tilt + (∫ z(a, ·)ᵀξ* dT_X^tilt - ∫ z(a, ·)ᵀξ* dν)`. -/
theorem commonLimitFollowUp_limits (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m)
    (hz : ∀ a j, Measurable fun x => z a x j)
    (hz2 : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ)
    (hG : (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ).PosDef)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {ν : Measure 𝒳} (a : Bool) (hzν : ∀ j, Integrable (fun x => z a x j) ν) :
    TendstoInMeasure P (sampleBalancedArmMean φ t O a) atTop
        (fun _ => ∫ x, m a x ∂commonLimitFollowUpTilted T φ t) ∧
      TendstoInMeasure P (fun n ω => ∫ x, z a x ⬝ᵥ
          leastSquaresFit (recordDesign z) recordResponse O n ω ∂ν) atTop
        (fun _ => ∫ x, z a x ⬝ᵥ commonLimitFollowUpCoef T z ∂ν) ∧
      TendstoInMeasure P (fun n ω => sampleBalancedArmMean φ t O a n ω - ∫ x, z a x ⬝ᵥ
          leastSquaresFit (recordDesign z) recordResponse O n ω ∂ν) atTop
        (fun _ => ∫ x, (m a x - z a x ⬝ᵥ commonLimitFollowUpCoef T z)
            ∂commonLimitFollowUpTilted T φ t +
          (∫ x, z a x ⬝ᵥ commonLimitFollowUpCoef T z ∂commonLimitFollowUpTilted T φ t -
            ∫ x, z a x ⬝ᵥ commonLimitFollowUpCoef T z ∂ν)) := by
  have hYi : ∀ a, Integrable (T.Y a) T.μ := fun a => (hY2 a).integrable one_le_two
  have hW := commonLimitFollowUp_tendstoInMeasure_weighted hT hYi hreg hO hlaw hφ hB hδ
    hmargin a
  have hS := commonLimitFollowUp_tendstoInMeasure_standardized hT hY2 hz hz2 hG hO hlaw a hzν
  refine ⟨hW, hS, ?_⟩
  have hD := hW.sub hS
  have hm : Integrable (m a) (commonLimitFollowUpTilted T φ t) :=
    commonLimitFollowUp_integrable_tiltedCovLaw hT hφ hB
      ((hT.isCondMean hYi hreg a).integrable hT.measurable_X)
  have hs : Integrable (fun x => z a x ⬝ᵥ commonLimitFollowUpCoef T z)
      (commonLimitFollowUpTilted T φ t) :=
    commonLimitFollowUp_integrable_tiltedCovLaw hT hφ hB
      (commonLimitFollowUp_integrable_surface_covLaw hT hz hz2 a _)
  have e : ∫ x, m a x ∂commonLimitFollowUpTilted T φ t -
      ∫ x, z a x ⬝ᵥ commonLimitFollowUpCoef T z ∂ν =
      ∫ x, (m a x - z a x ⬝ᵥ commonLimitFollowUpCoef T z) ∂commonLimitFollowUpTilted T φ t +
        (∫ x, z a x ⬝ᵥ commonLimitFollowUpCoef T z ∂commonLimitFollowUpTilted T φ t -
          ∫ x, z a x ⬝ᵥ commonLimitFollowUpCoef T z ∂ν) := by
    rw [integral_sub hm hs]; ring
  simp only [Pi.sub_def, e] at hD
  exact hD

omit [DecidableEq κ] [MeasurableSpace 𝒳] in
/-- A linear surface of a design whose coordinates are affine in the features is affine in the
features: `z(x)ᵀξ = cᵀξ + (∑ⱼ ξⱼ dⱼ)ᵀφ(x)` when `z(x)ⱼ = cⱼ + dⱼᵀφ(x)`. -/
theorem commonLimitFollowUp_surface_affine {zz : 𝒳 → κ → ℝ} {c : κ → ℝ}
    {d : κ → Fin p → ℝ} (hzz : ∀ j x, zz x j = c j + d j ⬝ᵥ φ x) (ξ : κ → ℝ) (x : 𝒳) :
    zz x ⬝ᵥ ξ = c ⬝ᵥ ξ + (∑ j, ξ j • d j) ⬝ᵥ φ x := by
  simp only [dotProduct, hzz, add_mul, Finset.sum_add_distrib, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- **The second term of the gap vanishes for a design spanned by the features.** If every design
coordinate of arm `a` is affine in the matched features, `z(a, x)ⱼ = cⱼ + dⱼᵀφ(x)`, and the target
covariate law has feature means `t`, then the tilted law and the target law give every fitted
surface `z(a, ·)ᵀξ` the same mean, and under the conditions of `commonLimitFollowUp_limits` the
difference of the two estimators converges in probability to the tilted mean of the regression
residual, `∫ (μ_a - z(a, ·)ᵀξ*) dT_X^tilt`. -/
theorem commonLimitFollowUp_gap_of_affine_design (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m)
    (hz : ∀ a j, Measurable fun x => z a x j)
    (hz2 : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ)
    (hG : (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ).PosDef)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {Q : Population Ω₂ 𝒳 ι} [IsProbabilityMeasure Q.μ] (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (a : Bool) {c : κ → ℝ} {d : κ → Fin p → ℝ} (hzaff : ∀ j x, z a x j = c j + d j ⬝ᵥ φ x) :
    (∀ ξ : κ → ℝ, ∫ x, z a x ⬝ᵥ ξ ∂commonLimitFollowUpTilted T φ t = ∫ x, z a x ⬝ᵥ ξ ∂Q.covLaw) ∧
      TendstoInMeasure P (fun n ω => sampleBalancedArmMean φ t O a n ω - ∫ x, z a x ⬝ᵥ
          leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw) atTop
        (fun _ => ∫ x, (m a x - z a x ⬝ᵥ commonLimitFollowUpCoef T z)
          ∂commonLimitFollowUpTilted T φ t) := by
  have hsame : ∀ ξ : κ → ℝ,
      ∫ x, z a x ⬝ᵥ ξ ∂commonLimitFollowUpTilted T φ t = ∫ x, z a x ⬝ᵥ ξ ∂Q.covLaw := fun ξ => by
    rw [commonLimitFollowUp_integral_affine_tiltedCovLaw hT hφ hB hδ hmargin
        (commonLimitFollowUp_surface_affine hzaff ξ),
      integral_affine_covLaw hφ hB ht (commonLimitFollowUp_surface_affine hzaff ξ)]
  have : IsProbabilityMeasure Q.covLaw := by unfold Population.covLaw; infer_instance
  have hzQ : ∀ j, Integrable (fun x => z a x j) Q.covLaw := fun j => by
    have hφk : ∀ k, Integrable (fun x => φ x k) Q.covLaw := fun k =>
      (integrable_const (B + ‖t‖)).mono' ((measurable_pi_apply k).comp hφ).aestronglyMeasurable
        (ae_of_all _ fun x => by
          calc ‖φ x k‖ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) k
            _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
            _ ≤ B + ‖t‖ := (norm_add_le _ _).trans (by linarith [hB x]))
    simp only [hzaff, dotProduct]
    exact (integrable_const _).add (integrable_finsetSum _ fun k _ => (hφk k).const_mul _)
  obtain ⟨-, -, hD⟩ := commonLimitFollowUp_limits hT hY2 hreg hz hz2 hG hO hlaw hφ hB hδ hmargin
    a hzQ
  simp only [hsame, sub_self, add_zero] at hD
  exact ⟨hsame, hD⟩

/-- **The projection coefficient of a correct design is the regression coefficient**: if
`E[Y | X, A] = z(A, X)ᵀξ₀` and the design second moment is positive definite, `ξ* = ξ₀`. -/
theorem commonLimitFollowUp_trialProjectionCoef_eq (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hz : ∀ a j, Measurable fun x => z a x j)
    (hz2 : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ)
    (hG : (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ).PosDef)
    {ξ₀ : κ → ℝ} (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome fun a x => z a x ⬝ᵥ ξ₀) :
    commonLimitFollowUpCoef T z = ξ₀ := by
  have hzA : ∀ j, MemLp (fun ω => z (T.A ω) (T.X ω) j) 2 T.μ := fun j =>
    memLp_two_select (f := fun a ω => z a (T.X ω) j) hT.measurable_A
      (fun a => (hz a j).comp hT.measurable_X) fun a => hz2 a j
  have hYo2 : MemLp T.obsOutcome 2 T.μ := memLp_two_select hT.measurable_A hT.measurable_Y hY2
  have hw : ∀ j, Measurable fun q : 𝒳 × Bool => z q.2 q.1 j := fun j =>
    measurable_from_prod_countable_left fun a => hz a j
  have hnorm := gram_mulVec_eq_cross_of_condExp (C := fun ω => (T.X ω, T.A ω))
    (hT.measurable_X.prodMk hT.measurable_A) (w := fun q => z q.2 q.1) hw
    (hYo2.integrable one_le_two) (fun j k => (hzA j).integrable_mul (hzA k))
    (fun j => (hzA j).integrable_mul hYo2) hreg.2
  rw [commonLimitFollowUpCoef, ← hnorm, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG.det_pos.ne'), one_mulVec]

/-- **Zero gap for a correct design and an affine regression.** If the design is a correct
model, `E[Y | X, A] = z(A, X)ᵀξ₀`, and the regression of arm `a` is affine in the matched
features, `z(a, x)ᵀξ₀ = α + βᵀφ(x)`, then under the conditions of `commonLimitFollowUp_limits`,
with a target covariate law of feature means `t`, the weighted and the standardized estimators
both converge in probability to `α + βᵀt` and their difference to `0`. With absolute constancy
of arm `a` and overlap, `α + βᵀt` is the target arm mean
(`Trial.LinearOutcomeModel.isCondMean_target`), which is `commonLimit_leastSquares_armMean`. -/
theorem commonLimitFollowUp_zero_gap (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hz : ∀ a j, Measurable fun x => z a x j)
    (hz2 : ∀ a j, MemLp (fun ω => z a (T.X ω) j) 2 T.μ)
    (hG : (Matrix.of fun j k => ∫ ω, z (T.A ω) (T.X ω) j * z (T.A ω) (T.X ω) k ∂T.μ).PosDef)
    {ξ₀ : κ → ℝ} (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome fun a x => z a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    {Q : Population Ω₂ 𝒳 ι} [IsProbabilityMeasure Q.μ] (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k)
    (a : Bool) (hzQ : ∀ j, Integrable (fun x => z a x j) Q.covLaw) {α : ℝ} {β : Fin p → ℝ}
    (haff : ∀ x, z a x ⬝ᵥ ξ₀ = α + β ⬝ᵥ φ x) :
    TendstoInMeasure P (sampleBalancedArmMean φ t O a) atTop (fun _ => α + β ⬝ᵥ t) ∧
      TendstoInMeasure P (fun n ω => ∫ x, z a x ⬝ᵥ
          leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw) atTop
        (fun _ => α + β ⬝ᵥ t) ∧
      TendstoInMeasure P (fun n ω => sampleBalancedArmMean φ t O a n ω - ∫ x, z a x ⬝ᵥ
          leastSquaresFit (recordDesign z) recordResponse O n ω ∂Q.covLaw) atTop
        (fun _ => 0) := by
  have hξ := commonLimitFollowUp_trialProjectionCoef_eq hT hY2 hz hz2 hG hreg
  obtain ⟨hW, hS, -⟩ := commonLimitFollowUp_limits hT hY2 hreg hz hz2 hG hO hlaw hφ hB hδ
    hmargin a hzQ
  rw [commonLimitFollowUp_integral_affine_tiltedCovLaw hT hφ hB hδ hmargin haff] at hW
  rw [hξ, integral_affine_covLaw hφ hB ht haff] at hS
  exact ⟨hW, hS, tendstoInMeasure_sub_zero_of_same_limit hW hS⟩

/-- **When the weighted limit is the target mean.** In a randomized trial with integrable
potential outcomes and regression `μ`, under the conditions of
`commonLimitFollowUp_tendstoInMeasure_weighted`, with absolute constancy of arm `a` of the trial
and treatment `s` of the target, overlap and an integrable `Y(s)`, the weighted arm mean is
consistent for the target mean `E_Q[Y(s)]` exactly when the tilted law and the target law give
the regression of the arm the same mean, `∫ μ_a dT_X^tilt = ∫ μ_a dQ_X`. -/
theorem commonLimitFollowUp_weighted_iff (hT : T.IsRandomizedTwoArm)
    (hYi : ∀ a, Integrable (T.Y a) T.μ) (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (a : Bool) {Q : Population Ω₂ 𝒳 ι} [IsProbabilityMeasure Q.μ] (hX₂ : Measurable Q.X) {s : ι}
    (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    IsConsistent (sampleBalancedArmMean φ t O a) (Q.armMean s) P ↔
      ∫ x, m a x ∂commonLimitFollowUpTilted T φ t = ∫ x, m a x ∂Q.covLaw := by
  have hW := commonLimitFollowUp_tendstoInMeasure_weighted hT hYi hreg hO hlaw hφ hB hδ
    hmargin a
  have hQ := (integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ
    (hT.isCondMean hYi hreg a) hsi hov).2
  rw [hQ]
  constructor
  · exact fun h => tendstoInMeasure_const_unique hW h
  · intro h
    rw [← h]
    exact hW

end Gap

/-! ### The interaction design -/

section Interaction

variable {Ω₁ Ξ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳] {p : ℕ}
  {T : Trial Ω₁ 𝒳 Bool} [IsProbabilityMeasure T.μ] {P : Measure Ξ} [IsProbabilityMeasure P]
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {m : Bool → 𝒳 → ℝ}

/-- **The two limits and their gap for the interaction design, from primitive conditions.** For
the design `z(a, x) = (1, φ(x), 1[a], 1[a]φ(x))`, the design conditions of
`commonLimitFollowUp_limits` follow from bounded measurable features and the margin condition, so
only the randomization, finite second moments of the potential outcomes, the i.i.d. sample and a
probability law `ν` remain; no outcome model is assumed. -/
theorem commonLimitFollowUp_interaction_limits (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome m)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ T.covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (ν : Measure 𝒳) [IsProbabilityMeasure ν] (a : Bool) :
    TendstoInMeasure P (sampleBalancedArmMean φ t O a) atTop
        (fun _ => ∫ x, m a x ∂commonLimitFollowUpTilted T φ t) ∧
      TendstoInMeasure P (fun n ω => ∫ x, featureInteractionDesign φ a x ⬝ᵥ
          leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω ∂ν)
        atTop (fun _ => ∫ x, featureInteractionDesign φ a x ⬝ᵥ
          commonLimitFollowUpCoef T (featureInteractionDesign φ) ∂ν) ∧
      TendstoInMeasure P (fun n ω => sampleBalancedArmMean φ t O a n ω -
          ∫ x, featureInteractionDesign φ a x ⬝ᵥ
            leastSquaresFit (recordDesign (featureInteractionDesign φ)) recordResponse O n ω ∂ν)
        atTop (fun _ => ∫ x, (m a x - featureInteractionDesign φ a x ⬝ᵥ
            commonLimitFollowUpCoef T (featureInteractionDesign φ))
            ∂commonLimitFollowUpTilted T φ t +
          (∫ x, featureInteractionDesign φ a x ⬝ᵥ
              commonLimitFollowUpCoef T (featureInteractionDesign φ)
              ∂commonLimitFollowUpTilted T φ t -
            ∫ x, featureInteractionDesign φ a x ⬝ᵥ
              commonLimitFollowUpCoef T (featureInteractionDesign φ) ∂ν)) :=
  commonLimitFollowUp_limits hT hY2 hreg (measurable_featureInteractionDesign hφ)
    (fun e k => MemLp.of_bound
      ((measurable_featureInteractionDesign hφ e k).comp hT.measurable_X).aestronglyMeasurable
      (1 + B + ‖t‖) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact abs_featureInteractionDesign_le hB _ _ k))
    (posDef_featureInteractionDesign_gram hT hφ hB hδ hmargin) hO hlaw hφ hB hδ hmargin a
    (integrable_featureInteractionDesign hφ hB a)

end Interaction

end PopulationAdjustment

end CausalInference
