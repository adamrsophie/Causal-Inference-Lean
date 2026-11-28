/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.Weighting
public import CausalInference.PointTreatment.OutcomeRegression

/-!
# Point treatment: augmented inverse probability weighting and double robustness

For a working score `ê` (with arm probability `π̂_a = armProb ê a`) and a working regression
`m̂ : Bool → 𝒲 → ℝ`, the augmented weighted outcome of the arm `a` is

`1{A = a} Y / π̂_a(W) - (1{A = a} - π̂_a(W)) / π̂_a(W) · m̂(a, W)`,

which equals `m̂(a, W) + 1{A = a} (Y - m̂(a, W)) / π̂_a(W)` wherever `π̂_a(W) ≠ 0`. Its mean is
`E[Y(a)]` when the score is correct (the augmentation `(1{A = a} - π_a(W)) / π_a(W) · m̂(a, W)`
has mean zero) and also when the regression is correct (the weighted residual
`1{A = a} (Y - m(a, W)) / π̂_a(W)` has mean zero): the augmented estimator is doubly robust.

## Main definitions

* `aipwTerm A Y W e m a`: the augmented weighted outcome of the arm `a`.
* `aipwArmMean`, `aipwAte`: its mean and the contrast of the two arms.

## Main results

* `aipwTerm_eq`: the pointwise decomposition.
* `integral_augmentation_eq_zero`: the augmentation has mean zero at the true score.
* `IndicatorIgnorable.integral_weightedResidual_eq_zero`: the weighted residual has mean zero
  at a correct regression, for any positive working score.
* `IndicatorIgnorable.aipwArmMean_eq_of_propensity`,
  `IndicatorIgnorable.aipwArmMean_eq_of_regression`: consistency under a correct score and
  under a correct regression.
* `Ignorable.aipwArmMean_eq`, `Ignorable.aipwAte_eq`: **double robustness**, for each arm and
  for the average effect, under ignorability `A ⫫ (Y(0), Y(1)) | W`.

## References

* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, Journal of the American Statistical Association 89
  (1994).
* H. Bang and J. M. Robins, *Doubly robust estimation in missing data and causal inference
  models*, Biometrics 61 (2005).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲] {μ : Measure Ω}
  {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}

section Definitions

omit [MeasurableSpace 𝒲]

/-- The augmented inverse probability weighted outcome of the arm `a` for a working score `e`
and a working regression `m`:
`1{A = a} Y / π_a(W) - (1{A = a} - π_a(W)) / π_a(W) · m(a, W)`. -/
noncomputable def aipwTerm (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲) (e : 𝒲 → ℝ)
    (m : Bool → 𝒲 → ℝ) (a : Bool) : Ω → ℝ :=
  fun ω => respInd (arm A a) ω * obsOutcome A Y ω / armProb e a (W ω) -
    (respInd (arm A a) ω - armProb e a (W ω)) / armProb e a (W ω) * m a (W ω)

/-- The augmented inverse probability weighted arm mean. -/
noncomputable def aipwArmMean (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool) : ℝ :=
  ∫ ω, aipwTerm A Y W e m a ω ∂μ

/-- The augmented inverse probability weighted average effect. -/
noncomputable def aipwAte (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) : ℝ :=
  aipwArmMean μ A Y W e m true - aipwArmMean μ A Y W e m false

/-- **The pointwise decomposition** of the augmented weighted outcome into the regression and
the weighted residual: where `π_a(W) ≠ 0`,
`aipwTerm = m(a, W) + 1{A = a} (Y - m(a, W)) / π_a(W)`. -/
theorem aipwTerm_eq (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲) (e : 𝒲 → ℝ)
    (m : Bool → 𝒲 → ℝ) (a : Bool) {ω : Ω} (h : armProb e a (W ω) ≠ 0) :
    aipwTerm A Y W e m a ω =
      m a (W ω) + respInd (arm A a) ω * (obsOutcome A Y ω - m a (W ω)) / armProb e a (W ω) := by
  simp only [aipwTerm]
  field_simp
  ring

end Definitions

/-- **The augmentation has mean zero at the true score.** If `e(W)` is a version of the
propensity score, the arm is positive and `h(W)` is integrable, then
`(1{A = a} - π_a(W)) / π_a(W) · h(W)` is integrable with mean zero. No ignorability is
needed. -/
theorem integral_augmentation_eq_zero [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) {h : 𝒲 → ℝ} (hh : Measurable h)
    (hhi : Integrable (fun ω => h (W ω)) μ) :
    Integrable (fun ω => (respInd (arm A a) ω - armProb e a (W ω)) / armProb e a (W ω) *
      h (W ω)) μ ∧
    ∫ ω, (respInd (arm A a) ω - armProb e a (W ω)) / armProb e a (W ω) * h (W ω) ∂μ = 0 := by
  obtain ⟨hint, hcov⟩ := ipw_identity_covariate hW (measurable_arm hA a)
    (measurable_armProb hps.1 a) (hps.condExp_arm hW hA a) hpos hh hhi
  have hrw : (fun ω => (respInd (arm A a) ω - armProb e a (W ω)) / armProb e a (W ω) *
      h (W ω)) =ᵐ[μ] fun ω => respInd (arm A a) ω * h (W ω) / armProb e a (W ω) - h (W ω) := by
    filter_upwards [hpos] with ω hω
    field_simp
  refine ⟨(hint.sub hhi).congr hrw.symm, ?_⟩
  rw [integral_congr_ae hrw, integral_sub hint hhi, hcov, sub_self]

/-- **The weighted residual has mean zero at a correct regression.** Under the indicator form of
ignorability, if `m(A, W)` is a version of `E[Y | W, A]`, the true arm probability is positive,
`ê` is any measurable working score and the weighted residual
`1{A = a} (Y - m(a, W)) / π̂_a(W)` is integrable, then it has mean zero. -/
theorem IndicatorIgnorable.integral_weightedResidual_eq_zero [IsFiniteMeasure μ]
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) {e' : 𝒲 → ℝ} (he' : Measurable e')
    (hint : Integrable (fun ω => respInd (arm A a) ω * (obsOutcome A Y ω - m a (W ω)) /
      armProb e' a (W ω)) μ) :
    ∫ ω, respInd (arm A a) ω * (obsOutcome A Y ω - m a (W ω)) / armProb e' a (W ω) ∂μ = 0 := by
  have hp' := measurable_armProb he' a
  have hp := measurable_armProb hps.1 a
  have hg : Measurable fun q : 𝒲 × ℝ => (q.2 - m a q.1) / armProb e' a q.1 :=
    (measurable_snd.sub ((hreg.1 a).comp measurable_fst)).div (hp'.comp measurable_fst)
  have hres : (fun ω => respInd (arm A a) ω * (obsOutcome A Y ω - m a (W ω)) /
      armProb e' a (W ω)) = fun ω => respInd (arm A a) ω *
        (fun q : 𝒲 × ℝ => (q.2 - m a q.1) / armProb e' a q.1) (W ω, Y a ω) := by
    funext ω
    simp only
    rw [mul_sub, respInd_arm_mul_obsOutcome, ← mul_sub, mul_div_assoc]
  obtain ⟨hiff, e1⟩ := hign.integral_respInd_arm_mul hW hA hY hps a hg
  rw [hres] at hint ⊢
  rw [e1]
  have hint1 := hiff.1 hint
  -- condition on `W`: the residual `Y(a) - m(a, W)` has conditional mean zero
  have hmi := hign.meanIgnorable hW hA hY a (hYi a)
  have hmW := integrable_regression hW hA hYi hreg hps a hmi hpos
  have hgW : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
      (fun ω => armProb e a (W ω) / armProb e' a (W ω)) :=
    ((hp.div hp').comp (comap_measurable W)).stronglyMeasurable
  have hzero : μ[fun ω => Y a ω - m a (W ω) | MeasurableSpace.comap W inferInstance] =ᵐ[μ]
      fun _ => (0 : ℝ) := by
    have hmeas : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
        (fun ω => m a (W ω)) := ((hreg.1 a).comp (comap_measurable W)).stronglyMeasurable
    filter_upwards [condExp_sub (m := MeasurableSpace.comap W inferInstance) (hYi a) hmW,
      hreg.ae_eq_condExp hW hA hYi hps a hmi hpos] with ω h1 h2
    rw [show (fun ω => Y a ω - m a (W ω)) = Y a - fun ω => m a (W ω) from rfl, h1,
      Pi.sub_apply, condExp_of_stronglyMeasurable hW.comap_le hmeas hmW, ← h2, sub_self]
  have hint2 : Integrable (fun ω => (Y a ω - m a (W ω)) *
      (armProb e a (W ω) / armProb e' a (W ω))) μ :=
    hint1.congr (Filter.Eventually.of_forall fun ω => by simp only; ring)
  have e2 := (integral_mul_eq_of_condExp_eq hW.comap_le ((hYi a).sub hmW) hgW hint2 hzero).2
  calc ∫ ω, armProb e a (W ω) * ((Y a ω - m a (W ω)) / armProb e' a (W ω)) ∂μ
      = ∫ ω, (Y a ω - m a (W ω)) * (armProb e a (W ω) / armProb e' a (W ω)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    _ = 0 := e2.trans (by simp)

/-- **Consistency under a correct score.** Under the indicator form of ignorability, if `e(W)`
is a version of the propensity score with a positive arm and the working regression `m̂(a, W)` is
integrable, then the augmented arm mean is `E[Y(a)]`, whatever `m̂`. -/
theorem IndicatorIgnorable.aipwArmMean_eq_of_propensity [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hign : IndicatorIgnorable μ A W Y)
    (hps : IsPropensityScore μ A W e) (a : Bool) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hYi : Integrable (Y a) μ) {m' : Bool → 𝒲 → ℝ} (hm' : Measurable (m' a))
    (hm'i : Integrable (fun ω => m' a (W ω)) μ) :
    aipwArmMean μ A Y W e m' a = armMean μ Y a := by
  obtain ⟨haug, haug0⟩ := integral_augmentation_eq_zero hW hA hps a hpos hm' hm'i
  simp only [aipwArmMean, aipwTerm]
  rw [integral_sub (hign.integrable_ipw hW hA hY hps a hpos hYi) haug,
    haug0, sub_zero, ← hign.armMean_eq_ipw hW hA hY hps a hpos hYi]

/-- **Consistency under a correct regression.** Under the indicator form of ignorability, if
`m(A, W)` is a version of `E[Y | W, A]` and the true arm probability is positive, then for any
measurable working score `ê` with `π̂_a(W) > 0` almost surely and an integrable weighted
residual, the augmented arm mean is `E[Y(a)]`. -/
theorem IndicatorIgnorable.aipwArmMean_eq_of_regression [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    {e' : 𝒲 → ℝ} (he' : Measurable e') (hpos' : ∀ᵐ ω ∂μ, 0 < armProb e' a (W ω))
    (hint : Integrable (fun ω => respInd (arm A a) ω * (obsOutcome A Y ω - m a (W ω)) /
      armProb e' a (W ω)) μ) :
    aipwArmMean μ A Y W e' m a = armMean μ Y a := by
  have hmi := hign.meanIgnorable hW hA hY a (hYi a)
  have hmW := integrable_regression hW hA hYi hreg hps a hmi hpos
  have hdec : aipwTerm A Y W e' m a =ᵐ[μ] fun ω => m a (W ω) +
      respInd (arm A a) ω * (obsOutcome A Y ω - m a (W ω)) / armProb e' a (W ω) := by
    filter_upwards [hpos'] with ω hω
    exact aipwTerm_eq A Y W e' m a hω.ne'
  rw [aipwArmMean, integral_congr_ae hdec, integral_add hmW hint,
    hign.integral_weightedResidual_eq_zero hW hA hY hYi hps a hpos hreg he' hint, add_zero,
    PointTreatment.armMean_eq_integral_regression hW hA hYi hreg hps a hmi hpos]

/-- **Double robustness for an arm** under ignorability `A ⫫ (Y(0), Y(1)) | W`. Let `e` be the
true propensity score, with a positive arm, and let `(ê, m̂)` be a working score and a working
regression such that either `ê` is a correct score or `m̂` is a correct regression. If
`π̂_a(W) > 0` almost surely, `m̂(a, W)` is integrable and the weighted residual
`1{A = a} (Y - m̂(a, W)) / π̂_a(W)` is integrable, then the augmented arm mean is `E[Y(a)]`. -/
theorem Ignorable.aipwArmMean_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ}
    (he' : Measurable e') (hm' : Measurable (m' a))
    (hcorrect : IsPropensityScore μ A W e' ∨ IsOutcomeRegression μ A W (obsOutcome A Y) m')
    (hpos' : ∀ᵐ ω ∂μ, 0 < armProb e' a (W ω)) (hm'i : Integrable (fun ω => m' a (W ω)) μ)
    (hint : Integrable (fun ω => respInd (arm A a) ω * (obsOutcome A Y ω - m' a (W ω)) /
      armProb e' a (W ω)) μ) :
    aipwArmMean μ A Y W e' m' a = armMean μ Y a := by
  have hii := (ignorable_iff_indicatorIgnorable hW hA hY).1 hign
  rcases hcorrect with hps' | hreg
  · exact hii.aipwArmMean_eq_of_propensity hW hA hY hps' a hpos' (hYi a) hm' hm'i
  · exact hii.aipwArmMean_eq_of_regression hW hA hY hYi hps a hpos hreg he' hpos' hint

/-- **Double robustness for the average effect** under ignorability `A ⫫ (Y(0), Y(1)) | W` and
positivity of the true score: if either the working score or the working regression is
correct, the working score satisfies positivity, and the working regression and the weighted
residuals of both arms are integrable, then the augmented average effect is `E[Y(1) - Y(0)]`. -/
theorem Ignorable.aipwAte_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e)
    (hov : OverlapAE e (μ.map W)) {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ} (he' : Measurable e')
    (hm' : ∀ a, Measurable (m' a))
    (hcorrect : IsPropensityScore μ A W e' ∨ IsOutcomeRegression μ A W (obsOutcome A Y) m')
    (hov' : OverlapAE e' (μ.map W)) (hm'i : ∀ a, Integrable (fun ω => m' a (W ω)) μ)
    (hint : ∀ a, Integrable (fun ω => respInd (arm A a) ω * (obsOutcome A Y ω - m' a (W ω)) /
      armProb e' a (W ω)) μ) :
    aipwAte μ A Y W e' m' = ate μ Y := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  have hpos' := armProb_pos_of_ae (hov'.ae_comp hW.aemeasurable)
  rw [aipwAte, ate_eq_armMean_sub (hYi true) (hYi false),
    hign.aipwArmMean_eq hW hA hY hYi hps true (hpos true) he' (hm' true) hcorrect (hpos' true)
      (hm'i true) (hint true),
    hign.aipwArmMean_eq hW hA hY hYi hps false (hpos false) he' (hm' false) hcorrect
      (hpos' false) (hm'i false) (hint false)]

end PointTreatment

end CausalInference
