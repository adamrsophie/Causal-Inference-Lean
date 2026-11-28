/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredSurvivalLikelihood
public import CausalInference.Survival.PopulationHazard
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import CausalInference.NetworkMetaRegression.AggregationIdentity

/-!
# The accelerated failure time branch of an unanchored survival comparison

**Time scale: continuous.** In the accelerated failure time model the event time of a patient
with linear predictor `η` is `T = exp(η + σ ε)`, for a scale `σ > 0` and an error `ε` with law
`μ_ε`, error survival `S_ε(z) = P(ε > z)` and error density `f_ε` (`S_ε' = -f_ε`). The survival
and density of `T` are
`S(t | η) = S_ε((log t - η) / σ)` and `f(t | η) = f_ε((log t - η) / σ) / (σ t)` at `t > 0`
(`acceleratedSurvival`, `acceleratedDensity`). Every statement is in density form: the censored
contribution is `f(t | η)^δ S(t | η)^(1 - δ)` and the marginal hazard is `∫ f / ∫ S`; the
conditional hazard `f / S` appears only where `S > 0` is a hypothesis.

## Main results

* `acceleratedSurvival_eq_prob`, `hasDerivAt_acceleratedSurvival`,
  `isSurvivalFamily_acceleratedSurvival` (so that `restrictedMean_popSurvival_sub` applies).
* `acceleratedSurvival_eq_expSurvival`: where the error survival is positive, the survival is
  `exp(-∫₀ᵗ h)` with the hazard `h = f / S`; `popSurvival_acceleratedSurvival_eq_hazardCurves`.
* `integral_acceleratedContribution_le`, `integral_acceleratedContribution_le_of_envelope`: the
  integrated censored likelihood of the reconstructed arm is finite.
* `hasDerivAt_popSurvival_accelerated`, `popHazard_accelerated`: the target survival has
  derivative `-∫ f(t | x) F(dx)` and hazard `∫ f / ∫ S`.
* `popHazard_accelerated_instance`: a standard minimum extreme value error, a two valued
  covariate, and the marginal hazard `(e^{-t} + 2 e^{-2t}) / (e^{-t} + e^{-2t})`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Set
open Survival.ContinuousTime

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **accelerated failure time survival** `S_ε((log t - η) / σ)` at `t > 0`, and `1` at
`t ≤ 0`. -/
noncomputable def acceleratedSurvival (με : Measure ℝ) (σ η t : ℝ) : ℝ :=
  if 0 < t then με.real (Ioi ((Real.log t - η) / σ)) else 1

/-- The **accelerated failure time density** `f_ε((log t - η) / σ) / (σ t)` at `t > 0`, and `0`
at `t ≤ 0`. -/
noncomputable def acceleratedDensity (fε : ℝ → ℝ) (σ η t : ℝ) : ℝ :=
  if 0 < t then fε ((Real.log t - η) / σ) / (σ * t) else 0

theorem antitone_measureReal_Ioi (με : Measure ℝ) [IsFiniteMeasure με] :
    Antitone fun z : ℝ => με.real (Ioi z) :=
  fun _ _ hab => measureReal_mono (Ioi_subset_Ioi hab)

theorem acceleratedSurvival_mem_Icc (με : Measure ℝ) [IsProbabilityMeasure με] (σ η t : ℝ) :
    acceleratedSurvival με σ η t ∈ Icc 0 1 := by
  unfold acceleratedSurvival
  split_ifs
  · exact ⟨measureReal_nonneg, (measureReal_mono (subset_univ _)).trans (by simp)⟩
  · exact ⟨zero_le_one, le_rfl⟩

theorem acceleratedDensity_nonneg {fε : ℝ → ℝ} (hf0 : ∀ z, 0 ≤ fε z) {σ : ℝ} (hσ : 0 < σ)
    (η t : ℝ) : 0 ≤ acceleratedDensity fε σ η t := by
  unfold acceleratedDensity
  split_ifs with ht
  · exact div_nonneg (hf0 _) (by positivity)
  · exact le_rfl

/-- **The accelerated failure time model**: for an error `ε` with law `P.map ε` and `σ > 0`, the
event time `exp(η + σ ε)` has `P(T > t) = acceleratedSurvival (P.map ε) σ η t` at `t > 0`. -/
theorem acceleratedSurvival_eq_prob {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ε : Ω → ℝ} (hε : Measurable ε) {σ : ℝ} (hσ : 0 < σ) (η : ℝ) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t < Real.exp (η + σ * ε ω)} = acceleratedSurvival (P.map ε) σ η t := by
  rw [acceleratedSurvival, ite_eq_left ht, measureReal_def, measureReal_def,
    Measure.map_apply hε measurableSet_Ioi]
  congr 2
  ext ω
  simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
  rw [div_lt_iff₀ hσ, ← Real.log_lt_iff_lt_exp ht]
  constructor <;> intro h <;> linarith

/-- **The survival has derivative minus the density** at every `t > 0`, when the error
survival has derivative `-f_ε` everywhere. -/
theorem hasDerivAt_acceleratedSurvival {με : Measure ℝ} {fε : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt (fun z => με.real (Ioi z)) (-fε z) z) (σ η : ℝ) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (acceleratedSurvival με σ η) (-acceleratedDensity fε σ η t) t := by
  have hz : HasDerivAt (fun s => (Real.log s - η) / σ) (t⁻¹ / σ) t :=
    ((Real.hasDerivAt_log ht.ne').sub_const η).div_const σ
  have hc := (hf ((Real.log t - η) / σ)).comp t hz
  have heq : acceleratedSurvival με σ η =ᶠ[𝓝 t]
      (fun z => με.real (Ioi z)) ∘ fun s => (Real.log s - η) / σ :=
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => by
      simp only [acceleratedSurvival, ite_eq_left (show 0 < s from hs), Function.comp_apply]
  rw [acceleratedDensity, ite_eq_left ht]
  convert hc.congr_of_eventuallyEq heq using 1
  field_simp

/-- The error density is measurable: it is minus a derivative. -/
theorem measurable_errorDensity {με : Measure ℝ} {fε : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt (fun z => με.real (Ioi z)) (-fε z) z) : Measurable fε := by
  have h : fε = fun z => -deriv (fun z => με.real (Ioi z)) z :=
    funext fun z => by rw [(hf z).deriv, neg_neg]
  rw [h]
  exact (measurable_deriv _).neg

theorem measurable_acceleratedSurvival_uncurry (με : Measure ℝ) [IsFiniteMeasure με] (σ : ℝ)
    {η : 𝒳 → ℝ} (hη : Measurable η) :
    Measurable (Function.uncurry fun x s => acceleratedSurvival με σ (η x) s) := by
  change Measurable fun p : 𝒳 × ℝ => acceleratedSurvival με σ (η p.1) p.2
  unfold acceleratedSurvival
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  exact (antitone_measureReal_Ioi με).measurable.comp
    (((Real.measurable_log.comp measurable_snd).sub (hη.comp measurable_fst)).div_const σ)

/-- The accelerated failure time curves form a survival family, so the restricted mean
collapsibility `restrictedMean_popSurvival_sub` applies to them. -/
theorem isSurvivalFamily_acceleratedSurvival (με : Measure ℝ) [IsProbabilityMeasure με] (σ : ℝ)
    {η : 𝒳 → ℝ} (hη : Measurable η) :
    IsSurvivalFamily fun x s => acceleratedSurvival με σ (η x) s :=
  ⟨measurable_acceleratedSurvival_uncurry με σ hη,
    fun x s _ => (acceleratedSurvival_mem_Icc με σ (η x) s).1,
    fun x s _ => (acceleratedSurvival_mem_Icc με σ (η x) s).2⟩

/-! ### The survival as an exponential of a cumulative hazard -/

theorem tendsto_measureReal_Ioi_atBot (με : Measure ℝ) [IsProbabilityMeasure με] :
    Tendsto (fun z => με.real (Ioi z)) atBot (𝓝 1) := by
  have h : (fun z => με.real (Ioi z)) = fun z => 1 - cdf με z := funext fun z => by
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]
  rw [h]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atBot με)

theorem continuousWithinAt_acceleratedSurvival_zero (με : Measure ℝ) [IsProbabilityMeasure με]
    {σ : ℝ} (hσ : 0 < σ) (η : ℝ) : ContinuousWithinAt (acceleratedSurvival με σ η) (Ici 0) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  have h0 : acceleratedSurvival με σ η 0 = 1 := by simp [acceleratedSurvival]
  rw [h0]
  have hz : Tendsto (fun s => (Real.log s + -η) / σ) (𝓝[>] 0) atBot :=
    (tendsto_atBot_add_const_right _ (-η) Real.tendsto_log_nhdsGT_zero).atBot_div_const hσ
  refine ((tendsto_measureReal_Ioi_atBot με).comp hz).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, acceleratedSurvival, ite_eq_left (show (0 : ℝ) < s from hs),
    sub_eq_add_neg]

/-- **The survival is `exp(-∫₀ᵗ h)`** with the hazard `h = f / S`, for an error law with a
nonnegative density `f_ε` (`S_ε' = -f_ε`) and a positive error survival, `σ > 0` and `t ≥ 0`. -/
theorem acceleratedSurvival_eq_expSurvival {με : Measure ℝ} [IsProbabilityMeasure με]
    {fε : ℝ → ℝ} (hf : ∀ z, HasDerivAt (fun z => με.real (Ioi z)) (-fε z) z)
    (hf0 : ∀ z, 0 ≤ fε z) (hSpos : ∀ z, 0 < με.real (Ioi z)) {σ : ℝ} (hσ : 0 < σ) (η : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    acceleratedSurvival με σ η t = expSurvival (cumHazard fun s =>
      acceleratedDensity fε σ η s / acceleratedSurvival με σ η s) t := by
  have hSp : ∀ s, 0 < acceleratedSurvival με σ η s := fun s => by
    unfold acceleratedSurvival
    split_ifs
    exacts [hSpos _, one_pos]
  have hcont : ContinuousOn (acceleratedSurvival με σ η) (Icc 0 t) := by
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · subst h
      exact (continuousWithinAt_acceleratedSurvival_zero με hσ η).mono Icc_subset_Ici_self
    · exact (hasDerivAt_acceleratedSurvival hf σ η h).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun s => -Real.log (acceleratedSurvival με σ η s)) (Icc 0 t) :=
    (hcont.log fun s _ => (hSp s).ne').neg
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt (fun s => -Real.log (acceleratedSurvival με σ η s))
      (acceleratedDensity fε σ η s / acceleratedSurvival με σ η s) s := by
    intro s hs
    have h := ((hasDerivAt_acceleratedSurvival hf σ η hs.1).log (hSp s).ne').neg
    rw [neg_div, neg_neg] at h
    exact h
  have hnn : ∀ s ∈ Ioo 0 t, 0 ≤ acceleratedDensity fε σ η s / acceleratedSurvival με σ η s :=
    fun s _ => div_nonneg (acceleratedDensity_nonneg hf0 hσ η s) (hSp s).le
  have hint : IntervalIntegrable (fun s => acceleratedDensity fε σ η s /
      acceleratedSurvival με σ η s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hg hd hnn)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hg hd hint
  have h0 : acceleratedSurvival με σ η 0 = 1 := by simp [acceleratedSurvival]
  rw [expSurvival, cumHazard, hFTC]
  simp only [h0, Real.log_one, neg_zero, sub_zero, neg_neg]
  exact (Real.exp_log (hSp t)).symm

/-- **The target survival of the accelerated branch is a population survival of hazard
curves**: under the hypotheses of `acceleratedSurvival_eq_expSurvival`, at every `t ≥ 0`, the
target survival is `popSurvival F (hazardCurves h) t` with the conditional hazards `h = f / S`,
the object of the proportional hazards results. -/
theorem popSurvival_acceleratedSurvival_eq_hazardCurves (F : Measure 𝒳) {με : Measure ℝ}
    [IsProbabilityMeasure με] {fε : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt (fun z => με.real (Ioi z)) (-fε z) z) (hf0 : ∀ z, 0 ≤ fε z)
    (hSpos : ∀ z, 0 < με.real (Ioi z)) {σ : ℝ} (hσ : 0 < σ) (η : 𝒳 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    popSurvival F (fun x => acceleratedSurvival με σ (η x)) t =
      popSurvival F (hazardCurves fun x s =>
        acceleratedDensity fε σ (η x) s / acceleratedSurvival με σ (η x) s) t := by
  simp only [popSurvival, hazardCurves]
  exact integral_congr_ae (ae_of_all _ fun x =>
    acceleratedSurvival_eq_expSurvival hf hf0 hSpos hσ (η x) ht)

/-! ### The censored likelihood -/

/-- The **censored contribution** `f(t | η)^δ S(t | η)^(1 - δ)` of an observation `(t, δ)`. -/
noncomputable def acceleratedContribution (με : Measure ℝ) (fε : ℝ → ℝ) (σ η : ℝ)
    (z : ℝ × Bool) : ℝ :=
  censoredContribution (acceleratedDensity fε σ η) (acceleratedSurvival με σ η) z.1 z.2

theorem measurable_acceleratedContribution {με : Measure ℝ} [IsFiniteMeasure με] {fε : ℝ → ℝ}
    (hfm : Measurable fε) (σ : ℝ) {η : 𝒳 → ℝ} (hη : Measurable η) (z : ℝ × Bool) :
    Measurable fun x => acceleratedContribution με fε σ (η x) z := by
  unfold acceleratedContribution censoredContribution
  split_ifs
  · unfold acceleratedDensity
    split_ifs
    · exact (hfm.comp ((measurable_const.sub hη).div_const σ)).div_const _
    · exact measurable_const
  · exact (measurable_acceleratedSurvival_uncurry με σ hη).comp
      (measurable_id.prodMk measurable_const)

/-- **The integrated censored likelihood under an envelope of the density.** For an error law
with a nonnegative measurable density, `σ > 0`, a measurable predictor `η`, a covariate
probability law `F` and an `F` integrable envelope `g` of the density at the observed time `t`
(`f(t | η(x)) ≤ g(x)`), the contribution `x ↦ f(t | x)^δ S(t | x)^(1 - δ)` is integrable and its
integral lies in `[0, ∫ g dF]` at an event and in `[0, 1]` at a censoring. -/
theorem integral_acceleratedContribution_le_of_envelope (F : Measure 𝒳) [IsProbabilityMeasure F]
    {με : Measure ℝ} [IsProbabilityMeasure με] {fε : ℝ → ℝ} (hfm : Measurable fε)
    (hf0 : ∀ z, 0 ≤ fε z) {σ : ℝ} (hσ : 0 < σ) {η : 𝒳 → ℝ} (hη : Measurable η) {g : 𝒳 → ℝ}
    (hg : Integrable g F) (z : ℝ × Bool) (henv : ∀ x, acceleratedDensity fε σ (η x) z.1 ≤ g x) :
    Integrable (fun x => acceleratedContribution με fε σ (η x) z) F ∧
      0 ≤ ∫ x, acceleratedContribution με fε σ (η x) z ∂F ∧
      ∫ x, acceleratedContribution με fε σ (η x) z ∂F ≤ if z.2 then ∫ x, g x ∂F else 1 := by
  have hm := measurable_acceleratedContribution (με := με) hfm σ hη z
  have h0 : ∀ x, 0 ≤ acceleratedContribution με fε σ (η x) z := fun x => by
    unfold acceleratedContribution censoredContribution
    split_ifs
    · exact acceleratedDensity_nonneg hf0 hσ _ _
    · exact (acceleratedSurvival_mem_Icc με σ (η x) z.1).1
  rcases z with ⟨t, δ⟩
  cases δ
  · have hb : ∀ x, acceleratedContribution με fε σ (η x) (t, false) ≤ 1 := fun x =>
      (acceleratedSurvival_mem_Icc με σ (η x) t).2
    have hint : Integrable (fun x => acceleratedContribution με fε σ (η x) (t, false)) F :=
      Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
        exact hb x)
    refine ⟨hint, integral_nonneg h0, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    calc ∫ x, acceleratedContribution με fε σ (η x) (t, false) ∂F ≤ ∫ _x, (1 : ℝ) ∂F :=
          integral_mono hint (integrable_const _) hb
      _ = 1 := by simp
  · have hb : ∀ x, acceleratedContribution με fε σ (η x) (t, true) ≤ g x := fun x => henv x
    have hint : Integrable (fun x => acceleratedContribution με fε σ (η x) (t, true)) F :=
      hg.mono' hm.aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
        exact hb x)
    exact ⟨hint, integral_nonneg h0, integral_mono hint hg hb⟩

/-- **The integrated censored likelihood under a bounded error density**: if `f_ε ≤ M`, the
integral of the contribution at `(t, δ)`, `t > 0`, lies in `[0, M / (σ t)]` at an event and in
`[0, 1]` at a censoring, whatever the covariate law. -/
theorem integral_acceleratedContribution_le (F : Measure 𝒳) [IsProbabilityMeasure F]
    {με : Measure ℝ} [IsProbabilityMeasure με] {fε : ℝ → ℝ} (hfm : Measurable fε)
    (hf0 : ∀ z, 0 ≤ fε z) {M : ℝ} (hM : ∀ z, fε z ≤ M) {σ : ℝ} (hσ : 0 < σ) {η : 𝒳 → ℝ}
    (hη : Measurable η) {z : ℝ × Bool} (ht : 0 < z.1) :
    Integrable (fun x => acceleratedContribution με fε σ (η x) z) F ∧
      0 ≤ ∫ x, acceleratedContribution με fε σ (η x) z ∂F ∧
      ∫ x, acceleratedContribution με fε σ (η x) z ∂F ≤ if z.2 then M / (σ * z.1) else 1 := by
  have h := integral_acceleratedContribution_le_of_envelope (με := με) F hfm hf0 hσ hη
    (integrable_const (M / (σ * z.1))) z fun x => by
      rw [acceleratedDensity, ite_eq_left ht]
      exact div_le_div_of_nonneg_right (hM _) (by have := ht; positivity)
  simpa using h

/-! ### The target survival and its hazard -/

/-- **The target survival has derivative `-∫ f(t | x) F(dx)`** at every `t > 0`, for an error
law with a density `0 ≤ f_ε ≤ M` (`S_ε' = -f_ε`), `σ > 0`, a measurable predictor `η` and a
covariate probability law `F`. -/
theorem hasDerivAt_popSurvival_accelerated (F : Measure 𝒳) [IsProbabilityMeasure F]
    {με : Measure ℝ} [IsProbabilityMeasure με] {fε : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt (fun z => με.real (Ioi z)) (-fε z) z) (hf0 : ∀ z, 0 ≤ fε z) {M : ℝ}
    (hM : ∀ z, fε z ≤ M) {σ : ℝ} (hσ : 0 < σ) {η : 𝒳 → ℝ} (hη : Measurable η) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (popSurvival F fun x => acceleratedSurvival με σ (η x))
      (-∫ x, acceleratedDensity fε σ (η x) t ∂F) t := by
  have ht2 : (0 : ℝ) < t / 2 := by linarith
  have hM0 : 0 ≤ M := (hf0 0).trans (hM 0)
  have hfm := measurable_errorDensity hf
  have hSm : ∀ u, Measurable fun x => acceleratedSurvival με σ (η x) u := fun u =>
    (measurable_acceleratedSurvival_uncurry με σ hη).comp (measurable_id.prodMk measurable_const)
  have hdm : Measurable fun x => acceleratedDensity fε σ (η x) t := by
    have := measurable_acceleratedContribution (με := με) hfm σ hη (t, true)
    simpa [acceleratedContribution, censoredContribution] using this
  have hball : ∀ u ∈ Metric.ball t (t / 2), t / 2 < u := fun u hu => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu
    linarith [hu.1]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := F) (x₀ := t)
    (F := fun u x => acceleratedSurvival με σ (η x) u)
    (F' := fun u x => -acceleratedDensity fε σ (η x) u)
    (bound := fun _ => M / (σ * (t / 2))) (Metric.ball_mem_nhds t ht2)
    (Eventually.of_forall fun u => (hSm u).aestronglyMeasurable)
    (Integrable.of_bound (hSm t).aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (acceleratedSurvival_mem_Icc με σ (η x) t).1]
      exact (acceleratedSurvival_mem_Icc με σ (η x) t).2))
    hdm.neg.aestronglyMeasurable
    (ae_of_all _ fun x u hu => by
      have hu2 := hball u hu
      have hu0 : 0 < u := ht2.trans hu2
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (acceleratedDensity_nonneg hf0 hσ _ _),
        acceleratedDensity, ite_eq_left hu0]
      calc fε ((Real.log u - η x) / σ) / (σ * u) ≤ M / (σ * u) :=
            div_le_div_of_nonneg_right (hM _) (by positivity)
        _ ≤ M / (σ * (t / 2)) :=
            div_le_div_of_nonneg_left hM0 (by positivity)
              (mul_le_mul_of_nonneg_left hu2.le hσ.le))
    (integrable_const _)
    (ae_of_all _ fun x u hu => hasDerivAt_acceleratedSurvival hf σ (η x) (ht2.trans (hball u hu)))
  have h2 := key.2
  rw [integral_neg] at h2
  exact h2

/-- **The marginal hazard of the target survival**: at every `t > 0` with a positive target
survival, under the hypotheses of `hasDerivAt_popSurvival_accelerated`, the marginal hazard times
the target survival is the target density `∫ f(t | x) F(dx)`, so the marginal hazard is
`∫ f(t | x) F(dx) / ∫ S(t | x) F(dx)`. -/
theorem popHazard_accelerated (F : Measure 𝒳) [IsProbabilityMeasure F]
    {με : Measure ℝ} [IsProbabilityMeasure με] {fε : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt (fun z => με.real (Ioi z)) (-fε z) z) (hf0 : ∀ z, 0 ≤ fε z) {M : ℝ}
    (hM : ∀ z, fε z ≤ M) {σ : ℝ} (hσ : 0 < σ) {η : 𝒳 → ℝ} (hη : Measurable η) {t : ℝ}
    (ht : 0 < t) (hpos : 0 < popSurvival F (fun x => acceleratedSurvival με σ (η x)) t) :
    popHazard F (fun x => acceleratedSurvival με σ (η x)) t *
        popSurvival F (fun x => acceleratedSurvival με σ (η x)) t =
      ∫ x, acceleratedDensity fε σ (η x) t ∂F := by
  rw [popHazard, curveHazard,
    (hasDerivAt_popSurvival_accelerated F hf hf0 hM hσ hη ht).deriv, neg_neg,
    div_mul_cancel₀ _ hpos.ne']

/-! ### Instance: a minimum extreme value error -/

section Instance

/-- The **standard minimum extreme value law**: the law of `log E` for a unit exponential `E`. -/
noncomputable def minExtremeLaw : Measure ℝ := (expMeasure 1).map Real.log

instance : IsProbabilityMeasure minExtremeLaw := by
  have := isProbabilityMeasure_expMeasure (zero_lt_one' ℝ)
  exact (Measure.isProbabilityMeasure_map_iff Real.measurable_log.aemeasurable).2 this

/-- The error survival of the minimum extreme value law is `P(ε > z) = exp(-e^z)`. -/
theorem minExtremeLaw_real_Ioi (z : ℝ) : minExtremeLaw.real (Ioi z) = Real.exp (-Real.exp z) := by
  have := isProbabilityMeasure_expMeasure (zero_lt_one' ℝ)
  have hneg : expMeasure 1 (Iic 0) = 0 := by
    have h : (expMeasure 1).real (Iic 0) = 0 := by
      rw [← cdf_eq_real, cdf_expMeasure_eq one_pos, ite_eq_left le_rfl]
      simp
    rwa [measureReal_eq_zero_iff] at h
  have hset : expMeasure 1 (Real.log ⁻¹' Ioi z) = expMeasure 1 (Ioi (Real.exp z)) := by
    refine le_antisymm ?_ (measure_mono fun x (hx : Real.exp z < x) => ?_)
    · calc expMeasure 1 (Real.log ⁻¹' Ioi z) ≤ expMeasure 1 (Ioi (Real.exp z) ∪ Iic 0) :=
            measure_mono fun x (hx : z < Real.log x) => by
              rcases le_or_gt x 0 with h | h
              · exact Or.inr h
              · exact Or.inl ((Real.lt_log_iff_exp_lt h).1 hx)
        _ ≤ expMeasure 1 (Ioi (Real.exp z)) + expMeasure 1 (Iic 0) := measure_union_le _ _
        _ = expMeasure 1 (Ioi (Real.exp z)) := by rw [hneg, add_zero]
    · exact (Real.lt_log_iff_exp_lt ((Real.exp_pos z).trans hx)).2 hx
  rw [minExtremeLaw, measureReal_def, Measure.map_apply Real.measurable_log measurableSet_Ioi,
    hset, ← measureReal_def, expMeasure_real_Ioi one_pos (Real.exp_pos z).le, one_mul]

/-- The minimum extreme value error density `e^z exp(-e^z)`. -/
noncomputable def minExtremeDensity (z : ℝ) : ℝ := Real.exp z * Real.exp (-Real.exp z)

theorem hasDerivAt_minExtremeLaw (z : ℝ) :
    HasDerivAt (fun z => minExtremeLaw.real (Ioi z)) (-minExtremeDensity z) z := by
  have e : (fun z => minExtremeLaw.real (Ioi z)) = fun z => Real.exp (-Real.exp z) :=
    funext minExtremeLaw_real_Ioi
  rw [e, minExtremeDensity]
  convert (Real.hasDerivAt_exp z).neg.exp using 1
  simp only [Pi.neg_apply]
  ring

theorem exp_log_sub {t : ℝ} (ht : 0 < t) (η : ℝ) :
    Real.exp (Real.log t - η) = t * Real.exp (-η) := by
  rw [Real.exp_sub, Real.exp_log ht, Real.exp_neg, div_eq_mul_inv]

theorem acceleratedSurvival_minExtreme (η : ℝ) {t : ℝ} (ht : 0 < t) :
    acceleratedSurvival minExtremeLaw 1 η t = Real.exp (-(t * Real.exp (-η))) := by
  rw [acceleratedSurvival, ite_eq_left ht, div_one, minExtremeLaw_real_Ioi, exp_log_sub ht]

theorem acceleratedDensity_minExtreme (η : ℝ) {t : ℝ} (ht : 0 < t) :
    acceleratedDensity minExtremeDensity 1 η t = Real.exp (-η) * Real.exp (-(t * Real.exp (-η))) :=
  by
  rw [acceleratedDensity, ite_eq_left ht, div_one, minExtremeDensity, exp_log_sub ht]
  field_simp

/-- **Instance: the accelerated branch with a minimum extreme value error.** With `σ = 1`, the
error law `minExtremeLaw` (density `e^z exp(-e^z) ≤ e^{-1}`), and the linear predictor
`η(x) = -log 2 · x` of a covariate taking the values `0` and `1` with probability `1/2`, the
conditional survivals are `e^{-t}` and `e^{-2t}`, and at every `t > 0` the marginal hazard of the
target survival is `(e^{-t} + 2 e^{-2t}) / (e^{-t} + e^{-2t})`. -/
theorem popHazard_accelerated_instance {t : ℝ} (ht : 0 < t) :
    popHazard (twoAtomLaw ![0] ![1] (1 / 2))
        (fun x => acceleratedSurvival minExtremeLaw 1 (-(Real.log 2 * x 0))) t =
      (Real.exp (-t) + 2 * Real.exp (-(2 * t))) / (Real.exp (-t) + Real.exp (-(2 * t))) := by
  have := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  have hη : Measurable fun x : Fin 1 → ℝ => -(Real.log 2 * x 0) := by fun_prop
  have hS : popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
      (fun x => acceleratedSurvival minExtremeLaw 1 (-(Real.log 2 * x 0))) t =
      (Real.exp (-t) + Real.exp (-(2 * t))) / 2 := by
    rw [popSurvival, integral_twoAtomLaw (by norm_num) (by norm_num)]
    simp only [Matrix.cons_val_fin_one, mul_zero, neg_zero, mul_one]
    rw [acceleratedSurvival_minExtreme _ ht, acceleratedSurvival_minExtreme _ ht]
    simp only [neg_zero, neg_neg, Real.exp_zero, Real.exp_log two_pos, mul_one]
    rw [show -(t * 2) = -(2 * t) by ring]
    ring
  have h1 := Real.exp_pos (-t)
  have h2 := Real.exp_pos (-(2 * t))
  have hpos : 0 < popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
      (fun x => acceleratedSurvival minExtremeLaw 1 (-(Real.log 2 * x 0))) t := by
    rw [hS]; positivity
  have h := popHazard_accelerated (fε := minExtremeDensity) (M := Real.exp (-1)) _
    hasDerivAt_minExtremeLaw (fun z => by unfold minExtremeDensity; positivity)
    (fun z => Real.mul_exp_neg_le_exp_neg_one _) one_pos hη ht hpos
  rw [integral_twoAtomLaw (by norm_num) (by norm_num)] at h
  simp only [Matrix.cons_val_fin_one, mul_zero, neg_zero, mul_one] at h
  rw [acceleratedDensity_minExtreme _ ht, acceleratedDensity_minExtreme _ ht] at h
  simp only [neg_zero, neg_neg, Real.exp_zero, Real.exp_log two_pos, mul_one, one_mul] at h
  rw [show -(t * 2) = -(2 * t) by ring, hS] at h
  rw [eq_div_iff (by positivity)]
  linarith

/-- **Instance: the remaining hypotheses discharged.** For the minimum extreme value error
(positive error survival `exp(-e^z)`, density at most `e^{-1}`), `σ = 1` and the linear predictor
`η(x) = -log 2 · x` of the two valued covariate: the survival at `η = 0` is
`e^{-t} = exp(-∫₀ᵗ h)` with the hazard `h = f / S` (`acceleratedSurvival_eq_expSurvival`), the
target survival is a population survival of hazard curves at every `t ≥ 0`, and at every `t > 0`
the integrated censored contribution at an event is at most `e^{-1} / t`
(`integral_acceleratedContribution_le`). -/
theorem accelerated_instance {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) = expSurvival (cumHazard fun s =>
      acceleratedDensity minExtremeDensity 1 0 s / acceleratedSurvival minExtremeLaw 1 0 s) t ∧
    popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
        (fun x => acceleratedSurvival minExtremeLaw 1 (-(Real.log 2 * x 0))) t =
      popSurvival (twoAtomLaw ![0] ![1] (1 / 2)) (hazardCurves fun x s =>
        acceleratedDensity minExtremeDensity 1 (-(Real.log 2 * x 0)) s /
          acceleratedSurvival minExtremeLaw 1 (-(Real.log 2 * x 0)) s) t ∧
    ∫ x, acceleratedContribution minExtremeLaw minExtremeDensity 1 (-(Real.log 2 * x 0))
        (t, true) ∂twoAtomLaw ![0] ![1] (1 / 2) ≤ Real.exp (-1) / t := by
  have := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  have hpos : ∀ z, 0 < minExtremeLaw.real (Ioi z) := fun z => by
    rw [minExtremeLaw_real_Ioi]; exact Real.exp_pos _
  have hf0 : ∀ z, 0 ≤ minExtremeDensity z := fun z => by unfold minExtremeDensity; positivity
  have hη : Measurable fun x : Fin 1 → ℝ => -(Real.log 2 * x 0) := by fun_prop
  refine ⟨?_, popSurvival_acceleratedSurvival_eq_hazardCurves _ hasDerivAt_minExtremeLaw hf0 hpos
    one_pos _ ht.le, ?_⟩
  · have h := acceleratedSurvival_eq_expSurvival hasDerivAt_minExtremeLaw hf0 hpos one_pos 0 ht.le
    rw [acceleratedSurvival_minExtreme 0 ht, neg_zero, Real.exp_zero, mul_one] at h
    exact h
  · have h := (integral_acceleratedContribution_le (twoAtomLaw ![0] ![1] (1 / 2))
      (με := minExtremeLaw) (measurable_errorDensity hasDerivAt_minExtremeLaw) hf0
      (fun z => Real.mul_exp_neg_le_exp_neg_one _) one_pos hη (z := (t, true)) ht).2.2
    simpa using h

end Instance

end NetworkMetaRegression

end CausalInference
