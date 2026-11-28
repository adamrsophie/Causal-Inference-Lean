/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.WeightingConsistency
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Point treatment: consistency of g-computation

The g-computation (outcome regression plug-in) estimator of `E[Y(a)]` averages a regression over
the sampled covariates, `n⁻¹ ∑_{i < n} m̂(a, W_i)`. With the true regression `m` (a version of
`E[Y | W, A]`) it is a sample mean whose limit is `E[m(a, W)] = E[Y(a)]` under mean ignorability
and positivity (`orArmMean_eq_armMean`). With a fitted regression it has the same limit when
either

* the fitted regressions converge to `m` at the sampled covariates (`TendstoOnSample`): each
  term moves by at most `δ`; or
* the regression is a parametric family `m θ` evaluated at a consistent estimate `θ̂` of `θ₀`,
  with `m θ₀` the true regression, `θ ↦ m θ (a, w)` continuous on a compact neighborhood `K` of
  `θ₀` for almost every `w` and dominated on `K` by an integrable envelope; the uniform law of
  large numbers (`uniform_law_of_large_numbers_real`) and the plug-in lemma
  (`TendstoUniformlyOnInProbability.comp_tendstoInMeasure`) give the limit.

No positivity bound away from zero is needed. The hypotheses on nuisance functions can always be
met: a propensity score and an outcome regression exist for every model
(`exists_isPropensityScore`, `exists_isOutcomeRegression`, by the Doob and Dynkin factorization
of a conditional expectation). In a randomized trial without covariates the arm means form the
true regression (`isOutcomeRegression_const_of_indepFun`), and g-computation with the observed
arm means as fitted regression is consistent (`isConsistent_sampleOrArmMean_trial`).

## Main results

* `exists_isPropensityScore`, `exists_isOutcomeRegression`.
* `isOutcomeRegression_of_condExp`: under mean ignorability, versions of `E[Y(a) | W]` form the
  outcome regression.
* `isConsistent_sampleOrArmMean`, `isConsistent_sampleOrArmMean_fitted`,
  `isConsistent_sampleOrArmMean_param`: known, fitted and parametric regression.
* `IndicatorIgnorable.isConsistent_sampleOrAte_fitted`, `Ignorable.isConsistent_sampleOrAte_fitted`:
  the average effect.
* `isOutcomeRegression_const_of_indepFun`, `isConsistent_sampleOrArmMean_trial`,
  `isConsistent_sampleOrArmMean_param_trial`: the randomized trial without covariates.

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* R. I. Jennrich, *Asymptotic properties of non-linear least squares estimators*, Annals of
  Mathematical Statistics 40 (1969) (the uniform law of large numbers on a compact set).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Filter Finset
open scoped Topology

variable {Ω Ξ 𝒲 : Type*} {mΩ : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ} [MeasurableSpace 𝒲]
  {μ : Measure Ω} {P : Measure Ξ} {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ}
  {m : Bool → 𝒲 → ℝ} {O : ℕ → Ξ → 𝒲 × Bool × ℝ}

/-! ### Existence of the nuisance functions -/

/-- **Every model has a propensity score**: `E[1{A} | W]` factors through `W` as a measurable
function (Doob and Dynkin). -/
theorem exists_isPropensityScore (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲) :
    ∃ e : 𝒲 → ℝ, IsPropensityScore μ A W e := by
  obtain ⟨h, hh, heq⟩ := (stronglyMeasurable_condExp (μ := μ) (f := respInd A)
    (m := MeasurableSpace.comap W inferInstance)).exists_eq_measurable_comp
  exact ⟨h, hh.measurable, by rw [heq]; rfl⟩

/-- **Every model has an outcome regression**: `E[Yo | W, A]` factors through `(W, A)` as a
measurable function (Doob and Dynkin). -/
theorem exists_isOutcomeRegression (μ : Measure Ω) (A : Ω → Bool) (W : Ω → 𝒲) (Yo : Ω → ℝ) :
    ∃ m : Bool → 𝒲 → ℝ, IsOutcomeRegression μ A W Yo m := by
  obtain ⟨h, hh, heq⟩ := (stronglyMeasurable_condExp (μ := μ) (f := Yo)
    (m := MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance)).exists_eq_measurable_comp
  exact ⟨fun a w => h (w, a), fun a => hh.measurable.comp (measurable_id.prodMk measurable_const),
    by rw [heq]; rfl⟩

/-- **The outcome regression from the arm regressions.** Under mean ignorability of both arms
and integrable potential outcomes, if `m(a, W)` is a version of `E[Y(a) | W]` for each arm,
then `m(A, W)` is a version of `E[Y | W, A]`. No positivity is needed. -/
theorem isOutcomeRegression_of_condExp [IsFiniteMeasure μ] (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    (hm : ∀ a, Measurable (m a))
    (hg : ∀ a, μ[Y a | MeasurableSpace.comap W inferInstance] =ᵐ[μ] fun ω => m a (W ω)) :
    IsOutcomeRegression μ A W (obsOutcome A Y) m := by
  refine ⟨hm, ?_⟩
  have hdec : obsOutcome A Y =
      respInd (arm A true) * Y true + respInd (arm A false) * Y false := by
    funext ω
    cases h : A ω <;> simp [obsOutcome, respInd_arm_apply, h]
  have hb : ∀ a, StronglyMeasurable[MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance]
      (respInd (arm A a)) := fun a => (measurable_respInd_arm_comap W A a).stronglyMeasurable
  have hbm : ∀ a, Measurable (respInd (arm A a)) := fun a =>
    measurable_respInd (measurable_arm hA a)
  have hbd : ∀ a, ∀ᵐ ω ∂μ, ‖respInd (arm A a) ω‖ ≤ 1 := fun a =>
    Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (respInd_nonneg _ ω)]; exact respInd_le_one _ ω
  have hi : ∀ a, Integrable (respInd (arm A a) * Y a) μ := fun a =>
    (hYi a).bdd_mul (hbm a).aestronglyMeasurable (hbd a)
  have c : ∀ a, μ[respInd (arm A a) * Y a | MeasurableSpace.comap (fun ω => (W ω, A ω))
      inferInstance] =ᵐ[μ] respInd (arm A a) *
        μ[Y a | MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance] := fun a =>
    condExp_mul_of_stronglyMeasurable_left (hb a) (hi a) (hYi a)
  rw [hdec]
  filter_upwards [condExp_add (hi true) (hi false)
      (MeasurableSpace.comap (fun ω => (W ω, A ω)) inferInstance), c true, c false,
    hmi true, hmi false, hg true, hg false] with ω h0 h1 h2 h3 h4 h5 h6
  rw [h0, Pi.add_apply, h1, h2, Pi.mul_apply, Pi.mul_apply, h3, h4, h5, h6]
  cases h : A ω <;> simp [respInd_arm_apply, h]

/-! ### Known regression -/

section Consistency

variable [IsProbabilityMeasure P] [IsProbabilityMeasure μ]

/-- **g-computation with the known regression.** Under mean ignorability and positivity of the
arm, with integrable potential outcomes and a version `m` of `E[Y | W, A]`, for an i.i.d. sample
of `(W, A, Y)` the estimator `n⁻¹ ∑ m(a, W_i)` is consistent for `E[Y(a)]`. -/
theorem isConsistent_sampleOrArmMean (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hps : IsPropensityScore μ A W e)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleOrArmMean (fun _ _ => m) a O) (armMean μ Y a) P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have h := isConsistent_sampleMean_of_map_eq hO hD.aemeasurable hlaw
    (measurable_regObs (hreg.1 a)) (integrable_regression hW hA hYi hreg hps a hmi hpos)
  rw [← orArmMean_eq_armMean hW hA hYi hreg hps a hmi hpos]
  exact h

/-- **g-computation with a fitted regression.** Under the hypotheses of
`isConsistent_sampleOrArmMean`, if the fitted regressions `m̂ n ξ a` converge to `m a` on the
sample, the g-computation estimator with `m̂` is consistent for `E[Y(a)]`. The fitted regression
may be computed from the same sample and need not be measurable. -/
theorem isConsistent_sampleOrArmMean_fitted (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hps : IsPropensityScore μ A W e)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω))
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {mh : ℕ → Ξ → Bool → 𝒲 → ℝ} (hfit : TendstoOnSample P O (fun n ξ => mh n ξ a) (m a)) :
    IsConsistent (sampleOrArmMean mh a O) (armMean μ Y a) P :=
  isConsistent_sampleMean_fitted hO
    (isConsistent_sampleOrArmMean hW hA hY hYi hreg hps a hmi hpos hO hlaw)
    (g := fun _ => 1) measurable_const (integrable_const 1) fun η hη =>
      (hfit η hη).mono fun n ξ hξ i hi => by rw [mul_one]; exact hξ i hi

/-- **g-computation with a parametric regression at a consistent parameter estimate.** Let
`m θ₀` be the true regression, let `θ ↦ m θ (a, w)` be continuous on a compact neighborhood `K`
of `θ₀` for almost every covariate value `w` and dominated on `K` by an integrable envelope
`H(w)`, with each `m θ a` measurable for `θ ∈ K`. Under mean ignorability and positivity of the
arm, for every estimator `θ̂` converging in probability to `θ₀` the estimator
`n⁻¹ ∑ m θ̂ (a, W_i)` is consistent for `E[Y(a)]`. -/
theorem isConsistent_sampleOrArmMean_param {Θ : Type*} [MetricSpace Θ]
    [SecondCountableTopology Θ] (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ) {mθ : Θ → Bool → 𝒲 → ℝ}
    {θ₀ : Θ} (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) (mθ θ₀))
    (hps : IsPropensityScore μ A W e) (a : Bool) (hmi : MeanIgnorable μ A W Y a)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) {K : Set Θ} (hK : IsCompact K) (hK0 : K ∈ 𝓝 θ₀)
    (hmeas : ∀ θ ∈ K, Measurable (mθ θ a))
    (hcont : ∀ᵐ w ∂(μ.map W), ContinuousOn (fun θ => mθ θ a w) K) {H : 𝒲 → ℝ}
    (hH : Measurable H) (hHi : Integrable (fun ω => H (W ω)) μ)
    (hdom : ∀ᵐ w ∂(μ.map W), ∀ θ ∈ K, |mθ θ a w| ≤ H w) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {θh : ℕ → Ξ → Θ} (hθ : TendstoInMeasure P θh atTop (fun _ => θ₀)) :
    IsConsistent (sampleOrArmMean (fun n ξ => mθ (θh n ξ)) a O) (armMean μ Y a) P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hHν : Integrable (fun z : 𝒲 × Bool × ℝ => H z.1) (P.map (O 0)) := by
    rw [hlaw]
    exact (integrable_map_measure (hH.comp measurable_fst).aestronglyMeasurable
      hD.aemeasurable).2 hHi
  obtain ⟨hMc, hU⟩ := uniform_law_of_large_numbers_real hO hK
    (ψ := fun z θ => mθ θ a z.1) (fun θ hθ => (hmeas θ hθ).comp measurable_fst)
    (ae_fst_of_map_eq hW hA hY hlaw hcont) hHν (ae_fst_of_map_eq hW hA hY hlaw hdom)
  have h := hU.comp_tendstoInMeasure hK0 (hMc.continuousAt hK0) hθ
  have hval : ∫ z, mθ θ₀ a z.1 ∂(P.map (O 0)) = armMean μ Y a := by
    rw [hlaw, integral_map (f := fun z : 𝒲 × Bool × ℝ => mθ θ₀ a z.1) hD.aemeasurable
      ((hreg.1 a).comp measurable_fst).aestronglyMeasurable]
    exact orArmMean_eq_armMean hW hA hYi hreg hps a hmi hpos
  rw [hval] at h
  exact h

/-- **g-computation of the average effect with a fitted regression**, under the indicator form
of ignorability, positivity `0 < e(W) < 1` and integrable potential outcomes, for fitted
regressions converging to the true regression on the sample at both arms. -/
theorem IndicatorIgnorable.isConsistent_sampleOrAte_fitted (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (hov : OverlapAE e (μ.map W)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {mh : ℕ → Ξ → Bool → 𝒲 → ℝ} (hfit : ∀ a, TendstoOnSample P O (fun n ξ => mh n ξ a) (m a)) :
    IsConsistent (sampleOrAte mh O) (ate μ Y) P := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  have hmi := fun a => hign.meanIgnorable hW hA hY a (hYi a)
  rw [ate_eq_armMean_sub (hYi true) (hYi false)]
  exact (isConsistent_sampleOrArmMean_fitted hW hA hY hYi hreg hps true (hmi true) (hpos true)
    hO hlaw (hfit true)).sub (isConsistent_sampleOrArmMean_fitted hW hA hY hYi hreg hps false
      (hmi false) (hpos false) hO hlaw (hfit false))

/-- **g-computation of the average effect with a fitted regression under ignorability**
`A ⫫ (Y(0), Y(1)) | W` and positivity. -/
theorem Ignorable.isConsistent_sampleOrAte_fitted [StandardBorelSpace Ω] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hps : IsPropensityScore μ A W e) (hov : OverlapAE e (μ.map W)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {mh : ℕ → Ξ → Bool → 𝒲 → ℝ} (hfit : ∀ a, TendstoOnSample P O (fun n ξ => mh n ξ a) (m a)) :
    IsConsistent (sampleOrAte mh O) (ate μ Y) P :=
  ((ignorable_iff_indicatorIgnorable hW hA hY).1 hign).isConsistent_sampleOrAte_fitted hW hA hY
    hYi hreg hps hov hO hlaw hfit

end Consistency

/-! ### The randomized trial without covariates -/

/-- **In a randomized trial without covariates the arm means are the outcome regression**: if
`A ⫫ (Y(0), Y(1))` and the potential outcomes are integrable, `E[Y | A] = E[Y(A)]`, that is,
`(a, _) ↦ E[Y(a)]` is the outcome regression given the trivial covariate. -/
theorem isOutcomeRegression_const_of_indepFun [IsProbabilityMeasure μ] (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hind : IndepFun A (potentialPair Y) μ) :
    IsOutcomeRegression μ A (fun _ => ()) (obsOutcome A Y) (fun a _ => armMean μ Y a) := by
  have hW : Measurable fun _ : Ω => () := measurable_const
  have hind' : IndepFun A (fun ω => ((), potentialPair Y ω)) μ :=
    hind.comp measurable_id (measurable_const.prodMk measurable_id)
  have hign := indicatorIgnorable_of_indepFun hW hA hY hind'
  refine isOutcomeRegression_of_condExp hA hYi (fun a => hign.meanIgnorable hW hA hY a (hYi a))
    (fun a => measurable_const) fun a => ?_
  rw [MeasurableSpace.comap_const, condExp_bot]
  rfl

/-- **g-computation in a randomized trial with the observed arm means as fitted regression.**
Without covariates, if `A ⫫ (Y(0), Y(1))`, `0 < P(A = 1) < 1` and the potential outcomes are
integrable, the g-computation estimator whose fitted regression at the arm `b` is the observed
arm mean of `b` is consistent for `E[Y(a)]`. This exercises `isConsistent_sampleOrArmMean_fitted`
with a regression estimated from the same sample. -/
theorem isConsistent_sampleOrArmMean_trial [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hind : IndepFun A (potentialPair Y) μ) (h0 : 0 < μ.real (A ⁻¹' {true}))
    (h1 : μ.real (A ⁻¹' {true}) < 1) (a : Bool) {O : ℕ → Ξ → Unit × Bool × ℝ}
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => ((), A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleOrArmMean (fun n ξ b _ => sampleArmMean b O n ξ) a O)
      (armMean μ Y a) P := by
  have hW : Measurable fun _ : Ω => () := measurable_const
  have hind' : IndepFun A (fun ω => ((), potentialPair Y ω)) μ :=
    hind.comp measurable_id (measurable_const.prodMk measurable_id)
  have hign := indicatorIgnorable_of_indepFun hW hA hY hind'
  have hps := isPropensityScore_const_of_indepFun hW hA (hind'.comp measurable_id measurable_fst)
  have hpos : ∀ᵐ ω ∂μ, 0 < armProb (fun _ : Unit => μ.real (A ⁻¹' {true})) a () :=
    Filter.Eventually.of_forall fun _ =>
      Overlap.armProb_pos (fun _ => ⟨h0, h1⟩) a ()
  have hθ := isConsistent_sampleArmMean_of_indepFun hW hA hY hind' h0 h1 a (hYi a) hO hlaw
  exact isConsistent_sampleOrArmMean_fitted hW hA hY hYi
    (isOutcomeRegression_const_of_indepFun hA hY hYi hind) hps a
    (hign.meanIgnorable hW hA hY a (hYi a)) hpos hO hlaw
    (TendstoOnSample.of_param (h := fun θ (_ : Unit) => θ)
      (fun ε hε => ⟨ε, hε, fun θ hθ _ => by rw [Real.dist_eq] at hθ; exact hθ.le⟩) hθ)

/-- **The parametric g-computation theorem in a randomized trial.** Without covariates, if
`A ⫫ (Y(0), Y(1))`, `0 < P(A = 1) < 1` and the potential outcomes are integrable, take the
one parameter family of regressions `m θ (b, _) = θ` for `b = a` and `E[Y(b)]` otherwise, with
`θ₀ = E[Y(a)]`, and the observed arm mean of `a` as parameter estimate. The hypotheses of
`isConsistent_sampleOrArmMean_param` hold on `K = [θ₀ - 1, θ₀ + 1]` with the envelope
`|θ₀| + 1`, and the g-computation estimator is consistent for `E[Y(a)]`. -/
theorem isConsistent_sampleOrArmMean_param_trial [IsProbabilityMeasure P]
    [IsProbabilityMeasure μ] (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hYi : ∀ a, Integrable (Y a) μ) (hind : IndepFun A (potentialPair Y) μ)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) (a : Bool)
    {O : ℕ → Ξ → Unit × Bool × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => ((), A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleOrArmMean (fun n ξ b (_ : Unit) =>
        if b = a then sampleArmMean a O n ξ else armMean μ Y b) a O) (armMean μ Y a) P := by
  have hW : Measurable fun _ : Ω => () := measurable_const
  have hind' : IndepFun A (fun ω => ((), potentialPair Y ω)) μ :=
    hind.comp measurable_id (measurable_const.prodMk measurable_id)
  have hign := indicatorIgnorable_of_indepFun hW hA hY hind'
  have hps := isPropensityScore_const_of_indepFun hW hA (hind'.comp measurable_id measurable_fst)
  have hpos : ∀ᵐ ω ∂μ, 0 < armProb (fun _ : Unit => μ.real (A ⁻¹' {true})) a () :=
    Filter.Eventually.of_forall fun _ => Overlap.armProb_pos (fun _ => ⟨h0, h1⟩) a ()
  set θ₀ := armMean μ Y a
  let mθ : ℝ → Bool → Unit → ℝ := fun θ b _ => if b = a then θ else armMean μ Y b
  have hθ₀ : mθ θ₀ = fun b _ => armMean μ Y b := by
    funext b u
    by_cases hb : b = a
    · subst hb; simp [mθ, θ₀]
    · simp [mθ, hb]
  have hreg : IsOutcomeRegression μ A (fun _ => ()) (obsOutcome A Y) (mθ θ₀) := by
    rw [hθ₀]; exact isOutcomeRegression_const_of_indepFun hA hY hYi hind
  have hdom : ∀ᵐ w ∂(μ.map fun _ : Ω => ()), ∀ θ ∈ Metric.closedBall θ₀ 1,
      |mθ θ a w| ≤ |θ₀| + 1 :=
    Filter.Eventually.of_forall fun w θ hθ => by
      simp only [mθ, ↓reduceIte]
      rw [Metric.mem_closedBall, Real.dist_eq] at hθ
      calc |θ| = |(θ - θ₀) + θ₀| := by ring_nf
        _ ≤ |θ - θ₀| + |θ₀| := abs_add_le _ _
        _ ≤ |θ₀| + 1 := by linarith
  exact isConsistent_sampleOrArmMean_param hW hA hY hYi hreg hps a
    (hign.meanIgnorable hW hA hY a (hYi a)) hpos (isCompact_closedBall θ₀ 1)
    (Metric.closedBall_mem_nhds θ₀ one_pos) (fun _ _ => measurable_const)
    (Filter.Eventually.of_forall fun w => by
      simp only [mθ, ↓reduceIte]; exact continuousOn_id)
    measurable_const (integrable_const _) hdom hO hlaw
    (isConsistent_sampleArmMean_of_indepFun hW hA hY hind' h0 h1 a (hYi a) hO hlaw)

end PointTreatment

end CausalInference
