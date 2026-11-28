/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.RegressionConsistency

/-!
# Point treatment: double robustness of the augmented estimator as consistency

The augmented inverse probability weighted estimator of `E[Y(a)]` with a fitted score `ê` and a
fitted regression `m̂` is the sample mean of
`1{A_i = a} Y_i / π̂_a(W_i) - (1{A_i = a} - π̂_a(W_i)) / π̂_a(W_i) · m̂(a, W_i)`.

Assume that the fitted score converges on the sample to a limit score `e'` satisfying strict
positivity `ε ≤ e'(W) ≤ 1 - ε`, and that the fitted regression converges on the sample to a limit
regression `m'` with `m'(a, W)` integrable. Neither limit need be correct. Then the estimator
converges in probability to the population augmented mean `aipwArmMean μ A Y W e' m' a`: on the
events where both fits are within `δ` at the sampled points, each term moves by at most `η` times
`1 + |Y_i| + |m'(a, W_i)|`. The population double robustness
(`IndicatorIgnorable.aipwArmMean_eq_of_propensity`,
`IndicatorIgnorable.aipwArmMean_eq_of_regression`) then gives the limit `E[Y(a)]` as soon as
**either** `e'` is the propensity score **or** `m'` is the outcome regression. The integrability of
the weighted residual needed there is derived from strict positivity of `e'`.

Both branches are exercised in a randomized trial: with the sample proportion of treated units as
fitted score and the observed arm means as fitted regression (the score branch, for any
covariate), and without covariates with a fixed wrong constant score and the observed arm means
as fitted regression (the regression branch).

## Main results

* `abs_aipw_sub_le`: the perturbation bound for one term.
* `isConsistent_sampleAipwArmMean_fitted_of_oracle`: the fitted estimator has the limit of the
  estimator with the limits of the fits.
* `integrable_weightedResidual`: the weighted residual is integrable under strict positivity.
* `IndicatorIgnorable.isConsistent_sampleAipwArmMean_fitted`,
  `IndicatorIgnorable.isConsistent_sampleAipwAte_fitted`,
  `Ignorable.isConsistent_sampleAipwAte_fitted`: **double robustness**, for an arm and for the
  average effect.
* `isConsistent_sampleAipwArmMean_trial_score`, `isConsistent_sampleAipwArmMean_trial_regression`:
  the two branches in a randomized trial.

## References

* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, Journal of the American Statistical Association 89
  (1994).
* D. O. Scharfstein, A. Rotnitzky and J. M. Robins, *Adjusting for nonignorable drop-out using
  semiparametric nonresponse models*, Journal of the American Statistical Association 94 (1999).
* H. Bang and J. M. Robins, *Doubly robust estimation in missing data and causal inference
  models*, Biometrics 61 (2005).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Filter Finset
open scoped Topology

variable {Ω Ξ 𝒲 : Type*} {mΩ : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ} [MeasurableSpace 𝒲]
  {μ : Measure Ω} {P : Measure Ξ} {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {e : 𝒲 → ℝ}
  {O : ℕ → Ξ → 𝒲 × Bool × ℝ}

/-- **The perturbation bound for one augmented term.** If the arm probability `p ≥ ε > 0` moves
to `q` with `|q - p| ≤ δ` and the regression value `m` moves to `m'` with `|m' - m| ≤ δ`, where
`δ ≤ ε / 2`, `δ ≤ (η / 2) ε² / 2` and `δ (1 + 2 / ε) ≤ η / 2`, then the augmented term with an
indicator `I ∈ [0, 1]` moves by at most `η (1 + |y| + |m|)`. -/
theorem abs_aipw_sub_le {I y p q m m' ε δ η : ℝ} (hI : 0 ≤ I) (hI1 : I ≤ 1) (hε : 0 < ε)
    (hp : ε ≤ p) (hpq : |q - p| ≤ δ) (hmm : |m' - m| ≤ δ) (hδ1 : δ ≤ ε / 2)
    (hδ2 : δ ≤ η / 2 * ε ^ 2 / 2) (hδ3 : δ * (1 + 2 / ε) ≤ η / 2) (hη : 0 ≤ η) :
    |(I * y / q - (I - q) / q * m') - (I * y / p - (I - p) / p * m)| ≤ η * (1 + |y| + |m|) := by
  have hq : ε / 2 ≤ q := by linarith [(abs_le.1 hpq).1]
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hmm
  have e4 : (I * y / q - (I - q) / q * m') - (I * y / p - (I - p) / p * m) =
      (m' - m) + I * (((y - m) / q - (y - m) / p) - (m' - m) / q) := by
    field_simp
    ring
  have b1 : |(y - m) / q - (y - m) / p| ≤ η / 2 * |y - m| :=
    abs_div_sub_div_le hε hp hpq hδ1 hδ2 (by positivity)
  have b2 : |(m' - m) / q| ≤ 2 * δ / ε := by
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    calc |m' - m| ≤ δ := hmm
      _ = 2 * δ / ε * (ε / 2) := by field_simp
      _ ≤ 2 * δ / ε * q := mul_le_mul_of_nonneg_left hq (by positivity)
  have b3 : |y - m| ≤ |y| + |m| := abs_sub _ _
  have hX : |I * (((y - m) / q - (y - m) / p) - (m' - m) / q)| ≤
      η / 2 * (|y| + |m|) + 2 * δ / ε := by
    rw [abs_mul, abs_of_nonneg hI]
    have h := (abs_sub _ _).trans (add_le_add
      (b1.trans (mul_le_mul_of_nonneg_left b3 (by positivity))) b2)
    calc I * |((y - m) / q - (y - m) / p) - (m' - m) / q|
        ≤ 1 * |((y - m) / q - (y - m) / p) - (m' - m) / q| :=
          mul_le_mul_of_nonneg_right hI1 (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h
  have hsplit : δ * (1 + 2 / ε) = δ + 2 * δ / ε := by field_simp
  rw [e4]
  calc |(m' - m) + I * (((y - m) / q - (y - m) / p) - (m' - m) / q)|
      ≤ |m' - m| + |I * (((y - m) / q - (y - m) / p) - (m' - m) / q)| := abs_add_le _ _
    _ ≤ δ + (η / 2 * (|y| + |m|) + 2 * δ / ε) := add_le_add hmm hX
    _ ≤ η * (1 + |y| + |m|) := by
        nlinarith [abs_nonneg y, abs_nonneg m]

/-- **Convergence to the population augmented mean of the limits.** Let the limit score `e'`
satisfy strict positivity at almost every observed covariate, let `Y` and `m'(a, W)` be
integrable over an observation, and let the fitted score and regression converge to `e'` and
`m' a` on the sample. If the augmented estimator with the limits is consistent for `c`, so is
the augmented estimator with the fitted functions. -/
theorem isConsistent_sampleAipwArmMean_fitted_of_oracle [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {ε : ℝ} (hε : 0 < ε) {e' : 𝒲 → ℝ}
    (hstrict : ∀ᵐ z ∂(P.map (O 0)), ε ≤ e' z.1 ∧ e' z.1 ≤ 1 - ε) (a : Bool)
    {m' : Bool → 𝒲 → ℝ} (hm' : Measurable (m' a)) (hyi : Integrable (fun ξ => (O 0 ξ).2.2) P)
    (hmi : Integrable (fun ξ => m' a (O 0 ξ).1) P) {c : ℝ}
    (h₀ : IsConsistent (sampleAipwArmMean (fun _ _ => e') (fun _ _ => m') a O) c P)
    {ê : ℕ → Ξ → 𝒲 → ℝ} {mh : ℕ → Ξ → Bool → 𝒲 → ℝ} (hfe : TendstoOnSample P O ê e')
    (hfm : TendstoOnSample P O (fun n ξ => mh n ξ a) (m' a)) :
    IsConsistent (sampleAipwArmMean ê mh a O) c P := by
  refine isConsistent_sampleMean_fitted hO h₀ (g := fun z => 1 + |z.2.2| + |m' a z.1|)
    ((measurable_const.add (continuous_abs.measurable.comp measurable_snd.snd)).add
      (continuous_abs.measurable.comp (hm'.comp measurable_fst)))
    (((integrable_const 1).add hyi.abs).add hmi.abs) fun η hη => ?_
  set δ := min (ε / 2) (min (η / 2 * ε ^ 2 / 2) (η / 2 / (1 + 2 / ε))) with hδdef
  have hc : 0 < 1 + 2 / ε := by positivity
  have hδ : 0 < δ := lt_min (half_pos hε) (lt_min (by positivity) (by positivity))
  have hδ3 : δ * (1 + 2 / ε) ≤ η / 2 := by
    rw [← le_div_iff₀ hc]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine (((WithProbTendingToOne.of_ae (hO.ae_forall hstrict)).inter (hfe δ hδ)).inter
    (hfm δ hδ)).mono fun n ξ hξ i hi => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hξ
  simp only [Set.mem_ofPred_eq] at h1 h2 h3
  have hq : |armProb (ê n ξ) a (O i ξ).1 - armProb e' a (O i ξ).1| ≤ δ := by
    rw [abs_armProb_sub_armProb]; exact h2 i hi
  exact abs_aipw_sub_le (armIndObs_nonneg a _) (armIndObs_le_one a _) hε
    (le_armProb_of_mem (h1 i) a) hq (h3 i hi) (min_le_left _ _)
    ((min_le_right _ _).trans (min_le_left _ _)) hδ3 hη.le

/-! ### Integrability under strict positivity of the limit score -/

/-- Under strict positivity of a working score `e'`, the weighted residual
`1{A = a} (Y - m'(a, W)) / π'_a(W)` is integrable when `Y` and `m'(a, W)` are. -/
theorem integrable_weightedResidual (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    {e' : 𝒲 → ℝ} (he' : Measurable e') {m' : Bool → 𝒲 → ℝ} (a : Bool)
    (hm' : Measurable (m' a)) (hW : Measurable W) {ε : ℝ}
    (hε : 0 < ε) (hstrict : ∀ᵐ ω ∂μ, ε ≤ e' (W ω) ∧ e' (W ω) ≤ 1 - ε)
    (hYo : Integrable (obsOutcome A Y) μ) (hm'i : Integrable (fun ω => m' a (W ω)) μ) :
    Integrable (fun ω => respInd (arm A a) ω * (obsOutcome A Y ω - m' a (W ω)) /
      armProb e' a (W ω)) μ := by
  refine ((hYo.abs.add hm'i.abs).div_const ε).mono' ?_ ?_
  · exact (((measurable_respInd (measurable_arm hA a)).mul
      ((measurable_obsOutcome hA hY).sub (hm'.comp hW))).div
        ((measurable_armProb he' a).comp hW)).aestronglyMeasurable
  · filter_upwards [hstrict] with ω hω
    have hp := le_armProb_of_mem hω a
    have hp0 : 0 < armProb e' a (W ω) := hε.trans_le hp
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (respInd_nonneg _ _),
      abs_of_pos hp0, div_le_div_iff₀ hp0 hε]
    calc respInd (arm A a) ω * |obsOutcome A Y ω - m' a (W ω)| * ε
        ≤ 1 * (|obsOutcome A Y ω| + |m' a (W ω)|) * ε := by
          gcongr
          · exact respInd_le_one _ _
          · exact abs_sub _ _
      _ ≤ (|obsOutcome A Y ω| + |m' a (W ω)|) * armProb e' a (W ω) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hp (by positivity)

/-! ### Double robustness -/

section DoubleRobustness

variable [IsProbabilityMeasure P] [IsProbabilityMeasure μ]

/-- **Double robustness of the augmented estimator, as consistency.** Under the indicator form of
ignorability, with integrable potential outcomes, a propensity score `e` positive on the arm,
limits `e'` (strictly positive) and `m'` (with `m'(a, W)` integrable) of the fitted score and the
fitted regression on the sample, and an i.i.d. sample of `(W, A, Y)`: if `e'` is the propensity
score or `m'` is the outcome regression, the augmented estimator is consistent for `E[Y(a)]`. -/
theorem IndicatorIgnorable.isConsistent_sampleAipwArmMean_fitted (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hps : IsPropensityScore μ A W e) (a : Bool)
    (hpos : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω)) {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ}
    (he' : Measurable e') (hm' : Measurable (m' a)) {ε : ℝ}
    (hov' : StrictOverlapAE e' (μ.map W) ε) (hm'i : Integrable (fun ω => m' a (W ω)) μ)
    (hcorrect : IsPropensityScore μ A W e' ∨ IsOutcomeRegression μ A W (obsOutcome A Y) m')
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {ê : ℕ → Ξ → 𝒲 → ℝ} {mh : ℕ → Ξ → Bool → 𝒲 → ℝ} (hfe : TendstoOnSample P O ê e')
    (hfm : TendstoOnSample P O (fun n ξ => mh n ξ a) (m' a)) :
    IsConsistent (sampleAipwArmMean ê mh a O) (armMean μ Y a) P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hYo : Integrable (obsOutcome A Y) μ := integrable_obsOutcome hA hYi
  have hstrictμ := hov'.ae_comp hW.aemeasurable
  have hpos' := armProb_pos_of_ae (hov'.overlapAE.ae_comp hW.aemeasurable) a
  have hres := integrable_weightedResidual hA hY he' a hm' hW
    hov'.1 hstrictμ hYo hm'i
  have hterm : Integrable (aipwTerm A Y W e' m' a) μ := by
    refine (hm'i.add hres).congr ?_
    filter_upwards [hpos'] with ω hω
    exact (aipwTerm_eq A Y W e' m' a hω.ne').symm
  have hlim : aipwArmMean μ A Y W e' m' a = armMean μ Y a := by
    rcases hcorrect with hps' | hreg
    · exact hign.aipwArmMean_eq_of_propensity hW hA hY hps' a hpos' (hYi a) hm' hm'i
    · exact hign.aipwArmMean_eq_of_regression hW hA hY hYi hps a hpos hreg he' hpos' hres
  have hint : Integrable (fun ω => aipwObs e' m' a (W ω, A ω, obsOutcome A Y ω)) μ := by
    rw [aipwObs_comp]; exact hterm
  have h₀ := isConsistent_sampleMean_of_map_eq hO hD.aemeasurable hlaw
    (measurable_aipwObs he' hm') hint
  rw [aipwObs_comp] at h₀
  have h₀' : IsConsistent (sampleAipwArmMean (fun _ _ => e') (fun _ _ => m') a O)
      (armMean μ Y a) P := by
    rw [← hlim]; exact h₀
  exact isConsistent_sampleAipwArmMean_fitted_of_oracle hO hov'.1
    (ae_fst_of_map_eq hW hA hY hlaw hov'.2) a hm'
    (integrable_comp_of_map_eq hO hD.aemeasurable hlaw measurable_snd.snd hYo)
    (integrable_comp_of_map_eq hO hD.aemeasurable hlaw (hm'.comp measurable_fst) hm'i)
    h₀' hfe hfm

/-- **Double robustness for the average effect, as consistency**, under the indicator form of
ignorability and positivity `0 < e(W) < 1` of the propensity score: if the limit score is
strictly positive, the limit regression is integrable at both arms, the fits converge on the
sample, and either limit is correct, the augmented estimator of the average effect is consistent
for `E[Y(1) - Y(0)]`. -/
theorem IndicatorIgnorable.isConsistent_sampleAipwAte_fitted (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : IndicatorIgnorable μ A W Y) (hps : IsPropensityScore μ A W e)
    (hov : OverlapAE e (μ.map W)) {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ} (he' : Measurable e')
    (hm' : ∀ a, Measurable (m' a)) {ε : ℝ} (hov' : StrictOverlapAE e' (μ.map W) ε)
    (hm'i : ∀ a, Integrable (fun ω => m' a (W ω)) μ)
    (hcorrect : IsPropensityScore μ A W e' ∨ IsOutcomeRegression μ A W (obsOutcome A Y) m')
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {ê : ℕ → Ξ → 𝒲 → ℝ} {mh : ℕ → Ξ → Bool → 𝒲 → ℝ} (hfe : TendstoOnSample P O ê e')
    (hfm : ∀ a, TendstoOnSample P O (fun n ξ => mh n ξ a) (m' a)) :
    IsConsistent (sampleAipwAte ê mh O) (ate μ Y) P := by
  have hpos := armProb_pos_of_ae (hov.ae_comp hW.aemeasurable)
  rw [ate_eq_armMean_sub (hYi true) (hYi false)]
  exact (hign.isConsistent_sampleAipwArmMean_fitted hW hA hY hYi hps true (hpos true) he'
    (hm' true) hov' (hm'i true) hcorrect hO hlaw hfe (hfm true)).sub
      (hign.isConsistent_sampleAipwArmMean_fitted hW hA hY hYi hps false (hpos false) he'
        (hm' false) hov' (hm'i false) hcorrect hO hlaw hfe (hfm false))

/-- **Double robustness for the average effect under ignorability** `A ⫫ (Y(0), Y(1)) | W`. -/
theorem Ignorable.isConsistent_sampleAipwAte_fitted [StandardBorelSpace Ω] (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hign : Ignorable μ A hW Y) (hps : IsPropensityScore μ A W e)
    (hov : OverlapAE e (μ.map W)) {e' : 𝒲 → ℝ} {m' : Bool → 𝒲 → ℝ} (he' : Measurable e')
    (hm' : ∀ a, Measurable (m' a)) {ε : ℝ} (hov' : StrictOverlapAE e' (μ.map W) ε)
    (hm'i : ∀ a, Integrable (fun ω => m' a (W ω)) μ)
    (hcorrect : IsPropensityScore μ A W e' ∨ IsOutcomeRegression μ A W (obsOutcome A Y) m')
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω))
    {ê : ℕ → Ξ → 𝒲 → ℝ} {mh : ℕ → Ξ → Bool → 𝒲 → ℝ} (hfe : TendstoOnSample P O ê e')
    (hfm : ∀ a, TendstoOnSample P O (fun n ξ => mh n ξ a) (m' a)) :
    IsConsistent (sampleAipwAte ê mh O) (ate μ Y) P :=
  ((ignorable_iff_indicatorIgnorable hW hA hY).1 hign).isConsistent_sampleAipwAte_fitted hW hA
    hY hYi hps hov he' hm' hov' hm'i hcorrect hO hlaw hfe hfm

/-! ### The two branches in a randomized trial -/

/-- **The score branch in a randomized trial.** If `A ⫫ (W, (Y(0), Y(1)))`,
`0 < P(A = 1) < 1` and the potential outcomes are integrable, the augmented estimator with the
sample proportion of treated units as fitted score and the observed arm means as fitted
regression (constant in the covariate) is consistent for `E[Y(a)]`. The limit of the fitted
regression, `(b, w) ↦ E[Y(b)]`, is in general not the outcome regression given `W`; the limit of
the fitted score is the propensity score. -/
theorem isConsistent_sampleAipwArmMean_trial_score (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hind : IndepFun A (fun ω => (W ω, potentialPair Y ω)) μ)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) (a : Bool)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleAipwArmMean (fun n ξ _ => sampleMean (armIndObs true) O n ξ)
      (fun n ξ b _ => sampleArmMean b O n ξ) a O) (armMean μ Y a) P := by
  have hD : Measurable fun ω => (W ω, A ω, obsOutcome A Y ω) :=
    hW.prodMk (hA.prodMk (measurable_obsOutcome hA hY))
  have hps := isPropensityScore_const_of_indepFun hW hA (hind.comp measurable_id measurable_fst)
  have hign := indicatorIgnorable_of_indepFun hW hA hY hind
  have hov := (strictOverlap_const (𝒲 := 𝒲) h0 h1).strictOverlapAE (μ.map W)
  have hpos := armProb_pos_of_ae (hov.overlapAE.ae_comp hW.aemeasurable) a
  have hp : IsConsistent (sampleMean (armIndObs true) O) (μ.real (A ⁻¹' {true})) P := by
    have hint : Integrable (fun ω => armIndObs true (W ω, A ω, obsOutcome A Y ω)) μ := by
      simp only [armIndObs_comp, arm_true]; exact integrable_respInd hA
    have h := isConsistent_sampleMean_of_map_eq hO hD.aemeasurable hlaw
      (measurable_armIndObs true) hint
    simp only [armIndObs_comp, arm_true, integral_respInd hA] at h
    exact h
  have hcont : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ θ : ℝ, dist θ (μ.real (A ⁻¹' {true})) < δ →
      ∀ _ : 𝒲, |θ - μ.real (A ⁻¹' {true})| ≤ ε :=
    fun ε hε => ⟨ε, hε, fun θ hθ _ => by rw [Real.dist_eq] at hθ; exact hθ.le⟩
  have hcont' : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ θ : ℝ, dist θ (armMean μ Y a) < δ →
      ∀ _ : 𝒲, |θ - armMean μ Y a| ≤ ε :=
    fun ε hε => ⟨ε, hε, fun θ hθ _ => by rw [Real.dist_eq] at hθ; exact hθ.le⟩
  exact hign.isConsistent_sampleAipwArmMean_fitted hW hA hY hYi hps a hpos
    (m' := fun b _ => armMean μ Y b) measurable_const measurable_const hov
    (integrable_const _) (Or.inl hps) hO hlaw
    (TendstoOnSample.of_param (h := fun θ (_ : 𝒲) => θ) hcont hp)
    (TendstoOnSample.of_param (h := fun θ (_ : 𝒲) => θ) hcont'
      (isConsistent_sampleArmMean_of_indepFun hW hA hY hind h0 h1 a (hYi a) hO hlaw))

/-- **The regression branch in a randomized trial without covariates.** If `A ⫫ (Y(0), Y(1))`,
`0 < P(A = 1) < 1` and the potential outcomes are integrable, the augmented estimator with a
fixed constant score `c ∈ (0, 1)` (wrong unless `c = P(A = 1)`) and the observed arm means as
fitted regression is consistent for `E[Y(a)]`: the limit of the fitted regression is the outcome
regression. -/
theorem isConsistent_sampleAipwArmMean_trial_regression (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hind : IndepFun A (potentialPair Y) μ) (h0 : 0 < μ.real (A ⁻¹' {true}))
    (h1 : μ.real (A ⁻¹' {true}) < 1) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (a : Bool)
    {O : ℕ → Ξ → Unit × Bool × ℝ} (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => ((), A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleAipwArmMean (fun _ _ _ => c) (fun n ξ b _ => sampleArmMean b O n ξ) a O)
      (armMean μ Y a) P := by
  have hW : Measurable fun _ : Ω => () := measurable_const
  have hind' : IndepFun A (fun ω => ((), potentialPair Y ω)) μ :=
    hind.comp measurable_id (measurable_const.prodMk measurable_id)
  have hign := indicatorIgnorable_of_indepFun hW hA hY hind'
  have hps := isPropensityScore_const_of_indepFun hW hA (hind'.comp measurable_id measurable_fst)
  have hpos : ∀ᵐ ω ∂μ, 0 < armProb (fun _ : Unit => μ.real (A ⁻¹' {true})) a () :=
    Filter.Eventually.of_forall fun _ => Overlap.armProb_pos (fun _ => ⟨h0, h1⟩) a ()
  have hcont' : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ ∀ θ : ℝ, dist θ (armMean μ Y a) < δ →
      ∀ _ : Unit, |θ - armMean μ Y a| ≤ ε :=
    fun ε hε => ⟨ε, hε, fun θ hθ _ => by rw [Real.dist_eq] at hθ; exact hθ.le⟩
  exact hign.isConsistent_sampleAipwArmMean_fitted hW hA hY hYi hps a hpos
    (e' := fun _ => c) (m' := fun b _ => armMean μ Y b) measurable_const measurable_const
    ((strictOverlap_const hc0 hc1).strictOverlapAE _) (integrable_const _)
    (Or.inr (isOutcomeRegression_const_of_indepFun hA hY hYi hind)) hO hlaw
    (tendstoOnSample_const P O _)
    (TendstoOnSample.of_param (h := fun θ (_ : Unit) => θ) hcont'
      (isConsistent_sampleArmMean_of_indepFun hW hA hY hind' h0 h1 a (hYi a) hO hlaw))

end DoubleRobustness

end PointTreatment

end CausalInference
