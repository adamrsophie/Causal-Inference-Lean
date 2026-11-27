/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MissingData.Mechanisms

/-!
# Identification under MAR: inverse probability weighting and outcome regression

Identification of the full-data mean `E[Y]` from the observed data when the outcome is missing
at random given an always observed covariate `X`, in the mean-independence form `MARMean`.
All statements use conditional expectations (`MeasureTheory.condExp`), so no conditioning on
events of probability zero occurs.

## Setting

A measurable space `Ω` with a finite measure `μ`, measurable `X : Ω → 𝒳`, `Y : Ω → ℝ` and
`R : Ω → Bool`. The response propensity is a measurable `π : 𝒳 → ℝ` such that `π ∘ X` is a
version of `E[1{R} | X]`, the conditional probability of response given `X`.

## Main results

* `integral_mul_eq_of_condExp_eq`: the weighting lemma. If `E[r | m] = p` and `g` is
  `m`-measurable then `E[r g] = E[p g]`.
* `lintegral_ofReal_mul_eq_of_condExp_eq`, `integrable_mul_of_condExp_eq`: the weighting lemma
  for a nonnegative `r` and Lebesgue integrals, and its consequence that `r g` is integrable
  whenever `p g` is.
* `integrable_ipw`, `ipw_identity`: under MAR and almost sure positivity of `π(X)`, integrability
  of `Y` gives integrability of the weighted outcome and `E[1{R} Y / π(X)] = E[Y]`.
  `integrable_ipw_of_condExp_eq` and `ipw_identity_of_condExp_eq` are the same statements for
  any `σ(X)`-measurable version of the propensity on the sample space.
* `ipw_identity_of_integrable_weighted`: the IPW identity assuming integrability of the weighted
  outcome instead of that of `Y`; `ipw_identity_of_le`: the IPW identity with `π(X) ≥ c > 0`.
* `ipw_weight_integral`: the normalization `E[1{R} / π(X)] = 1`.
* `aipw_identity_of_propensity`, `aipw_identity_of_regression`: the augmented IPW identity
  `E[1{R} Y / π(X) - (1{R} - π(X)) / π(X) h(X)] = E[Y]` when `π` is the true propensity (any
  `h`), and when `h(X)` is a version of `E[Y | X]` (any positive `π`): double robustness.
* `regression_ae_eq`, `regression_identity`: if `μ₁ : 𝒳 → ℝ` satisfies
  `E[1{R} Y | X] = π(X) μ₁(X)` (so `μ₁(X)` is a version of `E[Y | X, R = true]` computed from
  observed data), then under MAR and positivity `μ₁(X)` is a version of `E[Y | X]`, and
  `E[μ₁(X)] = E[Y]`.
* `ipcw_identity`: the IPW identity read as inverse probability of censoring weighting.
* `ipcw_identity_two_period`: inverse probability of censoring weighting over two periods with
  a time-varying covariate; the weight is the product of the two conditional probabilities of
  remaining uncensored.

## References

* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, JASA 89 (1994).
* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, Wiley.
-/

@[expose] public section

namespace CausalInference

namespace MissingData

open MeasureTheory ProbabilityTheory
open scoped ENNReal

section Weighting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The weighting lemma. If the conditional expectation of `r` given a sub-σ-algebra `m` is
almost everywhere `p`, and `g` is `m`-measurable with `r g` integrable, then the product
`p g` is integrable and `E[r g] = E[p g]`. -/
theorem integral_mul_eq_of_condExp_eq [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {r g p : Ω → ℝ} (hr : Integrable r μ) (hg : StronglyMeasurable[m] g)
    (hrg : Integrable (fun ω => r ω * g ω) μ) (hp : μ[r | m] =ᵐ[μ] p) :
    Integrable (fun ω => p ω * g ω) μ ∧ ∫ ω, r ω * g ω ∂μ = ∫ ω, p ω * g ω ∂μ := by
  have hpull : μ[r * g | m] =ᵐ[μ] fun ω => p ω * g ω :=
    (condExp_mul_of_stronglyMeasurable_right hg hrg hr).trans (hp.mul (by rfl))
  refine ⟨integrable_condExp.congr hpull, ?_⟩
  calc ∫ ω, r ω * g ω ∂μ = ∫ ω, (μ[r * g | m]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, p ω * g ω ∂μ := integral_congr_ae hpull

/-- The weighting lemma for nonnegative weights and Lebesgue integrals. If `r ≥ 0` is
integrable with `E[r | m] = p` almost everywhere, then `∫⁻ r G = ∫⁻ p G` for every
`m`-measurable `G : Ω → [0, ∞]`. No integrability of the products is needed. -/
theorem lintegral_ofReal_mul_eq_of_condExp_eq [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {r p : Ω → ℝ} (hr : Integrable r μ) (hr0 : 0 ≤ᵐ[μ] r)
    (hp : μ[r | m] =ᵐ[μ] p) {G : Ω → ℝ≥0∞} (hG : Measurable[m] G) :
    ∫⁻ ω, ENNReal.ofReal (r ω) * G ω ∂μ = ∫⁻ ω, ENNReal.ofReal (p ω) * G ω ∂μ := by
  have hp0 : 0 ≤ᵐ[μ] p := by
    filter_upwards [condExp_nonneg (m := m) hr0, hp] with ω h1 h2
    rw [← h2]; exact h1
  have hpi : Integrable p μ := integrable_condExp.congr hp
  have hGm : AEMeasurable G μ := (hG.mono hm le_rfl).aemeasurable
  have htrim : (μ.withDensity fun ω => ENNReal.ofReal (r ω)).trim hm =
      (μ.withDensity fun ω => ENNReal.ofReal (p ω)).trim hm := by
    ext s hs
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs,
      withDensity_apply _ (hm s hs), withDensity_apply _ (hm s hs),
      ← ofReal_integral_eq_lintegral_ofReal hr.integrableOn (ae_restrict_of_ae hr0),
      ← ofReal_integral_eq_lintegral_ofReal hpi.integrableOn (ae_restrict_of_ae hp0),
      ← setIntegral_condExp hm hr hs, setIntegral_congr_ae (hm s hs) (hp.mono fun _ h _ => h)]
  have h1 := lintegral_withDensity_eq_lintegral_mul₀
    hr.aestronglyMeasurable.aemeasurable.ennreal_ofReal hGm
  have h2 := lintegral_withDensity_eq_lintegral_mul₀
    hpi.aestronglyMeasurable.aemeasurable.ennreal_ofReal hGm
  simp only [Pi.mul_apply] at h1 h2
  rw [← h1, ← h2, ← lintegral_trim hm hG, ← lintegral_trim hm hG, htrim]

/-- The converse integrability half of the weighting lemma for nonnegative weights. If `r ≥ 0`
is integrable with `E[r | m] = p` almost everywhere, `g` is `m`-measurable, and `p g` is
integrable, then `r g` is integrable. -/
theorem integrable_mul_of_condExp_eq [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {r g p : Ω → ℝ} (hr : Integrable r μ) (hr0 : 0 ≤ᵐ[μ] r) (hg : StronglyMeasurable[m] g)
    (hp : μ[r | m] =ᵐ[μ] p) (hpg : Integrable (fun ω => p ω * g ω) μ) :
    Integrable (fun ω => r ω * g ω) μ := by
  have hp0 : 0 ≤ᵐ[μ] p := by
    filter_upwards [condExp_nonneg (m := m) hr0, hp] with ω h1 h2
    rw [← h2]; exact h1
  refine ⟨hr.aestronglyMeasurable.mul (hg.mono hm).aestronglyMeasurable, ?_⟩
  have key := lintegral_ofReal_mul_eq_of_condExp_eq hm hr hr0 hp (G := fun ω => ‖g ω‖ₑ)
    hg.measurable.eNorm
  have e1 : ∫⁻ ω, ‖r ω * g ω‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal (r ω) * ‖g ω‖ₑ ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hr0] with ω hω
    rw [eNorm_mul, Real.eNorm_eq_ofReal hω]
  have e2 : ∫⁻ ω, ‖p ω * g ω‖ₑ ∂μ = ∫⁻ ω, ENNReal.ofReal (p ω) * ‖g ω‖ₑ ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hp0] with ω hω
    rw [eNorm_mul, Real.eNorm_eq_ofReal hω]
  unfold HasFiniteIntegral
  rw [e1, key, ← e2]
  exact hpg.2

end Weighting

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {μ : Measure Ω}
  {X : Ω → 𝒳} {Y : Ω → ℝ} {R : Ω → Bool}

omit [MeasurableSpace Ω] in
/-- A function of `(X, Y)` is measurable for the σ-algebra generated by `(X, Y)`. -/
theorem measurable_comap_prod {β : Type*} [MeasurableSpace β] {h : 𝒳 × ℝ → β}
    (hh : Measurable h) :
    Measurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (fun ω => h (X ω, Y ω)) :=
  hh.comp (comap_measurable _)

/-- Integrability of the inverse probability weighted outcome. Let `p` be a `σ(X)`-measurable
version of the response propensity `E[1{R} | X]`, assume the mean-independence form of MAR and
`p > 0` almost surely. If `Y` is integrable then so is `1{R} Y / p`; indeed
`E[1{R} |Y| / p] = E[|Y|]`. -/
theorem integrable_ipw_of_condExp_eq [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {p : Ω → ℝ}
    (hpm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] p)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] p)
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < p ω) (hYi : Integrable Y μ) :
    Integrable (fun ω => respInd R ω * Y ω / p ω) μ := by
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hg : StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (fun ω => Y ω / p ω) :=
    (measurable_comap_prod (h := fun q : 𝒳 × ℝ => q.2) measurable_snd).stronglyMeasurable.div
      (hpm.mono comap_le_comap_prod)
  have h := integrable_mul_of_condExp_eq (r := respInd R) hXY.comap_le
    ((integrable_const 1).indicator (hR (measurableSet_singleton true)))
    (Filter.Eventually.of_forall fun ω => respInd_nonneg R ω) hg (hmar.trans hprop)
    (hYi.congr (by filter_upwards [hpos] with ω hω; field_simp))
  simpa only [mul_div_assoc] using h

/-- Inverse probability weighting under MAR with a `σ(X)`-measurable version `p` of the response
propensity `E[1{R} | X]` (for instance the conditional expectation itself). Under the
mean-independence form of MAR, `p > 0` almost surely and integrability of `Y`,
`E[1{R} Y / p] = E[Y]`. -/
theorem ipw_identity_of_condExp_eq [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {p : Ω → ℝ}
    (hpm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] p)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] p)
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < p ω) (hYi : Integrable Y μ) :
    ∫ ω, respInd R ω * Y ω / p ω ∂μ = ∫ ω, Y ω ∂μ := by
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hg : StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (fun ω => Y ω / p ω) :=
    (measurable_comap_prod (h := fun q : 𝒳 × ℝ => q.2) measurable_snd).stronglyMeasurable.div
      (hpm.mono comap_le_comap_prod)
  have hint' : Integrable (fun ω => respInd R ω * (Y ω / p ω)) μ := by
    simpa only [mul_div_assoc] using integrable_ipw_of_condExp_eq hX hY hR hpm hprop hmar hpos hYi
  have key := (integral_mul_eq_of_condExp_eq (r := respInd R) hXY.comap_le
    ((integrable_const 1).indicator (hR (measurableSet_singleton true))) hg hint'
    (hmar.trans hprop)).2
  simp only [mul_div_assoc] at key ⊢
  rw [key]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with ω hω
  field_simp

/-- Integrability of the inverse probability weighted outcome: if `π ∘ X` is a version of the
response propensity `E[1{R} | X]`, MAR holds in the mean-independence form, `π(X) > 0` almost
surely and `Y` is integrable, then `1{R} Y / π(X)` is integrable. -/
theorem integrable_ipw [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {π : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) (hYi : Integrable Y μ) :
    Integrable (fun ω => respInd R ω * Y ω / π (X ω)) μ :=
  integrable_ipw_of_condExp_eq hX hY hR (hπ.comp (comap_measurable X)).stronglyMeasurable hprop
    hmar hpos hYi

/-- Inverse probability weighting under MAR. Let `π ∘ X` be a version of the response
propensity `E[1{R} | X]`, assume the mean-independence form of MAR, almost sure positivity of
`π(X)`, and integrability of `Y`. Then the weighted outcome is integrable (`integrable_ipw`) and
`E[1{R} Y / π(X)] = E[Y]`. -/
theorem ipw_identity [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {π : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) (hYi : Integrable Y μ) :
    ∫ ω, respInd R ω * Y ω / π (X ω) ∂μ = ∫ ω, Y ω ∂μ :=
  ipw_identity_of_condExp_eq hX hY hR (hπ.comp (comap_measurable X)).stronglyMeasurable hprop
    hmar hpos hYi

/-- Inverse probability weighting under MAR, assuming integrability of the weighted outcome
instead of that of `Y`. Let `π ∘ X` be a version of the response propensity `E[1{R} | X]`,
assume the mean-independence form of MAR, almost sure positivity of `π(X)`, and integrability
of `1{R} Y / π(X)`. Then `E[1{R} Y / π(X)] = E[Y]`. -/
theorem ipw_identity_of_integrable_weighted [IsFiniteMeasure μ] (hX : Measurable X)
    (hY : Measurable Y) (hR : Measurable R) {π : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω))
    (hint : Integrable (fun ω => respInd R ω * Y ω / π (X ω)) μ) :
    ∫ ω, respInd R ω * Y ω / π (X ω) ∂μ = ∫ ω, Y ω ∂μ := by
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hg : StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (fun ω => Y ω / π (X ω)) :=
    (measurable_comap_prod (h := fun q : 𝒳 × ℝ => q.2 / π q.1)
      (measurable_snd.div (hπ.comp measurable_fst))).stronglyMeasurable
  have hint' : Integrable (fun ω => respInd R ω * (Y ω / π (X ω))) μ := by
    simpa only [mul_div_assoc] using hint
  have key := (integral_mul_eq_of_condExp_eq (r := respInd R) hXY.comap_le
    ((integrable_const 1).indicator (hR (measurableSet_singleton true))) hg hint'
    (hmar.trans hprop)).2
  simp only [mul_div_assoc] at key ⊢
  rw [key]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with ω hω
  field_simp

/-- Inverse probability weighting with the propensity bounded away from zero: if `Y` is
integrable and `π(X) ≥ c > 0` almost surely, then under MAR `E[1{R} Y / π(X)] = E[Y]`. -/
theorem ipw_identity_of_le [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {π : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hmar : MARMean μ X Y R) {c : ℝ} (hc : 0 < c) (hbd : ∀ᵐ ω ∂μ, c ≤ π (X ω))
    (hYi : Integrable Y μ) :
    ∫ ω, respInd R ω * Y ω / π (X ω) ∂μ = ∫ ω, Y ω ∂μ :=
  ipw_identity hX hY hR hπ hprop hmar (hbd.mono fun _ hω => hc.trans_le hω) hYi

/-- Normalization of the inverse probability weights: if `π ∘ X` is a version of the response
propensity `E[1{R} | X]` on a probability space and `π(X) > 0` almost surely, then the weight
`1{R} / π(X)` is integrable and `E[1{R} / π(X)] = 1`. No missingness assumption is needed. This
is the normalization behind the Hajek form of the IPW estimator. -/
theorem ipw_weight_integral [IsProbabilityMeasure μ] (hX : Measurable X) (hR : Measurable R)
    {π : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) :
    Integrable (fun ω => respInd R ω / π (X ω)) μ ∧ ∫ ω, respInd R ω / π (X ω) ∂μ = 1 := by
  have hri : Integrable (respInd R) μ :=
    (integrable_const 1).indicator (hR (measurableSet_singleton true))
  have hg : StronglyMeasurable[MeasurableSpace.comap X inferInstance] fun ω => 1 / π (X ω) :=
    ((measurable_const.div hπ).comp (comap_measurable X)).stronglyMeasurable
  have hone : (fun ω => π (X ω) * (1 / π (X ω))) =ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [hpos] with ω hω
    field_simp
  have hint := integrable_mul_of_condExp_eq hX.comap_le hri
    (Filter.Eventually.of_forall fun ω => respInd_nonneg R ω) hg hprop
    ((integrable_const 1).congr hone.symm)
  have key := (integral_mul_eq_of_condExp_eq hX.comap_le hri hg hint hprop).2
  simp only [mul_one_div] at hint key
  refine ⟨hint, ?_⟩
  rw [key, integral_congr_ae (by simpa only [mul_one_div] using hone)]
  simp

/-- Inverse probability weighting of a function of the covariate: if `π ∘ X` is a version of
the response propensity `E[1{R} | X]`, `π(X) > 0` almost surely and `h(X)` is integrable, then
`1{R} h(X) / π(X)` is integrable and `E[1{R} h(X) / π(X)] = E[h(X)]`. -/
theorem ipw_identity_covariate [IsFiniteMeasure μ] (hX : Measurable X) (hR : Measurable R)
    {π : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) {h : 𝒳 → ℝ} (hh : Measurable h)
    (hhi : Integrable (fun ω => h (X ω)) μ) :
    Integrable (fun ω => respInd R ω * h (X ω) / π (X ω)) μ ∧
      ∫ ω, respInd R ω * h (X ω) / π (X ω) ∂μ = ∫ ω, h (X ω) ∂μ := by
  have hri : Integrable (respInd R) μ :=
    (integrable_const 1).indicator (hR (measurableSet_singleton true))
  have hg : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      fun ω => h (X ω) / π (X ω) :=
    ((hh.div hπ).comp (comap_measurable X)).stronglyMeasurable
  have hcancel : (fun ω => π (X ω) * (h (X ω) / π (X ω))) =ᵐ[μ] fun ω => h (X ω) := by
    filter_upwards [hpos] with ω hω
    field_simp
  have hint := integrable_mul_of_condExp_eq hX.comap_le hri
    (Filter.Eventually.of_forall fun ω => respInd_nonneg R ω) hg hprop (hhi.congr hcancel.symm)
  have key := (integral_mul_eq_of_condExp_eq hX.comap_le hri hg hint hprop).2
  simp only [← mul_div_assoc] at hint key
  exact ⟨hint, key.trans (integral_congr_ae (by simpa only [← mul_div_assoc] using hcancel))⟩

/-- The augmented inverse probability weighted identity of Robins, Rotnitzky and Zhao (1994),
first robustness case: the propensity is correct. If `π ∘ X` is a version of `E[1{R} | X]`,
MAR holds in the mean-independence form, `π(X) > 0` almost surely, `Y` is integrable and
`h(X)` is any integrable function of the covariate, then
`E[1{R} Y / π(X) - (1{R} - π(X)) / π(X) h(X)] = E[Y]`. -/
theorem aipw_identity_of_propensity [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {π : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) (hYi : Integrable Y μ)
    {h : 𝒳 → ℝ} (hh : Measurable h) (hhi : Integrable (fun ω => h (X ω)) μ) :
    ∫ ω, (respInd R ω * Y ω / π (X ω) - (respInd R ω - π (X ω)) / π (X ω) * h (X ω)) ∂μ =
      ∫ ω, Y ω ∂μ := by
  obtain ⟨hint, hcov⟩ := ipw_identity_covariate hX hR hπ hprop hpos hh hhi
  have hrw : (fun ω => respInd R ω * Y ω / π (X ω) - (respInd R ω - π (X ω)) / π (X ω) *
      h (X ω)) =ᵐ[μ] fun ω => respInd R ω * Y ω / π (X ω) -
        respInd R ω * h (X ω) / π (X ω) + h (X ω) := by
    filter_upwards [hpos] with ω hω
    field_simp
    ring
  have hipw := integrable_ipw hX hY hR hπ hprop hmar hpos hYi
  have hA : Integrable (fun ω => respInd R ω * Y ω / π (X ω) -
      respInd R ω * h (X ω) / π (X ω)) μ := hipw.sub hint
  have e1 := integral_add hA hhi
  have e2 := integral_sub hipw hint
  rw [integral_congr_ae hrw, e1, e2, ipw_identity hX hY hR hπ hprop hmar hpos hYi, hcov]
  ring

/-- The augmented inverse probability weighted identity, second robustness case: the outcome
regression is correct. If `h(X)` is a version of `E[Y | X]`, MAR holds in the mean-independence
form and `π` is any measurable function with `π(X) > 0` almost surely (not necessarily the
response propensity), then `E[1{R} Y / π(X) - (1{R} - π(X)) / π(X) h(X)] = E[Y]`, provided the
weighted residual `1{R} (Y - h(X)) / π(X)` is integrable. Together with
`aipw_identity_of_propensity` this is the double robustness of the augmented estimator. -/
theorem aipw_identity_of_regression [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {π : 𝒳 → ℝ} (hπ : Measurable π) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω))
    (hmar : MARMean μ X Y R) (hYi : Integrable Y μ) {h : 𝒳 → ℝ} (hh : Measurable h)
    (hreg : μ[Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => h (X ω))
    (hint : Integrable (fun ω => respInd R ω * (Y ω - h (X ω)) / π (X ω)) μ) :
    ∫ ω, (respInd R ω * Y ω / π (X ω) - (respInd R ω - π (X ω)) / π (X ω) * h (X ω)) ∂μ =
      ∫ ω, Y ω ∂μ := by
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hri : Integrable (respInd R) μ :=
    (integrable_const 1).indicator (hR (measurableSet_singleton true))
  have hhm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] fun ω => h (X ω) :=
    (hh.comp (comap_measurable X)).stronglyMeasurable
  have hhi : Integrable (fun ω => h (X ω)) μ := integrable_condExp.congr hreg
  -- first step: condition on `(X, Y)`, replacing `1{R}` by `E[1{R} | X]`
  have hg : StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      fun ω => (Y ω - h (X ω)) / π (X ω) :=
    (measurable_comap_prod (h := fun q : 𝒳 × ℝ => (q.2 - h q.1) / π q.1)
      ((measurable_snd.sub (hh.comp measurable_fst)).div
        (hπ.comp measurable_fst))).stronglyMeasurable
  obtain ⟨hint₁, key₁⟩ := integral_mul_eq_of_condExp_eq (r := respInd R) hXY.comap_le hri hg
    (by simpa only [mul_div_assoc] using hint) hmar
  -- second step: condition on `X`, where the residual has conditional mean zero
  have hres : μ[fun ω => Y ω - h (X ω) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun _ => (0 : ℝ) := by
    filter_upwards [condExp_sub hYi hhi (MeasurableSpace.comap X inferInstance), hreg]
      with ω h1 h2
    change μ[Y - (fun ω => h (X ω)) | MeasurableSpace.comap X inferInstance] ω = 0
    rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable hX.comap_le hhm hhi, sub_self]
  have hg' : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      fun ω => (μ[respInd R | MeasurableSpace.comap X inferInstance]) ω / π (X ω) :=
    stronglyMeasurable_condExp.div ((hπ.comp (comap_measurable X)).stronglyMeasurable)
  have key₂ := (integral_mul_eq_of_condExp_eq (r := fun ω => Y ω - h (X ω)) hX.comap_le
    (hYi.sub hhi) hg' (hint₁.congr (Filter.Eventually.of_forall fun ω => by
      simp only; ring)) hres).2
  have hzero : ∫ ω, respInd R ω * (Y ω - h (X ω)) / π (X ω) ∂μ = 0 := by
    simp only [mul_div_assoc] at key₁ ⊢
    rw [key₁]
    calc ∫ ω, (μ[respInd R | MeasurableSpace.comap X inferInstance]) ω *
          ((Y ω - h (X ω)) / π (X ω)) ∂μ
        = ∫ ω, (Y ω - h (X ω)) *
          ((μ[respInd R | MeasurableSpace.comap X inferInstance]) ω / π (X ω)) ∂μ := by
          congr 1; funext ω; ring
      _ = 0 := by rw [key₂]; simp
  have hrw : (fun ω => respInd R ω * Y ω / π (X ω) - (respInd R ω - π (X ω)) / π (X ω) *
      h (X ω)) =ᵐ[μ] fun ω => respInd R ω * (Y ω - h (X ω)) / π (X ω) + h (X ω) := by
    filter_upwards [hpos] with ω hω
    field_simp
    ring
  rw [integral_congr_ae hrw, integral_add hint hhi, hzero, zero_add,
    ← integral_congr_ae hreg, integral_condExp hX.comap_le]

/-- Outcome regression (standardization) under MAR, almost everywhere form. Let `π ∘ X` be a
version of `E[1{R} | X]` and let `μ₁ : 𝒳 → ℝ` satisfy `E[1{R} Y | X] = π(X) μ₁(X)` almost
everywhere; on `{π(X) > 0}` this makes `μ₁(X)` a version of the complete-case regression
`E[Y | X, R = true]`, and it involves only observed quantities. Under the mean-independence
form of MAR, almost sure positivity of `π(X)` and integrability of `Y`, `μ₁(X)` is a version of
`E[Y | X]`. -/
theorem regression_ae_eq [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {π μ₁ : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) (hYi : Integrable Y μ)
    (hreg : μ[respInd R * Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => π (X ω) * μ₁ (X ω)) :
    (fun ω => μ₁ (X ω)) =ᵐ[μ] μ[Y | MeasurableSpace.comap X inferInstance] := by
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hri : Integrable (respInd R) μ :=
    (integrable_const 1).indicator (hR (measurableSet_singleton true))
  have hrYi : Integrable (respInd R * Y) μ := by
    refine Integrable.mono' hYi.norm
      ((measurable_respInd hR).mul hY).aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro ω
    rw [Pi.mul_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (respInd_nonneg R ω)]
    exact mul_le_of_le_one_left (abs_nonneg _) (respInd_le_one R ω)
  have hYm :
      StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance] Y :=
    (measurable_comap_prod (h := fun q : 𝒳 × ℝ => q.2) measurable_snd).stronglyMeasurable
  have hπm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] fun ω => π (X ω) :=
    (hπ.comp (comap_measurable X)).stronglyMeasurable
  -- `|π(X)| ≤ 1` almost everywhere, since `π(X)` is a version of `E[1{R} | X]`
  have hbd : ∀ᵐ ω ∂μ, ‖π (X ω)‖ ≤ (1 : ℝ) := by
    have h1 : ∀ᵐ ω ∂μ, |respInd R ω| ≤ (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => by
        rw [abs_of_nonneg (respInd_nonneg R ω)]; exact respInd_le_one R ω
    filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs
      (m := MeasurableSpace.comap X inferInstance) h1, hprop] with ω hω hω'
    rw [Real.norm_eq_abs, ← hω']; exact hω
  -- `E[1{R} Y | X] = π(X) E[Y | X]`
  have hstep : μ[respInd R * Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => π (X ω) * (μ[Y | MeasurableSpace.comap X inferInstance]) ω := by
    refine (condExp_condExp_of_le comap_le_comap_prod hXY.comap_le).symm.trans ?_
    have h1 : μ[respInd R * Y | MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
        =ᵐ[μ] fun ω => π (X ω) * Y ω :=
      (condExp_mul_of_stronglyMeasurable_right hYm hrYi hri).trans
        ((hmar.trans hprop).mul (by rfl))
    refine (condExp_congr_ae h1).trans ?_
    exact condExp_stronglyMeasurable_mul_of_bound hX.comap_le hπm hYi 1 hbd
  filter_upwards [hreg, hstep, hpos] with ω h1 h2 h3
  rw [h1] at h2
  exact mul_left_cancel₀ h3.ne' h2

/-- Outcome regression (standardization) under MAR. Under the hypotheses of `regression_ae_eq`,
`μ₁(X)` is a version of `E[Y | X]`, hence `E[μ₁(X)] = E[Y]`. -/
theorem regression_identity [IsFiniteMeasure μ] (hX : Measurable X) (hY : Measurable Y)
    (hR : Measurable R) {π μ₁ : 𝒳 → ℝ} (hπ : Measurable π)
    (hprop : μ[respInd R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => π (X ω))
    (hmar : MARMean μ X Y R) (hpos : ∀ᵐ ω ∂μ, 0 < π (X ω)) (hYi : Integrable Y μ)
    (hreg : μ[respInd R * Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      fun ω => π (X ω) * μ₁ (X ω)) :
    ∫ ω, μ₁ (X ω) ∂μ = ∫ ω, Y ω ∂μ := by
  rw [integral_congr_ae (regression_ae_eq hX hY hR hπ hprop hmar hpos hYi hreg),
    integral_condExp hX.comap_le]

/-- Inverse probability of censoring weighting. An outcome `Y` is observed only for the
uncensored units, `Δ ω = true`. If `K ∘ X` is a version of the probability `E[1{Δ} | X]` of
remaining uncensored given the baseline covariate `X`, censoring is noninformative in the
mean-independence sense `E[1{Δ} | X, Y] = E[1{Δ} | X]`, `K(X) > 0` almost surely, and the
weighted outcome is integrable, then `E[1{Δ} Y / K(X)] = E[Y]`. This is `ipw_identity` with the
uncensored indicator in the role of the response indicator. -/
theorem ipcw_identity [IsFiniteMeasure μ] {Δ : Ω → Bool} (hX : Measurable X) (hY : Measurable Y)
    (hΔ : Measurable Δ) {K : 𝒳 → ℝ} (hK : Measurable K)
    (hprop : μ[respInd Δ | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => K (X ω))
    (hnoninf : MARMean μ X Y Δ) (hpos : ∀ᵐ ω ∂μ, 0 < K (X ω))
    (hint : Integrable (fun ω => respInd Δ ω * Y ω / K (X ω)) μ) :
    ∫ ω, respInd Δ ω * Y ω / K (X ω) ∂μ = ∫ ω, Y ω ∂μ :=
  ipw_identity_of_integrable_weighted hX hY hΔ hK hprop hnoninf hpos hint

/-- Inverse probability of censoring weighting over two periods with a time-varying covariate.
A unit has baseline covariate `L₀`, a covariate `L₁` measured at time one, and outcome `Y`;
`R₁ ω = true` means the unit is uncensored at time one and `R₂ ω = true` that it is uncensored
at time two (so `Y` is observed). Assume:

* `h₁`: given `(L₀, L₁, Y)`, the probability of remaining uncensored at time one is `π₁(L₀)`,
  that is `E[1{R₁} | L₀, L₁, Y] = π₁(L₀)` (censoring at time one is noninformative given `L₀`,
  and `π₁(L₀)` is that probability);
* `h₂`: given `(L₀, L₁, Y, R₁)`, the probability of being uncensored at time two is
  `1{R₁} π₂(L₀, L₁)`, that is `E[1{R₂} | L₀, L₁, Y, R₁] = 1{R₁} π₂(L₀, L₁)` (units censored at
  time one stay censored, and among the others censoring at time two is noninformative given
  `(L₀, L₁)` with probability `π₂(L₀, L₁)` of remaining uncensored);
* positivity: `π₁(L₀) > 0` and `π₂(L₀, L₁) > 0` almost surely;
* the weighted outcome `1{R₂} Y / (π₁(L₀) π₂(L₀, L₁))` is integrable.

Then `E[1{R₂} Y / (π₁(L₀) π₂(L₀, L₁))] = E[Y]`. -/
theorem ipcw_identity_two_period [IsFiniteMeasure μ] {𝒴 : Type*} [MeasurableSpace 𝒴]
    {L₀ : Ω → 𝒳} {L₁ : Ω → 𝒴} {R₁ R₂ : Ω → Bool} (hL₀ : Measurable L₀) (hL₁ : Measurable L₁)
    (hY : Measurable Y) (hR₁ : Measurable R₁) (hR₂ : Measurable R₂) {π₁ : 𝒳 → ℝ}
    {π₂ : 𝒳 × 𝒴 → ℝ} (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂)
    (h₁ : μ[respInd R₁ | MeasurableSpace.comap (fun ω => (L₀ ω, L₁ ω, Y ω)) inferInstance]
      =ᵐ[μ] fun ω => π₁ (L₀ ω))
    (h₂ : μ[respInd R₂ |
        MeasurableSpace.comap (fun ω => (L₀ ω, L₁ ω, Y ω, R₁ ω)) inferInstance]
      =ᵐ[μ] fun ω => respInd R₁ ω * π₂ (L₀ ω, L₁ ω))
    (hpos₁ : ∀ᵐ ω ∂μ, 0 < π₁ (L₀ ω)) (hpos₂ : ∀ᵐ ω ∂μ, 0 < π₂ (L₀ ω, L₁ ω))
    (hint : Integrable (fun ω => respInd R₂ ω * Y ω / (π₁ (L₀ ω) * π₂ (L₀ ω, L₁ ω))) μ) :
    ∫ ω, respInd R₂ ω * Y ω / (π₁ (L₀ ω) * π₂ (L₀ ω, L₁ ω)) ∂μ = ∫ ω, Y ω ∂μ := by
  set V₁ : Ω → 𝒳 × 𝒴 × ℝ := fun ω => (L₀ ω, L₁ ω, Y ω)
  set V₂ : Ω → 𝒳 × 𝒴 × ℝ × Bool := fun ω => (L₀ ω, L₁ ω, Y ω, R₁ ω)
  have hV₁ : Measurable V₁ := hL₀.prodMk (hL₁.prodMk hY)
  have hV₂ : Measurable V₂ := hL₀.prodMk (hL₁.prodMk (hY.prodMk hR₁))
  -- second period: condition on `(L₀, L₁, Y, R₁)`
  have hg₂ : StronglyMeasurable[MeasurableSpace.comap V₂ inferInstance]
      (fun ω => Y ω / (π₁ (L₀ ω) * π₂ (L₀ ω, L₁ ω))) := by
    have hh : Measurable fun q : 𝒳 × 𝒴 × ℝ × Bool =>
        q.2.2.1 / (π₁ q.1 * π₂ (q.1, q.2.1)) :=
      measurable_snd.snd.fst.div
        ((hπ₁.comp measurable_fst).mul (hπ₂.comp (measurable_fst.prodMk measurable_snd.fst)))
    exact (hh.comp (comap_measurable V₂)).stronglyMeasurable
  have hint₂ : Integrable
      (fun ω => respInd R₂ ω * (Y ω / (π₁ (L₀ ω) * π₂ (L₀ ω, L₁ ω)))) μ := by
    simpa only [mul_div_assoc] using hint
  obtain ⟨hint₁', key₂⟩ := integral_mul_eq_of_condExp_eq (r := respInd R₂) hV₂.comap_le
    ((integrable_const 1).indicator (hR₂ (measurableSet_singleton true))) hg₂ hint₂ h₂
  -- the product weight collapses to the first period weight
  have hcollapse : (fun ω => respInd R₁ ω * π₂ (L₀ ω, L₁ ω) *
      (Y ω / (π₁ (L₀ ω) * π₂ (L₀ ω, L₁ ω)))) =ᵐ[μ]
      fun ω => respInd R₁ ω * (Y ω / π₁ (L₀ ω)) := by
    filter_upwards [hpos₁, hpos₂] with ω h1 h2
    field_simp
  -- first period: condition on `(L₀, L₁, Y)`
  have hg₁ : StronglyMeasurable[MeasurableSpace.comap V₁ inferInstance]
      (fun ω => Y ω / π₁ (L₀ ω)) := by
    have hh : Measurable fun q : 𝒳 × 𝒴 × ℝ => q.2.2 / π₁ q.1 :=
      measurable_snd.snd.div (hπ₁.comp measurable_fst)
    exact (hh.comp (comap_measurable V₁)).stronglyMeasurable
  have key₁ := (integral_mul_eq_of_condExp_eq (r := respInd R₁) hV₁.comap_le
    ((integrable_const 1).indicator (hR₁ (measurableSet_singleton true))) hg₁
    (hint₁'.congr hcollapse) h₁).2
  simp only [mul_div_assoc] at key₂ ⊢
  rw [key₂, integral_congr_ae hcollapse, key₁]
  refine integral_congr_ae ?_
  filter_upwards [hpos₁] with ω hω
  field_simp

end MissingData

end CausalInference
