/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityWaldTwoSample
public import CausalInference.Estimation.VectorDeltaMethodExamples

/-!
# Wald intervals with an estimated aggregate variance

The coverage theorems `tendsto_unanchored_waldInterval_coverage` and
`tendsto_anchored_waldInterval_coverage` hold for any estimate `wHat` of the variance of the
aggregate that is consistent and measurable at each `n`. Here the aggregate comes from an
independent second sample, as in `WeightedNormalityWaldTwoSample`, and its variance is
estimated by the plug-in **sample variance** of that sample, `n⁻¹ ∑ Bᵢ² - B̄ₙ²`.

* `sampleVariance_isConsistent`: for an i.i.d. sample with a finite second moment, the plug-in
  sample variance is consistent for the variance (weak law of large numbers for the first two
  moments and the continuous mapping theorem).
* In the two coin model with a second sample of fair coins, the sample variance of the coins is
  consistent for `1/4` (`coin_sampleVariance_isConsistent`), and the 95% Wald intervals built
  with it cover with probability tending to `0.95`:
  `example_twoSample_unanchored_coverage_estimated`,
  `example_twoSample_anchored_coverage_estimated`. The limiting variances are unchanged,
  `5/4` and `5/2`.

## Main results

* `sampleVariance_isConsistent`, `aemeasurable_sampleVariance`,
  `coin_sampleVariance_isConsistent`, `example_twoSample_unanchored_coverage_estimated`,
  `example_twoSample_anchored_coverage_estimated`.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology NNReal

namespace CausalInference

/-- **Consistency of the plug-in sample variance**: if `O` is an i.i.d. sample under a
probability measure `μ`, `f` is measurable and `f (O 0)` has a finite second moment, then
`n⁻¹ ∑ f(Oᵢ)² - (n⁻¹ ∑ f(Oᵢ))²` is consistent for `Var f (O 0)`. -/
theorem sampleVariance_isConsistent {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) :
    IsConsistent (sampleVariance f O) (Var[fun ω ↦ f (O 0 ω); μ]) μ := by
  have h1 := sampleMean_isConsistent hO (hf.pow_const 2) hf2.integrable_sq
  have h2 := sampleMean_isConsistent hO hf (hf2.integrable one_le_two)
  have hg : Continuous (Function.uncurry fun a b : ℝ ↦ a - b ^ 2) :=
    continuous_fst.sub (continuous_snd.pow 2)
  have h3 := h1.comp₂ hg.continuousAt h2
  have hX : (fun ω ↦ f (O 0 ω)) ^ 2 = fun ω ↦ f (O 0 ω) ^ 2 := by
    ext ω
    simp only [Pi.pow_apply]
  rw [variance_eq_sub hf2, hX]
  exact h3

/-- The plug-in sample variance of measurable observations is measurable at each `n`. -/
theorem aemeasurable_sampleVariance {Ω 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    {μ : Measure Ω} {O : ℕ → Ω → 𝒪} (hOm : ∀ i, Measurable (O i)) {f : 𝒪 → ℝ}
    (hf : Measurable f) (n : ℕ) : AEMeasurable (sampleVariance f O n) μ := by
  have h1 : Measurable (sampleMean (fun z ↦ f z ^ 2) O n) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => (hf.pow_const 2).comp (hOm i))
  have h2 : Measurable (sampleMean f O n) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hf.comp (hOm i))
  exact (h1.sub (h2.pow_const 2)).aemeasurable

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {O : ℕ → Ω₁ → Bool × Bool × ℝ} {Bc : ℕ → Ω₂ → Bool}

/-- **The sample variance of fair coins is consistent for `1/4`**, on the product of the two
sample spaces. -/
theorem coin_sampleVariance_isConsistent (hBm : ∀ i, Measurable (Bc i))
    (hB : IsIIDSample Bc P₂) (hlawB : P₂.map (Bc 0) = halfLaw) :
    IsConsistent (sampleVariance coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) (1 / 4)
      (P₁.prod P₂) := by
  have hB' := isIIDSample_comp_snd_prod (P₁ := P₁) hBm hB
  have hmap : (P₁.prod P₂).map (Bc 0 ∘ Prod.snd) = halfLaw := by
    rw [← hlawB, ← Measure.map_map (hBm 0) measurable_snd, Measure.map_snd_prod, measure_univ,
      one_smul]
  have hint : ∀ f : Bool → ℝ, ∫ ω, f (Bc 0 ω.2) ∂(P₁.prod P₂) = (f true + f false) / 2 := by
    intro f
    have h := integral_map (μ := P₁.prod P₂) ((hBm 0).comp measurable_snd).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable
    rw [hmap, integral_halfLaw] at h
    exact h.symm
  have hL2 : MemLp (fun ω : Ω₁ × Ω₂ => coinVal (Bc 0 ω.2)) 2 (P₁.prod P₂) :=
    MemLp.of_bound (measurable_coinVal.comp ((hBm 0).comp measurable_snd)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        unfold coinVal; split_ifs <;> norm_num)
  have h := sampleVariance_isConsistent hB' measurable_coinVal hL2
  have hvar : Var[fun ω : Ω₁ × Ω₂ => coinVal (Bc 0 ω.2); P₁.prod P₂] = 1 / 4 := by
    rw [variance_eq_sub hL2]
    have e : (fun ω : Ω₁ × Ω₂ => coinVal (Bc 0 ω.2)) ^ 2 =
        fun ω => (fun b => coinVal b ^ 2) (Bc 0 ω.2) := by
      ext ω; simp only [Pi.pow_apply]
    rw [e, hint, hint]
    norm_num [coinVal]
  rwa [hvar] at h

/-- **Unanchored comparison with an estimated aggregate variance.** As in
`example_twoSample_unanchored_coverage`, with the constant `1/4` replaced by the sample variance
of the second sample. The 95% Wald interval built from `B̄ₙ - m̂ₙ` and
`σ̂ₙ = √(σ̂_T² + n⁻¹ ∑ Bᵢ² - B̄ₙ²)` covers `1/2 - 2` with probability tending to `0.95`. -/
theorem example_twoSample_unanchored_coverage_estimated (hOm : ∀ i, Measurable (O i))
    (hO : IsIIDSample O P₁) (hlaw : P₁.map (O 0) = exampleRecordLaw)
    (hBm : ∀ i, Measurable (Bc i)) (hB : IsIIDSample Bc P₂) (hlawB : P₂.map (Bc 0) = halfLaw)
    {z : ℝ} (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => (P₁.prod P₂).real {ω | 1 / 2 - 2 ∈
      waldInterval (unanchoredBalancedEstimate id exampleFeature exampleTarget
        (fun i (ω : Ω₁ × Ω₂) => O i ω.1)
        (sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) n ω)
        (unanchoredSdHat (fun _ => 1) exampleFeature exampleTarget
          (fun i (ω : Ω₁ × Ω₂) => O i ω.1)
          (sampleVariance coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) n ω) z n}) atTop
      (𝓝 (1 - 0.05)) := by
  have hO' := isIIDSample_comp_fst_prod (P₂ := P₂) hOm hO
  have hlaw' : (P₁.prod P₂).map (fun ω : Ω₁ × Ω₂ => O 0 ω.1) = exampleRecordLaw := by
    rw [map_comp_fst_prod hOm, hlaw]
  have h := tendsto_unanchored_waldInterval_coverage hO' measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw']; exact example_margin)
    (by rw [hlaw', example_prob_arm]; norm_num) (by rw [hlaw']; exact example_memLp_outcome)
    (g := id) (dg := fun _ => 1) measurable_id measurable_const (hasDerivAt_id _)
    continuousAt_const (mB := sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2))
    (mB₀ := 1 / 2)
    (fun n => indepFun_comp_fst_comp_snd (F := fun ω (i : Fin n) => O i ω)
      (measurable_pi_iff.2 fun i => hOm i) (measurable_sampleMean_coinVal hBm n))
    (coin_sampleMean_tendstoInDistribution hBm hB hlawB) HasLaw.id
    (by rw [coe_toNNReal_quarter]; exact coin_sampleVariance_isConsistent hBm hB hlawB)
    (aemeasurable_sampleVariance (fun i => (hBm i).comp measurable_snd) measurable_coinVal)
    (by rw [hlaw', example_weightedArmVariance_true, coe_toNNReal_quarter]; norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw', example_tiltArmMean_true] at h

/-- **Anchored comparison with an estimated aggregate variance.** As in
`example_twoSample_anchored_coverage`, with the constant `1/4` replaced by the sample variance of
the second sample. The 95% Wald interval built from `(m̂_false - m̂_true) - B̄ₙ` covers
`(1/2 - 2) - 1/2` with probability tending to `0.95`. -/
theorem example_twoSample_anchored_coverage_estimated (hOm : ∀ i, Measurable (O i))
    (hO : IsIIDSample O P₁) (hlaw : P₁.map (O 0) = exampleRecordLaw)
    (hBm : ∀ i, Measurable (Bc i)) (hB : IsIIDSample Bc P₂) (hlawB : P₂.map (Bc 0) = halfLaw)
    {z : ℝ} (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => (P₁.prod P₂).real {ω | 1 / 2 - 2 - 1 / 2 ∈
      waldInterval (anchoredBalancedEstimate id exampleFeature exampleTarget
        (fun i (ω : Ω₁ × Ω₂) => O i ω.1)
        (sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) n ω)
        (anchoredSdHat (fun _ => 1) (fun _ => 1) exampleFeature exampleTarget
          (fun i (ω : Ω₁ × Ω₂) => O i ω.1)
          (sampleVariance coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) n ω) z n}) atTop
      (𝓝 (1 - 0.05)) := by
  have hO' := isIIDSample_comp_fst_prod (P₂ := P₂) hOm hO
  have hlaw' : (P₁.prod P₂).map (fun ω : Ω₁ × Ω₂ => O 0 ω.1) = exampleRecordLaw := by
    rw [map_comp_fst_prod hOm, hlaw]
  have hagg := (coin_sampleMean_tendstoInDistribution (P₁ := P₁) hBm hB hlawB).continuous_comp
    continuous_neg
  have hagg' : TendstoInDistribution (fun (n : ℕ) (ω : Ω₁ × Ω₂) =>
      √n * (1 / 2 - sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2) n ω)) atTop
      (fun x : ℝ => -x) (fun _ => P₁.prod P₂) (gaussianReal 0 (1 / 4 : ℝ).toNNReal) :=
    hagg.congr (fun n => ae_of_all _ fun ω => by simp only [Function.comp_apply]; ring)
      (ae_eq_refl _)
  have hY : HasLaw (fun x : ℝ => -x) (gaussianReal 0 (1 / 4 : ℝ).toNNReal)
      (gaussianReal 0 (1 / 4 : ℝ).toNNReal) :=
    ⟨measurable_neg.aemeasurable, by rw [gaussianReal_map_neg, neg_zero]⟩
  have h := tendsto_anchored_waldInterval_coverage hO' measurable_exampleFeature
    example_bound (by norm_num : (0 : ℝ) < 1 / 2) (by rw [hlaw']; exact example_margin)
    (fun a => by rw [hlaw', example_prob_arm]; norm_num)
    (by rw [hlaw']; exact example_memLp_outcome)
    (g := id) (dgF := fun _ => 1) (dgT := fun _ => 1) measurable_id measurable_const
    measurable_const (hasDerivAt_id _) (hasDerivAt_id _) continuousAt_const continuousAt_const
    (dBC := sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) (d := 1 / 2)
    (fun n => indepFun_comp_fst_comp_snd (F := fun ω (i : Fin n) => O i ω)
      (measurable_pi_iff.2 fun i => hOm i) (measurable_sampleMean_coinVal hBm n)) hagg' hY
    (by rw [coe_toNNReal_quarter]; exact coin_sampleVariance_isConsistent hBm hB hlawB)
    (aemeasurable_sampleVariance (fun i => (hBm i).comp measurable_snd) measurable_coinVal)
    (by
      rw [hlaw', example_weightedArmVariance_false, example_weightedInfluenceCov,
        example_weightedArmVariance_true, coe_toNNReal_quarter]
      norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw', example_tiltArmMean_false, example_tiltArmMean_true] at h

end PopulationAdjustment

end CausalInference
