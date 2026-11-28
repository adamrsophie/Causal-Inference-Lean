/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityWaldExamples

/-!
# Wald intervals with a random aggregate from an independent second sample

The aggregate comparator data are modeled by a second i.i.d. sample, independent of the index
trial: on the product `Ω₁ × Ω₂` with the product law `P₁ ⊗ P₂`, the index records are
`O i ∘ fst` and the aggregate is a function of the second coordinate. Both remain i.i.d., and
every statistic of the index records is independent of every statistic of the second sample.

In the two coin model of `WeightedConsistencyExamples`, with a second sample of fair coins
`B_i ∈ {0, 1}` whose sample mean `B̄ₙ` estimates `1/2` with variance `1/4`:

* the unanchored comparison `B̄ₙ - m̂ₙ` of the treated arm has limiting variance
  `σ_T² + 1/4 = 5/4`, and its 95% Wald interval covers `1/2 - 2` with probability tending to
  `0.95`;
* the anchored comparison `(m̂_false - m̂_true) - B̄ₙ` has limiting variance `9/4 + 1/4 = 5/2`,
  and its 95% Wald interval covers `(1/2 - 2) - 1/2` with probability tending to `0.95`.

## Main definitions

* `coinVal`: the value `1{b}` of a coin.

## Main results

* `isIIDSample_comp_fst_prod`, `isIIDSample_comp_snd_prod`: the two samples on the product.
* `indepFun_comp_fst_comp_snd`: independence of the two samples.
* `coin_sampleMean_tendstoInDistribution`: `√n (B̄ₙ - 1/2) → N(0, 1/4)` on the product.
* `example_twoSample_unanchored_coverage`, `example_twoSample_anchored_coverage`.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
* Stefanski, Boos, *The calculus of M-estimation* (2002).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology NNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

section TwoSamples

variable {Ω₁ Ω₂ 𝒪 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒪]
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]

/-- An i.i.d. sample stays i.i.d. along a measurable map that carries `μ` to the sample's law. -/
theorem isIIDSample_comp_of_map_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {O : ℕ → Ω → 𝒪} (hOm : ∀ i, Measurable (O i)) {e : Ω' → Ω} (he : Measurable e)
    {μ : Measure Ω'} [IsProbabilityMeasure μ] {P : Measure Ω} (hmap : μ.map e = P)
    (h : IsIIDSample O P) :
    IsIIDSample (fun i => O i ∘ e) μ where
  indep := by
    subst hmap
    have hm := h.indep
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => (hOm i).aemeasurable)] at hm
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => ((hOm i).comp he).aemeasurable)]
    have e1 : (fun ω i => (O i ∘ e) ω) = (fun ω i => O i ω) ∘ e := rfl
    rw [e1, ← Measure.map_map (measurable_pi_iff.2 hOm) he, hm]
    congr 1
    funext i
    rw [Measure.map_map (hOm i) he]
  ident i := ⟨((hOm i).comp he).aemeasurable, ((hOm 0).comp he).aemeasurable, by
    subst hmap
    rw [← Measure.map_map (hOm i) he, ← Measure.map_map (hOm 0) he]
    exact (h.ident i).map_eq⟩

/-- **The first sample on the product is i.i.d.** -/
theorem isIIDSample_comp_fst_prod {O : ℕ → Ω₁ → 𝒪} (hOm : ∀ i, Measurable (O i))
    (hO : IsIIDSample O P₁) :
    IsIIDSample (fun i (ω : Ω₁ × Ω₂) => O i ω.1) (P₁.prod P₂) :=
  isIIDSample_comp_of_map_eq hOm measurable_fst
    (by rw [Measure.map_fst_prod, measure_univ, one_smul]) hO

/-- **The second sample on the product is i.i.d.** -/
theorem isIIDSample_comp_snd_prod {O : ℕ → Ω₂ → 𝒪} (hOm : ∀ i, Measurable (O i))
    (hO : IsIIDSample O P₂) :
    IsIIDSample (fun i (ω : Ω₁ × Ω₂) => O i ω.2) (P₁.prod P₂) :=
  isIIDSample_comp_of_map_eq hOm measurable_snd
    (by rw [Measure.map_snd_prod, measure_univ, one_smul]) hO

/-- **The two samples are independent**: a measurable function of the first coordinate and a
measurable function of the second are independent under the product law. -/
theorem indepFun_comp_fst_comp_snd {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {F : Ω₁ → β} {G : Ω₂ → γ} (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun ω : Ω₁ × Ω₂ => F ω.1) (fun ω => G ω.2) (P₁.prod P₂) := by
  have h0 : IndepFun (Prod.fst : Ω₁ × Ω₂ → Ω₁) Prod.snd (P₁.prod P₂) := by
    rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ,
      measure_univ, one_smul, one_smul]
    exact Measure.map_id
  exact h0.comp hF hG

end TwoSamples

/-- The value `1{b}` of a coin. -/
def coinVal (b : Bool) : ℝ := if b then 1 else 0

theorem measurable_coinVal : Measurable coinVal := measurable_of_countable _

section Instance

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {O : ℕ → Ω₁ → Bool × Bool × ℝ} {Bc : ℕ → Ω₂ → Bool}

/-- The sample mean of the coins is asymptotically linear for `1/2`, with influence function
`1{b} - 1/2`, and `√n (B̄ₙ - 1/2) → N(0, 1/4)`. -/
theorem coin_sampleMean_tendstoInDistribution (hBm : ∀ i, Measurable (Bc i))
    (hB : IsIIDSample Bc P₂) (hlawB : P₂.map (Bc 0) = halfLaw) :
    TendstoInDistribution (fun (n : ℕ) (ω : Ω₁ × Ω₂) =>
      √n * (sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2) n ω - 1 / 2)) atTop
      (fun x : ℝ => x) (fun _ => P₁.prod P₂) (gaussianReal 0 (1 / 4 : ℝ).toNNReal) := by
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
  have hAL := sampleMean_isAsymptoticallyLinear (O := fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)
    measurable_coinVal hL2
  have hmean : ∫ ω, coinVal (Bc 0 ω.2) ∂(P₁.prod P₂) = 1 / 2 := by
    rw [hint]; norm_num [coinVal]
  rw [hmean] at hAL
  have hvar : ∫ ω, (coinVal (Bc 0 ω.2) - 1 / 2) ^ 2 ∂(P₁.prod P₂) = 1 / 4 := by
    rw [hint (fun b => (coinVal b - 1 / 2) ^ 2)]; norm_num [coinVal]
  have hmeas : ∀ n, AEMeasurable (sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2) n)
      (P₁.prod P₂) := fun n =>
    (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      measurable_coinVal.comp ((hBm i).comp measurable_snd))).aemeasurable
  exact hAL.tendstoInDistribution hB' hmeas (by rw [hvar]; exact HasLaw.id)

theorem measurable_sampleMean_coinVal (hBm : ∀ i, Measurable (Bc i)) (n : ℕ) :
    Measurable (sampleMean coinVal Bc n) :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_coinVal.comp (hBm i))

omit [IsProbabilityMeasure P₁] in
theorem map_comp_fst_prod (hOm : ∀ i, Measurable (O i)) :
    (P₁.prod P₂).map (fun ω : Ω₁ × Ω₂ => O 0 ω.1) = P₁.map (O 0) := by
  rw [show (fun ω : Ω₁ × Ω₂ => O 0 ω.1) = O 0 ∘ Prod.fst from rfl,
    ← Measure.map_map (hOm 0) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

theorem coe_toNNReal_quarter : (((1 / 4 : ℝ)).toNNReal : ℝ) = 1 / 4 :=
  Real.coe_toNNReal _ (by norm_num)

/-- **Unanchored comparison with a random aggregate.** The aggregate mean is the sample mean
`B̄ₙ` of an independent second sample of fair coins, estimating `1/2` with variance `1/4`. The
95% Wald interval built from `B̄ₙ - m̂ₙ` and `σ̂ₙ = √(σ̂_T² + 1/4)` covers `1/2 - 2` with
probability tending to `0.95`; the limiting variance is `1 + 1/4 = 5/4`. -/
theorem example_twoSample_unanchored_coverage (hOm : ∀ i, Measurable (O i))
    (hO : IsIIDSample O P₁) (hlaw : P₁.map (O 0) = exampleRecordLaw)
    (hBm : ∀ i, Measurable (Bc i)) (hB : IsIIDSample Bc P₂) (hlawB : P₂.map (Bc 0) = halfLaw)
    {z : ℝ} (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => (P₁.prod P₂).real {ω | 1 / 2 - 2 ∈
      waldInterval (unanchoredBalancedEstimate id exampleFeature exampleTarget
        (fun i (ω : Ω₁ × Ω₂) => O i ω.1)
        (sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) n ω)
        (unanchoredSdHat (fun _ => 1) exampleFeature exampleTarget
          (fun i (ω : Ω₁ × Ω₂) => O i ω.1) (fun _ _ => 1 / 4) n ω) z n}) atTop
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
    (by rw [coe_toNNReal_quarter]; exact tendstoInMeasure_const _) (fun _ => aemeasurable_const)
    (by rw [hlaw', example_weightedArmVariance_true, coe_toNNReal_quarter]; norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw', example_tiltArmMean_true] at h

/-- **Anchored comparison with a random aggregate.** The comparator contrast is the sample mean
`B̄ₙ` of an independent second sample of fair coins. The 95% Wald interval built from
`(m̂_false - m̂_true) - B̄ₙ` on the identity scale covers `(1/2 - 2) - 1/2` with probability
tending to `0.95`; the limiting variance is `9/4 + 1/4 = 5/2`. -/
theorem example_twoSample_anchored_coverage (hOm : ∀ i, Measurable (O i))
    (hO : IsIIDSample O P₁) (hlaw : P₁.map (O 0) = exampleRecordLaw)
    (hBm : ∀ i, Measurable (Bc i)) (hB : IsIIDSample Bc P₂) (hlawB : P₂.map (Bc 0) = halfLaw)
    {z : ℝ} (hzα : cdf (gaussianReal 0 1) z = 1 - 0.05 / 2) :
    Tendsto (fun n => (P₁.prod P₂).real {ω | 1 / 2 - 2 - 1 / 2 ∈
      waldInterval (anchoredBalancedEstimate id exampleFeature exampleTarget
        (fun i (ω : Ω₁ × Ω₂) => O i ω.1)
        (sampleMean coinVal (fun i (ω : Ω₁ × Ω₂) => Bc i ω.2)) n ω)
        (anchoredSdHat (fun _ => 1) (fun _ => 1) exampleFeature exampleTarget
          (fun i (ω : Ω₁ × Ω₂) => O i ω.1) (fun _ _ => 1 / 4) n ω) z n}) atTop
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
    (by rw [coe_toNNReal_quarter]; exact tendstoInMeasure_const _) (fun _ => aemeasurable_const)
    (by
      rw [hlaw', example_weightedArmVariance_false, example_weightedInfluenceCov,
        example_weightedArmVariance_true, coe_toNNReal_quarter]
      norm_num)
    (nonneg_of_cdf_gaussianReal_eq (by norm_num) hzα) hzα
  rwa [hlaw', example_tiltArmMean_false, example_tiltArmMean_true] at h

end Instance

end PopulationAdjustment

end CausalInference
