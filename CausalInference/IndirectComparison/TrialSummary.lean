/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Constancy
public import CausalInference.PartialIdentification.Manski
public import Mathlib.Probability.Independence.Integration

/-!
# The aggregate data of a randomized trial

The aggregate data of a trial report, for each arm `t`, the mean outcome among the units
assigned to `t`, `E[Y | A = t]` (`Trial.armSummary`, a mean under the conditional measure
`μ[|A = t]`). In a randomized trial this is the arm mean `E[Y(t)]` of the trial population: if
the assignment `A` is measurable and independent of the potential outcome `Y(t)`, the arm `t` has
positive probability and `Y(t)` is integrable, then `E[Y | A = t] = E[Y(t)]`
(`Trial.armSummary_eq_armMean`). The proof: on `{A = t}` the observed outcome is `Y(t)`, and
`E[1{A = t} Y(t)] = P(A = t) E[Y(t)]` by independence.

Consequences:

* the aggregate contrast `g(E[Y | A = b]) - g(E[Y | A = a])` of a randomized trial is the
  marginal effect of `b` relative to `a` in its population (`Trial.aggregateContrast_eq`), and,
  with conditional mean functions of the two arms, it is `linkMarginal` of the covariate law of
  the trial (`Trial.aggregateContrast_eq_linkMarginal`);
* the indirect estimate formed from the aggregate data of a trial of `a` against `c` and a trial
  of `b` against `c` is the difference of the two trials' marginal effects
  (`indirectAggregate_eq`), and under constancy of the two contrasts against `c` it is the
  effect of `b` relative to `a` in every population of the family
  (`indirectAggregate_eq_of_constant`).

The instance: a trial on the product space `𝒳 × ι` with covariates and assignment drawn
independently (`productTrial`), where `E[Y | A = t] = ∫ m_t dν` (`productTrial_armSummary`), and
the two arm trial on a binary covariate with arm summaries `2` and `1/2` and aggregate mean
difference `3/2` (`productTrial_example`).

## Main definitions

* `Trial.aggregateContrast`, `indirectAggregate`, `productTrial`.

## Main results

* `Trial.armSummary_eq_armMean`, `Trial.aggregate_armMean_eq`, `Trial.aggregateContrast_eq`,
  `Trial.aggregateContrast_eq_linkMarginal`.
* `indirectAggregate_eq`, `indirectAggregate_eq_of_constant`.
* `productTrial_armSummary`, `productTrial_example`.

## References

* P. W. Holland, *Statistics and causal inference*, Journal of the American Statistical
  Association 81 (1986).
* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure

namespace Trial

variable {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace ι]

/-- The **aggregate contrast** of `b` relative to `a` on the scale `g` reported by a trial,
`g(E[Y | A = b]) - g(E[Y | A = a])`. -/
noncomputable def aggregateContrast (g : ℝ → ℝ) (T : Trial Ω 𝒳 ι) (a b : ι) : ℝ :=
  g (T.armSummary b) - g (T.armSummary a)

variable [MeasurableSingletonClass ι] {T : Trial Ω 𝒳 ι}

omit [MeasurableSpace 𝒳] in
/-- **The arm summary of a randomized trial is the arm mean.** If the assignment is measurable
and independent of `Y(t)`, `P(A = t) > 0` and `Y(t)` is integrable, then the observed outcome is
integrable in the arm `{A = t}` and `E[Y | A = t] = E[Y(t)]`. -/
theorem armSummary_eq_armMean [IsProbabilityMeasure T.μ] {t : ι} (hA : Measurable T.A)
    (hind : IndepFun T.A (T.Y t) T.μ) (hY : Integrable (T.Y t) T.μ)
    (ht : T.μ (T.A ⁻¹' {t}) ≠ 0) :
    Integrable T.obsOutcome (T.μ[|T.A ⁻¹' {t}]) ∧ T.armSummary t = T.toPopulation.armMean t := by
  set s := T.A ⁻¹' {t} with hs_def
  have hs : MeasurableSet s := hA (measurableSet_singleton t)
  have hae : T.obsOutcome =ᵐ[T.μ[|s]] T.Y t := by
    filter_upwards [ae_cond_mem hs] with ω hω
    simp only [hs_def, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [obsOutcome, hω]
  have hYc : Integrable (T.Y t) (T.μ[|s]) :=
    (hY.restrict).smul_measure (ENNReal.inv_ne_top.2 ht)
  refine ⟨hYc.congr hae.symm, ?_⟩
  set f : ι → ℝ := ({t} : Set ι).indicator fun _ => 1 with hf_def
  have hg : Measurable f := measurable_const.indicator (measurableSet_singleton t)
  have hmul := (hind.comp hg measurable_id).integral_mul_eq_mul_integral
    (hg.comp hA).aestronglyMeasurable hY.aestronglyMeasurable
  have hind1 : f ∘ T.A = s.indicator 1 := by
    funext ω
    by_cases h : T.A ω = t <;> simp [Set.indicator, hf_def, hs_def, h]
  have hset : ∫ ω in s, T.Y t ω ∂T.μ = ∫ ω, ((f ∘ T.A) * (id ∘ T.Y t)) ω ∂T.μ := by
    rw [← integral_indicator hs]
    congr 1
    funext ω
    by_cases h : T.A ω = t <;> simp [Set.indicator, hf_def, hs_def, h]
  have hne : T.μ.real s ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 ht
  have h := Manski.setIntegral_eq_measureReal_mul_cond s (T.Y t) (μ := T.μ)
  rw [hset, hmul, hind1, integral_indicator_one hs] at h
  rw [armSummary, integral_congr_ae hae, Population.armMean]
  exact mul_left_cancel₀ hne (h.symm.trans (by rfl))

omit [MeasurableSpace 𝒳] in
/-- **The aggregate data of a randomized trial report the arm means**: under the hypotheses of
`armSummary_eq_armMean`, the arm mean component of `T.aggregate φ` at `t` is `E[Y(t)]`, for any
covariate features `φ`. -/
theorem aggregate_armMean_eq [IsProbabilityMeasure T.μ] {p : ℕ} (φ : 𝒳 → Fin p → ℝ) {t : ι}
    (hA : Measurable T.A) (hind : IndepFun T.A (T.Y t) T.μ) (hY : Integrable (T.Y t) T.μ)
    (ht : T.μ (T.A ⁻¹' {t}) ≠ 0) : (T.aggregate φ).armMean t = T.toPopulation.armMean t :=
  (armSummary_eq_armMean hA hind hY ht).2

omit [MeasurableSpace 𝒳] in
/-- **The aggregate contrast of a randomized trial is the marginal effect of its population.**
For two arms `a, b`, each with assignment independent of its potential outcome, positive
probability and an integrable potential outcome, `g(E[Y | A = b]) - g(E[Y | A = a])` is
`g(E[Y(b)]) - g(E[Y(a)])`, whatever the scale `g`. -/
theorem aggregateContrast_eq [IsProbabilityMeasure T.μ] (g : ℝ → ℝ) {a b : ι}
    (hA : Measurable T.A) (hinda : IndepFun T.A (T.Y a) T.μ) (hindb : IndepFun T.A (T.Y b) T.μ)
    (hYa : Integrable (T.Y a) T.μ) (hYb : Integrable (T.Y b) T.μ)
    (ha : T.μ (T.A ⁻¹' {a}) ≠ 0) (hb : T.μ (T.A ⁻¹' {b}) ≠ 0) :
    T.aggregateContrast g a b = T.toPopulation.marginalEffect g a b := by
  rw [aggregateContrast, Population.marginalEffect, (armSummary_eq_armMean hA hinda hYa ha).2,
    (armSummary_eq_armMean hA hindb hYb hb).2]

/-- **The aggregate contrast of a randomized trial is `linkMarginal` of its covariate law.**
Under the hypotheses of `aggregateContrast_eq`, with measurable covariates and conditional mean
functions `m_a`, `m_b` of the two arms, the aggregate contrast is
`g(∫ m_b dP_X) - g(∫ m_a dP_X)`. -/
theorem aggregateContrast_eq_linkMarginal [IsProbabilityMeasure T.μ] (g : ℝ → ℝ) {a b : ι}
    {ma mb : 𝒳 → ℝ} (hA : Measurable T.A) (hX : Measurable T.X)
    (hinda : IndepFun T.A (T.Y a) T.μ) (hindb : IndepFun T.A (T.Y b) T.μ)
    (hYa : Integrable (T.Y a) T.μ) (hYb : Integrable (T.Y b) T.μ)
    (ha : T.μ (T.A ⁻¹' {a}) ≠ 0) (hb : T.μ (T.A ⁻¹' {b}) ≠ 0)
    (hma : T.IsCondMean a ma) (hmb : T.IsCondMean b mb) :
    T.aggregateContrast g a b = linkMarginal g T.covLaw ma mb := by
  rw [aggregateContrast_eq g hA hinda hindb hYa hYb ha hb,
    Population.marginalEffect_eq_linkMarginal g hX hYa hYb hma hmb]

end Trial

/-! ### The indirect estimate from two randomized trials -/

section Indirect

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The **indirect comparison of aggregate data**: the contrast of `c` relative to `a` reported
by the trial `T₁` minus the contrast of `c` relative to `b` reported by the trial `T₂`. -/
noncomputable def indirectAggregate {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (g : ℝ → ℝ) (T₁ : Trial Ω₁ 𝒳 ι) (T₂ : Trial Ω₂ 𝒳 ι) (a b c : ι) : ℝ :=
  T₁.aggregateContrast g a c - T₂.aggregateContrast g b c

omit [MeasurableSpace 𝒳] in
/-- **The indirect comparison of two randomized trials is the difference of their marginal
effects.** If `T₁` randomizes `a` and `c` and `T₂` randomizes `b` and `c` (each arm with
assignment independent of its potential outcome, positive probability and integrable potential
outcome), the indirect comparison of their aggregate data is
`d_ac(T₁) - d_bc(T₂)` for the populations of the two trials. -/
theorem indirectAggregate_eq {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (g : ℝ → ℝ) (T₁ : Trial Ω₁ 𝒳 ι) (T₂ : Trial Ω₂ 𝒳 ι) [IsProbabilityMeasure T₁.μ]
    [IsProbabilityMeasure T₂.μ] {a b c : ι} (hA₁ : Measurable T₁.A) (hA₂ : Measurable T₂.A)
    (hind₁a : IndepFun T₁.A (T₁.Y a) T₁.μ) (hind₁c : IndepFun T₁.A (T₁.Y c) T₁.μ)
    (hind₂b : IndepFun T₂.A (T₂.Y b) T₂.μ) (hind₂c : IndepFun T₂.A (T₂.Y c) T₂.μ)
    (hY₁a : Integrable (T₁.Y a) T₁.μ) (hY₁c : Integrable (T₁.Y c) T₁.μ)
    (hY₂b : Integrable (T₂.Y b) T₂.μ) (hY₂c : Integrable (T₂.Y c) T₂.μ)
    (h₁a : T₁.μ (T₁.A ⁻¹' {a}) ≠ 0) (h₁c : T₁.μ (T₁.A ⁻¹' {c}) ≠ 0)
    (h₂b : T₂.μ (T₂.A ⁻¹' {b}) ≠ 0) (h₂c : T₂.μ (T₂.A ⁻¹' {c}) ≠ 0) :
    indirectAggregate g T₁ T₂ a b c =
      T₁.toPopulation.marginalEffect g a c - T₂.toPopulation.marginalEffect g b c := by
  rw [indirectAggregate, Trial.aggregateContrast_eq g hA₁ hind₁a hind₁c hY₁a hY₁c h₁a h₁c,
    Trial.aggregateContrast_eq g hA₂ hind₂b hind₂c hY₂b hY₂c h₂b h₂c]

omit [MeasurableSpace 𝒳] in
/-- **The indirect comparison of two randomized trials under constancy.** Let the populations
`P j` have constant effects of `c` relative to `a` and relative to `b` on the scale `g`, and let
the randomized trials `T₁` (of `a` against `c`) and `T₂` (of `b` against `c`) have the
populations `P k` and `P l`. Then the indirect comparison of their aggregate data is the effect
of `b` relative to `a` in every population `P j`, the target included. -/
theorem indirectAggregate_eq_of_constant {J : Type*} {Ω : J → Type*}
    [∀ j, MeasurableSpace (Ω j)] {g : ℝ → ℝ} {P : ∀ j, Population (Ω j) 𝒳 ι} {a b c : ι}
    (hcon : ConstantRelativeEffects g P {(a, c), (b, c)}) (j : J) {k l : J}
    (T₁ : Trial (Ω k) 𝒳 ι) (T₂ : Trial (Ω l) 𝒳 ι) (hT₁ : T₁.toPopulation = P k)
    (hT₂ : T₂.toPopulation = P l) [IsProbabilityMeasure T₁.μ] [IsProbabilityMeasure T₂.μ]
    (hA₁ : Measurable T₁.A) (hA₂ : Measurable T₂.A)
    (hind₁a : IndepFun T₁.A (T₁.Y a) T₁.μ) (hind₁c : IndepFun T₁.A (T₁.Y c) T₁.μ)
    (hind₂b : IndepFun T₂.A (T₂.Y b) T₂.μ) (hind₂c : IndepFun T₂.A (T₂.Y c) T₂.μ)
    (hY₁a : Integrable (T₁.Y a) T₁.μ) (hY₁c : Integrable (T₁.Y c) T₁.μ)
    (hY₂b : Integrable (T₂.Y b) T₂.μ) (hY₂c : Integrable (T₂.Y c) T₂.μ)
    (h₁a : T₁.μ (T₁.A ⁻¹' {a}) ≠ 0) (h₁c : T₁.μ (T₁.A ⁻¹' {c}) ≠ 0)
    (h₂b : T₂.μ (T₂.A ⁻¹' {b}) ≠ 0) (h₂c : T₂.μ (T₂.A ⁻¹' {c}) ≠ 0) :
    indirectAggregate g T₁ T₂ a b c = (P j).marginalEffect g a b := by
  rw [indirectAggregate_eq g T₁ T₂ hA₁ hA₂ hind₁a hind₁c hind₂b hind₂c hY₁a hY₁c hY₂b hY₂c h₁a h₁c
    h₂b h₂c, hT₁, hT₂, marginalEffect_eq_sub_of_constant hcon j k l]

end Indirect

/-! ### Trials on a product space -/

section Product

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳] [MeasurableSpace ι]

/-- The **product trial**: covariates drawn from `ν` and the assignment from `π`, independently,
with potential outcomes `Y(t) = m_t(X)`. Its law is `ν ⊗ π` on `𝒳 × ι`. -/
noncomputable def productTrial (ν : Measure 𝒳) (π : Measure ι) (m : ι → 𝒳 → ℝ) :
    Trial (𝒳 × ι) 𝒳 ι :=
  ⟨⟨ν.prod π, Prod.fst, fun t ω => m t ω.1⟩, Prod.snd⟩

variable {ν : Measure 𝒳} {π : Measure ι} {m : ι → 𝒳 → ℝ}

instance [IsProbabilityMeasure ν] [IsProbabilityMeasure π] :
    IsProbabilityMeasure (productTrial ν π m).μ := by
  unfold productTrial; infer_instance

/-- The covariate law of the product trial is `ν`. -/
theorem productTrial_covLaw [IsProbabilityMeasure ν] [IsProbabilityMeasure π] :
    (productTrial ν π m).covLaw = ν := by
  simp [productTrial, Population.covLaw, Measure.map_fst_prod]

/-- In the product trial the assignment is independent of every potential outcome. -/
theorem productTrial_indepFun [IsProbabilityMeasure ν] [IsProbabilityMeasure π] {t : ι}
    (hm : Measurable (m t)) :
    IndepFun (productTrial ν π m).A ((productTrial ν π m).Y t) (productTrial ν π m).μ :=
  (indepFun_prod (μ := ν) (ν := π) hm measurable_id).symm

/-- The arm `t` of the product trial has probability `π {t}`. -/
theorem productTrial_measure_arm [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    [MeasurableSingletonClass ι] (t : ι) :
    (productTrial ν π m).μ ((productTrial ν π m).A ⁻¹' {t}) = π {t} := by
  have : (productTrial ν π m).A ⁻¹' {t} = Set.univ ×ˢ {t} := by
    ext ω; simp [productTrial]
  rw [this]
  change (ν.prod π) (Set.univ ×ˢ {t}) = π {t}
  rw [Measure.prod_prod, measure_univ, one_mul]

/-- A potential outcome of the product trial is integrable when `m_t` is integrable under `ν`. -/
theorem productTrial_integrable [IsProbabilityMeasure ν] [IsProbabilityMeasure π] {t : ι}
    (hm : Measurable (m t)) (hi : Integrable (m t) ν) :
    Integrable ((productTrial ν π m).Y t) (productTrial ν π m).μ := by
  have hmap : (ν.prod π).map Prod.fst = ν := by simp [Measure.map_fst_prod]
  exact (integrable_map_measure (μ := ν.prod π) hm.aestronglyMeasurable
    measurable_fst.aemeasurable).1 (hmap.symm ▸ hi)

/-- `m_t` is a conditional mean function of `Y(t)` in the product trial. -/
theorem productTrial_isCondMean [IsProbabilityMeasure ν] [IsProbabilityMeasure π] {t : ι}
    (hm : Measurable (m t)) (hi : Integrable (m t) ν) :
    (productTrial ν π m).IsCondMean t (m t) :=
  Population.isCondMean_of_eq_comp measurable_fst hm rfl (productTrial_integrable hm hi)

/-- **The arm summary of the product trial**: for an arm of positive probability under `π` and
a measurable `m_t` integrable under `ν`, `E[Y | A = t] = ∫ m_t dν`. -/
theorem productTrial_armSummary [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    [MeasurableSingletonClass ι] {t : ι} (hm : Measurable (m t)) (hi : Integrable (m t) ν)
    (ht : π {t} ≠ 0) : (productTrial ν π m).armSummary t = ∫ x, m t x ∂ν := by
  rw [(Trial.armSummary_eq_armMean measurable_snd (productTrial_indepFun hm)
      (productTrial_integrable hm hi) (by rwa [productTrial_measure_arm])).2,
    ← (productTrial_isCondMean hm hi).integral_eq measurable_fst (productTrial_integrable hm hi),
    productTrial_covLaw]

end Product

/-- **An instance with numbers.** A binary covariate with both levels of probability `1/2`, fair
assignment to the arms `false` and `true`, and conditional means `m_false = (0, 1)` and
`m_true = (1, 3)` at the levels `(false, true)`. The arm summaries are `1/2` and `2`, and the
aggregate mean difference `3/2` is the marginal mean difference of the trial population. -/
theorem productTrial_example :
    let m : Bool → Bool → ℝ := fun t x => if t then (if x then 3 else 1) else (if x then 1 else 0)
    (productTrial halfLaw halfLaw m).armSummary false = 1 / 2 ∧
      (productTrial halfLaw halfLaw m).armSummary true = 2 ∧
      (productTrial halfLaw halfLaw m).aggregateContrast id false true = 3 / 2 ∧
      (productTrial halfLaw halfLaw m).toPopulation.marginalEffect id false true = 3 / 2 := by
  intro m
  have hpos : ∀ t : Bool, halfLaw {t} ≠ 0 := fun t h => by
    have := (measure_eq_zero_iff_ae_notMem.1 h)
    exact (ae_halfLaw_iff.1 this) t rfl
  have hs : ∀ t, (productTrial halfLaw halfLaw m).armSummary t = (m t true + m t false) / 2 :=
    fun t => by
      rw [productTrial_armSummary (Measurable.of_discrete) (Integrable.of_finite) (hpos t),
        integral_halfLaw]
  have h0 : (productTrial halfLaw halfLaw m).armSummary false = 1 / 2 := by
    rw [hs]; norm_num [m]
  have h1 : (productTrial halfLaw halfLaw m).armSummary true = 2 := by
    rw [hs]; norm_num [m]
  have hc : (productTrial halfLaw halfLaw m).aggregateContrast id false true = 3 / 2 := by
    rw [Trial.aggregateContrast, h0, h1]; norm_num
  refine ⟨h0, h1, hc, ?_⟩
  rw [← Trial.aggregateContrast_eq id measurable_snd
    (productTrial_indepFun Measurable.of_discrete) (productTrial_indepFun Measurable.of_discrete)
    (productTrial_integrable Measurable.of_discrete Integrable.of_finite)
    (productTrial_integrable Measurable.of_discrete Integrable.of_finite)
    (by rw [productTrial_measure_arm]; exact hpos _)
    (by rw [productTrial_measure_arm]; exact hpos _), hc]

end IndirectComparison

end CausalInference
