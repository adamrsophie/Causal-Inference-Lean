/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationIdentification
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The anchored identification theorem

The anchored setting (`IndirectComparison.AnchoredSetting`) has a trial of `a` against the common
comparator `c` (individual data), a trial of `b` against `c` (aggregate data) and a target
population, all with covariates in `𝒳`. Write `m₁`, `m₂`, `m` for conditional mean functions
of the arms in the first trial, the second trial and the target, `τ¹_ac = g(m₁ c) - g(m₁ a)` and
`τ²_bc = g(m₂ c) - g(m₂ b)` for the two trial contrasts on the scale `g`, and `Q_X` for the
target covariate law. The anchored estimand is
`anchoredEstimand Q_X τ¹_ac τ²_bc = ∫ τ¹_ac dQ_X - ∫ τ²_bc dQ_X`.

The assumptions (`AnchoredSetting.IdentificationAssumptions`): measurable covariates; integrable
potential outcomes of the arms used; conditional mean functions with values almost surely in the
domain `D` of the link; conditional constancy of the relative effect of `c` against `a` from the
first trial to the target and of `c` against `b` from the second trial to the target
(`IndirectComparison.RelativeConstancy`); overlap `Q_X ≪ P_X` with each trial; and integrable
trial contrasts under `Q_X`.

* **(a) Conditional transport** (`AnchoredSetting.IdentificationAssumptions.identification`):
  `τ¹_ac = τ_ac` and `τ²_bc = τ_bc` almost everywhere under `Q_X`, so
  `τ_ab = τ¹_ac - τ²_bc` almost everywhere under `Q_X`.
* **(b) Recovery of the average conditional effect** (same theorem): each standardized trial
  contrast is the target average conditional effect against `c`, and the anchored estimand is the
  target average conditional effect `Δ_ab(Q) = ∫ τ_ab dQ_X`, also in the form of density ratio
  weighted trial means.
* **(c) Recovery of the marginal effect.** On a directly collapsible scale, or on a collapsible
  scale when the target conditional effect is constant, the anchored estimand is the target
  marginal effect (`AnchoredSetting.IdentificationAssumptions.anchoredEstimand_eq_marginalEffect`).
  Under absolute constancy of the four trial arms the marginal effect is recovered on every scale,
  by the difference of the standardized marginal contrasts
  (`AnchoredSetting.marginalEffect_eq_of_structurallyInvariant`).
* **(d) A non collapsible scale.** On every scale that is not collapsible there is an anchored
  setting satisfying all the assumptions, with a constant conditional effect, in which the
  anchored estimand is not the target marginal effect
  (`AnchoredSetting.exists_anchoredEstimand_ne_marginalEffect`). Concrete models for all parts
  are in the module `CausalInference.PopulationAdjustment.AnchoredWitnesses`.
* **(e) An omitted covariate.** If the adjustment set is `X` while the full covariate is `(X, W)`,
  and the joint law of `(X, W)` is the law of `X` composed with a Markov kernel `κ`, the
  conditional mean given `X` is the `κ`-average of the conditional mean given `(X, W)`
  (`Population.IsCondMean.kernelAverage`). The estimand computed from the reduced means misses the
  target by the residual `∫∫ τ(x, w) (κ_src x - κ_* x)(dw) dν(x)`
  (`integral_kernelAverage_sub_integral_compProd`); on the identity scale the anchored bias is the
  difference of the two residuals of the trials
  (`anchoredEstimand_kernelAverage_sub_integral_compProd`), and it vanishes when `W` is balanced
  given `X`.

**Collapsibility on any covariate space.** `EffectMeasure.LinkCollapsible` and
`EffectMeasure.LinkDirectlyCollapsible` quantify over covariate types in the lowest universe;
`LinkCollapsible.apply` and `LinkDirectlyCollapsible.apply` apply them on any covariate space by
passing to the joint law of the two means on `ℝ × ℝ`, for a measurable link and a measurable
domain.

Where the parts come from: (a) is `IndirectComparison.RelativeConstancy.ae_eq` and
`IndirectComparison.linkContrast_eq_sub`; (b) is
`IndirectComparison.linkConditional_eq_of_relativeConstancy` and
`IndirectComparison.linkConditional_eq_sub`; the marginal form under absolute constancy is
`PopulationAdjustment.marginalEffect_eq_linkMarginal_of_structurallyInvariant`.

## Main definitions

* `AnchoredSetting.IdentificationAssumptions`.
* `Population.fstCovariate`: the population with the reduced adjustment set.

## Main results

* `LinkCollapsible.apply`, `LinkDirectlyCollapsible.apply`.
* `AnchoredSetting.IdentificationAssumptions.identification`,
  `AnchoredSetting.IdentificationAssumptions.anchoredEstimand_eq_marginalEffect`,
  `AnchoredSetting.marginalEffect_eq_of_structurallyInvariant`,
  `AnchoredSetting.exists_anchoredEstimand_ne_marginalEffect`.
* `Population.IsCondMean.kernelAverage`, `integral_kernelAverage_sub_integral_compProd`,
  `anchoredEstimand_kernelAverage_sub_integral_compProd`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison Transport

/-! ### Collapsibility on any covariate space -/

section Collapsible

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {D : Set ℝ} {g : ℝ → ℝ} {ν : Measure 𝒳}
  [IsProbabilityMeasure ν] {a b : 𝒳 → ℝ}

/-- **Collapsibility on any covariate space.** If the effect measure on the measurable scale `g`
is collapsible for means in the measurable set `D`, then for every probability law `ν` on any
covariate space, integrable means `a, b` with values almost surely in `D` and a conditional
effect almost surely equal to `c`, the marginal effect is `c`. The definition is applied to the
joint law of `(a, b)` on `ℝ × ℝ`. -/
theorem _root_.CausalInference.EffectMeasure.LinkCollapsible.apply (h : LinkCollapsible D g)
    (hD : MeasurableSet D) (hg : Measurable g) (ha : Integrable a ν) (hb : Integrable b ν)
    (hab : ∀ᵐ x ∂ν, a x ∈ D ∧ b x ∈ D) {c : ℝ} (hc : ∀ᵐ x ∂ν, linkContrast g a b x = c) :
    linkMarginal g ν a b = c := by
  have hm : AEMeasurable (fun x => (a x, b x)) ν :=
    ha.aemeasurable.prodMk hb.aemeasurable
  have : IsProbabilityMeasure (ν.map fun x => (a x, b x)) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  have key := h (ℝ × ℝ) (ν.map fun x => (a x, b x)) Prod.fst Prod.snd
    ((integrable_map_measure measurable_fst.aestronglyMeasurable hm).2 ha)
    ((integrable_map_measure measurable_snd.aestronglyMeasurable hm).2 hb)
    ((ae_map_iff hm ((measurable_fst hD).inter (measurable_snd hD))).2 hab) c
    ((ae_map_iff hm (measurableSet_eq_fun
      ((hg.comp measurable_snd).sub (hg.comp measurable_fst)) measurable_const)).2 hc)
  rwa [linkMarginal, integral_map hm measurable_snd.aestronglyMeasurable,
    integral_map hm measurable_fst.aestronglyMeasurable] at key

/-- **Direct collapsibility on any covariate space.** If the effect measure on the measurable
scale `g` is directly collapsible for means in the measurable set `D`, then for every probability
law on any covariate space and integrable means with values almost surely in `D` and an
integrable conditional effect, the marginal effect is the average conditional effect. -/
theorem _root_.CausalInference.EffectMeasure.LinkDirectlyCollapsible.apply
    (h : LinkDirectlyCollapsible D g) (hD : MeasurableSet D) (hg : Measurable g)
    (ha : Integrable a ν) (hb : Integrable b ν) (hab : ∀ᵐ x ∂ν, a x ∈ D ∧ b x ∈ D)
    (hτ : Integrable (linkContrast g a b) ν) :
    linkMarginal g ν a b = linkConditional g ν a b := by
  have hm : AEMeasurable (fun x => (a x, b x)) ν :=
    ha.aemeasurable.prodMk hb.aemeasurable
  have : IsProbabilityMeasure (ν.map fun x => (a x, b x)) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 inferInstance
  have hτm : Measurable (linkContrast g (Prod.fst : ℝ × ℝ → ℝ) Prod.snd) :=
    (hg.comp measurable_snd).sub (hg.comp measurable_fst)
  have key := h (ℝ × ℝ) (ν.map fun x => (a x, b x)) Prod.fst Prod.snd
    ((integrable_map_measure measurable_fst.aestronglyMeasurable hm).2 ha)
    ((integrable_map_measure measurable_snd.aestronglyMeasurable hm).2 hb)
    ((ae_map_iff hm ((measurable_fst hD).inter (measurable_snd hD))).2 hab)
    ((integrable_map_measure hτm.aestronglyMeasurable hm).2 hτ)
  rwa [linkMarginal, linkConditional, integral_map hm measurable_snd.aestronglyMeasurable,
    integral_map hm measurable_fst.aestronglyMeasurable,
    integral_map hm hτm.aestronglyMeasurable] at key

end Collapsible

end PopulationAdjustment

/-! ### The assumptions and parts (a) and (b) -/

namespace IndirectComparison.AnchoredSetting

open MeasureTheory ProbabilityTheory EffectMeasure Transport PopulationAdjustment

section Anchored

variable {Ω₁ Ω₂ Ω₃ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
  [MeasurableSpace 𝒳]

/-- The **assumptions of the anchored identification theorem** on the scale `g` with domain `D`,
for conditional mean functions `m₁` in the trial of `a` against `c`, `m₂` in the trial of `b`
against `c`, and `m` in the target. -/
structure IdentificationAssumptions
    (S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι) (g : ℝ → ℝ) (D : Set ℝ) (m₁ m₂ m : ι → 𝒳 → ℝ) :
    Prop where
  /-- The covariates of the first trial are measurable. -/
  measurable_ipd : Measurable S.ipdTrial.X
  /-- The covariates of the second trial are measurable. -/
  measurable_agd : Measurable S.agdTrial.X
  /-- The target covariates are measurable. -/
  measurable_target : Measurable S.target.X
  /-- `Y(a)` is integrable in the first trial. -/
  integrable_ipd_a : Integrable (S.ipdTrial.Y S.a) S.ipdTrial.μ
  /-- `Y(c)` is integrable in the first trial. -/
  integrable_ipd_c : Integrable (S.ipdTrial.Y S.c) S.ipdTrial.μ
  /-- `Y(b)` is integrable in the second trial. -/
  integrable_agd_b : Integrable (S.agdTrial.Y S.b) S.agdTrial.μ
  /-- `Y(c)` is integrable in the second trial. -/
  integrable_agd_c : Integrable (S.agdTrial.Y S.c) S.agdTrial.μ
  /-- The target potential outcomes of the three arms are integrable. -/
  integrable_target : ∀ t ∈ ({S.a, S.b, S.c} : Set ι), Integrable (S.target.Y t) S.target.μ
  /-- `m₁ a` is a conditional mean function of `Y(a)` in the first trial. -/
  isCondMean_ipd_a : S.ipdTrial.IsCondMean S.a (m₁ S.a)
  /-- `m₁ c` is a conditional mean function of `Y(c)` in the first trial. -/
  isCondMean_ipd_c : S.ipdTrial.IsCondMean S.c (m₁ S.c)
  /-- `m₂ b` is a conditional mean function of `Y(b)` in the second trial. -/
  isCondMean_agd_b : S.agdTrial.IsCondMean S.b (m₂ S.b)
  /-- `m₂ c` is a conditional mean function of `Y(c)` in the second trial. -/
  isCondMean_agd_c : S.agdTrial.IsCondMean S.c (m₂ S.c)
  /-- `m t` is a conditional mean function of `Y(t)` in the target, for the three arms. -/
  isCondMean_target : ∀ t ∈ ({S.a, S.b, S.c} : Set ι), S.target.IsCondMean t (m t)
  /-- The trial means lie in the domain of the link in the first trial. -/
  mem_ipd : ∀ᵐ x ∂S.ipdTrial.covLaw, m₁ S.a x ∈ D ∧ m₁ S.c x ∈ D
  /-- The trial means lie in the domain of the link in the second trial. -/
  mem_agd : ∀ᵐ x ∂S.agdTrial.covLaw, m₂ S.b x ∈ D ∧ m₂ S.c x ∈ D
  /-- The target means lie in the domain of the link. -/
  mem_target : ∀ᵐ x ∂S.target.covLaw, m S.a x ∈ D ∧ m S.b x ∈ D ∧ m S.c x ∈ D
  /-- Conditional constancy of the effect of `c` against `a` from the first trial to the
  target. -/
  relativeConstancy_ipd : RelativeConstancy g S.ipdTrial.toPopulation S.target S.a S.c
  /-- Conditional constancy of the effect of `c` against `b` from the second trial to the
  target. -/
  relativeConstancy_agd : RelativeConstancy g S.agdTrial.toPopulation S.target S.b S.c
  /-- Overlap of the target with the first trial. -/
  overlap_ipd : S.target.covLaw ≪ S.ipdTrial.covLaw
  /-- Overlap of the target with the second trial. -/
  overlap_agd : S.target.covLaw ≪ S.agdTrial.covLaw
  /-- The contrast of the first trial is integrable under the target covariate law. -/
  integrable_ipd_contrast : Integrable (linkContrast g (m₁ S.a) (m₁ S.c)) S.target.covLaw
  /-- The contrast of the second trial is integrable under the target covariate law. -/
  integrable_agd_contrast : Integrable (linkContrast g (m₂ S.b) (m₂ S.c)) S.target.covLaw

namespace IdentificationAssumptions

variable {S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι} {g : ℝ → ℝ} {D : Set ℝ} {m₁ m₂ m : ι → 𝒳 → ℝ}

/-- The target conditional mean function of arm `a`. -/
theorem target_a (h : S.IdentificationAssumptions g D m₁ m₂ m) :
    S.target.IsCondMean S.a (m S.a) := h.isCondMean_target S.a (by simp)

/-- The target conditional mean function of arm `b`. -/
theorem target_b (h : S.IdentificationAssumptions g D m₁ m₂ m) :
    S.target.IsCondMean S.b (m S.b) := h.isCondMean_target S.b (by simp)

/-- The target conditional mean function of arm `c`. -/
theorem target_c (h : S.IdentificationAssumptions g D m₁ m₂ m) :
    S.target.IsCondMean S.c (m S.c) := h.isCondMean_target S.c (by simp)

/-- **The anchored identification theorem, parts (a) and (b).** Under the assumptions, with
finite measures and a measurable link:

* (a) the trial contrasts are the target contrasts almost everywhere under the target covariate
  law, `τ¹_ac = τ_ac` and `τ²_bc = τ_bc`, so `τ_ab = τ¹_ac - τ²_bc`;
* (b) each standardized trial contrast is the target average conditional effect against `c`,
  the anchored estimand `∫ τ¹_ac dQ_X - ∫ τ²_bc dQ_X` is the target average conditional effect
  of `b` relative to `a`, and it is the difference of the density ratio weighted trial means
  `E₁[w₁(X) τ¹_ac(X)] - E₂[w₂(X) τ²_bc(X)]`. -/
theorem identification [IsFiniteMeasure S.ipdTrial.μ] [IsFiniteMeasure S.agdTrial.μ]
    [IsFiniteMeasure S.target.μ] (hg : Measurable g) (h : S.IdentificationAssumptions g D m₁ m₂ m) :
    (∀ᵐ x ∂S.target.covLaw,
        linkContrast g (m₁ S.a) (m₁ S.c) x = linkContrast g (m S.a) (m S.c) x) ∧
      (∀ᵐ x ∂S.target.covLaw,
        linkContrast g (m₂ S.b) (m₂ S.c) x = linkContrast g (m S.b) (m S.c) x) ∧
      (∀ᵐ x ∂S.target.covLaw, linkContrast g (m S.a) (m S.b) x =
        linkContrast g (m₁ S.a) (m₁ S.c) x - linkContrast g (m₂ S.b) (m₂ S.c) x) ∧
      ∫ x, linkContrast g (m₁ S.a) (m₁ S.c) x ∂S.target.covLaw =
        linkConditional g S.target.covLaw (m S.a) (m S.c) ∧
      ∫ x, linkContrast g (m₂ S.b) (m₂ S.c) x ∂S.target.covLaw =
        linkConditional g S.target.covLaw (m S.b) (m S.c) ∧
      anchoredEstimand S.target.covLaw (linkContrast g (m₁ S.a) (m₁ S.c))
          (linkContrast g (m₂ S.b) (m₂ S.c)) =
        linkConditional g S.target.covLaw (m S.a) (m S.b) ∧
      anchoredEstimand S.target.covLaw (linkContrast g (m₁ S.a) (m₁ S.c))
          (linkContrast g (m₂ S.b) (m₂ S.c)) =
        ∫ ω, densityRatio S.ipdTrial.μ S.ipdTrial.X S.target.μ S.target.X (S.ipdTrial.X ω) *
            linkContrast g (m₁ S.a) (m₁ S.c) (S.ipdTrial.X ω) ∂S.ipdTrial.μ -
          ∫ ω, densityRatio S.agdTrial.μ S.agdTrial.X S.target.μ S.target.X (S.agdTrial.X ω) *
            linkContrast g (m₂ S.b) (m₂ S.c) (S.agdTrial.X ω) ∂S.agdTrial.μ := by
  have e₁ := h.relativeConstancy_ipd.ae_eq h.measurable_ipd h.measurable_target h.overlap_ipd
    h.isCondMean_ipd_a h.isCondMean_ipd_c h.target_a h.target_c
  have e₂ := h.relativeConstancy_agd.ae_eq h.measurable_agd h.measurable_target h.overlap_agd
    h.isCondMean_agd_b h.isCondMean_agd_c h.target_b h.target_c
  have e₃ : ∀ᵐ x ∂S.target.covLaw, linkContrast g (m S.a) (m S.b) x =
      linkContrast g (m₁ S.a) (m₁ S.c) x - linkContrast g (m₂ S.b) (m₂ S.c) x := by
    filter_upwards [e₁, e₂] with x h₁ h₂
    rw [h₁, h₂, linkContrast_eq_sub g (m S.a) (m S.b) (m S.c) x]
  have t₁ := linkConditional_eq_of_relativeConstancy hg h.relativeConstancy_ipd h.measurable_ipd
    h.measurable_target h.overlap_ipd h.isCondMean_ipd_a h.isCondMean_ipd_c h.target_a h.target_c
  have t₂ := linkConditional_eq_of_relativeConstancy hg h.relativeConstancy_agd h.measurable_agd
    h.measurable_target h.overlap_agd h.isCondMean_agd_b h.isCondMean_agd_c h.target_b h.target_c
  have hest : anchoredEstimand S.target.covLaw (linkContrast g (m₁ S.a) (m₁ S.c))
      (linkContrast g (m₂ S.b) (m₂ S.c)) = linkConditional g S.target.covLaw (m S.a) (m S.b) := by
    rw [anchoredEstimand, linkConditional,
      ← integral_sub h.integrable_ipd_contrast h.integrable_agd_contrast]
    exact integral_congr_ae (e₃.mono fun _ hx => hx.symm)
  refine ⟨e₁, e₂, e₃, t₁.1.symm, t₂.1.symm, hest, ?_⟩
  rw [anchoredEstimand, ← t₁.1, ← t₂.1, t₁.2, t₂.2]

/-! ### Part (c): the marginal effect -/

/-- **The anchored identification theorem, part (c), on a collapsible scale.** Under the
assumptions, with a probability target, a measurable link and a measurable domain, if the scale
is directly collapsible, or collapsible and the target conditional effect of `b` relative to `a`
is almost surely a constant (as under shared effect modifiers on the model scale), then the
anchored estimand is the marginal estimand of the target conditional means and the target
marginal effect `g(E_*[Y(b)]) - g(E_*[Y(a)])`. -/
theorem anchoredEstimand_eq_marginalEffect [IsFiniteMeasure S.ipdTrial.μ]
    [IsFiniteMeasure S.agdTrial.μ] [IsProbabilityMeasure S.target.μ] (hg : Measurable g)
    (hD : MeasurableSet D) (h : S.IdentificationAssumptions g D m₁ m₂ m)
    (hcase : LinkDirectlyCollapsible D g ∨
      (LinkCollapsible D g ∧ ∃ c : ℝ,
        ∀ᵐ x ∂S.target.covLaw, linkContrast g (m S.a) (m S.b) x = c)) :
    anchoredEstimand S.target.covLaw (linkContrast g (m₁ S.a) (m₁ S.c))
        (linkContrast g (m₂ S.b) (m₂ S.c)) = linkMarginal g S.target.covLaw (m S.a) (m S.b) ∧
      anchoredEstimand S.target.covLaw (linkContrast g (m₁ S.a) (m₁ S.c))
        (linkContrast g (m₂ S.b) (m₂ S.c)) = S.target.marginalEffect g S.a S.b := by
  have hQ := h.measurable_target
  have : IsProbabilityMeasure S.target.covLaw := S.target.isProbabilityMeasure_covLaw hQ
  obtain ⟨-, -, e₃, -, -, hest, -⟩ := h.identification hg
  have hai := h.target_a.integrable hQ
  have hbi := h.target_b.integrable hQ
  have hab : ∀ᵐ x ∂S.target.covLaw, m S.a x ∈ D ∧ m S.b x ∈ D :=
    h.mem_target.mono fun _ hx => ⟨hx.1, hx.2.1⟩
  have hmarg : linkMarginal g S.target.covLaw (m S.a) (m S.b) =
      S.target.marginalEffect g S.a S.b :=
    (S.target.marginalEffect_eq_linkMarginal g hQ (h.integrable_target S.a (by simp))
      (h.integrable_target S.b (by simp)) h.target_a h.target_b).symm
  suffices hc : linkConditional g S.target.covLaw (m S.a) (m S.b) =
      linkMarginal g S.target.covLaw (m S.a) (m S.b) by
    rw [hest, hc]; exact ⟨rfl, hmarg⟩
  rcases hcase with hdir | ⟨hcol, c, hc⟩
  · have hτ : Integrable (linkContrast g (m S.a) (m S.b)) S.target.covLaw :=
      (h.integrable_ipd_contrast.sub h.integrable_agd_contrast).congr (e₃.mono fun _ hx => hx.symm)
    exact (hdir.apply hD hg hai hbi hab hτ).symm
  · rw [hcol.apply hD hg hai hbi hab hc, linkConditional, integral_congr_ae hc]
    simp

end IdentificationAssumptions

/-- **The anchored identification theorem, part (c), under absolute constancy.** If the
conditional means of `Y(a)` and `Y(c)` are common to the first trial and the target, those of
`Y(b)` and `Y(c)` common to the second trial and the target, the potential outcomes are
integrable and the target overlaps both trials, then on every scale `g` the target marginal effect
of `b` relative to `a` is the difference of the standardized marginal contrasts of the two trials,
`linkMarginal g Q_X m₁_a m₁_c - linkMarginal g Q_X m₂_b m₂_c`, and it is
`g(∫ m₂_b dQ_X) - g(∫ m₁_a dQ_X)`. No collapsibility is needed; the anchored estimand of
conditional contrasts is not this quantity on a non collapsible scale. -/
theorem marginalEffect_eq_of_structurallyInvariant
    (S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι) [IsFiniteMeasure S.target.μ] (g : ℝ → ℝ)
    {m₁ m₂ : ι → 𝒳 → ℝ} (hX₁ : Measurable S.ipdTrial.X) (hX₂ : Measurable S.agdTrial.X)
    (hX : Measurable S.target.X) (hY₁a : Integrable (S.ipdTrial.Y S.a) S.ipdTrial.μ)
    (hY₁c : Integrable (S.ipdTrial.Y S.c) S.ipdTrial.μ)
    (hY₂b : Integrable (S.agdTrial.Y S.b) S.agdTrial.μ)
    (hY₂c : Integrable (S.agdTrial.Y S.c) S.agdTrial.μ)
    (hYt : ∀ t ∈ ({S.a, S.b, S.c} : Set ι), Integrable (S.target.Y t) S.target.μ)
    (h₁a : S.ipdTrial.IsCondMean S.a (m₁ S.a)) (h₁c : S.ipdTrial.IsCondMean S.c (m₁ S.c))
    (h₂b : S.agdTrial.IsCondMean S.b (m₂ S.b)) (h₂c : S.agdTrial.IsCondMean S.c (m₂ S.c))
    (hs₁a : StructurallyInvariant S.ipdTrial.μ S.ipdTrial.X (S.ipdTrial.Y S.a) S.target.μ
      S.target.X (S.target.Y S.a))
    (hs₁c : StructurallyInvariant S.ipdTrial.μ S.ipdTrial.X (S.ipdTrial.Y S.c) S.target.μ
      S.target.X (S.target.Y S.c))
    (hs₂b : StructurallyInvariant S.agdTrial.μ S.agdTrial.X (S.agdTrial.Y S.b) S.target.μ
      S.target.X (S.target.Y S.b))
    (hs₂c : StructurallyInvariant S.agdTrial.μ S.agdTrial.X (S.agdTrial.Y S.c) S.target.μ
      S.target.X (S.target.Y S.c))
    (hov₁ : S.target.covLaw ≪ S.ipdTrial.covLaw) (hov₂ : S.target.covLaw ≪ S.agdTrial.covLaw) :
    S.target.marginalEffect g S.a S.b =
        linkMarginal g S.target.covLaw (m₁ S.a) (m₁ S.c) -
          linkMarginal g S.target.covLaw (m₂ S.b) (m₂ S.c) ∧
      S.target.marginalEffect g S.a S.b =
        g (∫ x, m₂ S.b x ∂S.target.covLaw) - g (∫ x, m₁ S.a x ∂S.target.covLaw) := by
  have hYa := hYt S.a (by simp)
  have hYb := hYt S.b (by simp)
  have hYc := hYt S.c (by simp)
  have hac := marginalEffect_eq_linkMarginal_of_structurallyInvariant
    (P' := S.ipdTrial.toPopulation) g hX₁ hX₁ hX hY₁a hY₁c hYa hYc h₁a h₁c hs₁a hs₁c hov₁ hov₁
  have hbc := marginalEffect_eq_linkMarginal_of_structurallyInvariant
    (P' := S.agdTrial.toPopulation) g hX₂ hX₂ hX hY₂b hY₂c hYb hYc h₂b h₂c hs₂b hs₂c hov₂ hov₂
  have hab := marginalEffect_eq_linkMarginal_of_structurallyInvariant g hX₁ hX₂ hX hY₁a hY₂b
    hYa hYb h₁a h₂b hs₁a hs₂b hov₁ hov₂
  exact ⟨by rw [S.target.marginalEffect_eq_sub S.a S.b S.c, hac, hbc], hab⟩

/-! ### Part (d): a non collapsible scale -/

/-- **The anchored identification theorem, part (d).** If the effect measure on the scale `g`
with domain `D` is not collapsible, there is an anchored setting on some covariate space, with
treatments `a = 0`, `b = 1`, `c = 2`, a probability target and the two trials equal to the target,
satisfying all the assumptions of the anchored theorem, in which the target conditional effect of
`b` relative to `a` is almost surely a constant `c₀`, so the anchored estimand and the target
average conditional effect are `c₀`, but the target marginal effect is not `c₀`. -/
theorem exists_anchoredEstimand_ne_marginalEffect {D : Set ℝ} {g : ℝ → ℝ}
    (h : ¬ LinkCollapsible D g) :
    ∃ (𝒳 : Type) (_ : MeasurableSpace 𝒳) (S : AnchoredSetting 𝒳 𝒳 𝒳 𝒳 (Fin 3))
      (m : Fin 3 → 𝒳 → ℝ) (c₀ : ℝ),
      IsProbabilityMeasure S.target.μ ∧ S.a = 0 ∧ S.b = 1 ∧ S.c = 2 ∧
      S.IdentificationAssumptions g D m m m ∧
      (∀ᵐ x ∂S.target.covLaw, linkContrast g (m S.a) (m S.b) x = c₀) ∧
      anchoredEstimand S.target.covLaw (linkContrast g (m S.a) (m S.c))
          (linkContrast g (m S.b) (m S.c)) = c₀ ∧
      linkConditional g S.target.covLaw (m S.a) (m S.b) = c₀ ∧
      S.target.marginalEffect g S.a S.b ≠ c₀ := by
  simp only [LinkCollapsible, not_forall] at h
  obtain ⟨𝒳, _, ν, _, a, b, ha, hb, hD, c₀, hc, hne⟩ := h
  set a' := ha.aestronglyMeasurable.mk a
  set b' := hb.aestronglyMeasurable.mk b
  have ea : a =ᵐ[ν] a' := ha.aestronglyMeasurable.ae_eq_mk
  have eb : b =ᵐ[ν] b' := hb.aestronglyMeasurable.ae_eq_mk
  have ma : Measurable a' := ha.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have mb : Measurable b' := hb.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  let m : Fin 3 → 𝒳 → ℝ := fun t => if t = 1 then b' else a'
  have m0 : m 0 = a' := by simp [m]
  have m1 : m 1 = b' := by simp [m]
  have m2 : m 2 = a' := by simp [m, show (2 : Fin 3) ≠ 1 by decide]
  have mm : ∀ t, Measurable (m t) := fun t => by
    by_cases ht : t = 1 <;> simp [m, ht, ma, mb]
  have mi : ∀ t, Integrable (m t) ν := fun t => by
    by_cases ht : t = 1
    · simpa [m, ht] using (integrable_congr eb).1 hb
    · simpa [m, ht] using (integrable_congr ea).1 ha
  let P : Population 𝒳 𝒳 (Fin 3) := ⟨ν, id, m⟩
  let T : Trial 𝒳 𝒳 (Fin 3) := ⟨P, fun _ => 0⟩
  let S : AnchoredSetting 𝒳 𝒳 𝒳 𝒳 (Fin 3) := ⟨T, T, P, 0, 1, 2⟩
  have hP : IsProbabilityMeasure P.μ := ‹_›
  have hcov : P.covLaw = ν := Measure.map_id
  have hcm : ∀ t, P.IsCondMean t (m t) := fun t =>
    Population.isCondMean_of_eq_comp measurable_id (mm t) rfl (mi t)
  have hD' : ∀ᵐ x ∂ν, a' x ∈ D ∧ b' x ∈ D := by
    filter_upwards [hD, ea, eb] with x hx hxa hxb
    rw [← hxa, ← hxb]; exact hx
  have hc' : ∀ᵐ x ∂ν, linkContrast g a' b' x = c₀ := by
    filter_upwards [hc, ea, eb] with x hx hxa hxb
    simpa [linkContrast, ← hxa, ← hxb] using hx
  have hbc : ∀ᵐ x ∂ν, linkContrast g b' a' x = -c₀ := by
    filter_upwards [hc'] with x hx
    simp only [linkContrast] at hx ⊢; linarith
  have hiac : Integrable (linkContrast g a' a') ν := by
    rw [show linkContrast g a' a' = 0 from funext fun _ => sub_self _]
    exact integrable_zero _ _ _
  have hibc : Integrable (linkContrast g b' a') ν :=
    (integrable_const (-c₀)).congr (hbc.mono fun _ hx => hx.symm)
  have hrel : ∀ s t, RelativeConstancy g P P s t := fun s t =>
    RelativeConstancy.refl (hcm s) (hcm t)
  have hA : S.IdentificationAssumptions g D m m m := by
    refine ⟨measurable_id, measurable_id, measurable_id, mi 0, mi 2, mi 1, mi 2,
      fun t _ => mi t, hcm 0, hcm 2, hcm 1, hcm 2, fun t _ => hcm t, ?_, ?_, ?_, hrel _ _,
      hrel _ _, Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl, ?_, ?_⟩
    · change ∀ᵐ x ∂P.covLaw, m 0 x ∈ D ∧ m 2 x ∈ D
      rw [hcov, m0, m2]; exact hD'.mono fun _ hx => ⟨hx.1, hx.1⟩
    · change ∀ᵐ x ∂P.covLaw, m 1 x ∈ D ∧ m 2 x ∈ D
      rw [hcov, m1, m2]; exact hD'.mono fun _ hx => ⟨hx.2, hx.1⟩
    · change ∀ᵐ x ∂P.covLaw, m 0 x ∈ D ∧ m 1 x ∈ D ∧ m 2 x ∈ D
      rw [hcov, m0, m1, m2]; exact hD'.mono fun _ hx => ⟨hx.1, hx.2, hx.1⟩
    · change Integrable (linkContrast g (m 0) (m 2)) P.covLaw
      rw [hcov, m0, m2]; exact hiac
    · change Integrable (linkContrast g (m 1) (m 2)) P.covLaw
      rw [hcov, m1, m2]; exact hibc
  refine ⟨𝒳, _, S, m, c₀, hP, rfl, rfl, rfl, hA, ?_, ?_, ?_, ?_⟩
  · change ∀ᵐ x ∂P.covLaw, linkContrast g (m 0) (m 1) x = c₀
    rw [hcov, m0, m1]; exact hc'
  · change anchoredEstimand P.covLaw (linkContrast g (m 0) (m 2)) (linkContrast g (m 1) (m 2)) = c₀
    rw [hcov, m0, m1, m2, anchoredEstimand, integral_congr_ae hbc]
    simp [linkContrast]
  · change linkConditional g P.covLaw (m 0) (m 1) = c₀
    rw [hcov, m0, m1, linkConditional, integral_congr_ae hc']
    simp
  · change g (∫ ω, m 1 ω ∂ν) - g (∫ ω, m 0 ω ∂ν) ≠ c₀
    rw [m0, m1, ← integral_congr_ae ea, ← integral_congr_ae eb]
    exact hne

end Anchored

end IndirectComparison.AnchoredSetting
/-! ### Part (e): an omitted covariate -/

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison

section Omitted

variable {Ω 𝒳 𝒲 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒲]

/-- The population with the **reduced adjustment set**: of the covariates `(X, W)`, only `X` is
kept. -/
def _root_.CausalInference.IndirectComparison.Population.fstCovariate
    (P : Population Ω (𝒳 × 𝒲) ι) : Population Ω 𝒳 ι :=
  ⟨P.μ, fun ω => (P.X ω).1, P.Y⟩

/-- **The conditional mean given a reduced adjustment set is a kernel average.** Let the
covariates be `(X, W)`, with joint law the law `ν` of `X` composed with a Markov kernel `κ`
(the conditional law of `W` given `X`). If `m` is a conditional mean function of an integrable
`Y(t)` given `(X, W)`, then `x ↦ ∫ m(x, w) κ(x, dw)` is a conditional mean function of `Y(t)`
given `X` alone. -/
theorem _root_.CausalInference.IndirectComparison.Population.IsCondMean.kernelAverage
    {P : Population Ω (𝒳 × 𝒲) ι} [IsFiniteMeasure P.μ] {κ : Kernel 𝒳 𝒲} [IsMarkovKernel κ]
    (hX : Measurable P.X) (hlaw : P.covLaw = P.fstCovariate.covLaw ⊗ₘ κ) {t : ι}
    {m : 𝒳 × 𝒲 → ℝ} (hm : P.IsCondMean t m) (hY : Integrable (P.Y t) P.μ) :
    P.fstCovariate.IsCondMean t (fun x => ∫ w, m (x, w) ∂κ x) := by
  set X₁ : Ω → 𝒳 := fun ω => (P.X ω).1 with hX₁def
  have hX₁ : Measurable X₁ := measurable_fst.comp hX
  have hν : P.fstCovariate.covLaw = P.μ.map X₁ := rfl
  set ν := P.fstCovariate.covLaw
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have : IsFiniteMeasure P.fstCovariate.μ := ‹IsFiniteMeasure P.μ›
  have hmi : Integrable m (ν ⊗ₘ κ) := hlaw ▸ hm.integrable hX
  have hhm : Measurable (fun x => ∫ w, m (x, w) ∂κ x) :=
    (hm.1.stronglyMeasurable.integral_kernel_prod_right').measurable
  have hhi : Integrable (fun x => ∫ w, m (x, w) ∂κ x) ν := by
    have h := hmi
    rw [Measure.compProd] at h
    simpa using h.integral_compProd
  refine ⟨hhm, ?_⟩
  refine ae_eq_condExp_of_forall_setIntegral_eq hX₁.comap_le hY ?_ ?_ ?_
  · intro s _ _
    exact ((integrable_map_measure hhm.aestronglyMeasurable hX₁.aemeasurable).1
      (hν ▸ hhi)).integrableOn
  · rintro s ⟨A, hA, rfl⟩ _
    have hsX : MeasurableSet[MeasurableSpace.comap P.X inferInstance] (X₁ ⁻¹' A) :=
      ⟨Prod.fst ⁻¹' A, measurable_fst hA, rfl⟩
    have e1 : ∫ ω in X₁ ⁻¹' A, (fun x => ∫ w, m (x, w) ∂κ x) (X₁ ω) ∂P.μ =
        ∫ x in A, ∫ w, m (x, w) ∂κ x ∂ν := by
      rw [hν, setIntegral_map hA hhm.aestronglyMeasurable hX₁.aemeasurable]
    have e2 : ∫ ω in X₁ ⁻¹' A, P.Y t ω ∂P.μ = ∫ ω in X₁ ⁻¹' A, m (P.X ω) ∂P.μ := by
      rw [← setIntegral_condExp hX.comap_le hY hsX]
      exact setIntegral_congr_ae (hX₁ hA) (hm.2.mono fun ω h _ => h.symm)
    have e3 : ∫ ω in X₁ ⁻¹' A, m (P.X ω) ∂P.μ = ∫ z in A ×ˢ Set.univ, m z ∂(ν ⊗ₘ κ) := by
      rw [← hlaw, Set.prod_univ, Population.covLaw,
        setIntegral_map (measurable_fst hA) hm.1.aestronglyMeasurable hX.aemeasurable]
      rfl
    change ∫ ω in X₁ ⁻¹' A, (fun x => ∫ w, m (x, w) ∂κ x) (X₁ ω) ∂P.μ =
      ∫ ω in X₁ ⁻¹' A, P.Y t ω ∂P.μ
    rw [e1, e2, e3, Measure.setIntegral_compProd hA MeasurableSet.univ hmi.integrableOn]
    simp
  · exact (hhm.comp (comap_measurable X₁)).aestronglyMeasurable

/-- **The omitted covariate residual.** For a law `ν` of the adjustment set `X`, conditional
laws `κ_src` and `κ_*` of the omitted `W` given `X`, and a function `τ(x, w)` integrable under
both joint laws, averaging `τ` over `κ_src` and then standardizing to `ν` misses the target
`∫ τ d(ν ⊗ κ_*)` by `∫ (∫ τ(x, ·) dκ_src x - ∫ τ(x, ·) dκ_* x) dν(x)`. -/
theorem integral_kernelAverage_sub_integral_compProd {ν : Measure 𝒳} [SFinite ν]
    {κs κt : Kernel 𝒳 𝒲} [IsSFiniteKernel κs] [IsSFiniteKernel κt] {τ : 𝒳 × 𝒲 → ℝ}
    (hs : Integrable τ (ν ⊗ₘ κs)) (ht : Integrable τ (ν ⊗ₘ κt)) :
    ∫ x, (∫ w, τ (x, w) ∂κs x) ∂ν - ∫ z, τ z ∂(ν ⊗ₘ κt) =
      ∫ x, (∫ w, τ (x, w) ∂κs x - ∫ w, τ (x, w) ∂κt x) ∂ν := by
  have is : Integrable (fun x => ∫ w, τ (x, w) ∂κs x) ν := by
    have h := hs
    rw [Measure.compProd] at h
    simpa using h.integral_compProd
  have it : Integrable (fun x => ∫ w, τ (x, w) ∂κt x) ν := by
    have h := ht
    rw [Measure.compProd] at h
    simpa using h.integral_compProd
  rw [Measure.integral_compProd ht, integral_sub is it]

/-- **The anchored bias with an omitted covariate.** Let `τ₁(x, w)` and `τ₂(x, w)` be the
contrasts of `c` against `a` and against `b` given the full covariate `(X, W)`, and `κ₁`, `κ₂`,
`κ_*` the conditional laws of `W` given `X` in the two trials and the target, with target law `ν`
of `X`. On the identity scale the contrasts given `X` alone are the kernel averages
`τ̃ⱼ(x) = ∫ τⱼ(x, ·) dκⱼ x` (`Population.IsCondMean.kernelAverage`). The anchored estimand built
from them under `ν`, minus the anchored estimand of the full contrasts under the target joint law
`ν ⊗ κ_*`, is the difference of the two residuals; it vanishes when `κ₁ = κ₂ = κ_*`, that is,
when `W` is balanced given `X`. -/
theorem anchoredEstimand_kernelAverage_sub_integral_compProd {ν : Measure 𝒳} [SFinite ν]
    {κ₁ κ₂ κt : Kernel 𝒳 𝒲} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] [IsSFiniteKernel κt]
    {τ₁ τ₂ : 𝒳 × 𝒲 → ℝ} (h₁ : Integrable τ₁ (ν ⊗ₘ κ₁)) (h₁t : Integrable τ₁ (ν ⊗ₘ κt))
    (h₂ : Integrable τ₂ (ν ⊗ₘ κ₂)) (h₂t : Integrable τ₂ (ν ⊗ₘ κt)) :
    anchoredEstimand ν (fun x => ∫ w, τ₁ (x, w) ∂κ₁ x) (fun x => ∫ w, τ₂ (x, w) ∂κ₂ x) -
        anchoredEstimand (ν ⊗ₘ κt) τ₁ τ₂ =
      ∫ x, (∫ w, τ₁ (x, w) ∂κ₁ x - ∫ w, τ₁ (x, w) ∂κt x) ∂ν -
        ∫ x, (∫ w, τ₂ (x, w) ∂κ₂ x - ∫ w, τ₂ (x, w) ∂κt x) ∂ν := by
  rw [← integral_kernelAverage_sub_integral_compProd h₁ h₁t,
    ← integral_kernelAverage_sub_integral_compProd h₂ h₂t, anchoredEstimand, anchoredEstimand]
  ring

end Omitted

end PopulationAdjustment

end CausalInference
