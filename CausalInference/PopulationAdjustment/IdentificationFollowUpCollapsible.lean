/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.AnchoredWitnesses
public import CausalInference.PopulationAdjustment.UnanchoredWitnesses

/-!
# The marginal effect on a directly collapsible scale

On a directly collapsible scale (`EffectMeasure.LinkDirectlyCollapsible`) the marginal effect of
a population is the average conditional effect of its conditional mean functions, on a covariate
space in any universe (`Population.marginalEffect_eq_linkConditional_of_directlyCollapsible`).
The proof composes the tower property (`Population.marginalEffect_eq_linkMarginal`) with
`EffectMeasure.LinkDirectlyCollapsible.apply`.

* **Anchored comparison.** Under the assumptions of the anchored identification theorem on a
  directly collapsible scale, the target marginal effect of `b` relative to `a`, the target
  average conditional effect and the anchored estimand coincide (in the namespace
  `AnchoredSetting`,
  `IdentificationAssumptions.marginalEffect_eq_linkConditional_of_directlyCollapsible`).
* **Unanchored comparison.** Under the assumptions of the unanchored identification theorem on a
  directly collapsible scale, with the two source surfaces in the domain almost everywhere under
  the target covariate law and an integrable contrast, the target marginal effect, the unanchored
  estimand and the average conditional effect of the source surfaces coincide (in the namespace
  `UnanchoredSetting`,
  `IdentificationAssumptions.marginalEffect_eq_linkConditional_of_directlyCollapsible`).
* **Scales.** Every affine scale is directly collapsible (`linkDirectlyCollapsible_affine`); the
  library proves that the log scale is not (`not_linkDirectlyCollapsible_log`), and the logit is
  not either (`not_linkDirectlyCollapsible_logit`).
* **Instances.** On the scale `u ↦ 2u + 1` in `anchoredExampleSetting` the three anchored
  quantities are `5/2` (`anchored_affine_directlyCollapsible_example`); on the identity scale in
  `standardizationUnanchored` the three unanchored quantities are `1/4`
  (`unanchored_id_directlyCollapsible_example`). On the logit scale in `anchoredLogitSetting`
  every hypothesis of the standalone theorem except direct collapsibility holds, and the target
  marginal effect differs from the average conditional effect `3/2`
  (`anchored_logit_marginalEffect_ne_linkConditional`).

## Main results

* `linkDirectlyCollapsible_affine`, `not_linkDirectlyCollapsible_logit`.
* `Population.marginalEffect_eq_linkConditional_of_directlyCollapsible`.
* `IdentificationAssumptions.marginalEffect_eq_linkConditional_of_directlyCollapsible`, in the
  namespaces `AnchoredSetting` and `UnanchoredSetting`.
* `anchored_affine_directlyCollapsible_example`, `unanchored_id_directlyCollapsible_example`,
  `anchored_logit_marginalEffect_ne_linkConditional`.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Fine Point 4.3.
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory ProbabilityTheory

namespace EffectMeasure

/-- **Every affine scale is directly collapsible**: for `g u = c u + d` the marginal effect is the
average conditional effect, for every covariate law and every pair of integrable means. -/
theorem linkDirectlyCollapsible_affine (c d : ℝ) :
    LinkDirectlyCollapsible Set.univ (fun u => c * u + d) := by
  intro X _ ν _ a b ha hb _ _
  exact linkMarginal_eq_linkConditional_affine ha hb c d

/-- **The odds ratio is not directly collapsible**, since it is not collapsible. -/
theorem not_linkDirectlyCollapsible_logit : ¬ LinkDirectlyCollapsible (Set.Ioo 0 1) logit :=
  fun h => not_linkCollapsible_logit h.collapsible

end EffectMeasure

namespace IndirectComparison

open EffectMeasure Transport PopulationAdjustment

/-! ### The standalone theorem -/

/-- **On a directly collapsible scale the marginal effect is the average conditional effect.**
In a probability population with measurable covariates in any measurable space, let `m_a`, `m_b`
be conditional mean functions of integrable `Y(a)`, `Y(b)`, with values almost surely in the
measurable domain `D` of the measurable link `g` under the covariate law `P_X`, and with an
integrable conditional effect. If the scale `g` is directly collapsible on `D`, then
`g(E[Y(b)]) - g(E[Y(a)]) = ∫ (g ∘ m_b - g ∘ m_a) dP_X`. -/
theorem Population.marginalEffect_eq_linkConditional_of_directlyCollapsible
    {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] {P : Population Ω 𝒳 ι}
    [IsProbabilityMeasure P.μ] {D : Set ℝ} {g : ℝ → ℝ} (hdir : LinkDirectlyCollapsible D g)
    (hD : MeasurableSet D) (hg : Measurable g) (hX : Measurable P.X) {a b : ι} {ma mb : 𝒳 → ℝ}
    (hYa : Integrable (P.Y a) P.μ) (hYb : Integrable (P.Y b) P.μ) (ha : P.IsCondMean a ma)
    (hb : P.IsCondMean b mb) (hmem : ∀ᵐ x ∂P.covLaw, ma x ∈ D ∧ mb x ∈ D)
    (hτ : Integrable (linkContrast g ma mb) P.covLaw) :
    P.marginalEffect g a b = linkConditional g P.covLaw ma mb := by
  have : IsProbabilityMeasure P.covLaw := P.isProbabilityMeasure_covLaw hX
  rw [P.marginalEffect_eq_linkMarginal g hX hYa hYb ha hb]
  exact hdir.apply hD hg (ha.integrable hX) (hb.integrable hX) hmem hτ

/-! ### The anchored comparison -/

namespace AnchoredSetting.IdentificationAssumptions

variable {Ω₁ Ω₂ Ω₃ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
  [MeasurableSpace 𝒳] {S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι} {g : ℝ → ℝ} {D : Set ℝ}
  {m₁ m₂ m : ι → 𝒳 → ℝ}

/-- **The anchored comparison on a directly collapsible scale.** Under the assumptions of the
anchored identification theorem, with finite trials, a probability target, a measurable link and
a measurable domain, if the scale is directly collapsible then the target marginal effect of `b`
relative to `a` is the target average conditional effect `∫ τ_ab dQ_X`, which is the anchored
estimand `∫ τ¹_ac dQ_X - ∫ τ²_bc dQ_X`. The target contrast `τ_ab` is integrable because it is
almost everywhere the difference of the two integrable trial contrasts. -/
theorem marginalEffect_eq_linkConditional_of_directlyCollapsible [IsFiniteMeasure S.ipdTrial.μ]
    [IsFiniteMeasure S.agdTrial.μ] [IsProbabilityMeasure S.target.μ] (hg : Measurable g)
    (hD : MeasurableSet D) (h : S.IdentificationAssumptions g D m₁ m₂ m)
    (hdir : LinkDirectlyCollapsible D g) :
    S.target.marginalEffect g S.a S.b = linkConditional g S.target.covLaw (m S.a) (m S.b) ∧
      linkConditional g S.target.covLaw (m S.a) (m S.b) =
        anchoredEstimand S.target.covLaw (linkContrast g (m₁ S.a) (m₁ S.c))
          (linkContrast g (m₂ S.b) (m₂ S.c)) := by
  obtain ⟨-, -, e₃, -, -, hest, -⟩ := h.identification hg
  have hτ : Integrable (linkContrast g (m S.a) (m S.b)) S.target.covLaw :=
    (h.integrable_ipd_contrast.sub h.integrable_agd_contrast).congr (e₃.mono fun _ hx => hx.symm)
  refine ⟨?_, hest.symm⟩
  exact Population.marginalEffect_eq_linkConditional_of_directlyCollapsible hdir hD hg
    h.measurable_target (h.integrable_target S.a (by simp)) (h.integrable_target S.b (by simp))
    h.target_a h.target_b (h.mem_target.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hτ

end AnchoredSetting.IdentificationAssumptions

/-! ### The unanchored comparison -/

namespace UnanchoredSetting.IdentificationAssumptions

variable {Ω₁ Ω₂ Ω₃ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
  [MeasurableSpace 𝒳] {S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι} {D : Set ℝ} {ma mb : 𝒳 → ℝ}

/-- **The unanchored comparison on a directly collapsible scale.** Under the assumptions of the
unanchored identification theorem, with finite sources and a probability target, a measurable
link `g`, a measurable domain `D` and a directly collapsible scale, if moreover the source
surfaces lie in `D` almost everywhere under the target covariate law `Q_X` and their contrast is
integrable under `Q_X` (the assumptions put only the target arm means in `D`), then the target
marginal effect of `b` relative to `a` is the average conditional effect
`∫ (g ∘ m_b - g ∘ m_a) dQ_X` of the source surfaces, and so is the unanchored estimand
`linkMarginal g Q_X m_a m_b`. -/
theorem marginalEffect_eq_linkConditional_of_directlyCollapsible [IsFiniteMeasure S.sourceA.μ]
    [IsFiniteMeasure S.sourceB.μ] [IsProbabilityMeasure S.target.μ] {g : ℝ → ℝ}
    (hg : Measurable g) (hD : MeasurableSet D) (h : S.IdentificationAssumptions D ma mb)
    (hdir : LinkDirectlyCollapsible D g) (hmem : ∀ᵐ x ∂S.target.covLaw, ma x ∈ D ∧ mb x ∈ D)
    (hτ : Integrable (linkContrast g ma mb) S.target.covLaw) :
    S.target.marginalEffect g S.a S.b = linkConditional g S.target.covLaw ma mb ∧
      linkMarginal g S.target.covLaw ma mb = linkConditional g S.target.covLaw ma mb := by
  obtain ⟨hca, hcb, -, -, -, -, -, -, -, -, hm⟩ := h.identification g
  have key := Population.marginalEffect_eq_linkConditional_of_directlyCollapsible hdir hD hg
    h.measurable_target h.integrable_target_a h.integrable_target_b hca hcb hmem hτ
  exact ⟨key, hm.symm.trans key⟩

end UnanchoredSetting.IdentificationAssumptions

end IndirectComparison

/-! ### Instances -/

namespace PopulationAdjustment

open EffectMeasure IndirectComparison Transport

/-- **An anchored instance on the affine scale `u ↦ 2u + 1`.** In `anchoredExampleSetting` all
the assumptions of the anchored identification theorem hold on the scale `g u = 2u + 1` (its
contrasts are twice those of the identity scale, so relative constancy carries over), the scale
is directly collapsible, and the target marginal effect, the target average conditional effect
and the anchored estimand of `b` relative to `a` are all `5/2`. -/
theorem anchored_affine_directlyCollapsible_example :
    anchoredExampleSetting.IdentificationAssumptions (fun u => 2 * u + 1) Set.univ
        anchoredExampleIpdMean anchoredExampleAgdMean anchoredExampleTargetMean ∧
      anchoredExampleSetting.target.marginalEffect (fun u => 2 * u + 1) 0 1 = 5 / 2 ∧
      linkConditional (fun u => 2 * u + 1) anchoredExampleSetting.target.covLaw
          (anchoredExampleTargetMean 0) (anchoredExampleTargetMean 1) = 5 / 2 ∧
      anchoredEstimand anchoredExampleSetting.target.covLaw
          (linkContrast (fun u => 2 * u + 1) (anchoredExampleIpdMean 0) (anchoredExampleIpdMean 2))
          (linkContrast (fun u => 2 * u + 1) (anchoredExampleAgdMean 1)
            (anchoredExampleAgdMean 2)) = 5 / 2 := by
  have hov : standardizationTargetLaw ≪ halfLaw := by
    rw [halfLaw]; exact stratumLaw_absolutelyContinuous_of_pos (fun _ => by norm_num) _
  have hc : ∀ x, linkContrast (fun u => 2 * u + 1) (anchoredExampleIpdMean 0)
      (anchoredExampleIpdMean 2) x = linkContrast (fun u => 2 * u + 1)
        (anchoredExampleTargetMean 0) (anchoredExampleTargetMean 2) x := fun x => by
    cases x <;> norm_num [linkContrast, anchoredExampleIpdMean, anchoredExampleTargetMean]
  have hc' : ∀ x, linkContrast (fun u => 2 * u + 1) (anchoredExampleAgdMean 1)
      (anchoredExampleAgdMean 2) x = linkContrast (fun u => 2 * u + 1)
        (anchoredExampleTargetMean 1) (anchoredExampleTargetMean 2) x := fun x => by
    cases x <;> norm_num [linkContrast, anchoredExampleAgdMean, anchoredExampleTargetMean]
  have hA : anchoredExampleSetting.IdentificationAssumptions (fun u => 2 * u + 1) Set.univ
      anchoredExampleIpdMean anchoredExampleAgdMean anchoredExampleTargetMean :=
    finiteCovSetting_identificationAssumptions
      (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩)
      (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩)
      (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial, trivial⟩)
      (Filter.Eventually.of_forall hc) (Filter.Eventually.of_forall hc') hov hov
  have hcov : anchoredExampleSetting.target.covLaw = standardizationTargetLaw :=
    finiteCovTrial_covLaw _ _
  have hint : ∀ f : Bool → ℝ, ∫ x, f x ∂standardizationTargetLaw = f true / 4 + 3 * f false / 4 :=
    fun f => by
      rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
      simp [standardizedRisk]; ring
  have hcond : linkConditional (fun u => 2 * u + 1) anchoredExampleSetting.target.covLaw
      (anchoredExampleTargetMean 0) (anchoredExampleTargetMean 1) = 5 / 2 := by
    rw [hcov, linkConditional, hint]
    norm_num [linkContrast, anchoredExampleTargetMean]
  obtain ⟨hm, he⟩ := hA.marginalEffect_eq_linkConditional_of_directlyCollapsible
    (by fun_prop) MeasurableSet.univ (linkDirectlyCollapsible_affine 2 1)
  exact ⟨hA, hm.trans hcond, hcond, he ▸ hcond⟩

/-- **An unanchored instance on the identity scale.** In `standardizationUnanchored` the
assumptions of the unanchored identification theorem hold with the domain `ℝ`, the source
surfaces `m_t(x) = (t + 1)/4 + 1{x}/8` have the constant contrast `1/4`, and the target marginal
mean difference of `1` against `0` (`17/32 - 9/32`), the unanchored estimand and the average
conditional effect of the source surfaces are all `1/4`. -/
theorem unanchored_id_directlyCollapsible_example :
    standardizationUnanchored.IdentificationAssumptions Set.univ (standardizationSurface 0)
        (standardizationSurface 1) ∧
      standardizationUnanchored.target.marginalEffect id 0 1 = 1 / 4 ∧
      linkMarginal id standardizationUnanchored.target.covLaw (standardizationSurface 0)
          (standardizationSurface 1) = 1 / 4 ∧
      linkConditional id standardizationUnanchored.target.covLaw (standardizationSurface 0)
          (standardizationSurface 1) = 1 / 4 := by
  have hA0 := (unanchored_identification_example).1
  have hA : standardizationUnanchored.IdentificationAssumptions Set.univ
      (standardizationSurface 0) (standardizationSurface 1) :=
    { hA0 with mem_a := trivial, mem_b := trivial }
  have hcov : standardizationUnanchored.target.covLaw = standardizationTargetLaw :=
    standardizationTarget_covLaw
  have : IsProbabilityMeasure standardizationUnanchored.target.covLaw := by
    rw [hcov]; infer_instance
  have hcon : ∀ x, linkContrast id (standardizationSurface 0) (standardizationSurface 1) x =
      1 / 4 := fun x => by
    cases x <;> norm_num [linkContrast, standardizationSurface]
  have hcond : linkConditional id standardizationUnanchored.target.covLaw
      (standardizationSurface 0) (standardizationSurface 1) = 1 / 4 := by
    rw [linkConditional, integral_congr_ae (Filter.Eventually.of_forall hcon), integral_const,
      probReal_univ, one_smul]
  obtain ⟨hm, hl⟩ := hA.marginalEffect_eq_linkConditional_of_directlyCollapsible measurable_id
    MeasurableSet.univ linkDirectlyCollapsible_id
    (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩)
    ((integrable_const (1 / 4 : ℝ)).congr
      (Filter.Eventually.of_forall fun x => (hcon x).symm))
  exact ⟨hA, hm.trans hcond, hl.trans hcond, hcond⟩

/-- **The standalone theorem fails on the logit scale.** In the target of `anchoredLogitSetting`
every hypothesis of `Population.marginalEffect_eq_linkConditional_of_directlyCollapsible` except
direct collapsibility holds for the arms `0` and `1` on the logit scale with the domain `(0, 1)`:
the link is measurable, the domain is measurable, the covariate is measurable, the potential
outcomes are integrable, the means are conditional mean functions with values in `(0, 1)`, and
the conditional effect `3/2` is integrable. The logit is not directly collapsible, and the target
marginal log odds ratio differs from the average conditional log odds ratio `3/2`. -/
theorem anchored_logit_marginalEffect_ne_linkConditional :
    ¬ LinkDirectlyCollapsible (Set.Ioo 0 1) logit ∧ Measurable logit ∧
      MeasurableSet (Set.Ioo (0 : ℝ) 1) ∧ Measurable anchoredLogitSetting.target.X ∧
      Integrable (anchoredLogitSetting.target.Y 0) anchoredLogitSetting.target.μ ∧
      Integrable (anchoredLogitSetting.target.Y 1) anchoredLogitSetting.target.μ ∧
      anchoredLogitSetting.target.IsCondMean 0 (anchoredLogitMean 0) ∧
      anchoredLogitSetting.target.IsCondMean 1 (anchoredLogitMean 1) ∧
      (∀ᵐ x ∂anchoredLogitSetting.target.covLaw,
        anchoredLogitMean 0 x ∈ Set.Ioo 0 1 ∧ anchoredLogitMean 1 x ∈ Set.Ioo 0 1) ∧
      Integrable (linkContrast logit (anchoredLogitMean 0) (anchoredLogitMean 1))
        anchoredLogitSetting.target.covLaw ∧
      linkConditional logit anchoredLogitSetting.target.covLaw (anchoredLogitMean 0)
        (anchoredLogitMean 1) = 3 / 2 ∧
      anchoredLogitSetting.target.marginalEffect logit 0 1 ≠
        linkConditional logit anchoredLogitSetting.target.covLaw (anchoredLogitMean 0)
          (anchoredLogitMean 1) := by
  obtain ⟨-, hA, hcon, -, hcond, -, hlt, -, -⟩ := anchored_logit_witness
  have := anchoredLogitSetting.target.isProbabilityMeasure_covLaw hA.measurable_target
  refine ⟨not_linkDirectlyCollapsible_logit, measurable_logit, measurableSet_Ioo,
    hA.measurable_target, hA.integrable_target anchoredLogitSetting.a (by simp),
    hA.integrable_target anchoredLogitSetting.b (by simp),
    hA.target_a, hA.target_b,
    hA.mem_target.mono fun _ hx => ⟨hx.1, hx.2.1⟩,
    (integrable_const (3 / 2 : ℝ)).congr (Filter.Eventually.of_forall fun x => (hcon x).symm),
    hcond, ?_⟩
  rw [hcond]
  exact hlt.ne

end PopulationAdjustment

end CausalInference
