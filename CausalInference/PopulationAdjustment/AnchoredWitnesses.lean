/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.AnchoredIdentification
public import CausalInference.PopulationAdjustment.StandardizationExamples

/-!
# Concrete models for the anchored identification theorem

All models have three treatments `a = 0`, `b = 1`, `c = 2` and finite covariate spaces; every
number is computed in the proof.

* **Relative constancy without absolute constancy** (`anchored_identification_example`). Binary
  covariate `x`; both trials have two equally likely strata, the target has `P(x) = 1/4`. Target
  means `m_a = 1 + 1{x}`, `m_b = 2 + 2·1{x}`, `m_c = 0`; first trial means `m₁_a = 2 + 1{x}`,
  `m₁_c = 1`; second trial means `m₂_b = 5 + 2·1{x}`, `m₂_c = 3`. The contrasts on the identity
  scale are common (`τ_ac = -(1 + 1{x})`, `τ_bc = -(2 + 2·1{x})`), the conditional means of `c`
  are not. All assumptions of the anchored theorem hold, and the anchored estimand, the target
  average conditional effect and the target marginal effect are all `5/4`.
* **The logit scale: the conditional, not the marginal, effect** (`anchored_logit_witness`). All
  three populations have two equally likely strata `x = ±1` and the risks `σ(x)` under `a` and
  `c`, `σ(x + 3/2)` under `b`. All assumptions hold with the domain `(0, 1)` of the logit, the
  anchored estimand is the conditional log odds ratio `3/2`, and the target marginal log odds
  ratio lies strictly between `0` and `3/2`; here absolute constancy also holds, and the marginal
  effect is the difference of the standardized marginal contrasts. `anchored_logit_exists` is
  the general part (d) applied to the logit.
* **The log scale: collapsible, not directly collapsible** (`anchored_log_witness`). Two equally
  likely strata, risks `1/4` and `1/2` under `a` and `c`, doubled under `b`. All assumptions hold
  with the domain `(0, ∞)`, the conditional log risk ratio is `log 2` in both strata, and the
  anchored estimand, the average conditional effect and the marginal effect are all `log 2`.
* **An omitted effect modifier** (`anchored_omitted_witness`). Covariates `(x, w)`, the adjustment
  set is `x` and `w` is omitted; `x` has two equally likely strata everywhere and `w` is
  independent of `x`, binary with `P(w) = 1/2` in the trials and `1/4` in the target. The means
  `m_a = 1{x}`, `m_b = m_c = 1{x} + 1{w}` are common to all populations, so with the full
  covariate all assumptions hold and the anchored estimand is the target effect `1/4`. Adjusting
  for `x` alone, the reduced means are the averages over the law of `w`, the anchored estimand
  built from them is `1/2`, and the bias `1/4` is the residual term of
  `PopulationAdjustment.anchoredEstimand_kernelAverage_sub_integral_compProd`.
* **An imbalanced effect modifier with zero bias** (`anchored_omitted_zero_bias_witness`). The
  same construction with `w ∈ {0, 1, 2}`, `m_b = m_c = 1{x} + w/2`, the law `(1/4, 1/2, 1/4)` of
  `w` in the trials and `(2/5, 1/5, 2/5)` in the target: `w` modifies the effect of `c` against
  `a` and is imbalanced, yet the reduced anchored estimand is the target effect `1/2`.

## Main definitions

* `finiteCovTrial`, `finiteCovSetting`: trials on a finite covariate whose potential outcomes are
  their own conditional means.
* `omittedSetting`: the setting with covariates `(x, w)` and `w` independent of `x`.

## Main results

* `finiteCovSetting_identificationAssumptions`, `omittedSetting_identificationAssumptions`,
  `finiteCovTrial_prod_isCondMean`.
* `anchored_identification_example`, `anchored_logit_witness`, `anchored_logit_exists`,
  `anchored_log_witness`, `anchored_omitted_witness`, `anchored_omitted_zero_bias_witness`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison Transport

/-! ### Trials on a finite covariate -/

section Finite

variable {α : Type*} [MeasurableSpace α] [Finite α] [DiscreteMeasurableSpace α]

/-- A trial on the finite covariate `x` (the identity of the sample space `α`) with law `ν`
and potential outcomes `m t x`, which are their own conditional means. The assigned treatment
plays no role in the identification theorem; it is fixed at the comparator `2`. -/
noncomputable def finiteCovTrial (ν : Measure α) (m : Fin 3 → α → ℝ) : Trial α α (Fin 3) :=
  ⟨⟨ν, id, m⟩, fun _ => 2⟩

/-- A trial with a finite law is a finite population. -/
instance (ν : Measure α) [IsFiniteMeasure ν] (m : Fin 3 → α → ℝ) :
    IsFiniteMeasure (finiteCovTrial ν m).μ :=
  ‹_›

/-- In `finiteCovTrial ν m` the function `m t` is a conditional mean function of arm `t`. -/
theorem finiteCovTrial_isCondMean (ν : Measure α) [IsFiniteMeasure ν] (m : Fin 3 → α → ℝ)
    (t : Fin 3) : (finiteCovTrial ν m).IsCondMean t (m t) :=
  Population.isCondMean_of_eq_comp measurable_id (measurable_of_finite _) rfl Integrable.of_finite

omit [Finite α] [DiscreteMeasurableSpace α] in
/-- The covariate law of `finiteCovTrial ν m` is `ν`. -/
theorem finiteCovTrial_covLaw (ν : Measure α) (m : Fin 3 → α → ℝ) :
    (finiteCovTrial ν m).covLaw = ν :=
  Measure.map_id

/-- The anchored setting of three trials on `α` with laws `ν₁`, `ν₂`, `ν` and means `m₁`, `m₂`,
`m`, with `a = 0`, `b = 1`, `c = 2`. -/
noncomputable def finiteCovSetting (ν₁ ν₂ ν : Measure α) (m₁ m₂ m : Fin 3 → α → ℝ) :
    AnchoredSetting α α α α (Fin 3) :=
  ⟨finiteCovTrial ν₁ m₁, finiteCovTrial ν₂ m₂, (finiteCovTrial ν m).toPopulation, 0, 1, 2⟩

section Instances

variable {α : Type*} [MeasurableSpace α] (ν₁ ν₂ ν : Measure α) (m₁ m₂ m : Fin 3 → α → ℝ)

/-- The first trial of the setting is a finite population. -/
instance [IsFiniteMeasure ν₁] : IsFiniteMeasure (finiteCovSetting ν₁ ν₂ ν m₁ m₂ m).ipdTrial.μ :=
  ‹_›

/-- The second trial of the setting is a finite population. -/
instance [IsFiniteMeasure ν₂] : IsFiniteMeasure (finiteCovSetting ν₁ ν₂ ν m₁ m₂ m).agdTrial.μ :=
  ‹_›

/-- The target of the setting is a finite population. -/
instance [IsFiniteMeasure ν] : IsFiniteMeasure (finiteCovSetting ν₁ ν₂ ν m₁ m₂ m).target.μ :=
  ‹_›

/-- The target of the setting is a probability population. -/
instance [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (finiteCovSetting ν₁ ν₂ ν m₁ m₂ m).target.μ :=
  ‹_›

end Instances

/-- **The assumptions for trials on a finite covariate**: on finite measures everything is
integrable and the potential outcomes are their own conditional means, so the assumptions of the
anchored theorem reduce to the domain conditions, relative constancy and overlap. -/
theorem finiteCovSetting_identificationAssumptions {ν₁ ν₂ ν : Measure α} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] [IsFiniteMeasure ν] {m₁ m₂ m : Fin 3 → α → ℝ} {g : ℝ → ℝ}
    {D : Set ℝ} (h₁ : ∀ᵐ x ∂ν₁, m₁ 0 x ∈ D ∧ m₁ 2 x ∈ D) (h₂ : ∀ᵐ x ∂ν₂, m₂ 1 x ∈ D ∧ m₂ 2 x ∈ D)
    (h : ∀ᵐ x ∂ν, m 0 x ∈ D ∧ m 1 x ∈ D ∧ m 2 x ∈ D)
    (hr₁ : ∀ᵐ x ∂ν, linkContrast g (m₁ 0) (m₁ 2) x = linkContrast g (m 0) (m 2) x)
    (hr₂ : ∀ᵐ x ∂ν, linkContrast g (m₂ 1) (m₂ 2) x = linkContrast g (m 1) (m 2) x)
    (hov₁ : ν ≪ ν₁) (hov₂ : ν ≪ ν₂) :
    (finiteCovSetting ν₁ ν₂ ν m₁ m₂ m).IdentificationAssumptions g D m₁ m₂ m := by
  have c₁ := finiteCovTrial_isCondMean ν₁ m₁
  have c₂ := finiteCovTrial_isCondMean ν₂ m₂
  have c := finiteCovTrial_isCondMean ν m
  have e₁ := finiteCovTrial_covLaw ν₁ m₁
  have e₂ := finiteCovTrial_covLaw ν₂ m₂
  have e := finiteCovTrial_covLaw ν m
  refine ⟨measurable_id, measurable_id, measurable_id, Integrable.of_finite, Integrable.of_finite,
    Integrable.of_finite, Integrable.of_finite, fun _ _ => Integrable.of_finite, c₁ 0, c₁ 2,
    c₂ 1, c₂ 2, fun t _ => c t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ∀ᵐ x ∂(finiteCovTrial ν₁ m₁).covLaw, m₁ 0 x ∈ D ∧ m₁ 2 x ∈ D
    rw [e₁]; exact h₁
  · change ∀ᵐ x ∂(finiteCovTrial ν₂ m₂).covLaw, m₂ 1 x ∈ D ∧ m₂ 2 x ∈ D
    rw [e₂]; exact h₂
  · change ∀ᵐ x ∂(finiteCovTrial ν m).covLaw, m 0 x ∈ D ∧ m 1 x ∈ D ∧ m 2 x ∈ D
    rw [e]; exact h
  · refine ⟨linkContrast g (m₁ 0) (m₁ 2), _, _, _, _, c₁ 0, c₁ 2, c 0, c 2,
      Filter.Eventually.of_forall fun _ => rfl, ?_⟩
    change ∀ᵐ x ∂(finiteCovTrial ν m).covLaw, _
    rw [e]; exact hr₁.mono fun _ hx => hx.symm
  · refine ⟨linkContrast g (m₂ 1) (m₂ 2), _, _, _, _, c₂ 1, c₂ 2, c 1, c 2,
      Filter.Eventually.of_forall fun _ => rfl, ?_⟩
    change ∀ᵐ x ∂(finiteCovTrial ν m).covLaw, _
    rw [e]; exact hr₂.mono fun _ hx => hx.symm
  · change (finiteCovTrial ν m).covLaw ≪ (finiteCovTrial ν₁ m₁).covLaw
    rw [e, e₁]; exact hov₁
  · change (finiteCovTrial ν m).covLaw ≪ (finiteCovTrial ν₂ m₂).covLaw
    rw [e, e₂]; exact hov₂
  · change Integrable _ (finiteCovTrial ν m).covLaw
    rw [e]; exact Integrable.of_finite
  · change Integrable _ (finiteCovTrial ν m).covLaw
    rw [e]; exact Integrable.of_finite

end Finite

/-! ### Relative constancy without absolute constancy -/

/-- The target means `m_a = 1 + 1{x}`, `m_b = 2 + 2·1{x}`, `m_c = 0`. -/
noncomputable def anchoredExampleTargetMean (t : Fin 3) (x : Bool) : ℝ :=
  ![1 + if x then 1 else 0, 2 + if x then 2 else 0, 0] t

/-- The means of the first trial: `m₁_a = 2 + 1{x}`, `m₁_c = 1` (and `m₁_b = m_b`). -/
noncomputable def anchoredExampleIpdMean (t : Fin 3) (x : Bool) : ℝ :=
  ![2 + if x then 1 else 0, 2 + if x then 2 else 0, 1] t

/-- The means of the second trial: `m₂_b = 5 + 2·1{x}`, `m₂_c = 3` (and `m₂_a = m_a`). -/
noncomputable def anchoredExampleAgdMean (t : Fin 3) (x : Bool) : ℝ :=
  ![1 + if x then 1 else 0, 5 + if x then 2 else 0, 3] t

/-- The setting of `anchored_identification_example`. -/
noncomputable def anchoredExampleSetting : AnchoredSetting Bool Bool Bool Bool (Fin 3) :=
  finiteCovSetting halfLaw halfLaw standardizationTargetLaw anchoredExampleIpdMean
      anchoredExampleAgdMean
    anchoredExampleTargetMean

/-- The first trial of the setting is a finite population. -/
instance : IsFiniteMeasure anchoredExampleSetting.ipdTrial.μ := by
  unfold anchoredExampleSetting; infer_instance

/-- The second trial of the setting is a finite population. -/
instance : IsFiniteMeasure anchoredExampleSetting.agdTrial.μ := by
  unfold anchoredExampleSetting; infer_instance

/-- The target of the setting is a probability population. -/
instance : IsProbabilityMeasure anchoredExampleSetting.target.μ := by
  unfold anchoredExampleSetting; infer_instance

/-- A statement holding almost surely under `standardizationTargetLaw` holds at both values,
since both have positive probability. -/
theorem forall_of_ae_standardizationTargetLaw {P : Bool → Prop}
    (h : ∀ᵐ x ∂standardizationTargetLaw, P x) :
    ∀ x, P x := by
  intro x
  have := (ae_stratumLaw_iff _).1 h x
  cases x <;> norm_num at this <;> exact this

/-- **An instance of the anchored identification theorem with relative but not absolute constancy.**
In `anchoredExampleSetting` all the assumptions hold on the identity scale; the conditional mean of
the comparator is not common to the first trial and the target (`1` against `0`); and the anchored
estimand, the target average conditional effect of `b` relative to `a` and the target marginal
effect are all `5/4`. -/
theorem anchored_identification_example :
    anchoredExampleSetting.IdentificationAssumptions id Set.univ anchoredExampleIpdMean
        anchoredExampleAgdMean
        anchoredExampleTargetMean ∧
      ¬ StructurallyInvariant anchoredExampleSetting.ipdTrial.μ anchoredExampleSetting.ipdTrial.X
        (anchoredExampleSetting.ipdTrial.Y 2) anchoredExampleSetting.target.μ
            anchoredExampleSetting.target.X
        (anchoredExampleSetting.target.Y 2) ∧
      anchoredEstimand anchoredExampleSetting.target.covLaw
          (linkContrast id (anchoredExampleIpdMean 0) (anchoredExampleIpdMean 2))
          (linkContrast id (anchoredExampleAgdMean 1) (anchoredExampleAgdMean 2)) = 5 / 4 ∧
      linkConditional id anchoredExampleSetting.target.covLaw (anchoredExampleTargetMean 0)
          (anchoredExampleTargetMean 1) = 5 / 4 ∧
      anchoredExampleSetting.target.marginalEffect id 0 1 = 5 / 4 := by
  have hov : standardizationTargetLaw ≪ halfLaw := by
    intro s hs
    rw [measure_eq_zero_iff_ae_notMem, ae_halfLaw_iff] at hs
    rw [Set.eq_empty_of_forall_notMem hs, measure_empty]
  have hc : ∀ x, linkContrast id (anchoredExampleIpdMean 0) (anchoredExampleIpdMean 2) x =
      linkContrast id (anchoredExampleTargetMean 0) (anchoredExampleTargetMean 2) x := fun x => by
    cases x <;> norm_num [linkContrast, anchoredExampleIpdMean, anchoredExampleTargetMean]
  have hc' : ∀ x, linkContrast id (anchoredExampleAgdMean 1) (anchoredExampleAgdMean 2) x =
      linkContrast id (anchoredExampleTargetMean 1) (anchoredExampleTargetMean 2) x := fun x => by
    cases x <;> norm_num [linkContrast, anchoredExampleAgdMean, anchoredExampleTargetMean]
  have hA : anchoredExampleSetting.IdentificationAssumptions id Set.univ anchoredExampleIpdMean
      anchoredExampleAgdMean
      anchoredExampleTargetMean :=
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
  have hcond : linkConditional id anchoredExampleSetting.target.covLaw (anchoredExampleTargetMean 0)
      (anchoredExampleTargetMean 1) = 5 / 4 := by
    rw [hcov, linkConditional, hint]
    norm_num [linkContrast, anchoredExampleTargetMean]
  obtain ⟨-, -, -, -, -, hest, -⟩ := hA.identification measurable_id
  obtain ⟨-, hmarg⟩ := hA.anchoredEstimand_eq_marginalEffect measurable_id MeasurableSet.univ
    (Or.inl linkDirectlyCollapsible_id)
  refine ⟨hA, ?_, hest.trans hcond, hcond, hmarg ▸ hest.trans hcond⟩
  rintro ⟨f, hf⟩
  rw [Population.isCommonRegression_iff] at hf
  have e₁ := hf.1.ae_eq measurable_id (finiteCovTrial_isCondMean halfLaw anchoredExampleIpdMean 2)
  have e₂ := hf.2.ae_eq measurable_id (finiteCovTrial_isCondMean standardizationTargetLaw
    anchoredExampleTargetMean 2)
  rw [show anchoredExampleSetting.ipdTrial.covLaw = halfLaw from finiteCovTrial_covLaw _ _,
    ae_halfLaw_iff] at e₁
  have e₂' := forall_of_ae_standardizationTargetLaw (hcov ▸ e₂)
  have := (e₁ true).symm.trans (e₂' true)
  norm_num [anchoredExampleIpdMean, anchoredExampleTargetMean] at this

/-! ### The logit scale -/

/-- The means of the logit witness at `x = ±1`: `σ(x)` under `a` and `c`, `σ(x + 3/2)` under
`b`. -/
noncomputable def anchoredLogitMean (t : Fin 3) (v : Bool) : ℝ :=
  if t = 1 then logisticAct v else logisticRef v

/-- The setting of `anchored_logit_witness`: three equal populations with two equally likely
strata. -/
noncomputable def anchoredLogitSetting : AnchoredSetting Bool Bool Bool Bool (Fin 3) :=
  finiteCovSetting halfLaw halfLaw halfLaw anchoredLogitMean anchoredLogitMean anchoredLogitMean

/-- The first trial of the setting is a finite population. -/
instance : IsFiniteMeasure anchoredLogitSetting.ipdTrial.μ := by
  unfold anchoredLogitSetting; infer_instance

/-- The second trial of the setting is a finite population. -/
instance : IsFiniteMeasure anchoredLogitSetting.agdTrial.μ := by
  unfold anchoredLogitSetting; infer_instance

/-- The target of the setting is a probability population. -/
instance : IsProbabilityMeasure anchoredLogitSetting.target.μ := by
  unfold anchoredLogitSetting; infer_instance

/-- **The anchored theorem on the logit scale recovers the conditional, not the marginal, effect.**
The logit is not collapsible; in `anchoredLogitSetting` all the assumptions of the anchored theorem
hold with the domain `(0, 1)`; the conditional log odds ratio of `b` relative to `a` is `3/2` at
every covariate value, the anchored estimand and the target average conditional effect are `3/2`,
and the target marginal log odds ratio lies strictly between `0` and `3/2`. Absolute constancy holds
as well, and the marginal effect is the difference of the standardized marginal contrasts of the two
trials; the target arm means lie in `(0, 1)`. -/
theorem anchored_logit_witness :
    ¬ LinkCollapsible (Set.Ioo 0 1) logit ∧
      anchoredLogitSetting.IdentificationAssumptions logit (Set.Ioo 0 1) anchoredLogitMean
          anchoredLogitMean anchoredLogitMean ∧
      (∀ x, linkContrast logit (anchoredLogitMean 0) (anchoredLogitMean 1) x = 3 / 2) ∧
      anchoredEstimand anchoredLogitSetting.target.covLaw
          (linkContrast logit (anchoredLogitMean 0) (anchoredLogitMean 2))
          (linkContrast logit (anchoredLogitMean 1) (anchoredLogitMean 2)) = 3 / 2 ∧
      linkConditional logit anchoredLogitSetting.target.covLaw (anchoredLogitMean 0)
          (anchoredLogitMean 1) = 3 / 2 ∧
      0 < anchoredLogitSetting.target.marginalEffect logit 0 1 ∧
      anchoredLogitSetting.target.marginalEffect logit 0 1 < 3 / 2 ∧
      anchoredLogitSetting.target.marginalEffect logit 0 1 =
        linkMarginal logit anchoredLogitSetting.target.covLaw (anchoredLogitMean 0)
            (anchoredLogitMean 2) -
          linkMarginal logit anchoredLogitSetting.target.covLaw (anchoredLogitMean 1)
            (anchoredLogitMean 2) ∧
      ∀ t, anchoredLogitSetting.target.armMean t ∈ Set.Ioo 0 1 := by
  have m0 : anchoredLogitMean 0 = logisticRef := funext fun v => by simp [anchoredLogitMean]
  have m1 : anchoredLogitMean 1 = logisticAct := funext fun v => by simp [anchoredLogitMean]
  have m2 : anchoredLogitMean 2 = logisticRef := funext fun v => by
    simp [anchoredLogitMean, show (2 : Fin 3) ≠ 1 by decide]
  have hmem : ∀ t v, anchoredLogitMean t v ∈ Set.Ioo (0 : ℝ) 1 := fun t v => by
    unfold anchoredLogitMean logisticAct logisticRef
    split_ifs <;> exact sigmoid_mem_Ioo _
  have hall : ∀ v : Bool, (fun x : Bool => anchoredLogitMean 0 x ∈ Set.Ioo (0 : ℝ) 1 ∧
      anchoredLogitMean 2 x ∈ Set.Ioo (0 : ℝ) 1) v := fun v => ⟨hmem 0 v, hmem 2 v⟩
  have hA : anchoredLogitSetting.IdentificationAssumptions logit (Set.Ioo 0 1) anchoredLogitMean
      anchoredLogitMean
      anchoredLogitMean :=
    finiteCovSetting_identificationAssumptions (Filter.Eventually.of_forall hall)
      (Filter.Eventually.of_forall fun v => ⟨hmem 1 v, hmem 2 v⟩)
      (Filter.Eventually.of_forall fun v => ⟨hmem 0 v, hmem 1 v, hmem 2 v⟩)
      (Filter.Eventually.of_forall fun _ => rfl) (Filter.Eventually.of_forall fun _ => rfl)
      Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl
  have hcov : anchoredLogitSetting.target.covLaw = halfLaw := finiteCovTrial_covLaw _ _
  have hcon : ∀ x, linkContrast logit (anchoredLogitMean 0) (anchoredLogitMean 1) x = 3 / 2 := fun
      x => by
    rw [m0, m1]; exact logisticExample_contrast x
  have hcond : linkConditional logit anchoredLogitSetting.target.covLaw (anchoredLogitMean 0)
      (anchoredLogitMean 1) =
      3 / 2 := by
    rw [linkConditional, integral_congr_ae (Filter.Eventually.of_forall hcon), hcov,
      integral_const, probReal_univ, one_smul]
  have hmarg : anchoredLogitSetting.target.marginalEffect logit 0 1 =
      linkMarginal logit halfLaw logisticRef logisticAct := by
    rw [← m0, ← m1]; rfl
  obtain ⟨-, -, -, -, -, hest, -⟩ := hA.identification measurable_logit
  have hc : ∀ t, anchoredLogitSetting.target.IsCondMean t (anchoredLogitMean t) :=
      finiteCovTrial_isCondMean _ _
  have hsi : ∀ t, StructurallyInvariant anchoredLogitSetting.target.μ anchoredLogitSetting.target.X
      (anchoredLogitSetting.target.Y t) anchoredLogitSetting.target.μ anchoredLogitSetting.target.X
      (anchoredLogitSetting.target.Y t) := fun t =>
    ⟨_, (Population.isCommonRegression_iff t _).2 ⟨hc t, hc t⟩⟩
  have habs := anchoredLogitSetting.marginalEffect_eq_of_structurallyInvariant logit (m₁ :=
      anchoredLogitMean)
    (m₂ := anchoredLogitMean) measurable_id measurable_id measurable_id Integrable.of_finite
    Integrable.of_finite Integrable.of_finite Integrable.of_finite
    (fun _ _ => Integrable.of_finite) (hc 0) (hc 2) (hc 1) (hc 2) (hsi 0) (hsi 2) (hsi 1) (hsi 2)
    Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl
  refine ⟨not_linkCollapsible_logit, hA, hcon, hest.trans hcond, hcond, ?_, ?_, habs.1,
    fun t => ?_⟩
  · rw [hmarg]; exact logisticExample_bounds.1
  · rw [hmarg]; exact logisticExample_bounds.2
  · change ∫ v, anchoredLogitMean t v ∂halfLaw ∈ Set.Ioo 0 1
    rw [integral_halfLaw]
    obtain ⟨h₁, h₂⟩ := hmem t true
    obtain ⟨h₃, h₄⟩ := hmem t false
    constructor <;> linarith

/-- **Part (d) on the logit scale.** Since the logit is not collapsible on `(0, 1)`, there is an
anchored setting satisfying all the assumptions in which the target conditional log odds ratio is
almost surely a constant, equal to the anchored estimand, while the target marginal log odds ratio
differs from it. -/
theorem anchored_logit_exists :
    ∃ (𝒳 : Type) (_ : MeasurableSpace 𝒳) (S : AnchoredSetting 𝒳 𝒳 𝒳 𝒳 (Fin 3))
      (m : Fin 3 → 𝒳 → ℝ) (c₀ : ℝ),
      IsProbabilityMeasure S.target.μ ∧ S.a = 0 ∧ S.b = 1 ∧ S.c = 2 ∧
      S.IdentificationAssumptions logit (Set.Ioo 0 1) m m m ∧
      (∀ᵐ x ∂S.target.covLaw, linkContrast logit (m S.a) (m S.b) x = c₀) ∧
      anchoredEstimand S.target.covLaw (linkContrast logit (m S.a) (m S.c))
          (linkContrast logit (m S.b) (m S.c)) = c₀ ∧
      linkConditional logit S.target.covLaw (m S.a) (m S.b) = c₀ ∧
      S.target.marginalEffect logit S.a S.b ≠ c₀ :=
  AnchoredSetting.exists_anchoredEstimand_ne_marginalEffect not_linkCollapsible_logit

/-! ### The log scale: collapsible, not directly collapsible -/

/-- The means of the log scale witness: risks `1/4` and `1/2` in the two strata under `a` and
`c`, doubled under `b`. -/
noncomputable def anchoredLogMean (t : Fin 3) (v : Bool) : ℝ :=
  (if t = 1 then 2 else 1) * if v then 1 / 4 else 1 / 2

/-- The setting of `anchored_log_witness`: three equal populations with two equally likely
strata. -/
noncomputable def anchoredLogSetting : AnchoredSetting Bool Bool Bool Bool (Fin 3) :=
  finiteCovSetting halfLaw halfLaw halfLaw anchoredLogMean anchoredLogMean anchoredLogMean

/-- The first trial of the setting is a finite population. -/
instance : IsFiniteMeasure anchoredLogSetting.ipdTrial.μ := by
  unfold anchoredLogSetting; infer_instance

/-- The second trial of the setting is a finite population. -/
instance : IsFiniteMeasure anchoredLogSetting.agdTrial.μ := by
  unfold anchoredLogSetting; infer_instance

/-- The target of the setting is a probability population. -/
instance : IsProbabilityMeasure anchoredLogSetting.target.μ := by
  unfold anchoredLogSetting; infer_instance

/-- **The anchored theorem on a collapsible scale with a constant effect.** In `anchoredLogSetting`
all the assumptions hold on the log scale with the domain `(0, ∞)`; the conditional log risk ratio
of `b` relative to `a` is `log 2` in both strata, and the anchored estimand, the target average
conditional effect and the target marginal log risk ratio are all `log 2`; the target arm means are
positive. -/
theorem anchored_log_witness :
    anchoredLogSetting.IdentificationAssumptions Real.log (Set.Ioi 0) anchoredLogMean
        anchoredLogMean anchoredLogMean ∧
      (∀ x, linkContrast Real.log (anchoredLogMean 0) (anchoredLogMean 1) x = Real.log 2) ∧
      anchoredEstimand anchoredLogSetting.target.covLaw
          (linkContrast Real.log (anchoredLogMean 0) (anchoredLogMean 2))
          (linkContrast Real.log (anchoredLogMean 1) (anchoredLogMean 2)) = Real.log 2 ∧
      linkConditional Real.log anchoredLogSetting.target.covLaw (anchoredLogMean 0)
          (anchoredLogMean 1) = Real.log 2 ∧
      anchoredLogSetting.target.marginalEffect Real.log 0 1 = Real.log 2 ∧
      ∀ t, anchoredLogSetting.target.armMean t ∈ Set.Ioi 0 := by
  have hmem : ∀ t v, anchoredLogMean t v ∈ Set.Ioi (0 : ℝ) := fun t v => by
    unfold anchoredLogMean; split_ifs <;> norm_num
  have hA : anchoredLogSetting.IdentificationAssumptions Real.log (Set.Ioi 0) anchoredLogMean
      anchoredLogMean anchoredLogMean :=
    finiteCovSetting_identificationAssumptions
      (Filter.Eventually.of_forall fun v => ⟨hmem 0 v, hmem 2 v⟩)
      (Filter.Eventually.of_forall fun v => ⟨hmem 1 v, hmem 2 v⟩)
      (Filter.Eventually.of_forall fun v => ⟨hmem 0 v, hmem 1 v, hmem 2 v⟩)
      (Filter.Eventually.of_forall fun _ => rfl) (Filter.Eventually.of_forall fun _ => rfl)
      Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl
  have hcov : anchoredLogSetting.target.covLaw = halfLaw := finiteCovTrial_covLaw _ _
  have hcon : ∀ x, linkContrast Real.log (anchoredLogMean 0) (anchoredLogMean 1) x = Real.log 2 :=
      fun x => by
    simp only [linkContrast, anchoredLogMean, ite_true, show (0 : Fin 3) ≠ 1 by decide, ite_false]
    rw [← Real.log_div (by cases x <;> norm_num) (by cases x <;> norm_num)]
    cases x <;> norm_num
  have hcond : linkConditional Real.log anchoredLogSetting.target.covLaw (anchoredLogMean 0)
      (anchoredLogMean 1) =
      Real.log 2 := by
    rw [linkConditional, integral_congr_ae (Filter.Eventually.of_forall hcon), hcov,
      integral_const, probReal_univ, one_smul]
  obtain ⟨-, -, -, -, -, hest, -⟩ := hA.identification Real.measurable_log
  obtain ⟨-, hm⟩ := hA.anchoredEstimand_eq_marginalEffect Real.measurable_log
    measurableSet_Ioi (Or.inr ⟨linkCollapsible_log, Real.log 2,
      Filter.Eventually.of_forall hcon⟩)
  refine ⟨hA, hcon, hest.trans hcond, hcond, hm ▸ hest.trans hcond, fun t => ?_⟩
  change ∫ v, anchoredLogMean t v ∂halfLaw ∈ Set.Ioi 0
  rw [integral_halfLaw]
  have h₁ := hmem t true
  have h₂ := hmem t false
  simp only [Set.mem_Ioi] at h₁ h₂ ⊢
  linarith

/-! ### An omitted covariate -/

section Omitted

variable {𝒲 : Type*} [MeasurableSpace 𝒲] [Finite 𝒲] [DiscreteMeasurableSpace 𝒲]

/-- A law on finitely many strata with positive weights dominates every law on the strata. -/
theorem stratumLaw_absolutelyContinuous_of_pos {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {π : V → ℝ} (hπ : ∀ v, 0 < π v) (π' : V → ℝ) :
    stratumLaw π' ≪ stratumLaw π := by
  intro s hs
  rw [measure_eq_zero_iff_ae_notMem, ae_stratumLaw_iff] at hs ⊢
  exact fun v _ => hs v (hπ v)

/-- The anchored setting with covariates `(x, w)`: `x` has two equally likely strata everywhere,
`w` is independent of `x` with law `ρ` in both trials and `ρ_*` in the target, and the
potential outcome means `m` are common to the three populations. -/
noncomputable def omittedSetting (ρ ρt : Measure 𝒲) (m : Fin 3 → Bool × 𝒲 → ℝ) :
    AnchoredSetting (Bool × 𝒲) (Bool × 𝒲) (Bool × 𝒲) (Bool × 𝒲) (Fin 3) :=
  finiteCovSetting (halfLaw.prod ρ) (halfLaw.prod ρ) (halfLaw.prod ρt) m m m

/-- The first trial of the setting is a finite population. -/
instance (ρ ρt : Measure 𝒲) [IsFiniteMeasure ρ] (m : Fin 3 → Bool × 𝒲 → ℝ) :
    IsFiniteMeasure (omittedSetting ρ ρt m).ipdTrial.μ := by
  unfold omittedSetting; infer_instance

/-- The second trial of the setting is a finite population. -/
instance (ρ ρt : Measure 𝒲) [IsFiniteMeasure ρ] (m : Fin 3 → Bool × 𝒲 → ℝ) :
    IsFiniteMeasure (omittedSetting ρ ρt m).agdTrial.μ := by
  unfold omittedSetting; infer_instance

/-- The target of the setting is a probability population. -/
instance (ρ ρt : Measure 𝒲) [IsProbabilityMeasure ρt] (m : Fin 3 → Bool × 𝒲 → ℝ) :
    IsProbabilityMeasure (omittedSetting ρ ρt m).target.μ := by
  unfold omittedSetting; infer_instance

omit [DiscreteMeasurableSpace 𝒲] in
/-- The reduced adjustment set of a covariate `(x, w)` has the law of `x`, and the joint law is
that of `x` composed with the constant kernel `ρ`. -/
theorem finiteCovTrial_prod_covLaw (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]
    (m : Fin 3 → Bool × 𝒲 → ℝ) :
    (finiteCovTrial (halfLaw.prod ρ) m).fstCovariate.covLaw = halfLaw ∧
      (finiteCovTrial (halfLaw.prod ρ) m).covLaw =
        (finiteCovTrial (halfLaw.prod ρ) m).fstCovariate.covLaw ⊗ₘ Kernel.const Bool ρ := by
  have h : (finiteCovTrial (halfLaw.prod ρ) m).fstCovariate.covLaw = halfLaw := by
    change (halfLaw.prod ρ).map Prod.fst = halfLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨h, ?_⟩
  rw [h, Measure.compProd_const]
  exact finiteCovTrial_covLaw _ _

/-- **The reduced conditional means.** Given `x` alone, the conditional mean of arm `t` in the
population with law `halfLaw ⊗ ρ` is the average `x ↦ ∫ m t (x, w) dρ(w)`. -/
theorem finiteCovTrial_prod_isCondMean (ρ : Measure 𝒲) [IsProbabilityMeasure ρ]
    (m : Fin 3 → Bool × 𝒲 → ℝ) (t : Fin 3) :
    (finiteCovTrial (halfLaw.prod ρ) m).fstCovariate.IsCondMean t (fun x => ∫ w, m t (x, w) ∂ρ) :=
  (finiteCovTrial_isCondMean _ m t).kernelAverage measurable_id (finiteCovTrial_prod_covLaw ρ m).2
    Integrable.of_finite

/-- Integrals against `halfLaw ⊗ ρ` are iterated integrals. -/
theorem integral_halfLaw_prod (ρ : Measure 𝒲) [IsFiniteMeasure ρ] (f : Bool × 𝒲 → ℝ) :
    ∫ z, f z ∂(halfLaw.prod ρ) = ((∫ w, f (true, w) ∂ρ) + ∫ w, f (false, w) ∂ρ) / 2 := by
  rw [integral_prod f Integrable.of_finite, integral_halfLaw]

/-- **The assumptions with the full covariate.** With the covariate `(x, w)` and overlap
`ρ_* ≪ ρ`, all the assumptions of the anchored theorem hold on the identity scale in
`omittedSetting ρ ρ_* m`, since the means, and so the contrasts, are common. -/
theorem omittedSetting_identificationAssumptions (ρ ρt : Measure 𝒲) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ρt] (hρ : ρt ≪ ρ) (m : Fin 3 → Bool × 𝒲 → ℝ) :
    (omittedSetting ρ ρt m).IdentificationAssumptions id Set.univ m m m := by
  have hov : halfLaw.prod ρt ≪ halfLaw.prod ρ := by
    rw [← Measure.compProd_const, ← Measure.compProd_const]
    exact Measure.AbsolutelyContinuous.compProd_right (Filter.Eventually.of_forall fun _ => hρ)
  exact finiteCovSetting_identificationAssumptions
    (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩)
    (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩)
    (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial, trivial⟩)
    (Filter.Eventually.of_forall fun _ => rfl) (Filter.Eventually.of_forall fun _ => rfl) hov hov

/-- The means of the omitted effect modifier witness: `m_a = 1{x}`, `m_b = m_c = 1{x} + 1{w}`. -/
noncomputable def omittedMean (t : Fin 3) (z : Bool × Bool) : ℝ :=
  (if z.1 then 1 else 0) + if t = 0 then 0 else if z.2 then 1 else 0

/-- **An omitted effect modifier.** In `omittedSetting halfLaw standardizationTargetLaw
omittedMean`, `w` modifies the effect of `c` against `a` (`τ_ac(x, w) = 1{w}`) and has prevalence
`1/2` in the trials and `1/4` in the target. With the full covariate all assumptions hold and the
anchored estimand is the target marginal effect `1/4`. With the adjustment set `x` alone the
conditional means are the averages over the law of `w` in each population, so the reduced
contrasts are the averages of the full ones; the anchored estimand built from them is `1/2`, and,
by `anchoredEstimand_kernelAverage_sub_integral_compProd`, the bias `1/4` is the residual
`∫ (∫ τ_ac(x, ·) dρ - ∫ τ_ac(x, ·) dρ_*) dx - ∫ (∫ τ_bc(x, ·) dρ - ∫ τ_bc(x, ·) dρ_*) dx`. -/
theorem anchored_omitted_witness :
    let S := omittedSetting halfLaw standardizationTargetLaw omittedMean
    let m₁ : Fin 3 → Bool → ℝ := fun t x => ∫ w, omittedMean t (x, w) ∂halfLaw
    let mt : Fin 3 → Bool → ℝ := fun t x => ∫ w, omittedMean t (x, w) ∂standardizationTargetLaw
    S.IdentificationAssumptions id Set.univ omittedMean omittedMean omittedMean ∧
      anchoredEstimand S.target.covLaw (linkContrast id (omittedMean 0) (omittedMean 2))
          (linkContrast id (omittedMean 1) (omittedMean 2)) = 1 / 4 ∧
      S.target.marginalEffect id 0 1 = 1 / 4 ∧
      S.ipdTrial.fstCovariate.covLaw = halfLaw ∧ S.target.fstCovariate.covLaw = halfLaw ∧
      (∀ t, S.ipdTrial.fstCovariate.IsCondMean t (m₁ t)) ∧
      (∀ t, S.agdTrial.fstCovariate.IsCondMean t (m₁ t)) ∧
      (∀ t, S.target.fstCovariate.IsCondMean t (mt t)) ∧
      anchoredEstimand halfLaw (linkContrast id (m₁ 0) (m₁ 2)) (linkContrast id (m₁ 1) (m₁ 2)) =
        1 / 2 ∧
      (fun x => ∫ w, linkContrast id (omittedMean 0) (omittedMean 2) (x, w) ∂halfLaw) =
        linkContrast id (m₁ 0) (m₁ 2) ∧
      (fun x => ∫ w, linkContrast id (omittedMean 1) (omittedMean 2) (x, w) ∂halfLaw) =
        linkContrast id (m₁ 1) (m₁ 2) ∧
      anchoredEstimand halfLaw
          (fun x => ∫ w, linkContrast id (omittedMean 0) (omittedMean 2) (x, w) ∂halfLaw)
          (fun x => ∫ w, linkContrast id (omittedMean 1) (omittedMean 2) (x, w) ∂halfLaw) -
        anchoredEstimand S.target.covLaw (linkContrast id (omittedMean 0) (omittedMean 2))
          (linkContrast id (omittedMean 1) (omittedMean 2)) =
      (∫ x, (∫ w, linkContrast id (omittedMean 0) (omittedMean 2) (x, w) ∂halfLaw -
          ∫ w, linkContrast id (omittedMean 0) (omittedMean 2) (x, w) ∂standardizationTargetLaw)
            ∂halfLaw) -
        ∫ x, (∫ w, linkContrast id (omittedMean 1) (omittedMean 2) (x, w) ∂halfLaw -
          ∫ w, linkContrast id (omittedMean 1) (omittedMean 2) (x, w) ∂standardizationTargetLaw)
            ∂halfLaw ∧
      (∫ x, (∫ w, linkContrast id (omittedMean 0) (omittedMean 2) (x, w) ∂halfLaw -
          ∫ w, linkContrast id (omittedMean 0) (omittedMean 2) (x, w) ∂standardizationTargetLaw)
            ∂halfLaw) -
        ∫ x, (∫ w, linkContrast id (omittedMean 1) (omittedMean 2) (x, w) ∂halfLaw -
          ∫ w, linkContrast id (omittedMean 1) (omittedMean 2) (x, w) ∂standardizationTargetLaw)
            ∂halfLaw = 1 / 4 := by
  intro S m₁ mt
  have hA := omittedSetting_identificationAssumptions halfLaw standardizationTargetLaw
    (by rw [halfLaw]; exact stratumLaw_absolutelyContinuous_of_pos (fun _ => by norm_num) _)
    omittedMean
  have hint : ∀ f : Bool → ℝ, ∫ x, f x ∂standardizationTargetLaw = f true / 4 + 3 * f false / 4 :=
    fun f => by
      rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
      simp [standardizedRisk]; ring
  have hcov : S.target.covLaw = halfLaw.prod standardizationTargetLaw := finiteCovTrial_covLaw _ _
  have hmarg : S.target.marginalEffect id 0 1 = 1 / 4 := by
    change ∫ z, omittedMean 1 z ∂(halfLaw.prod standardizationTargetLaw) -
      ∫ z, omittedMean 0 z ∂(halfLaw.prod standardizationTargetLaw) = 1 / 4
    simp only [integral_halfLaw_prod, hint]
    norm_num [omittedMean]
  obtain ⟨-, -, -, -, -, hest, -⟩ := hA.identification measurable_id
  obtain ⟨-, hm⟩ := hA.anchoredEstimand_eq_marginalEffect measurable_id MeasurableSet.univ
    (Or.inl linkDirectlyCollapsible_id)
  refine ⟨hA, hm.trans hmarg, hmarg, (finiteCovTrial_prod_covLaw _ _).1,
    (finiteCovTrial_prod_covLaw _ _).1, finiteCovTrial_prod_isCondMean _ _,
    finiteCovTrial_prod_isCondMean _ _, finiteCovTrial_prod_isCondMean _ _, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [anchoredEstimand, linkContrast, m₁, integral_halfLaw]
    norm_num [omittedMean]
  · funext x
    simp only [linkContrast, id, m₁]
    exact integral_sub Integrable.of_finite Integrable.of_finite
  · funext x
    simp only [linkContrast, id, m₁]
    exact integral_sub Integrable.of_finite Integrable.of_finite
  · have key := anchoredEstimand_kernelAverage_sub_integral_compProd (ν := halfLaw)
      (κ₁ := Kernel.const Bool halfLaw) (κ₂ := Kernel.const Bool halfLaw)
      (κt := Kernel.const Bool standardizationTargetLaw)
      (τ₁ := linkContrast id (omittedMean 0) (omittedMean 2))
      (τ₂ := linkContrast id (omittedMean 1) (omittedMean 2)) Integrable.of_finite
      Integrable.of_finite Integrable.of_finite Integrable.of_finite
    simp only [Kernel.const_apply, Measure.compProd_const] at key
    rw [hcov]
    exact key
  · simp only [linkContrast, integral_halfLaw, hint]
    norm_num [omittedMean]

/-- The law `(1/4, 1/2, 1/4)` of the omitted `w ∈ {0, 1, 2}` in the trials. -/
noncomputable def zeroBiasTrialLaw : Measure (Fin 3) := stratumLaw ![1 / 4, 1 / 2, 1 / 4]

/-- The law `(2/5, 1/5, 2/5)` of the omitted `w ∈ {0, 1, 2}` in the target. -/
noncomputable def zeroBiasTargetLaw : Measure (Fin 3) := stratumLaw ![2 / 5, 1 / 5, 2 / 5]

/-- The law `(1/4, 1/2, 1/4)` is a probability measure. -/
instance : IsProbabilityMeasure zeroBiasTrialLaw :=
  isProbabilityMeasure_stratumLaw ⟨fun v => by fin_cases v <;> norm_num,
    by simp [Fin.sum_univ_three]; norm_num⟩

/-- The law `(2/5, 1/5, 2/5)` is a probability measure. -/
instance : IsProbabilityMeasure zeroBiasTargetLaw :=
  isProbabilityMeasure_stratumLaw ⟨fun v => by fin_cases v <;> norm_num,
    by simp [Fin.sum_univ_three]; norm_num⟩

/-- The means of the zero bias witness: `m_a = 1{x}`, `m_b = m_c = 1{x} + w/2`. -/
noncomputable def zeroBiasMean (t : Fin 3) (z : Bool × Fin 3) : ℝ :=
  (if z.1 then 1 else 0) + if t = 0 then 0 else ((z.2 : ℕ) : ℝ) / 2

/-- **An imbalanced effect modifier with zero bias.** In `omittedSetting zeroBiasTrialLaw
zeroBiasTargetLaw zeroBiasMean`, the omitted `w` modifies the effect of `c` against `a`
(`τ_ac(x, w) = w/2`) and its law differs between the trials and the target, yet both laws give
`w/2` the mean `1/2`. All assumptions hold with the full covariate, the target marginal effect is
`1/2`, and the anchored estimand built from the conditional means given `x` alone is also
`1/2`. -/
theorem anchored_omitted_zero_bias_witness :
    let S := omittedSetting zeroBiasTrialLaw zeroBiasTargetLaw zeroBiasMean
    let m₁ : Fin 3 → Bool → ℝ := fun t x => ∫ w, zeroBiasMean t (x, w) ∂zeroBiasTrialLaw
    S.IdentificationAssumptions id Set.univ zeroBiasMean zeroBiasMean zeroBiasMean ∧
      (∀ x, linkContrast id (zeroBiasMean 0) (zeroBiasMean 2) (x, 0) ≠
        linkContrast id (zeroBiasMean 0) (zeroBiasMean 2) (x, 1)) ∧
      zeroBiasTrialLaw ≠ zeroBiasTargetLaw ∧
      S.target.marginalEffect id 0 1 = 1 / 2 ∧
      S.ipdTrial.fstCovariate.covLaw = halfLaw ∧
      (∀ t, S.ipdTrial.fstCovariate.IsCondMean t (m₁ t)) ∧
      (∀ t, S.agdTrial.fstCovariate.IsCondMean t (m₁ t)) ∧
      anchoredEstimand halfLaw (linkContrast id (m₁ 0) (m₁ 2)) (linkContrast id (m₁ 1) (m₁ 2)) =
        1 / 2 := by
  intro S m₁
  have hA := omittedSetting_identificationAssumptions zeroBiasTrialLaw zeroBiasTargetLaw
    (stratumLaw_absolutelyContinuous_of_pos (fun v => by fin_cases v <;> norm_num) _) zeroBiasMean
  have hint : ∀ (π : Fin 3 → ℝ), (∀ v, 0 ≤ π v) → ∀ f : Fin 3 → ℝ,
      ∫ w, f w ∂stratumLaw π = π 0 * f 0 + π 1 * f 1 + π 2 * f 2 := fun π hπ f => by
    rw [integral_stratumLaw hπ, standardizedRisk, Fin.sum_univ_three]
  have h₁ : ∀ f : Fin 3 → ℝ, ∫ w, f w ∂zeroBiasTrialLaw = f 0 / 4 + f 1 / 2 + f 2 / 4 :=
    fun f => by
      rw [zeroBiasTrialLaw, hint _ (fun v => by fin_cases v <;> norm_num)]
      simp; ring
  have h₂ : ∀ f : Fin 3 → ℝ, ∫ w, f w ∂zeroBiasTargetLaw = 2 * f 0 / 5 + f 1 / 5 + 2 * f 2 / 5 :=
    fun f => by
      rw [zeroBiasTargetLaw, hint _ (fun v => by fin_cases v <;> norm_num)]
      simp; ring
  refine ⟨hA, fun x => ?_, fun h => ?_, ?_, (finiteCovTrial_prod_covLaw _ _).1,
    finiteCovTrial_prod_isCondMean _ _, finiteCovTrial_prod_isCondMean _ _, ?_⟩
  · norm_num [linkContrast, zeroBiasMean]
  · have := h₁ (fun w => if w = 0 then 1 else 0)
    rw [h, h₂] at this
    norm_num at this
  · change ∫ z, zeroBiasMean 1 z ∂(halfLaw.prod zeroBiasTargetLaw) -
      ∫ z, zeroBiasMean 0 z ∂(halfLaw.prod zeroBiasTargetLaw) = 1 / 2
    simp only [integral_halfLaw_prod, h₂]
    norm_num [zeroBiasMean]
  · simp only [anchoredEstimand, linkContrast, m₁, integral_halfLaw, h₁]
    norm_num [zeroBiasMean]

end Omitted

end PopulationAdjustment

end CausalInference
