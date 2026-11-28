/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.UnanchoredIdentification
public import CausalInference.PopulationAdjustment.AnchoredWitnesses

/-!
# Concrete models for the unanchored identification theorem

Every number is computed in the proof.

* **Recovery** (`unanchored_identification_example`). The source has two equally likely strata,
  the target has `P(x) = 1/4`, and the means `m_t(x) = (t + 1)/4 + 1{x}/8` are common to source and
  target. All assumptions hold on the log scale with the domain `(0, ∞)`; the target means of
  arms `0` and `1` are `9/32` and `17/32`, and the target marginal log risk ratio is
  `log (17/9)`, the unanchored estimand.
* **An omitted prognostic variable** (`unanchored_omitted_witness`). Covariates `(x, w)` with `x`
  in two equally likely strata everywhere and `w` independent of `x`, binary with prevalence `1/2`
  in the sources and `1/4` in the target; the means `m_a = 1{w}`, `m_b = 1{x}` are common to all
  populations. With the full covariate all assumptions hold and the target effect of `b`
  relative to `a` on the identity scale is `1/4`. Adjusting for `x` alone the surface of `a` is
  the constant `1/2`, its standardized value is `1/2` against the target mean `1/4` (the residual
  of `Population.armMean_omitted_residual` is `1/4`), and the unanchored estimand is `0`.
* **An imbalanced prognostic variable with zero bias** (`unanchored_omitted_zero_bias_witness`).
  The same construction with `w ∈ {0, 1, 2}`, law `(1/4, 1/2, 1/4)` in the sources and
  `(2/5, 1/5, 2/5)` in the target, and `m_a = w/2`: both laws give `w/2` the mean `1/2`, so the
  standardized surface of `a` given `x` alone is the target mean `1/2` and the residual is `0`.

## Main definitions

* `omittedUnanchored`: the unanchored setting with covariates `(x, w)`.

## Main results

* `omittedUnanchored_facts`, `unanchored_identification_example`, `unanchored_omitted_witness`,
  `unanchored_omitted_zero_bias_witness`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison Transport

/-! ### Recovery -/

/-- The unanchored setting with `standardizationSource` as the source of both arms `0` and `1`
and `standardizationTarget` as the target. -/
noncomputable def standardizationUnanchored : UnanchoredSetting Bool Bool Bool Bool (Fin 3) :=
  ⟨standardizationSource, standardizationSource, standardizationTarget, 0, 1⟩

/-- The first source of the setting is a finite population. -/
instance : IsFiniteMeasure standardizationUnanchored.sourceA.μ := by
  unfold standardizationUnanchored; infer_instance

/-- The second source of the setting is a finite population. -/
instance : IsFiniteMeasure standardizationUnanchored.sourceB.μ := by
  unfold standardizationUnanchored; infer_instance

/-- The target of the setting is a probability population. -/
instance : IsProbabilityMeasure standardizationUnanchored.target.μ := by
  unfold standardizationUnanchored; infer_instance

/-- **An instance of the unanchored identification theorem.** In `standardizationUnanchored`
all the assumptions hold on the log scale with the domain `(0, ∞)`, the target means of arms
`0` and `1` are `9/32` and `17/32`, and the target marginal log risk ratio of `1` against `0` is
`log (17/9)`, the unanchored estimand of the source surfaces. -/
theorem unanchored_identification_example :
    standardizationUnanchored.IdentificationAssumptions (Set.Ioi 0) (standardizationSurface 0)
        (standardizationSurface 1) ∧
      standardizationTarget.armMean 0 = 9 / 32 ∧ standardizationTarget.armMean 1 = 17 / 32 ∧
      standardizationUnanchored.target.marginalEffect Real.log 0 1 = Real.log (17 / 9) ∧
      standardizationUnanchored.target.marginalEffect Real.log 0 1 =
        linkMarginal Real.log standardizationTarget.covLaw (standardizationSurface 0)
          (standardizationSurface 1) := by
  have hX : Measurable standardizationSource.X := measurable_id
  have hX' : Measurable standardizationTarget.X := measurable_id
  have harm : ∀ t, standardizationTarget.armMean t = ((t : ℕ) + 1 : ℝ) / 4 + 1 / 32 := fun t => by
    rw [← (integral_covLaw_eq_armMean_of_structurallyInvariant hX hX' Integrable.of_finite
      Integrable.of_finite (standardizationSource_isCondMean t)
      (standardization_structurallyInvariant t) standardization_absolutelyContinuous).2,
      standardizationTarget_covLaw, integral_standardizationSurface]
  have h0 : standardizationTarget.armMean 0 = 9 / 32 := by rw [harm]; norm_num
  have h1 : standardizationTarget.armMean 1 = 17 / 32 := by rw [harm]; norm_num
  have hA : standardizationUnanchored.IdentificationAssumptions (Set.Ioi 0)
      (standardizationSurface 0) (standardizationSurface 1) :=
    ⟨hX, hX, hX', Integrable.of_finite, Integrable.of_finite, Integrable.of_finite,
      Integrable.of_finite, by change standardizationTarget.armMean 0 ∈ _; rw [h0]; norm_num,
      by change standardizationTarget.armMean 1 ∈ _; rw [h1]; norm_num,
      standardizationSource_isCondMean 0, standardizationSource_isCondMean 1,
      standardization_structurallyInvariant 0, standardization_structurallyInvariant 1,
      standardization_absolutelyContinuous, standardization_absolutelyContinuous,
      Integrable.of_finite, Integrable.of_finite⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hm⟩ := hA.identification Real.log
  refine ⟨hA, h0, h1, ?_, hm⟩
  change Real.log (standardizationTarget.armMean 1) - Real.log (standardizationTarget.armMean 0) =
    _
  rw [h0, h1, ← Real.log_div (by norm_num) (by norm_num)]
  norm_num

/-! ### An omitted prognostic variable -/

section Omitted

variable {𝒲 : Type*} [MeasurableSpace 𝒲] [Finite 𝒲] [DiscreteMeasurableSpace 𝒲]

/-- The unanchored setting with covariates `(x, w)`: `x` has two equally likely strata
everywhere, `w` is independent of `x` with law `ρ` in both sources and `ρ_*` in the target, and
the means `m` are common to the three populations; the arms are `a = 0` and `b = 1`. -/
noncomputable def omittedUnanchored (ρ ρt : Measure 𝒲) (m : Fin 3 → Bool × 𝒲 → ℝ) :
    UnanchoredSetting (Bool × 𝒲) (Bool × 𝒲) (Bool × 𝒲) (Bool × 𝒲) (Fin 3) :=
  ⟨(finiteCovTrial (halfLaw.prod ρ) m).toPopulation,
    (finiteCovTrial (halfLaw.prod ρ) m).toPopulation,
    (finiteCovTrial (halfLaw.prod ρt) m).toPopulation, 0, 1⟩

/-- The first source of the setting is a finite population. -/
instance (ρ ρt : Measure 𝒲) [IsFiniteMeasure ρ] (m : Fin 3 → Bool × 𝒲 → ℝ) :
    IsFiniteMeasure (omittedUnanchored ρ ρt m).sourceA.μ := by
  unfold omittedUnanchored; infer_instance

/-- The second source of the setting is a finite population. -/
instance (ρ ρt : Measure 𝒲) [IsFiniteMeasure ρ] (m : Fin 3 → Bool × 𝒲 → ℝ) :
    IsFiniteMeasure (omittedUnanchored ρ ρt m).sourceB.μ := by
  unfold omittedUnanchored; infer_instance

/-- The target of the setting is a probability population. -/
instance (ρ ρt : Measure 𝒲) [IsProbabilityMeasure ρt] (m : Fin 3 → Bool × 𝒲 → ℝ) :
    IsProbabilityMeasure (omittedUnanchored ρ ρt m).target.μ := by
  change IsProbabilityMeasure (halfLaw.prod ρt); infer_instance

/-- **The unanchored setting with an omitted covariate.** If `ρ_* ≪ ρ`, then with the full
covariate `(x, w)` all the assumptions of the unanchored theorem hold with the domain `ℝ`; given
`x` alone the source surface of each arm `t` is `m̃_t(x) = ∫ m_t(x, ·) dρ`; and its standardized
value under the law of `x` in the target misses the target mean of `Y(t)` by the residual
`∫ (∫ m_t(x, ·) dρ - ∫ m_t(x, ·) dρ_*) dx`. -/
theorem omittedUnanchored_facts (ρ ρt : Measure 𝒲) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ρt] (hρ : ρt ≪ ρ) (m : Fin 3 → Bool × 𝒲 → ℝ) :
    (omittedUnanchored ρ ρt m).IdentificationAssumptions Set.univ (m 0) (m 1) ∧
      (omittedUnanchored ρ ρt m).target.fstCovariate.covLaw = halfLaw ∧
      (∀ t, (omittedUnanchored ρ ρt m).sourceA.fstCovariate.IsCondMean t
        (fun x => ∫ w, m t (x, w) ∂ρ)) ∧
      ∀ t, ∫ x, (∫ w, m t (x, w) ∂ρ) ∂halfLaw - (omittedUnanchored ρ ρt m).target.armMean t =
        ∫ x, (∫ w, m t (x, w) ∂ρ - ∫ w, m t (x, w) ∂ρt) ∂halfLaw := by
  have hov : halfLaw.prod ρt ≪ halfLaw.prod ρ := by
    rw [← Measure.compProd_const, ← Measure.compProd_const]
    exact Measure.AbsolutelyContinuous.compProd_right (Filter.Eventually.of_forall fun _ => hρ)
  have cs := finiteCovTrial_isCondMean (halfLaw.prod ρ) m
  have ct := finiteCovTrial_isCondMean (halfLaw.prod ρt) m
  have es := finiteCovTrial_covLaw (halfLaw.prod ρ) m
  have et := finiteCovTrial_covLaw (halfLaw.prod ρt) m
  have hsi : ∀ t, StructurallyInvariant (halfLaw.prod ρ) id (m t) (halfLaw.prod ρt) id (m t) :=
    fun t => ⟨_, (Population.isCommonRegression_iff t _).2 ⟨cs t, ct t⟩⟩
  have hov' : (finiteCovTrial (halfLaw.prod ρt) m).covLaw ≪
      (finiteCovTrial (halfLaw.prod ρ) m).covLaw := by
    rw [es, et]; exact hov
  have lt := finiteCovTrial_prod_covLaw ρt m
  refine ⟨⟨measurable_id, measurable_id, measurable_id, Integrable.of_finite, Integrable.of_finite,
    Integrable.of_finite, Integrable.of_finite, trivial, trivial, cs 0, cs 1, hsi 0, hsi 1, hov',
    hov', Integrable.of_finite, Integrable.of_finite⟩, lt.1,
    finiteCovTrial_prod_isCondMean ρ m, fun t => ?_⟩
  have h := (Population.armMean_omitted_residual
    (P := (finiteCovTrial (halfLaw.prod ρ) m).toPopulation)
    (Q := (finiteCovTrial (halfLaw.prod ρt) m).toPopulation) measurable_id measurable_id
    (finiteCovTrial_prod_covLaw ρ m).2 lt.2 (cs t) (ct t) Integrable.of_finite Integrable.of_finite
    (by rw [lt.1]; exact Integrable.of_finite)).2
  rw [lt.1] at h
  simp only [Kernel.const_apply] at h
  exact h

/-- The means of the omitted prognostic witness: `m_a = 1{w}`, `m_b = 1{x}` (and `m_c = 0`). -/
noncomputable def prognosticMean (t : Fin 3) (z : Bool × Bool) : ℝ :=
  if t = 0 then (if z.2 then 1 else 0) else if t = 1 then (if z.1 then 1 else 0) else 0

/-- **An omitted prognostic variable.** In `omittedUnanchored halfLaw standardizationTargetLaw
prognosticMean` the variable `w` is prognostic for arm `a` (`m_a = 1{w}`) and has prevalence
`1/2` in the sources and `1/4` in the target. With the full covariate all the assumptions hold
and the target effect of `b` relative to `a` on the identity scale is `1/4`. Adjusting for `x`
alone the surface of `a` is `1/2`, its standardized value `1/2` misses the target mean `1/4` by
the residual `1/4`, and the unanchored estimand is `0`. -/
theorem unanchored_omitted_witness :
    let S := omittedUnanchored halfLaw standardizationTargetLaw prognosticMean
    let m₁ : Fin 3 → Bool → ℝ := fun t x => ∫ w, prognosticMean t (x, w) ∂halfLaw
    S.IdentificationAssumptions Set.univ (prognosticMean 0) (prognosticMean 1) ∧
      S.target.marginalEffect id 0 1 = 1 / 4 ∧
      (∀ t, S.sourceA.fstCovariate.IsCondMean t (m₁ t)) ∧
      (∀ t, S.sourceB.fstCovariate.IsCondMean t (m₁ t)) ∧
      S.target.armMean 0 = 1 / 4 ∧ ∫ x, m₁ 0 x ∂S.target.fstCovariate.covLaw = 1 / 2 ∧
      ∫ x, (∫ w, prognosticMean 0 (x, w) ∂halfLaw -
          ∫ w, prognosticMean 0 (x, w) ∂standardizationTargetLaw) ∂halfLaw = 1 / 4 ∧
      linkMarginal id S.target.fstCovariate.covLaw (m₁ 0) (m₁ 1) = 0 := by
  intro S m₁
  have hρ : standardizationTargetLaw ≪ halfLaw := by
    rw [halfLaw]; exact stratumLaw_absolutelyContinuous_of_pos (fun _ => by norm_num) _
  obtain ⟨hA, hcov, hcm, hres⟩ := omittedUnanchored_facts halfLaw standardizationTargetLaw hρ
    prognosticMean
  have hint : ∀ f : Bool → ℝ, ∫ x, f x ∂standardizationTargetLaw = f true / 4 + 3 * f false / 4 :=
    fun f => by
      rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
      simp [standardizedRisk]; ring
  have harm : ∀ t, S.target.armMean t =
      ∫ z, prognosticMean t z ∂(halfLaw.prod standardizationTargetLaw) := fun _ => rfl
  have h0 : S.target.armMean 0 = 1 / 4 := by
    rw [harm, integral_halfLaw_prod]; simp only [hint]; norm_num [prognosticMean]
  have h1 : S.target.armMean 1 = 1 / 2 := by
    rw [harm, integral_halfLaw_prod]; simp only [hint]; norm_num [prognosticMean]
  have hr := hres 0
  rw [h0] at hr
  refine ⟨hA, ?_, hcm, hcm, h0, ?_, ?_, ?_⟩
  · change S.target.armMean 1 - S.target.armMean 0 = 1 / 4
    rw [h0, h1]; norm_num
  · rw [hcov]; simp only [m₁, integral_halfLaw]; norm_num [prognosticMean]
  · rw [← hr]; simp only [integral_halfLaw]; norm_num [prognosticMean]
  · rw [hcov]; simp only [linkMarginal, m₁, integral_halfLaw]; norm_num [prognosticMean]

/-- The means of the zero bias witness: `m_a = w/2`, `m_b = 1{x}` (and `m_c = 0`). -/
noncomputable def zeroBiasPrognosticMean (t : Fin 3) (z : Bool × Fin 3) : ℝ :=
  if t = 0 then ((z.2 : ℕ) : ℝ) / 2 else if t = 1 then (if z.1 then 1 else 0) else 0

/-- **An imbalanced prognostic variable with zero bias.** In `omittedUnanchored zeroBiasTrialLaw
zeroBiasTargetLaw zeroBiasPrognosticMean` the omitted `w` is prognostic for arm `a`
(`m_a = w/2`) and its law differs between the sources and the target, yet both laws give `w/2`
the mean `1/2`: with `x` alone the standardized surface of `a` is the target mean `1/2` and the
residual is `0`. -/
theorem unanchored_omitted_zero_bias_witness :
    let S := omittedUnanchored zeroBiasTrialLaw zeroBiasTargetLaw zeroBiasPrognosticMean
    let m₁ : Fin 3 → Bool → ℝ := fun t x => ∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTrialLaw
    S.IdentificationAssumptions Set.univ (zeroBiasPrognosticMean 0) (zeroBiasPrognosticMean 1) ∧
      zeroBiasTrialLaw ≠ zeroBiasTargetLaw ∧
      (∀ x, zeroBiasPrognosticMean 0 (x, 0) ≠ zeroBiasPrognosticMean 0 (x, 1)) ∧
      (∀ t, S.sourceA.fstCovariate.IsCondMean t (m₁ t)) ∧
      S.target.armMean 0 = 1 / 2 ∧ ∫ x, m₁ 0 x ∂S.target.fstCovariate.covLaw = 1 / 2 ∧
      ∫ x, (∫ w, zeroBiasPrognosticMean 0 (x, w) ∂zeroBiasTrialLaw -
          ∫ w, zeroBiasPrognosticMean 0 (x, w) ∂zeroBiasTargetLaw) ∂halfLaw = 0 := by
  intro S m₁
  obtain ⟨hA, hcov, hcm, hres⟩ := omittedUnanchored_facts zeroBiasTrialLaw zeroBiasTargetLaw
    (stratumLaw_absolutelyContinuous_of_pos (fun v => by fin_cases v <;> norm_num) _)
    zeroBiasPrognosticMean
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
  have h0 : S.target.armMean 0 = 1 / 2 := by
    change ∫ z, zeroBiasPrognosticMean 0 z ∂(halfLaw.prod zeroBiasTargetLaw) = 1 / 2
    rw [integral_halfLaw_prod]; simp only [h₂]; norm_num [zeroBiasPrognosticMean]
  refine ⟨hA, fun h => ?_, fun x => ?_, hcm, h0, ?_, ?_⟩
  · have := h₁ (fun w => if w = 0 then 1 else 0)
    rw [h, h₂] at this
    norm_num at this
  · norm_num [zeroBiasPrognosticMean]
  · rw [hcov]; simp only [m₁, integral_halfLaw, h₁]; norm_num [zeroBiasPrognosticMean]
  · simp only [integral_halfLaw, h₁, h₂]; norm_num [zeroBiasPrognosticMean]

end Omitted

end PopulationAdjustment

end CausalInference
