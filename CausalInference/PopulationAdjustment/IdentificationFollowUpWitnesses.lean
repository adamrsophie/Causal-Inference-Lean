/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.UnanchoredWitnesses

/-!
# Zero bias with an omitted covariate, through the residual identities

With an omitted covariate `W` the estimand built from the conditional means given `X` alone
misses the target by a residual: the anchored residual identity
`PopulationAdjustment.anchoredEstimand_kernelAverage_sub_integral_compProd` and the unanchored
`IndirectComparison.Population.armMean_omitted_residual`. Each residual of one trial is the mean
under the target law of `X` of the difference `∫ τ(x, ·) dκ_src x - ∫ τ(x, ·) dκ_* x` of two
averages of the full conditional contrast (or mean). It vanishes when the two averages agree for
almost every `x`, which holds when `W` is balanced given `X` (`κ_src = κ_*`) but also with an
imbalanced `W` whose effect modifying (or prognostic) function has the same mean under both laws.

* `anchoredEstimand_kernelAverage_eq_of_ae_eq`: if, in each trial, the two averages of the full
  contrast agree almost everywhere, the anchored estimand of the reduced contrasts is the
  anchored estimand of the full contrasts under the target joint law.
* `Population.integral_kernelAverage_eq_armMean`: if the two averages of the common
  conditional mean agree almost everywhere, the standardized reduced surface is the target mean.
* `anchored_omitted_zero_bias_of_residual`: in the model of
  `anchored_omitted_zero_bias_witness`, `τ_ac(x, w) = w/2` has average `1/2` under the trial law
  `(1/4, 1/2, 1/4)` and under the target law `(2/5, 1/5, 2/5)` of `w` at every `x`, and
  `τ_bc = 0`. The residual is zero because it cancels, not because `w` is balanced (the laws of
  `w` differ): against the mass differences `(-3/20, 3/10, -3/20)` of the two laws, the level
  `w = 1` contributes `3/20` and the level `w = 2` contributes `-3/20`. There is no cancellation
  between the two trials: each residual is zero by itself. The reduced anchored estimand is the
  target marginal effect `1/2` by the residual identity.
* `unanchored_omitted_zero_bias_of_residual`: in the model of
  `unanchored_omitted_zero_bias_witness`, the averages of `m_a(x, w) = w/2` agree (both `1/2`)
  and `m_b(x, w) = 1{x}` does not depend on `w`, so both residuals are zero, the standardized
  reduced surfaces are the target means, and the unanchored estimand of the reduced surfaces is
  the target marginal effect `0`.

## Main results

* `anchoredEstimand_kernelAverage_eq_of_ae_eq`,
  `Population.integral_kernelAverage_eq_armMean`.
* `anchored_omitted_zero_bias_of_residual`, `unanchored_omitted_zero_bias_of_residual`.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

open MeasureTheory ProbabilityTheory EffectMeasure

namespace PopulationAdjustment

open IndirectComparison

section General

variable {𝒳 𝒲 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒲]

/-- **Zero anchored bias when the averages of the omitted contrasts agree.** Let `τ₁`, `τ₂` be
the full contrasts of the two trials, integrable under the trial and target joint laws
`ν ⊗ κⱼ` and `ν ⊗ κ_*`. If for `ν` almost every `x` the average of `τⱼ(x, ·)` under `κⱼ x` equals
its average under `κ_* x` (for `j = 1, 2`), then the anchored estimand of the reduced contrasts
`x ↦ ∫ τⱼ(x, ·) dκⱼ x` under `ν` is the anchored estimand of the full contrasts under
`ν ⊗ κ_*`: both residuals of `anchoredEstimand_kernelAverage_sub_integral_compProd` vanish. -/
theorem anchoredEstimand_kernelAverage_eq_of_ae_eq {ν : Measure 𝒳} [SFinite ν]
    {κ₁ κ₂ κt : Kernel 𝒳 𝒲} [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] [IsSFiniteKernel κt]
    {τ₁ τ₂ : 𝒳 × 𝒲 → ℝ} (h₁ : Integrable τ₁ (ν ⊗ₘ κ₁)) (h₁t : Integrable τ₁ (ν ⊗ₘ κt))
    (h₂ : Integrable τ₂ (ν ⊗ₘ κ₂)) (h₂t : Integrable τ₂ (ν ⊗ₘ κt))
    (e₁ : ∀ᵐ x ∂ν, ∫ w, τ₁ (x, w) ∂κ₁ x = ∫ w, τ₁ (x, w) ∂κt x)
    (e₂ : ∀ᵐ x ∂ν, ∫ w, τ₂ (x, w) ∂κ₂ x = ∫ w, τ₂ (x, w) ∂κt x) :
    anchoredEstimand ν (fun x => ∫ w, τ₁ (x, w) ∂κ₁ x) (fun x => ∫ w, τ₂ (x, w) ∂κ₂ x) =
      anchoredEstimand (ν ⊗ₘ κt) τ₁ τ₂ := by
  have key := anchoredEstimand_kernelAverage_sub_integral_compProd h₁ h₁t h₂ h₂t
  rw [integral_eq_zero_of_ae (e₁.mono fun _ hx => sub_eq_zero.2 hx),
    integral_eq_zero_of_ae (e₂.mono fun _ hx => sub_eq_zero.2 hx), sub_zero] at key
  exact sub_eq_zero.1 key

variable {Ω₁ Ω₂ ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- **Zero bias of an arm when the averages of the omitted prognostic variable agree.** In the
setting of `Population.armMean_omitted_residual` (joint laws `P_X ⊗ κ_src` and `Q_X ⊗ κ_*`, a
conditional mean `m(x, w)` common to source and target, integrable potential outcomes), if for
`Q_X` almost every `x` the averages of `m(x, ·)` under `κ_src x` and `κ_* x` agree, then the
source surface given `X` alone, `x ↦ ∫ m(x, ·) dκ_src x`, is a conditional mean function of `Y(t)`
in the source and its standardized value under `Q_X` is the target mean of `Y(t)`. -/
theorem _root_.CausalInference.IndirectComparison.Population.integral_kernelAverage_eq_armMean
    {P : Population Ω₁ (𝒳 × 𝒲) ι} {Q : Population Ω₂ (𝒳 × 𝒲) ι} [IsFiniteMeasure P.μ]
    [IsFiniteMeasure Q.μ] {κs κt : Kernel 𝒳 𝒲} [IsMarkovKernel κs] [IsMarkovKernel κt]
    (hXP : Measurable P.X) (hXQ : Measurable Q.X) (hlawP : P.covLaw = P.fstCovariate.covLaw ⊗ₘ κs)
    (hlawQ : Q.covLaw = Q.fstCovariate.covLaw ⊗ₘ κt) {t : ι} {m : 𝒳 × 𝒲 → ℝ}
    (hmP : P.IsCondMean t m) (hmQ : Q.IsCondMean t m) (hYP : Integrable (P.Y t) P.μ)
    (hYQ : Integrable (Q.Y t) Q.μ) (hint : Integrable m (Q.fstCovariate.covLaw ⊗ₘ κs))
    (e : ∀ᵐ x ∂Q.fstCovariate.covLaw, ∫ w, m (x, w) ∂κs x = ∫ w, m (x, w) ∂κt x) :
    P.fstCovariate.IsCondMean t (fun x => ∫ w, m (x, w) ∂κs x) ∧
      ∫ x, (∫ w, m (x, w) ∂κs x) ∂Q.fstCovariate.covLaw = Q.armMean t := by
  obtain ⟨hc, hr⟩ := Population.armMean_omitted_residual hXP hXQ hlawP hlawQ hmP hmQ hYP hYQ hint
  rw [integral_eq_zero_of_ae (e.mono fun _ hx => sub_eq_zero.2 hx)] at hr
  exact ⟨hc, sub_eq_zero.1 hr⟩

end General

/-! ### The anchored witness -/

/-- The integral against a law on `Fin 3` given by weights. -/
theorem integral_stratumLaw_fin_three {π : Fin 3 → ℝ} (hπ : ∀ v, 0 ≤ π v) (f : Fin 3 → ℝ) :
    ∫ w, f w ∂stratumLaw π = π 0 * f 0 + π 1 * f 1 + π 2 * f 2 := by
  rw [integral_stratumLaw hπ, standardizedRisk, Fin.sum_univ_three]

/-- Integrals against `zeroBiasTrialLaw`. -/
theorem integral_zeroBiasTrialLaw (f : Fin 3 → ℝ) :
    ∫ w, f w ∂zeroBiasTrialLaw = f 0 / 4 + f 1 / 2 + f 2 / 4 := by
  rw [zeroBiasTrialLaw, integral_stratumLaw_fin_three (fun v => by fin_cases v <;> norm_num)]
  simp; ring

/-- Integrals against `zeroBiasTargetLaw`. -/
theorem integral_zeroBiasTargetLaw (f : Fin 3 → ℝ) :
    ∫ w, f w ∂zeroBiasTargetLaw = 2 * f 0 / 5 + f 1 / 5 + 2 * f 2 / 5 := by
  rw [zeroBiasTargetLaw, integral_stratumLaw_fin_three (fun v => by fin_cases v <;> norm_num)]
  simp; ring

/-- **The zero bias of the imbalanced effect modifier, through the residual identity.** In
`omittedSetting zeroBiasTrialLaw zeroBiasTargetLaw zeroBiasMean`, with reduced means
`m₁ t x = ∫ zeroBiasMean t (x, w) dρ(w)` for the trial law `ρ`:
* the contrast `τ_ac(x, w) = w/2` has the same average `1/2` under the trial law and under the
  target law of `w`, at every `x`, although the two laws differ;
* the contrast `τ_bc` is identically `0`;
* the residual of the first trial is `0` by cancellation inside the average over `w`: at every
  `x` the difference of the two averages of `τ_ac(x, ·)` is the sum over the levels of `w` of
  `τ_ac(x, w)` times the difference of the masses of the two laws, where the level `0` has
  `τ_ac = 0`, the level `1` contributes `(1/2)(1/2 - 1/5) = 3/20` and the level `2` contributes
  `1 · (1/4 - 2/5) = -3/20`; the residual of the second trial is `0` because `τ_bc = 0`; so the
  two residuals of `anchoredEstimand_kernelAverage_sub_integral_compProd` do not cancel each
  other, each is `0`;
* the reduced contrasts are the kernel averages of the full contrasts, and by
  `anchoredEstimand_kernelAverage_eq_of_ae_eq` the reduced anchored estimand equals the anchored
  estimand of the full contrasts under the target joint law, which the anchored identification
  theorem identifies with the target marginal effect `1/2`. -/
theorem anchored_omitted_zero_bias_of_residual :
    let S := omittedSetting zeroBiasTrialLaw zeroBiasTargetLaw zeroBiasMean
    let m₁ : Fin 3 → Bool → ℝ := fun t x => ∫ w, zeroBiasMean t (x, w) ∂zeroBiasTrialLaw
    let τ₁ := linkContrast id (zeroBiasMean 0) (zeroBiasMean 2)
    let τ₂ := linkContrast id (zeroBiasMean 1) (zeroBiasMean 2)
    zeroBiasTrialLaw ≠ zeroBiasTargetLaw ∧
      (∀ x, ∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw = 1 / 2 ∧
        ∫ w, τ₁ (x, w) ∂zeroBiasTargetLaw = 1 / 2) ∧
      (∀ x, ∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw - ∫ w, τ₁ (x, w) ∂zeroBiasTargetLaw =
          τ₁ (x, 0) * (1 / 4 - 2 / 5) + τ₁ (x, 1) * (1 / 2 - 1 / 5) + τ₁ (x, 2) * (1 / 4 - 2 / 5) ∧
        τ₁ (x, 0) = 0 ∧ τ₁ (x, 1) * (1 / 2 - 1 / 5) = 3 / 20 ∧
        τ₁ (x, 2) * (1 / 4 - 2 / 5) = -(3 / 20)) ∧
      (∀ z, τ₂ z = 0) ∧
      ∫ x, (∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw - ∫ w, τ₁ (x, w) ∂zeroBiasTargetLaw) ∂halfLaw = 0 ∧
      ∫ x, (∫ w, τ₂ (x, w) ∂zeroBiasTrialLaw - ∫ w, τ₂ (x, w) ∂zeroBiasTargetLaw) ∂halfLaw = 0 ∧
      (fun x => ∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw) = linkContrast id (m₁ 0) (m₁ 2) ∧
      (fun x => ∫ w, τ₂ (x, w) ∂zeroBiasTrialLaw) = linkContrast id (m₁ 1) (m₁ 2) ∧
      anchoredEstimand halfLaw (linkContrast id (m₁ 0) (m₁ 2)) (linkContrast id (m₁ 1) (m₁ 2)) =
        anchoredEstimand S.target.covLaw τ₁ τ₂ ∧
      anchoredEstimand halfLaw (linkContrast id (m₁ 0) (m₁ 2)) (linkContrast id (m₁ 1) (m₁ 2)) =
        S.target.marginalEffect id 0 1 ∧
      S.target.marginalEffect id 0 1 = 1 / 2 := by
  intro S m₁ τ₁ τ₂
  obtain ⟨hA, -, hne, hmarg, -, -, -, -⟩ := anchored_omitted_zero_bias_witness
  have hτ₁ : ∀ x, ∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw = 1 / 2 ∧
      ∫ w, τ₁ (x, w) ∂zeroBiasTargetLaw = 1 / 2 := fun x => by
    simp only [τ₁, linkContrast, id, zeroBiasMean, integral_zeroBiasTrialLaw,
      integral_zeroBiasTargetLaw]
    norm_num
  have hτ₂ : ∀ z, τ₂ z = 0 := fun z => by
    simp [τ₂, linkContrast, zeroBiasMean]
  have e₁ : ∀ x, ∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw = ∫ w, τ₁ (x, w) ∂zeroBiasTargetLaw :=
    fun x => (hτ₁ x).1.trans (hτ₁ x).2.symm
  have e₂ : ∀ x, ∫ w, τ₂ (x, w) ∂zeroBiasTrialLaw = ∫ w, τ₂ (x, w) ∂zeroBiasTargetLaw :=
    fun x => by simp only [hτ₂, integral_zero]
  have hcov : S.target.covLaw = halfLaw ⊗ₘ Kernel.const Bool zeroBiasTargetLaw := by
    rw [Measure.compProd_const]; exact finiteCovTrial_covLaw _ _
  have hred := anchoredEstimand_kernelAverage_eq_of_ae_eq (ν := halfLaw)
    (κ₁ := Kernel.const Bool zeroBiasTrialLaw) (κ₂ := Kernel.const Bool zeroBiasTrialLaw)
    (κt := Kernel.const Bool zeroBiasTargetLaw) (τ₁ := τ₁) (τ₂ := τ₂) Integrable.of_finite
    Integrable.of_finite Integrable.of_finite Integrable.of_finite
    (Filter.Eventually.of_forall e₁) (Filter.Eventually.of_forall e₂)
  simp only [Kernel.const_apply] at hred
  have k₁ : (fun x => ∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw) = linkContrast id (m₁ 0) (m₁ 2) := by
    funext x
    simp only [τ₁, linkContrast, id, m₁]
    exact integral_sub Integrable.of_finite Integrable.of_finite
  have k₂ : (fun x => ∫ w, τ₂ (x, w) ∂zeroBiasTrialLaw) = linkContrast id (m₁ 1) (m₁ 2) := by
    funext x
    simp only [τ₂, linkContrast, id, m₁]
    exact integral_sub Integrable.of_finite Integrable.of_finite
  obtain ⟨-, hm⟩ := hA.anchoredEstimand_eq_marginalEffect measurable_id MeasurableSet.univ
    (Or.inl linkDirectlyCollapsible_id)
  have hred' : anchoredEstimand halfLaw (linkContrast id (m₁ 0) (m₁ 2))
      (linkContrast id (m₁ 1) (m₁ 2)) = anchoredEstimand S.target.covLaw τ₁ τ₂ := by
    rw [← k₁, ← k₂, hred, ← hcov]
  have hdec : ∀ x, ∫ w, τ₁ (x, w) ∂zeroBiasTrialLaw - ∫ w, τ₁ (x, w) ∂zeroBiasTargetLaw =
        τ₁ (x, 0) * (1 / 4 - 2 / 5) + τ₁ (x, 1) * (1 / 2 - 1 / 5) + τ₁ (x, 2) * (1 / 4 - 2 / 5) ∧
      τ₁ (x, 0) = 0 ∧ τ₁ (x, 1) * (1 / 2 - 1 / 5) = 3 / 20 ∧
      τ₁ (x, 2) * (1 / 4 - 2 / 5) = -(3 / 20) := fun x => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [integral_zeroBiasTrialLaw, integral_zeroBiasTargetLaw]; ring
    all_goals simp only [τ₁, linkContrast, id, zeroBiasMean]; norm_num
  refine ⟨hne, hτ₁, hdec, hτ₂, ?_, ?_, k₁, k₂, hred', hred'.trans hm, hmarg⟩
  · exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => sub_eq_zero.2 (e₁ x))
  · exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => sub_eq_zero.2 (e₂ x))

/-! ### The unanchored witness -/

/-- **The zero bias of the imbalanced prognostic variable, through the residual identity.** In
`omittedUnanchored zeroBiasTrialLaw zeroBiasTargetLaw zeroBiasPrognosticMean`, with reduced
surfaces `m₁ t x = ∫ zeroBiasPrognosticMean t (x, w) dρ(w)` for the source law `ρ`:
* `m_a(x, w) = w/2` has the same average `1/2` under the source law and under the target law of
  `w`, at every `x`, although the two laws differ;
* `m_b(x, w) = 1{x}` does not depend on `w`, so its two averages agree;
* so both residuals of `Population.armMean_omitted_residual` are `0` (for `m_a` by cancellation
  inside the average over `w`, for `m_b` trivially), and by
  `Population.integral_kernelAverage_eq_armMean` each standardized reduced surface is the target
  mean of its arm (`1/2` for both arms), and the unanchored estimand of the
  reduced surfaces is the target marginal effect `0` on the identity scale. -/
theorem unanchored_omitted_zero_bias_of_residual :
    let S := omittedUnanchored zeroBiasTrialLaw zeroBiasTargetLaw zeroBiasPrognosticMean
    let m₁ : Fin 3 → Bool → ℝ := fun t x => ∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTrialLaw
    zeroBiasTrialLaw ≠ zeroBiasTargetLaw ∧
      (∀ x, ∫ w, zeroBiasPrognosticMean 0 (x, w) ∂zeroBiasTrialLaw = 1 / 2 ∧
        ∫ w, zeroBiasPrognosticMean 0 (x, w) ∂zeroBiasTargetLaw = 1 / 2) ∧
      (∀ x w w', zeroBiasPrognosticMean 1 (x, w) = zeroBiasPrognosticMean 1 (x, w')) ∧
      (∀ t, t = 0 ∨ t = 1 →
        ∫ x, (∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTrialLaw -
          ∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTargetLaw) ∂halfLaw = 0) ∧
      ∫ x, m₁ 0 x ∂S.target.fstCovariate.covLaw = S.target.armMean 0 ∧
      ∫ x, m₁ 1 x ∂S.target.fstCovariate.covLaw = S.target.armMean 1 ∧
      S.target.armMean 0 = 1 / 2 ∧ S.target.armMean 1 = 1 / 2 ∧
      linkMarginal id S.target.fstCovariate.covLaw (m₁ 0) (m₁ 1) = S.target.marginalEffect id 0 1 ∧
      S.target.marginalEffect id 0 1 = 0 := by
  intro S m₁
  obtain ⟨-, hne, -, -, h0, -, -⟩ := unanchored_omitted_zero_bias_witness
  have ha : ∀ x, ∫ w, zeroBiasPrognosticMean 0 (x, w) ∂zeroBiasTrialLaw = 1 / 2 ∧
      ∫ w, zeroBiasPrognosticMean 0 (x, w) ∂zeroBiasTargetLaw = 1 / 2 := fun x => by
    simp only [zeroBiasPrognosticMean, integral_zeroBiasTrialLaw, integral_zeroBiasTargetLaw]
    norm_num
  have hb : ∀ x w w', zeroBiasPrognosticMean 1 (x, w) = zeroBiasPrognosticMean 1 (x, w') :=
    fun x w w' => by simp [zeroBiasPrognosticMean]
  have e : ∀ t, t = 0 ∨ t = 1 → ∀ x, ∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTrialLaw =
      ∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTargetLaw := by
    rintro t (rfl | rfl) x
    · exact (ha x).1.trans (ha x).2.symm
    · rw [integral_congr_ae (Filter.Eventually.of_forall fun w => hb x w 0),
        integral_congr_ae (Filter.Eventually.of_forall fun w => hb x w 0)]
      simp
  have hres0 : ∀ t, t = 0 ∨ t = 1 →
      ∫ x, (∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTrialLaw -
        ∫ w, zeroBiasPrognosticMean t (x, w) ∂zeroBiasTargetLaw) ∂halfLaw = 0 := fun t ht =>
    integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => sub_eq_zero.2 (e t ht x))
  have hstd : ∀ t, t = 0 ∨ t = 1 → ∫ x, m₁ t x ∂S.target.fstCovariate.covLaw =
      S.target.armMean t := fun t ht =>
    (Population.integral_kernelAverage_eq_armMean
      (P := (finiteCovTrial (halfLaw.prod zeroBiasTrialLaw) zeroBiasPrognosticMean).toPopulation)
      (Q := (finiteCovTrial (halfLaw.prod zeroBiasTargetLaw) zeroBiasPrognosticMean).toPopulation)
      measurable_id measurable_id (finiteCovTrial_prod_covLaw _ _).2
      (finiteCovTrial_prod_covLaw _ _).2 (finiteCovTrial_isCondMean _ _ t)
      (finiteCovTrial_isCondMean _ _ t) Integrable.of_finite Integrable.of_finite
      (by rw [(finiteCovTrial_prod_covLaw zeroBiasTargetLaw _).1]; exact Integrable.of_finite)
      (by
        rw [(finiteCovTrial_prod_covLaw zeroBiasTargetLaw _).1]
        exact Filter.Eventually.of_forall (e t ht))).2
  have h1 : S.target.armMean 1 = 1 / 2 := by
    change ∫ z, zeroBiasPrognosticMean 1 z ∂(halfLaw.prod zeroBiasTargetLaw) = 1 / 2
    rw [integral_halfLaw_prod]
    simp only [integral_zeroBiasTargetLaw]
    norm_num [zeroBiasPrognosticMean]
  have hm : linkMarginal id S.target.fstCovariate.covLaw (m₁ 0) (m₁ 1) =
      S.target.marginalEffect id 0 1 := by
    rw [linkMarginal, hstd 0 (Or.inl rfl), hstd 1 (Or.inr rfl)]
    rfl
  refine ⟨hne, ha, hb, hres0, hstd 0 (Or.inl rfl), hstd 1 (Or.inr rfl), h0, h1, hm, ?_⟩
  change S.target.armMean 1 - S.target.armMean 0 = 0
  rw [h0, h1]; norm_num

end PopulationAdjustment

end CausalInference
