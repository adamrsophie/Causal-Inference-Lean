/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Formula
public import CausalInference.Survival.RMST
public import CausalInference.Survival.HazardRatio

/-!
# Transport: survival effects

Survival times are discrete, `T : Ω → ℕ`, and the restricted mean survival time up to the
horizon `τ` is `rmst μ T τ = E[min(T, τ)]` (`rmst_eq_integral_min`).

* **The restricted mean survival time transports.** It is the mean of the outcome
  `min(T, τ)`, so the transport formula applies to it: under structural invariance of the
  conditional restricted mean `E[min(T(t), τ) | X]`, the target restricted mean is the mean of
  the common conditional restricted mean under the target covariate law
  (`rmst_eq_integral_common`), and the difference between arms is the mean of the conditional
  differences (`rmst_sub_eq_integral_sub`). The difference is collapsible: a conditional
  difference that does not vary with the covariates is the marginal difference in every
  population (`rmst_sub_eq_of_ae_eq_const`).
* **The hazard ratio does not.** With a common stratum hazard ratio, the conditional log
  hazard ratio is the same in every population, but the marginal hazard ratio at period `2`
  depends on the covariate law: with stratum hazard ratio
  `1/2` in two strata at both periods and fair treatment, the marginal period `2` hazard ratio is
  `329/578` when the strata have mass `1/2` each and `1/2` when one stratum has all the mass
  (`marginal_hazardRatio_not_transportable`). The marginal log hazard ratio is therefore not
  transportable.

## Main results

* `rmst_eq_integral_common`, `rmst_sub_eq_integral_sub`, `rmst_sub_eq_of_ae_eq_const`.
* `marginal_hazardRatio_not_transportable`.

## References

* P. Royston and M. K. B. Parmar, *Restricted mean survival time: an alternative to the hazard
  ratio for the design and analysis of randomized trials with a time-to-event outcome*, BMC
  Medical Research Methodology 13 (2013).
* M. A. Hernán, *The hazards of hazard ratios*, Epidemiology 21 (2010).
-/

@[expose] public section

namespace CausalInference

namespace Transport

open MeasureTheory ProbabilityTheory Survival

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsFiniteMeasure μ₁]
  [IsFiniteMeasure μ₂] {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳}

/-- The outcome `min(T, τ)` as a real random variable. -/
def truncTime {Ω : Type*} (T : Ω → ℕ) (τ : ℕ) : Ω → ℝ := fun ω => ((min (T ω) τ : ℕ) : ℝ)

theorem integrable_truncTime {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → ℕ} (hT : Measurable T) (τ : ℕ) : Integrable (truncTime T τ) μ := by
  refine Integrable.of_bound (C := τ)
    ((measurable_from_nat.comp (hT.min measurable_const)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  simp only [truncTime, Real.norm_eq_abs, Nat.abs_cast]
  exact_mod_cast min_le_right _ _

/-- **Transport of the restricted mean survival time.** If `g(X)` is a version of the
conditional restricted mean `E[min(T, τ) | X]` in the target, the target restricted mean is
`∫ g dP*_X`; if `g` is a common regression for the source and target survival times, this is
also `E₁[w(X₁) min(T₁, τ)]` under overlap, with `w` the density ratio. -/
theorem rmst_eq_integral_common {T₁ : Ω₁ → ℕ} {T₂ : Ω₂ → ℕ} (hX₁ : Measurable X₁)
    (hX₂ : Measurable X₂) (hT₁ : Measurable T₁) (hT₂ : Measurable T₂) (τ : ℕ) {g : 𝒳 → ℝ}
    (hcom : IsCommonRegression μ₁ X₁ (truncTime T₁ τ) μ₂ X₂ (truncTime T₂ τ) g)
    (hov : μ₂.map X₂ ≪ μ₁.map X₁) :
    rmst μ₂ T₂ τ = ∫ x, g x ∂(μ₂.map X₂) ∧
      rmst μ₂ T₂ τ = ∫ ω, densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * truncTime T₁ τ ω ∂μ₁ := by
  obtain ⟨hg, Hsrc, Htgt⟩ := hcom
  have h1 : rmst μ₂ T₂ τ = ∫ x, g x ∂(μ₂.map X₂) := by
    rw [rmst_eq_integral_min hT₂]
    exact (integral_target_eq_integral_common hX₂ (integrable_truncTime hT₂ τ) hg Htgt).2
  -- `w(X₁) min(T₁, τ)` is integrable since `w(X₁) g(X₁)` is and `0 ≤ min(T₁, τ) ≤ τ`
  have hwi : Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * truncTime T₁ τ ω) μ₁ := by
    have hw1 : Integrable (fun ω => densityRatio μ₁ X₁ μ₂ X₂ (X₁ ω) * (fun _ => (1 : ℝ)) (X₁ ω))
        μ₁ := (integrable_densityRatio_mul_iff hX₁ hov measurable_const).2 (integrable_const 1)
    refine (hw1.const_mul τ).mono' (((measurable_densityRatio μ₁ X₁ μ₂ X₂).comp hX₁).mul
      (measurable_from_nat.comp (hT₁.min measurable_const))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h0 := densityRatio_nonneg μ₁ X₁ μ₂ X₂ (X₁ ω)
    have hle : truncTime T₁ τ ω ≤ τ := by
      simp only [truncTime]; exact_mod_cast min_le_right _ _
    have hge : 0 ≤ truncTime T₁ τ ω := by simp only [truncTime]; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_nonneg hge, mul_one]
    nlinarith
  refine ⟨h1, ?_⟩
  rw [h1, integral_densityRatio_mul hX₁ hov hg,
    integral_densityRatio_mul_common hX₁ (integrable_truncTime hT₁ τ) Hsrc hwi]

/-- **The restricted mean difference is the mean of the conditional differences.** If `g t` is
a version of `E[min(T(t), τ) | X]` in a population, for both arms, the difference of the
restricted means is `∫ (g 1 - g 0) dP_X`. -/
theorem rmst_sub_eq_integral_sub {T : Bool → Ω₂ → ℕ} (hX₂ : Measurable X₂)
    (hT : ∀ t, Measurable (T t)) (τ : ℕ) {g : Bool → 𝒳 → ℝ} (hg : ∀ t, Measurable (g t))
    (H : ∀ t, (fun ω => g t (X₂ ω)) =ᵐ[μ₂]
      μ₂[truncTime (T t) τ | MeasurableSpace.comap X₂ inferInstance]) :
    rmst μ₂ (T true) τ - rmst μ₂ (T false) τ = ∫ x, (g true x - g false x) ∂(μ₂.map X₂) := by
  have h : ∀ t, rmst μ₂ (T t) τ = ∫ x, g t x ∂(μ₂.map X₂) := fun t => by
    rw [rmst_eq_integral_min (hT t)]
    exact (integral_target_eq_integral_common hX₂ (integrable_truncTime (hT t) τ) (hg t)
      (H t)).2
  have hi : ∀ t, Integrable (g t) (μ₂.map X₂) := fun t =>
    (integral_target_eq_integral_common hX₂ (integrable_truncTime (hT t) τ) (hg t) (H t)).1
  rw [h, h, integral_sub (hi true) (hi false)]

/-- **The restricted mean difference is collapsible, hence directly transportable.** Under the
hypotheses of `rmst_sub_eq_integral_sub` in a probability population, if the conditional
difference `g 1 - g 0` is the constant `c` almost everywhere under the covariate law, the
marginal difference of the restricted means is `c`. -/
theorem rmst_sub_eq_of_ae_eq_const [IsProbabilityMeasure μ₂] {T : Bool → Ω₂ → ℕ}
    (hX₂ : Measurable X₂) (hT : ∀ t, Measurable (T t)) (τ : ℕ) {g : Bool → 𝒳 → ℝ}
    (hg : ∀ t, Measurable (g t))
    (H : ∀ t, (fun ω => g t (X₂ ω)) =ᵐ[μ₂]
      μ₂[truncTime (T t) τ | MeasurableSpace.comap X₂ inferInstance]) {c : ℝ}
    (hc : ∀ᵐ x ∂(μ₂.map X₂), g true x - g false x = c) :
    rmst μ₂ (T true) τ - rmst μ₂ (T false) τ = c := by
  rw [rmst_sub_eq_integral_sub hX₂ hT τ hg H, integral_congr_ae hc]
  simp

/-! ### The hazard ratio -/

open Bias.HazardRatio PropHazards PropHazardsExample in
/-- **The marginal hazard ratio is not transportable.** Take fair treatment, two frailty strata
with untreated period risks `1/10` and `1/2` at both periods and a common stratum hazard ratio
`1/2` (`phRisk (1/2) ncRisk`). Both populations below share these stratum hazards (structural
invariance), and the stratum hazard ratio is `1/2` in each. With strata of mass `1/2` each the
marginal period `2` hazard ratio is `329/578`; with all the mass on the first stratum it is
`1/2`. Hence the marginal log hazard ratio differs between the two populations. -/
theorem marginal_hazardRatio_not_transportable :
    (∀ u, stratumHazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) true u /
        stratumHazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) false u =
          1 / 2) ∧
    hazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) true /
        hazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) false =
          329 / 578 ∧
    hazard2 exHalf (fun u => if u then 1 else 0) (phRisk (1 / 2) ncRisk)
        (phRisk (1 / 2) ncRisk) true /
      hazard2 exHalf (fun u => if u then 1 else 0) (phRisk (1 / 2) ncRisk)
        (phRisk (1 / 2) ncRisk) false = 1 / 2 ∧
    Real.log (329 / 578) ≠ Real.log (1 / 2) := by
  obtain ⟨-, h2, hs⟩ := noncollapsible_example
  refine ⟨hs, h2, ?_, ?_⟩
  · norm_num [hazard2, dead2Mass, surv1Mass, exHalf, phRisk, ncRisk, Fintype.sum_bool]
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (by norm_num : (0 : ℝ) < 329 / 578))
      (Set.mem_Ioi.2 (by norm_num : (0 : ℝ) < 1 / 2)) h
    norm_num at this

end Transport

end CausalInference
