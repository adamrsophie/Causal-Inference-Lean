/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.ContinuousTime
public import CausalInference.Measures.LinkScale

/-!
# The restricted mean survival time is collapsible

**Time scale: continuous.** For conditional survival curves `S x` (a jointly measurable family
with values in `[0, 1]` on `[0, ∞)`, `IsSurvivalFamily`), a finite covariate law `ν` and a
horizon `τ ≥ 0`, the restricted mean of the population curve `s ↦ ∫ S x s dν(x)` is the
average of the conditional restricted means (`restrictedMean_popSurvival`). The integrand is
bounded on `ν ⊗ [0, τ]`, so Fubini's theorem applies, and the conditional restricted means are
integrable in the covariate (`integrable_restrictedMean`).

Hence the difference in restricted mean of two arms is collapsible: the marginal difference,
computed from the two population curves, is the average conditional difference, that is the
marginal and the average conditional effect on the identity scale of the conditional
restricted means (`linkMarginal id`, `linkConditional id` of `Measures/LinkScale.lean`;
`restrictedMean_popSurvival_sub`). A conditional difference that is almost surely a constant
`c` gives the marginal difference `c` under every covariate law
(`restrictedMean_popSurvival_sub_of_ae_eq`), which is the restricted mean case of
`linkCollapsible_id` (`restrictedMean_popSurvival_sub_eq_of_linkCollapsible` derives it from
there).

## Main results

* `integrable_uncurry_restrict`, `integrable_restrictedMean`, `restrictedMean_popSurvival`.
* `restrictedMean_popSurvival_sub`, `restrictedMean_popSurvival_sub_of_ae_eq`,
  `restrictedMean_popSurvival_sub_eq_of_linkCollapsible`.
* `restrictedMean_popSurvival_example`: with two equally likely strata of constant hazards `1`
  and `2` and the horizon `log 2`, the conditional restricted means are `1/2` and `3/8` and the
  restricted mean of the population curve is `7/16`.

## References

* P. Royston and M. K. B. Parmar, *Restricted mean survival time: an alternative to the hazard
  ratio for the design and analysis of randomized trials with a time-to-event outcome*, BMC
  Medical Research Methodology 13 (2013).
-/

@[expose] public section

namespace CausalInference

namespace Survival

namespace ContinuousTime

open MeasureTheory Set EffectMeasure

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {S Sa Sb : 𝒳 → ℝ → ℝ} {ν : Measure 𝒳} {τ : ℝ}

/-- A family of survival curves is integrable on `ν ⊗ (0, τ]` for a finite covariate law: it is
jointly measurable and bounded by `1` there. -/
theorem integrable_uncurry_restrict (hS : IsSurvivalFamily S) (ν : Measure 𝒳)
    [IsFiniteMeasure ν] (τ : ℝ) :
    Integrable (Function.uncurry S) (ν.prod (volume.restrict (Ioc 0 τ))) := by
  have hmem : ∀ᵐ p ∂(ν.prod (volume.restrict (Ioc 0 τ))), p.2 ∈ Ioc 0 τ :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
  refine Integrable.of_bound hS.measurable.aestronglyMeasurable 1 (hmem.mono fun p hp => ?_)
  change ‖S p.1 p.2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (hS.nonneg _ _ hp.1.le)]
  exact hS.le_one _ _ hp.1.le

/-- The restricted mean is the integral over `(0, τ]` for `τ ≥ 0`. -/
theorem restrictedMean_eq_setIntegral (S : ℝ → ℝ) (hτ : 0 ≤ τ) :
    restrictedMean S τ = ∫ s in Ioc 0 τ, S s := by
  rw [restrictedMean, intervalIntegral.integral_of_le hτ]

/-- The conditional restricted means of a family of survival curves are integrable in the
covariate under a finite law. -/
theorem integrable_restrictedMean (hS : IsSurvivalFamily S) (ν : Measure 𝒳) [IsFiniteMeasure ν]
    (hτ : 0 ≤ τ) : Integrable (fun x => restrictedMean (S x) τ) ν := by
  simp only [restrictedMean_eq_setIntegral _ hτ]
  exact (integrable_uncurry_restrict hS ν τ).integral_prod_left

/-- **The restricted mean of the population curve is the average of the conditional restricted
means**: `∫₀^τ (∫ S x s dν(x)) ds = ∫ (∫₀^τ S x s ds) dν(x)`, for a family of survival curves,
a finite covariate law and `τ ≥ 0`. -/
theorem restrictedMean_popSurvival (hS : IsSurvivalFamily S) (ν : Measure 𝒳) [IsFiniteMeasure ν]
    (hτ : 0 ≤ τ) : restrictedMean (popSurvival ν S) τ = ∫ x, restrictedMean (S x) τ ∂ν := by
  simp only [restrictedMean_eq_setIntegral _ hτ, popSurvival]
  exact (integral_integral_swap (integrable_uncurry_restrict hS ν τ)).symm

/-- **The difference in restricted mean is collapsible.** For two families of survival curves,
a finite covariate law and `τ ≥ 0`, the difference of the restricted means of the two population
curves is the average conditional difference; it is the marginal and the average conditional
effect on the identity scale of the conditional restricted means. -/
theorem restrictedMean_popSurvival_sub (hSa : IsSurvivalFamily Sa) (hSb : IsSurvivalFamily Sb)
    (ν : Measure 𝒳) [IsFiniteMeasure ν] (hτ : 0 ≤ τ) :
    restrictedMean (popSurvival ν Sb) τ - restrictedMean (popSurvival ν Sa) τ =
        ∫ x, (restrictedMean (Sb x) τ - restrictedMean (Sa x) τ) ∂ν ∧
      restrictedMean (popSurvival ν Sb) τ - restrictedMean (popSurvival ν Sa) τ =
        linkMarginal id ν (fun x => restrictedMean (Sa x) τ) (fun x => restrictedMean (Sb x) τ) ∧
      restrictedMean (popSurvival ν Sb) τ - restrictedMean (popSurvival ν Sa) τ =
        linkConditional id ν (fun x => restrictedMean (Sa x) τ)
          (fun x => restrictedMean (Sb x) τ) := by
  have h1 : restrictedMean (popSurvival ν Sb) τ - restrictedMean (popSurvival ν Sa) τ =
      ∫ x, (restrictedMean (Sb x) τ - restrictedMean (Sa x) τ) ∂ν := by
    rw [restrictedMean_popSurvival hSa ν hτ, restrictedMean_popSurvival hSb ν hτ,
      integral_sub (integrable_restrictedMean hSb ν hτ) (integrable_restrictedMean hSa ν hτ)]
  refine ⟨h1, ?_, ?_⟩
  · rw [linkMarginal, restrictedMean_popSurvival hSa ν hτ, restrictedMean_popSurvival hSb ν hτ]
    rfl
  · rw [h1]
    rfl

/-- **Collapsibility of the difference in restricted mean**: if the conditional difference is
almost surely the constant `c` under a covariate probability law, the marginal difference of
the population curves is `c`. -/
theorem restrictedMean_popSurvival_sub_of_ae_eq (hSa : IsSurvivalFamily Sa)
    (hSb : IsSurvivalFamily Sb) (ν : Measure 𝒳) [IsProbabilityMeasure ν] (hτ : 0 ≤ τ) {c : ℝ}
    (hc : ∀ᵐ x ∂ν, restrictedMean (Sb x) τ - restrictedMean (Sa x) τ = c) :
    restrictedMean (popSurvival ν Sb) τ - restrictedMean (popSurvival ν Sa) τ = c := by
  rw [(restrictedMean_popSurvival_sub hSa hSb ν hτ).1, integral_congr_ae hc]
  simp

/-- The same statement obtained from the collapsibility of the identity scale
(`linkCollapsible_id`), for a covariate space in `Type`. -/
theorem restrictedMean_popSurvival_sub_eq_of_linkCollapsible {𝒴 : Type} [MeasurableSpace 𝒴]
    {Ta Tb : 𝒴 → ℝ → ℝ} (hTa : IsSurvivalFamily Ta) (hTb : IsSurvivalFamily Tb)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] (hτ : 0 ≤ τ) {c : ℝ}
    (hc : ∀ᵐ x ∂ν, restrictedMean (Tb x) τ - restrictedMean (Ta x) τ = c) :
    restrictedMean (popSurvival ν Tb) τ - restrictedMean (popSurvival ν Ta) τ = c := by
  rw [(restrictedMean_popSurvival_sub hTa hTb ν hτ).2.1]
  exact linkCollapsible_id 𝒴 ν _ _ (integrable_restrictedMean hTa ν hτ)
    (integrable_restrictedMean hTb ν hτ) (Filter.Eventually.of_forall fun _ => ⟨trivial, trivial⟩)
    c hc

/-! ### An instance -/

/-- `exp (-(n log 2)) = 1 / 2 ^ n`. -/
theorem exp_neg_mul_log_two (n : ℕ) : Real.exp (-(n * Real.log 2)) = 1 / 2 ^ n := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), one_div]

/-- The stratum hazards of the instance: `2` in the stratum `true`, `1` in the stratum
`false`. -/
noncomputable def exampleRate (v : Bool) : ℝ := if v then 2 else 1

/-- The conditional curves of the instance: constant hazard `exampleRate v` in the stratum
`v`. -/
noncomputable def exampleCurve (v : Bool) (s : ℝ) : ℝ := Real.exp (-(exampleRate v * s))

theorem isSurvivalFamily_exampleCurve : IsSurvivalFamily exampleCurve := by
  refine ⟨(((measurable_of_countable exampleRate).comp measurable_fst).mul
    measurable_snd).neg.exp, fun v s _ => (Real.exp_pos _).le, fun v s hs => ?_⟩
  refine Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg ?_ hs))
  cases v <;> norm_num [exampleRate]

/-- **An instance of collapsibility with numbers.** Two equally likely strata with constant
hazards `2` and `1` and the horizon `log 2`: the conditional restricted means are `3/8` and
`1/2`, and the restricted mean of the population curve is their average `7/16`. -/
theorem restrictedMean_popSurvival_example :
    restrictedMean (exampleCurve true) (Real.log 2) = 3 / 8 ∧
      restrictedMean (exampleCurve false) (Real.log 2) = 1 / 2 ∧
      restrictedMean (popSurvival halfLaw exampleCurve) (Real.log 2) = 7 / 16 := by
  have e1 : Real.exp (-(1 * Real.log 2)) = 1 / 2 := by
    simpa using exp_neg_mul_log_two 1
  have e2 : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
    have := exp_neg_mul_log_two 2
    push_cast at this
    rw [this]
    norm_num
  have ht : restrictedMean (exampleCurve true) (Real.log 2) = 3 / 8 := by
    have : exampleCurve true = fun s => Real.exp (-(2 * s)) := by
      funext s; simp [exampleCurve, exampleRate]
    rw [this, restrictedMean_exp_mul two_ne_zero, e2]
    norm_num
  have hf : restrictedMean (exampleCurve false) (Real.log 2) = 1 / 2 := by
    have : exampleCurve false = fun s => Real.exp (-(1 * s)) := by
      funext s; simp [exampleCurve, exampleRate]
    rw [this, restrictedMean_exp_mul one_ne_zero, e1]
    norm_num
  refine ⟨ht, hf, ?_⟩
  rw [restrictedMean_popSurvival isSurvivalFamily_exampleCurve halfLaw
    (Real.log_nonneg one_le_two), integral_halfLaw, ht, hf]
  norm_num

end ContinuousTime

end Survival

end CausalInference
