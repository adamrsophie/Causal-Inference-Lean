/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.ContinuousTime
public import CausalInference.Bias.HazardMixtureGeneral
public import CausalInference.Measures.LinkScale

/-!
# The population hazard of a mixture of proportional hazards models

**Time scale: continuous.** A proportional hazards model on a covariate space `𝒳` has the
conditional hazard `h₀(s) ρ(x)`, with a baseline cumulative hazard `Λ₀` (`Λ₀' = h₀`) and a
relative hazard `ρ(x) ≥ 0`, so the conditional curves are `exp (-(ρ(x) Λ₀(s)))`
(`phSurvival`; their hazard is `ρ(x) h₀(s)`, `curveHazard_phSurvival`). Under a covariate law
`ν` the population curve is the survival of the general mixture of exponential laws of
`Bias.HazardMixtureGeneral` with rate law `ν.map ρ`, evaluated at the time `Λ₀(s)`
(`popSurvival_phSurvival`). Hence at every time with `Λ₀(s) > 0` the population hazard is
`h₀(s)` times the mean relative hazard among the survivors (`popHazard_phSurvival`), that is
`∫ h(s | x) S(s | x) dν / ∫ S(s | x) dν` (`popHazard_phSurvival_eq_div`).

**The population hazards are not proportional.** Multiply every conditional hazard by
`ψ > 0`, a conditional hazard ratio that is the same at every covariate value and every time.
The marginal hazard ratio at time `s` is the ratio of the population hazards. It is `ψ` when the
relative hazard is `ν`-almost surely constant (`popHazard_ratio_of_ae_eq`, in particular under a
point mass), strictly below `ψ` for `ψ > 1` and strictly above `ψ` for `ψ < 1` at every time with
`Λ₀(s) > 0` and `h₀(s) > 0` otherwise (`popHazard_ratio_lt`, `lt_popHazard_ratio`). So the
marginal hazard ratio differs from the conditional one and depends on the covariate law
(`popHazard_ratio_ne_dirac`).

**Finite mixtures.** For a finite stratifier with law `stratumLaw p` and stratum rates `r`, the
population curve, hazard and cumulative hazard of the model are `mixSurvival p r`,
`mixHazard p r` and `mixCumHazard p r` of `Bias.HazardMixture` (`popSurvival_stratumLaw`,
`popHazard_stratumLaw`, `popCumHazard_stratumLaw`), and the marginal hazard ratio is the ratio
of `mixHazard_ratio_lt` (`popHazard_ratio_stratumLaw`). In general the population cumulative
hazard is `genCumHazard (ν.map ρ) (Λ₀ s)` (`popCumHazard_phSurvival`).

## Main definitions

* `phSurvival Λ₀ ρ x s = exp (-(ρ x * Λ₀ s))`.

## Main results

* `curveHazard_phSurvival`, `isSurvivalFamily_phSurvival`, `popSurvival_phSurvival`,
  `popCumHazard_phSurvival`.
* `popHazard_phSurvival`, `popHazard_phSurvival_eq_div`, `popHazard_pos`.
* `curveHazard_phSurvival_ratio`, `popHazard_ratio`, `popHazard_ratio_of_ae_eq`,
  `popHazard_ratio_lt`, `lt_popHazard_ratio`, `popHazard_ratio_ne_dirac`.
* `popSurvival_stratumLaw`, `popHazard_stratumLaw`, `popHazard_ratio_stratumLaw`,
  `popCumHazard_stratumLaw`.

## References

* M. A. Hernán, *The hazards of hazard ratios*, Epidemiology 21 (2010).
* O. O. Aalen, R. J. Cook and K. Røysland, *Does Cox analysis of a randomized survival study
  yield a causal treatment effect?*, Lifetime Data Analysis 21 (2015).
-/

@[expose] public section

namespace CausalInference

namespace Survival

namespace ContinuousTime

open MeasureTheory Set Bias.HazardMixture Bias.HazardMixtureGeneral EffectMeasure

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The conditional curves of a **proportional hazards model**: baseline cumulative hazard
`Λ₀` and relative hazard `ρ`, `S(s | x) = exp (-(ρ x * Λ₀ s))`. -/
noncomputable def phSurvival (Λ₀ : ℝ → ℝ) (ρ : 𝒳 → ℝ) (x : 𝒳) (s : ℝ) : ℝ :=
  Real.exp (-(ρ x * Λ₀ s))

omit [MeasurableSpace 𝒳] in
theorem phSurvival_eq_expSurvival (Λ₀ : ℝ → ℝ) (ρ : 𝒳 → ℝ) (x : 𝒳) :
    phSurvival Λ₀ ρ x = expSurvival (fun s => ρ x * Λ₀ s) := rfl

omit [MeasurableSpace 𝒳] in
/-- **The conditional hazard of the model**: where `Λ₀` has derivative `h₀`, the curve
`phSurvival Λ₀ ρ x` has hazard `ρ x * h₀`. -/
theorem curveHazard_phSurvival {Λ₀ : ℝ → ℝ} {h₀ s : ℝ} (hΛ : HasDerivAt Λ₀ h₀ s) (ρ : 𝒳 → ℝ)
    (x : 𝒳) : curveHazard (phSurvival Λ₀ ρ x) s = ρ x * h₀ := by
  rw [phSurvival_eq_expSurvival]
  exact curveHazard_expSurvival (hΛ.const_mul (ρ x))

omit [MeasurableSpace 𝒳] in
/-- **The conditional hazard ratio is `ψ`**: multiplying the relative hazard by `ψ` multiplies
the conditional hazard by `ψ`, at every covariate value with `ρ x ≠ 0` and every time with
`h₀ ≠ 0`. -/
theorem curveHazard_phSurvival_ratio {Λ₀ : ℝ → ℝ} {h₀ s : ℝ} (hΛ : HasDerivAt Λ₀ h₀ s)
    (hh₀ : h₀ ≠ 0) (ρ : 𝒳 → ℝ) (ψ : ℝ) {x : 𝒳} (hx : ρ x ≠ 0) :
    curveHazard (phSurvival Λ₀ (fun x => ψ * ρ x) x) s / curveHazard (phSurvival Λ₀ ρ x) s =
      ψ := by
  rw [curveHazard_phSurvival hΛ, curveHazard_phSurvival hΛ]
  field_simp

/-- The conditional curves of the model form a family of survival curves when `ρ` is measurable
and nonnegative and `Λ₀` is measurable and nonnegative on `[0, ∞)`. -/
theorem isSurvivalFamily_phSurvival {Λ₀ : ℝ → ℝ} {ρ : 𝒳 → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hΛ : Measurable Λ₀) (hΛ0 : ∀ s, 0 ≤ s → 0 ≤ Λ₀ s) :
    IsSurvivalFamily (phSurvival Λ₀ ρ) :=
  ⟨((hρ.comp measurable_fst).mul (hΛ.comp measurable_snd)).neg.exp,
    fun _ _ _ => (Real.exp_pos _).le,
    fun x s hs => Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (hρ0 x) (hΛ0 s hs)))⟩

/-- **The population curve is the survival of a mixture of exponential laws**: with the rate
law `ν.map ρ`, `∫ exp (-(ρ x Λ₀ s)) dν(x) = genSurvival (ν.map ρ) (Λ₀ s)`. -/
theorem popSurvival_phSurvival {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (ν : Measure 𝒳) (Λ₀ : ℝ → ℝ) :
    popSurvival ν (phSurvival Λ₀ ρ) = fun s => genSurvival (ν.map ρ) (Λ₀ s) := by
  funext s
  rw [genSurvival, integral_map hρ.aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  rfl

/-- **The population cumulative hazard** is the cumulative hazard of the mixture of exponential
laws with rate law `ν.map ρ` at the time `Λ₀ s`. -/
theorem popCumHazard_phSurvival {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (ν : Measure 𝒳) (Λ₀ : ℝ → ℝ)
    (s : ℝ) : popCumHazard ν (phSurvival Λ₀ ρ) s = genCumHazard (ν.map ρ) (Λ₀ s) := by
  rw [popCumHazard, popSurvival_phSurvival hρ, genCumHazard]

/-- A nonnegative relative hazard gives an almost surely nonnegative rate law. -/
theorem ae_nonneg_map {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) {ν : Measure 𝒳}
    (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x) : ∀ᵐ r ∂(ν.map ρ), 0 ≤ r :=
  (ae_map_iff hρ.aemeasurable measurableSet_Ici).2 hρ0

/-- **The population hazard of a proportional hazards model.** For a covariate probability law,
a measurable relative hazard that is almost surely nonnegative, and a time `s` at which `Λ₀`
has derivative `h₀` and `Λ₀ s > 0`, the population hazard at `s` is `h₀` times the mean rate
among the survivors of the rate law `ν.map ρ` at the time `Λ₀ s`. -/
theorem popHazard_phSurvival {ν : Measure 𝒳} [IsProbabilityMeasure ν] {ρ : 𝒳 → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x) {Λ₀ : ℝ → ℝ} {h₀ s : ℝ}
    (hΛ : HasDerivAt Λ₀ h₀ s) (hΛs : 0 < Λ₀ s) :
    popHazard ν (phSurvival Λ₀ ρ) s = h₀ * genHazard (ν.map ρ) (Λ₀ s) := by
  have hν := ae_nonneg_map hρ hρ0
  have hd := (hasDerivAt_genSurvival hν hΛs).comp s hΛ
  rw [popHazard, curveHazard, popSurvival_phSurvival hρ]
  change -deriv (genSurvival (ν.map ρ) ∘ Λ₀) s / genSurvival (ν.map ρ) (Λ₀ s) = _
  rw [hd.deriv, genHazard_eq_div]
  ring

/-- **The survivor weighted form of the population hazard**:
`h(s) = ∫ h(s | x) S(s | x) dν / ∫ S(s | x) dν` with `h(s | x) = ρ x h₀`, under the hypotheses
of `popHazard_phSurvival`. -/
theorem popHazard_phSurvival_eq_div {ν : Measure 𝒳} [IsProbabilityMeasure ν] {ρ : 𝒳 → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x) {Λ₀ : ℝ → ℝ} {h₀ s : ℝ}
    (hΛ : HasDerivAt Λ₀ h₀ s) (hΛs : 0 < Λ₀ s) :
    popHazard ν (phSurvival Λ₀ ρ) s =
      (∫ x, ρ x * h₀ * phSurvival Λ₀ ρ x s ∂ν) / ∫ x, phSurvival Λ₀ ρ x s ∂ν := by
  rw [popHazard_phSurvival hρ hρ0 hΛ hΛs, genHazard_eq_div, genSurvival,
    integral_map hρ.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop)),
    integral_map hρ.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop)),
    mul_div_assoc', ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [phSurvival]
  ring

/-- The mean rate among the survivors is positive at every time `t > 0` when the rate is almost
surely positive. -/
theorem genHazard_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : ∀ᵐ r ∂μ, 0 < r) {t : ℝ}
    (ht : 0 < t) : 0 < genHazard μ t := by
  have hμ0 : ∀ᵐ r ∂μ, 0 ≤ r := hμ.mono fun r hr => hr.le
  rw [genHazard_eq_div]
  refine div_pos (integral_pos_of_ae_pos ?_ (hμ.mono fun r hr => mul_pos hr (Real.exp_pos _)))
    (genSurvival_pos hμ0 ht.le)
  have h := ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mem_interior_integrableExpSet hμ0 ht) 1
  refine (h.neg).congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [pow_one, Pi.neg_apply, exp_mul_negRate]
  simp only [negRate]
  ring

/-- **The population hazard is positive** under an almost surely positive relative hazard, at
every time with `Λ₀ s > 0` and `h₀ > 0`. -/
theorem popHazard_pos {ν : Measure 𝒳} [IsProbabilityMeasure ν] {ρ : 𝒳 → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂ν, 0 < ρ x) {Λ₀ : ℝ → ℝ} {h₀ s : ℝ} (hΛ : HasDerivAt Λ₀ h₀ s)
    (hΛs : 0 < Λ₀ s) (hh₀ : 0 < h₀) : 0 < popHazard ν (phSurvival Λ₀ ρ) s := by
  rw [popHazard_phSurvival hρ (hρ0.mono fun x hx => hx.le) hΛ hΛs]
  exact mul_pos hh₀ (genHazard_pos ((ae_map_iff hρ.aemeasurable measurableSet_Ioi).2 hρ0) hΛs)

/-! ### The marginal hazard ratio -/

section Ratio

variable {ν : Measure 𝒳} [IsProbabilityMeasure ν] {ρ : 𝒳 → ℝ} {Λ₀ : ℝ → ℝ} {h₀ s ψ : ℝ}

omit [IsProbabilityMeasure ν] in
/-- The rate law of the treated arm is the image of the rate law of the control arm under
`r ↦ ψ r`. -/
theorem map_const_mul (hρ : Measurable ρ) (ψ : ℝ) :
    ν.map (fun x => ψ * ρ x) = (ν.map ρ).map (fun r => ψ * r) := by
  rw [Measure.map_map (measurable_const_mul ψ) hρ]
  rfl

/-- **The marginal hazard ratio as a ratio of survivor mean rates**: for `ψ ≥ 0`, `h₀ ≠ 0`,
`Λ₀ s > 0` and an almost surely positive relative hazard, the ratio of the population hazards
of the relative hazards `ψ ρ` and `ρ` at `s` is
`genHazard ((ν.map ρ).map (ψ ·)) (Λ₀ s) / genHazard (ν.map ρ) (Λ₀ s)`. -/
theorem popHazard_ratio (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂ν, 0 < ρ x) (hψ : 0 ≤ ψ)
    (hΛ : HasDerivAt Λ₀ h₀ s) (hΛs : 0 < Λ₀ s) (hh₀ : h₀ ≠ 0) :
    popHazard ν (phSurvival Λ₀ (fun x => ψ * ρ x)) s / popHazard ν (phSurvival Λ₀ ρ) s =
      genHazard ((ν.map ρ).map (fun r => ψ * r)) (Λ₀ s) / genHazard (ν.map ρ) (Λ₀ s) := by
  rw [popHazard_phSurvival (hρ.const_mul ψ) (hρ0.mono fun x hx => mul_nonneg hψ hx.le) hΛ hΛs,
    popHazard_phSurvival hρ (hρ0.mono fun x hx => hx.le) hΛ hΛs, map_const_mul hρ,
    mul_div_mul_left _ _ hh₀]

/-- **With an almost surely constant relative hazard the marginal hazard ratio is `ψ`**, for
`ψ ≥ 0`, a constant `c > 0`, `h₀ ≠ 0` and `Λ₀ s > 0`. This covers a point mass. -/
theorem popHazard_ratio_of_ae_eq (hρ : Measurable ρ) {c : ℝ} (hc : 0 < c)
    (hρc : ∀ᵐ x ∂ν, ρ x = c) (hψ : 0 ≤ ψ) (hΛ : HasDerivAt Λ₀ h₀ s) (hΛs : 0 < Λ₀ s)
    (hh₀ : h₀ ≠ 0) :
    popHazard ν (phSurvival Λ₀ (fun x => ψ * ρ x)) s / popHazard ν (phSurvival Λ₀ ρ) s = ψ := by
  have hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x := hρc.mono fun x hx => hx ▸ hc.le
  have hmc : ∀ᵐ r ∂(ν.map ρ), r = c :=
    (ae_map_iff hρ.aemeasurable (measurableSet_singleton c)).2 hρc
  have hmψ : ∀ᵐ r ∂((ν.map ρ).map (fun r => ψ * r)), r = ψ * c := by
    rw [← map_const_mul hρ]
    exact (ae_map_iff (hρ.const_mul ψ).aemeasurable (measurableSet_singleton _)).2
      (hρc.mono fun x hx => by rw [hx])
  rw [popHazard_ratio hρ (hρc.mono fun x hx => hx ▸ hc) hψ hΛ hΛs hh₀,
    genHazard_eq_of_ae_eq (ae_nonneg_map (measurable_const_mul ψ)
      ((ae_nonneg_map hρ hρ0).mono fun r hr => mul_nonneg hψ hr)) hmψ
      hΛs.le, genHazard_eq_of_ae_eq (ae_nonneg_map hρ hρ0) hmc hΛs.le]
  field_simp

omit [IsProbabilityMeasure ν] in
/-- A relative hazard that is not `ν`-almost surely constant gives a rate law that is not almost
surely constant. -/
theorem not_ae_eq_map (hρ : Measurable ρ) (hnc : ¬ ∃ c, ∀ᵐ x ∂ν, ρ x = c) :
    ¬ ∃ c, ∀ᵐ r ∂(ν.map ρ), r = c := fun ⟨c, hc⟩ =>
  hnc ⟨c, ae_of_ae_map hρ.aemeasurable hc⟩

/-- **For `ψ > 1` the marginal hazard ratio is below the conditional one**: if the relative
hazard is almost surely positive and not almost surely constant, then at every time with
`Λ₀ s > 0` and `h₀ > 0` the marginal hazard ratio is strictly below `ψ`. -/
theorem popHazard_ratio_lt (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂ν, 0 < ρ x)
    (hnc : ¬ ∃ c, ∀ᵐ x ∂ν, ρ x = c) (hψ : 1 < ψ) (hΛ : HasDerivAt Λ₀ h₀ s) (hΛs : 0 < Λ₀ s)
    (hh₀ : 0 < h₀) :
    popHazard ν (phSurvival Λ₀ (fun x => ψ * ρ x)) s / popHazard ν (phSurvival Λ₀ ρ) s < ψ := by
  have hρ0' : ∀ᵐ x ∂ν, 0 ≤ ρ x := hρ0.mono fun x hx => hx.le
  have hpos := genHazard_pos ((ae_map_iff hρ.aemeasurable measurableSet_Ioi).2 hρ0) hΛs
  rw [popHazard_ratio hρ hρ0 (by linarith) hΛ hΛs hh₀.ne', div_lt_iff₀ hpos]
  exact genHazard_map_lt (ae_nonneg_map hρ hρ0') (not_ae_eq_map hρ hnc) hψ hΛs

/-- **For `0 < ψ < 1` the marginal hazard ratio is above the conditional one**, under the
hypotheses of `popHazard_ratio_lt`. -/
theorem lt_popHazard_ratio (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂ν, 0 < ρ x)
    (hnc : ¬ ∃ c, ∀ᵐ x ∂ν, ρ x = c) (hψ0 : 0 < ψ) (hψ1 : ψ < 1) (hΛ : HasDerivAt Λ₀ h₀ s)
    (hΛs : 0 < Λ₀ s) (hh₀ : 0 < h₀) :
    ψ < popHazard ν (phSurvival Λ₀ (fun x => ψ * ρ x)) s / popHazard ν (phSurvival Λ₀ ρ) s := by
  have hρ0' : ∀ᵐ x ∂ν, 0 ≤ ρ x := hρ0.mono fun x hx => hx.le
  have hpos := genHazard_pos ((ae_map_iff hρ.aemeasurable measurableSet_Ioi).2 hρ0) hΛs
  rw [popHazard_ratio hρ hρ0 hψ0.le hΛ hΛs hh₀.ne', lt_div_iff₀ hpos]
  exact lt_genHazard_map (ae_nonneg_map hρ hρ0') (not_ae_eq_map hρ hnc) hψ0 hψ1 hΛs

end Ratio

/-- **The marginal hazard ratio depends on the covariate law.** For `ψ > 0` with `ψ ≠ 1`, a
positive measurable relative hazard that is not `ν`-almost surely constant, and a time with
`Λ₀ s > 0` and `h₀ > 0`, the marginal hazard ratio under `ν` differs from the one under the
point mass at any covariate value, which is `ψ`. -/
theorem popHazard_ratio_ne_dirac [MeasurableSingletonClass 𝒳] {ν : Measure 𝒳}
    [IsProbabilityMeasure ν] {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x)
    (hnc : ¬ ∃ c, ∀ᵐ x ∂ν, ρ x = c) {ψ : ℝ} (hψ0 : 0 < ψ) (hψ1 : ψ ≠ 1) {Λ₀ : ℝ → ℝ}
    {h₀ s : ℝ} (hΛ : HasDerivAt Λ₀ h₀ s) (hΛs : 0 < Λ₀ s) (hh₀ : 0 < h₀) (x₀ : 𝒳) :
    popHazard (Measure.dirac x₀) (phSurvival Λ₀ (fun x => ψ * ρ x)) s /
        popHazard (Measure.dirac x₀) (phSurvival Λ₀ ρ) s = ψ ∧
      popHazard ν (phSurvival Λ₀ (fun x => ψ * ρ x)) s / popHazard ν (phSurvival Λ₀ ρ) s ≠
        ψ := by
  refine ⟨?_, ?_⟩
  · exact popHazard_ratio_of_ae_eq hρ (hρ0 x₀) (by rw [ae_dirac_eq, Filter.eventually_pure])
      hψ0.le hΛ hΛs hh₀.ne'
  · rcases lt_or_gt_of_ne hψ1 with h | h
    · exact (lt_popHazard_ratio hρ (Filter.Eventually.of_forall hρ0) hnc hψ0 h hΛ hΛs hh₀).ne'
    · exact (popHazard_ratio_lt hρ (Filter.Eventually.of_forall hρ0) hnc h hΛ hΛs hh₀).ne

/-! ### Finite mixtures -/

section Finite

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **The population curve of a finite stratifier** with level probabilities `p` and stratum
rates `r` is the finite mixture `mixSurvival p r` at the time `Λ₀ s`. -/
theorem popSurvival_stratumLaw {p : V → ℝ} (hp : ∀ v, 0 ≤ p v) (r : V → ℝ) (Λ₀ : ℝ → ℝ)
    (s : ℝ) : popSurvival (stratumLaw p) (phSurvival Λ₀ r) s = mixSurvival p r (Λ₀ s) := by
  rw [popSurvival, integral_stratumLaw hp, standardizedRisk, mixSurvival]
  rfl

/-- **The population hazard of a finite stratifier** under the unit baseline (`Λ₀ s = s`) is
the finite mixture hazard `mixHazard p r`, at every time. -/
theorem popHazard_stratumLaw {p : V → ℝ} (hp : IsWeights p) (r : V → ℝ) (t : ℝ) :
    popHazard (stratumLaw p) (phSurvival id r) t = mixHazard p r t := by
  have : popSurvival (stratumLaw p) (phSurvival id r) = mixSurvival p r :=
    funext fun s => popSurvival_stratumLaw hp.1 r id s
  rw [popHazard, curveHazard, this, mixHazard_eq_neg_deriv_div]

/-- **The marginal hazard ratio of a finite stratifier** under the unit baseline, with stratum
rates `r` for the control arm and `ψ r` for the treated arm, is the ratio
`mixHazard p (ψ r) t / mixHazard p r t` of `Bias.HazardMixture`, whose bounds
(`mixHazard_ratio_lt`, `lt_mixHazard_ratio_of_lt_one`, `mixHazard_ratio_zero`) therefore apply
to it. Weights summing to one make the population curve positive (`mixSurvival_pos`). -/
theorem popHazard_ratio_stratumLaw {p : V → ℝ} (hp : IsWeights p) (r : V → ℝ) (ψ t : ℝ) :
    popHazard (stratumLaw p) (phSurvival id fun v => ψ * r v) t /
        popHazard (stratumLaw p) (phSurvival id r) t =
      mixHazard p (fun v => ψ * r v) t / mixHazard p r t := by
  rw [popHazard_stratumLaw hp, popHazard_stratumLaw hp]

/-- **The population cumulative hazard of a finite stratifier** is `mixCumHazard p r` at the
time `Λ₀ s`. -/
theorem popCumHazard_stratumLaw {p : V → ℝ} (hp : ∀ v, 0 ≤ p v) (r : V → ℝ) (Λ₀ : ℝ → ℝ)
    (s : ℝ) : popCumHazard (stratumLaw p) (phSurvival Λ₀ r) s = mixCumHazard p r (Λ₀ s) := by
  rw [popCumHazard, popSurvival_stratumLaw hp, mixCumHazard]

end Finite

end ContinuousTime

end Survival

end CausalInference
