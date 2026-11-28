/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.GeneralLikelihoodReductions
public import CausalInference.Survival.PopulationHazardInitial

/-!
# Instances of the general likelihoods, and the time varying marginal hazard ratio

**The marginal hazard ratio under a covariate dependent proportional hazards model varies in
time.** In the multilevel network meta-regression of survival outcomes (Phillippo et al. 2020)
the conditional hazard ratio `ψ` is constant in time, but the population hazard ratio of two arms
with the same covariate law is not.

* `marginalHazardRatio_not_const`: for a unit baseline hazard, a relative hazard `ρ` that is not
  almost surely constant and `ψ ≠ 1`, the right sided marginal hazard ratio is not constant on
  `[0, ∞)`: it equals `ψ` at `0` and differs from `ψ` at every positive time.
* `marginalHazardRatio_twoStrata`: two equally likely strata with rates `1` and `100` and the
  conditional hazard ratio `1/2` give the marginal hazard ratio `1/2` at the time `0`, `5/1.98`
  at the time `2 log 10 / 99` and about `0.549 < 1` at the time `6 log 10 / 99`, so it is
  neither monotone nor antitone on `[0, ∞)`, while every conditional ratio is `1/2`.

**Instances of the aggregate likelihoods.** `eventKernel q` is the binary outcome with event
probability `q(x)`; it is a Markov kernel for `0 ≤ q ≤ 1` (`isMarkovKernel_eventKernel`).

* `map_card_singleton_logistic`: with the covariate equally likely `0` or `1` and the event
  probability `σ(x)`, one event among two patients has probability `2 θ (1 - θ)` with
  `θ = (1/2 + σ(1)) / 2`.
* `snd_compProd_eventKernel`: the outcome of a patient with unreported covariate has the law
  with density `(1 - θ, θ)` with respect to the counting measure.

## Main definitions

* `eventKernel`, `twoStrataWeight`, `twoStrataRate`.

## Main results

* `marginalHazardRatio_not_const`, `marginalHazardRatio_twoStrata`,
  `isMarkovKernel_eventKernel`, `map_card_singleton_logistic`, `snd_compProd_eventKernel`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Set
open Survival.ContinuousTime Bias.HazardMixture EffectMeasure
open scoped ENNReal

/-! ### The marginal hazard ratio -/

/-- **The marginal hazard ratio is not constant in time.** In a proportional hazards model with
the unit baseline hazard and a measurable, integrable relative hazard `ρ` that is almost surely
positive and not almost surely constant under the covariate law `ν`, and a conditional hazard
ratio `ψ > 0` with `ψ ≠ 1`, the right sided marginal hazard ratio of the arms with relative
hazards `ψ ρ` and `ρ` takes no constant value on `[0, ∞)`. -/
theorem marginalHazardRatio_not_const {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure 𝒳}
    [IsProbabilityMeasure ν] {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (hρi : Integrable ρ ν)
    (hρ0 : ∀ᵐ x ∂ν, 0 < ρ x) (hnc : ¬ ∃ c, ∀ᵐ x ∂ν, ρ x = c) {ψ : ℝ} (hψ0 : 0 < ψ)
    (hψ1 : ψ ≠ 1) :
    ¬ ∃ c, ∀ s, 0 ≤ s →
      popHazardRight ν (phSurvival (cumHazard fun _ => (1 : ℝ)) fun x => ψ * ρ x) s /
        popHazardRight ν (phSurvival (cumHazard fun _ => (1 : ℝ)) ρ) s = c := by
  obtain ⟨⟨_, h0⟩, hpos⟩ := popHazardRight_ratio_phSurvival hρ hρi hρ0 hnc hψ0 hψ1
    (h₀ := fun _ => (1 : ℝ)) measurable_const (fun _ _ => zero_le_one)
    (fun _ _ => intervalIntegrable_const) continuousWithinAt_const one_pos
  have hd : HasDerivAt (cumHazard fun _ => (1 : ℝ)) 1 1 := by
    rw [cumHazard_const_one_eq_id]; exact hasDerivAt_id 1
  have hc : 0 < cumHazard (fun _ => (1 : ℝ)) 1 := by
    rw [cumHazard_const_one_eq_id]; exact one_pos
  rintro ⟨c, hcst⟩
  have hψ : c = ψ := (hcst 0 le_rfl).symm.trans h0
  exact (hpos 1 hd hc one_pos).2 ((hcst 1 zero_le_one).trans hψ)

/-- The equal weights of two strata. -/
noncomputable def twoStrataWeight (_ : Bool) : ℝ := 1 / 2

/-- The stratum rates `100` and `1`. -/
noncomputable def twoStrataRate (b : Bool) : ℝ := if b then 100 else 1

/-- The mixture hazard of two equally likely strata with rates `a` (for `false`) and `b` (for
`true`) is `(a + b q) / (1 + q)` with `q = e^{-(b - a) t}`. -/
theorem mixHazard_twoStrata (r : Bool → ℝ) (t : ℝ) :
    mixHazard twoStrataWeight r t =
      (r false + r true * Real.exp (-((r true - r false) * t))) /
        (1 + Real.exp (-((r true - r false) * t))) := by
  have he : Real.exp (-(r true * t)) =
      Real.exp (-(r false * t)) * Real.exp (-((r true - r false) * t)) := by
    rw [← Real.exp_add]; ring_nf
  have hp := Real.exp_pos (-(r false * t))
  have hq := Real.exp_pos (-((r true - r false) * t))
  simp only [mixHazard, mixDensity, mixSurvival, Fintype.sum_bool, twoStrataWeight, he]
  field_simp
  ring

/-- `e^{-(n log 10)} = 10^{-n}`. -/
theorem exp_neg_mul_log_ten (n : ℕ) : Real.exp (-(n * Real.log 10)) = 1 / 10 ^ n := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity), one_div]

/-- **A marginal hazard ratio that rises and falls.** Two equally likely strata with rates
`1` and `100`, every stratum hazard multiplied by the conditional hazard ratio `1/2` in the
treated arm. The marginal hazard ratio `R(t)` is `1/2` at `0`, `5 / (2 / 1.01) > 1` at
`t₁ = 2 log 10 / 99` and `(0.55 / 1.001) / (1.0001 / 1.000001) < 1` at `t₂ = 6 log 10 / 99`, so
it is neither monotone nor antitone on `[0, ∞)`, while every conditional ratio is `1/2`. -/
theorem marginalHazardRatio_twoStrata :
    let R : ℝ → ℝ := fun t =>
      popHazard (stratumLaw twoStrataWeight)
          (phSurvival id fun v => 1 / 2 * twoStrataRate v) t /
        popHazard (stratumLaw twoStrataWeight) (phSurvival id twoStrataRate) t
    (∀ v, 1 / 2 * twoStrataRate v / twoStrataRate v = 1 / 2) ∧
      R 0 = 1 / 2 ∧ 1 < R (2 * Real.log 10 / 99) ∧ R (6 * Real.log 10 / 99) < 1 ∧
      ¬ MonotoneOn R (Ici 0) ∧ ¬ AntitoneOn R (Ici 0) := by
  intro R
  have hw : IsWeights twoStrataWeight := ⟨fun _ => by norm_num [twoStrataWeight],
    by norm_num [twoStrataWeight]⟩
  have hR : ∀ t, R t = mixHazard twoStrataWeight (fun v => 1 / 2 * twoStrataRate v) t /
      mixHazard twoStrataWeight twoStrataRate t := fun t =>
    popHazard_ratio_stratumLaw hw twoStrataRate (1 / 2) t
  have hR0 : R 0 = 1 / 2 := by
    rw [hR, mixHazard_twoStrata, mixHazard_twoStrata]
    norm_num [twoStrataRate]
  have hR1 : 1 < R (2 * Real.log 10 / 99) := by
    rw [hR, mixHazard_twoStrata, mixHazard_twoStrata]
    have e1 : -((1 / 2 * twoStrataRate true - 1 / 2 * twoStrataRate false) *
        (2 * Real.log 10 / 99)) = -((1 : ℕ) * Real.log 10) := by
      simp only [twoStrataRate]; norm_num
    have e2 : -((twoStrataRate true - twoStrataRate false) * (2 * Real.log 10 / 99)) =
        -((2 : ℕ) * Real.log 10) := by
      simp only [twoStrataRate]; norm_num; ring
    rw [e1, e2, exp_neg_mul_log_ten, exp_neg_mul_log_ten]
    norm_num [twoStrataRate]
  have hR2 : R (6 * Real.log 10 / 99) < 1 := by
    rw [hR, mixHazard_twoStrata, mixHazard_twoStrata]
    have e1 : -((1 / 2 * twoStrataRate true - 1 / 2 * twoStrataRate false) *
        (6 * Real.log 10 / 99)) = -((3 : ℕ) * Real.log 10) := by
      simp only [twoStrataRate]; norm_num; ring
    have e2 : -((twoStrataRate true - twoStrataRate false) * (6 * Real.log 10 / 99)) =
        -((6 : ℕ) * Real.log 10) := by
      simp only [twoStrataRate]; norm_num; ring
    rw [e1, e2, exp_neg_mul_log_ten, exp_neg_mul_log_ten]
    norm_num [twoStrataRate]
  have hl : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have ht1 : (0 : ℝ) ≤ 2 * Real.log 10 / 99 := by positivity
  have ht12 : 2 * Real.log 10 / 99 ≤ 6 * Real.log 10 / 99 := by linarith
  refine ⟨fun v => ?_, hR0, hR1, hR2, fun hm => ?_, fun ha => ?_⟩
  · have : twoStrataRate v ≠ 0 := by unfold twoStrataRate; split_ifs <;> norm_num
    field_simp
  · have := hm (mem_Ici.mpr ht1) (mem_Ici.mpr (ht1.trans ht12)) ht12
    linarith
  · have := ha (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht1) ht1
    linarith

/-! ### Binary outcomes with unreported covariates -/

/-- The **binary outcome kernel** with event probability `q(x)`: the density `q(x)` at `true` and
`1 - q(x)` at `false` with respect to the counting measure. -/
noncomputable def eventKernel {𝒳 : Type*} [MeasurableSpace 𝒳] (q : 𝒳 → ℝ) : Kernel 𝒳 Bool :=
  (Kernel.const 𝒳 (Measure.count : Measure Bool)).withDensity
    fun x b => ENNReal.ofReal (if b then q x else 1 - q x)

theorem eventKernel_apply {𝒳 : Type*} [MeasurableSpace 𝒳] {q : 𝒳 → ℝ} (hq : Measurable q)
    (x : 𝒳) : eventKernel q x =
      Measure.count.withDensity fun b => ENNReal.ofReal (if b then q x else 1 - q x) := by
  rw [eventKernel, Kernel.withDensity_apply, Kernel.const_apply]
  refine measurable_from_prod_countable_left fun b => ?_
  cases b
  · exact (measurable_const.sub hq).ennreal_ofReal
  · exact hq.ennreal_ofReal

/-- The binary outcome kernel is a Markov kernel when `0 ≤ q ≤ 1`. -/
theorem isMarkovKernel_eventKernel {𝒳 : Type*} [MeasurableSpace 𝒳] {q : 𝒳 → ℝ}
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1) :
    IsMarkovKernel (eventKernel q) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [eventKernel_apply hq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count, tsum_fintype, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [← ENNReal.ofReal_add (hq0 x) (sub_nonneg.mpr (hq1 x))]
  simp

/-- The covariate law equally likely at `0` and at `1`. -/
noncomputable def halfLaw : Measure (Fin 1 → ℝ) := twoAtomLaw (fun _ => 0) (fun _ => 1) (1 / 2)

instance : IsProbabilityMeasure halfLaw :=
  isProbabilityMeasure_twoAtomLaw (by norm_num) (by norm_num)

theorem measurable_sigmoid_zero : Measurable fun x : Fin 1 → ℝ => Real.sigmoid (x 0) :=
  (_root_.continuous_sigmoid.measurable).comp (measurable_pi_apply 0)

/-- The integrated event probability `∫ σ(x) dF = (1/2 + σ(1)) / 2` under `halfLaw`. -/
theorem integral_sigmoid_halfLaw :
    ∫ x, Real.sigmoid (x 0) ∂halfLaw = (1 / 2 + Real.sigmoid 1) / 2 := by
  rw [halfLaw, integral_twoAtomLaw (by norm_num) (by norm_num), Real.sigmoid_zero]
  ring

/-- **One event among two patients with unreported covariates.** With the covariate equally
likely `0` or `1` and the logistic event probability `σ(x)`, the number of events among two
independent patients equals `1` with probability `2 θ (1 - θ)`, `θ = (1/2 + σ(1)) / 2`: the
binomial mass at the integrated event probability. -/
theorem map_card_singleton_logistic :
    haveI := isMarkovKernel_eventKernel measurable_sigmoid_zero
      (fun x => Real.sigmoid_nonneg (x 0)) (fun x => Real.sigmoid_le_one (x 0))
    (Measure.pi fun _ : Fin 2 => halfLaw ⊗ₘ eventKernel fun x => Real.sigmoid (x 0)).map
        (fun z => (Finset.univ.filter fun i => (z i).2 = true).card) {1} =
      ENNReal.ofReal (2 * ((1 / 2 + Real.sigmoid 1) / 2) * (1 - (1 / 2 + Real.sigmoid 1) / 2)) := by
  have := isMarkovKernel_eventKernel measurable_sigmoid_zero
    (fun x => Real.sigmoid_nonneg (x 0)) (fun x => Real.sigmoid_le_one (x 0))
  rw [map_pi_compProd_card_singleton halfLaw measurable_sigmoid_zero _
    (Filter.Eventually.of_forall (eventKernel_apply measurable_sigmoid_zero)),
    integral_sigmoid_halfLaw, binomialMass]
  norm_num

/-- **The outcome of a patient with an unreported covariate.** With the covariate equally likely
`0` or `1` and the logistic event probability `σ(x)`, the outcome has density
`(1 - θ, θ)` with respect to the counting measure, `θ = (1/2 + σ(1)) / 2`. -/
theorem snd_compProd_eventKernel :
    haveI := isMarkovKernel_eventKernel measurable_sigmoid_zero
      (fun x => Real.sigmoid_nonneg (x 0)) (fun x => Real.sigmoid_le_one (x 0))
    (halfLaw ⊗ₘ eventKernel fun x => Real.sigmoid (x 0)).snd =
      Measure.count.withDensity fun b => ENNReal.ofReal
        (if b then (1 / 2 + Real.sigmoid 1) / 2 else 1 - (1 / 2 + Real.sigmoid 1) / 2) := by
  have := isMarkovKernel_eventKernel measurable_sigmoid_zero
    (fun x => Real.sigmoid_nonneg (x 0)) (fun x => Real.sigmoid_le_one (x 0))
  have hπ : ∀ b : Bool, Measurable fun x : Fin 1 → ℝ =>
      if b then Real.sigmoid (x 0) else 1 - Real.sigmoid (x 0) := fun b => by
    cases b
    · exact measurable_const.sub measurable_sigmoid_zero
    · exact measurable_sigmoid_zero
  rw [snd_compProd_categorical halfLaw hπ (fun x b => by
      cases b
      · exact sub_nonneg.mpr (Real.sigmoid_le_one _)
      · exact Real.sigmoid_nonneg _) _
    (Filter.Eventually.of_forall (eventKernel_apply measurable_sigmoid_zero))]
  congr 1
  funext b
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [integral_sub (integrable_const 1) (Integrable.of_bound
      measurable_sigmoid_zero.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sigmoid_nonneg _)]
        exact Real.sigmoid_le_one _)), integral_sigmoid_halfLaw]
    simp
  · simp only [↓reduceIte, integral_sigmoid_halfLaw]

end NetworkMetaRegression

end CausalInference
