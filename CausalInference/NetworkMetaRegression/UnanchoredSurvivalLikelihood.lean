/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredSurvivalTarget
public import CausalInference.NetworkMetaRegression.GeneralLikelihoodCensored
public import CausalInference.NetworkMetaRegression.GeneralLikelihoodAggregate
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Kernel.WithDensity
public import CausalInference.NetworkMetaRegression.AggregationIdentity

/-!
# The censored and joint likelihoods of an unanchored survival comparison

**Time scale: continuous.** Arm `A` is observed as individual data: patient `i` has covariates
`x_i` and an observed time and event indicator. Arm `B` is observed through event data
reconstructed from its published Kaplan Meier curve: observed times and event indicators without
covariates, whose covariates are drawn from the covariate law `F_B` of its study. Both arms follow
a proportional hazards model with the multilevel linear predictor: the event time of a patient
with covariates `x` in arm `k` of study `j` has hazard `h₀(t) exp(η_{jk}(x))`. Censoring is
independent of the event time, with a censoring density `g` of each arm.

The event time law of a relative hazard `r > 0` is `phEventLaw h₀ r`, Lebesgue measure with the
density `r h₀(t) exp(-r H₀(t))` on `(0, ∞)` (`phDensity`). It is a probability law with survival
`exp(-r H₀(t))` when `H₀ → ∞` (`phEventLaw_real_Ioi`, `isProbabilityMeasure_phEventLaw`).

## Main definitions

* `phDensity`, `phEventLaw`, `phObservedDensity`, `phObservedKernel`.

## Main results

* `phEventLaw_real_Ioi`, `isProbabilityMeasure_phEventLaw`.
* `map_censoredObservation_phEventLaw`: the observed pair of a patient has density
  `phObservedDensity`, the censored contribution `f(t)^δ S(t)^(1 - δ)` times a censoring factor
  free of the covariates.
* `lintegral_phObservedDensity`: the integrated density of a patient of the reconstructed arm is
  the integrated censored contribution `∫ f(t | x)^δ S(t | x)^(1 - δ) F_B(dx)` times the censoring
  factor; `integral_phCensoredContribution_le`: the integrated contribution is finite, at most
  `h₀(t) e^{-1} / H₀(t)` at an event and `1` at a censoring.
* `map_unanchoredSurvival_eq_withDensity`: **the joint likelihood**; the observed data of the two
  arms have density `∏ᵢ L_A(x_i; y_i) ∏ᵢ ∫ L_B(x; z_i) F_B(dx)`.

## References

* D. R. Cox, *Regression models and life-tables*, Journal of the Royal Statistical Society
  Series B 34 (1972).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Set
open Survival.ContinuousTime
open scoped ENNReal

/-! ### The event time law of a proportional hazards model -/

section EventLaw

variable {h₀ : ℝ → ℝ}

/-- The **event time density** of the relative hazard `r`: `r h₀(t) exp(-r H₀(t))` at `t > 0`
and `0` otherwise, with `H₀ = cumHazard h₀`. -/
noncomputable def phDensity (h₀ : ℝ → ℝ) (r t : ℝ) : ℝ :=
  if 0 < t then r * h₀ t * Real.exp (-(r * cumHazard h₀ t)) else 0

/-- The **event time law** of the relative hazard `r`: Lebesgue measure with density
`phDensity h₀ r`. -/
noncomputable def phEventLaw (h₀ : ℝ → ℝ) (r : ℝ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (phDensity h₀ r t)

theorem phDensity_nonneg (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    0 ≤ phDensity h₀ r t := by
  unfold phDensity
  split_ifs with ht
  · exact mul_nonneg (mul_nonneg hr (hnn t ht.le)) (Real.exp_pos _).le
  · exact le_rfl

/-- `-exp(-r H₀)` has derivative `r h₀ exp(-r H₀)` for a continuous baseline hazard. -/
theorem hasDerivAt_neg_exp_cumHazard (hcont : Continuous h₀) (r t : ℝ) :
    HasDerivAt (fun u => -Real.exp (-(r * cumHazard h₀ u)))
      (r * h₀ t * Real.exp (-(r * cumHazard h₀ t))) t := by
  have h := (((hasDerivAt_cumHazard hcont t).const_mul r).neg.exp).neg
  convert h using 1
  simp only [Pi.neg_apply]
  ring

/-- The event time law gives no mass to `(-∞, 0]`. -/
theorem phEventLaw_Iic_zero (r : ℝ) : phEventLaw h₀ r (Iic 0) = 0 := by
  rw [phEventLaw, withDensity_apply _ measurableSet_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iic fun t ht => ?_).trans (lintegral_zero)
  simp [phDensity, not_lt.2 (mem_Iic.1 ht)]

/-- **The survival of the event time law.** For a continuous baseline hazard, nonnegative at
nonnegative times, with `H₀(t) → ∞`, and a relative hazard `r > 0`, the event time law has
`P(T > t) = exp(-r H₀(t))` for every `t ≥ 0`. -/
theorem phEventLaw_Ioi (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    phEventLaw h₀ r (Ioi t) = ENNReal.ofReal (Real.exp (-(r * cumHazard h₀ t))) := by
  have hd : ∀ u ∈ Ioi t, HasDerivAt (fun u => -Real.exp (-(r * cumHazard h₀ u)))
      (phDensity h₀ r u) u := fun u hu => by
    rw [phDensity, ite_eq_left (ht.trans_lt hu)]
    exact hasDerivAt_neg_exp_cumHazard hcont r u
  have hc : ContinuousWithinAt (fun u => -Real.exp (-(r * cumHazard h₀ u))) (Ici t) t :=
    (hasDerivAt_neg_exp_cumHazard hcont r t).continuousAt.continuousWithinAt
  have hlim : Tendsto (fun u => -Real.exp (-(r * cumHazard h₀ u))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u => -(r * cumHazard h₀ u)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hH.const_mul_atTop hr)
    simpa using (Real.tendsto_exp_atBot.comp h1).neg
  have hpos : ∀ u ∈ Ioi t, 0 ≤ phDensity h₀ r u := fun u _ => phDensity_nonneg hnn hr.le u
  have hint := integrableOn_Ioi_deriv_of_nonneg hc hd hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg hc hd hpos hlim
  rw [phEventLaw, withDensity_apply _ measurableSet_Ioi,
    ← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  congr 1
  ring

/-- **The event time law is a probability law** under the hypotheses of `phEventLaw_Ioi`. -/
theorem isProbabilityMeasure_phEventLaw (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (phEventLaw h₀ r) := by
  constructor
  have h1 := phEventLaw_Ioi hcont hnn hH hr le_rfl
  rw [show cumHazard h₀ 0 = 0 by simp [cumHazard], mul_zero, neg_zero, Real.exp_zero,
    ENNReal.ofReal_one] at h1
  have hu : (univ : Set ℝ) = Ioi 0 ∪ Iic 0 := by
    ext t; simp only [mem_univ, mem_union, mem_Ioi, mem_Iic, true_iff]; exact lt_or_ge 0 t
  refine le_antisymm ?_ (h1 ▸ measure_mono (subset_univ _))
  calc phEventLaw h₀ r univ ≤ phEventLaw h₀ r (Ioi 0) + phEventLaw h₀ r (Iic 0) := by
        rw [hu]; exact measure_union_le _ _
    _ = 1 := by rw [h1, phEventLaw_Iic_zero, add_zero]

/-- **The survival at every time**: under the hypotheses of `phEventLaw_Ioi`,
`P(T > t) = exp(-r H₀(max t 0))` for every real `t`. -/
theorem phEventLaw_real_Ioi (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (phEventLaw h₀ r).real (Ioi t) = Real.exp (-(r * cumHazard h₀ (max t 0))) := by
  have hle : phEventLaw h₀ r (Ioi t) = phEventLaw h₀ r (Ioi (max t 0)) := by
    refine le_antisymm ?_ (measure_mono (Ioi_subset_Ioi (le_max_left t 0)))
    calc phEventLaw h₀ r (Ioi t) ≤ phEventLaw h₀ r (Ioi (max t 0) ∪ Iic 0) :=
          measure_mono fun u hu => by
            by_cases h : 0 < u
            · exact Or.inl (max_lt hu h)
            · exact Or.inr (not_lt.1 h)
      _ ≤ phEventLaw h₀ r (Ioi (max t 0)) + phEventLaw h₀ r (Iic 0) := measure_union_le _ _
      _ = phEventLaw h₀ r (Ioi (max t 0)) := by rw [phEventLaw_Iic_zero, add_zero]
  rw [measureReal_def, hle, phEventLaw_Ioi hcont hnn hH hr (le_max_right t 0),
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem measurable_phDensity_uncurry (hcont : Continuous h₀) :
    Measurable fun q : ℝ × ℝ => phDensity h₀ q.1 q.2 := by
  have hH := continuous_cumHazard (h₀ := h₀) fun a b => hcont.intervalIntegrable a b
  unfold phDensity
  refine Measurable.ite (measurableSet_lt measurable_const measurable_snd) ?_ measurable_const
  exact (Continuous.measurable (by fun_prop))

end EventLaw

/-! ### The density of the observed pair -/

section Observed

variable {h₀ : ℝ → ℝ}

/-- The **censoring survival** `G(t) = P(C ≥ t)` of a censoring law with density `g`. -/
noncomputable def censoringSurvival (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (volume.withDensity fun t => ENNReal.ofReal (g t)).real (Ici t)

theorem measurable_censoringSurvival (g : ℝ → ℝ) : Measurable (censoringSurvival g) :=
  ENNReal.measurable_toReal.comp
    (Antitone.measurable fun _ _ hab => measure_mono (Ici_subset_Ici.2 hab))

/-- The survival `exp(-r H₀(max t 0))` of the event time law at every real time. -/
noncomputable def phEventSurvival (h₀ : ℝ → ℝ) (r t : ℝ) : ℝ :=
  Real.exp (-(r * cumHazard h₀ (max t 0)))

/-- The **density of the observed pair** `(t, δ)` of a patient with relative hazard `r`: the
censored contribution `f(t)^δ S(t)^(1 - δ)` of the event time density `f = phDensity h₀ r` and
survival `S = phEventSurvival h₀ r`, times the censoring factor `G(t)^δ g(t)^(1 - δ)`. -/
noncomputable def phObservedDensity (h₀ g : ℝ → ℝ) (r : ℝ) (z : ℝ × Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (censoredContribution (phDensity h₀ r) (phEventSurvival h₀ r) z.1 z.2 *
    censoringContribution (censoringSurvival g) g z.1 z.2)

theorem measurable_phObservedDensity_uncurry (hcont : Continuous h₀) {g : ℝ → ℝ}
    (hg : Measurable g) : Measurable fun q : ℝ × (ℝ × Bool) => phObservedDensity h₀ g q.1 q.2 := by
  have hH := continuous_cumHazard (h₀ := h₀) fun a b => hcont.intervalIntegrable a b
  have hm : Measurable fun q : (ℝ × ℝ) × Bool => phObservedDensity h₀ g q.1.1 (q.1.2, q.2) := by
    refine measurable_from_prod_countable_left fun δ => ?_
    refine ENNReal.measurable_ofReal.comp ?_
    cases δ
    · simp only [censoredContribution, censoringContribution,
        Bool.false_eq_true, ↓reduceIte, phEventSurvival]
      exact (Continuous.measurable (by fun_prop)).mul (hg.comp measurable_snd)
    · simp only [censoredContribution, censoringContribution, ↓reduceIte]
      exact (measurable_phDensity_uncurry hcont).mul
        ((measurable_censoringSurvival g).comp measurable_snd)
  exact hm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

/-- **The observed pair of a patient has density `phObservedDensity`.** For a continuous
baseline hazard, nonnegative at nonnegative times, with `H₀ → ∞`, a relative hazard `r > 0` and
a finite censoring law with measurable density `g`, independent of the event time, the observed
pair `(min T C, 1{T ≤ C})` has density `phObservedDensity h₀ g r` with respect to Lebesgue
measure times the counting measure. -/
theorem map_censoredObservation_phEventLaw (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ}
    (hg : Measurable g)
    [IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal (g t))] :
    ((phEventLaw h₀ r).prod (volume.withDensity fun t => ENNReal.ofReal (g t))).map
        censoredObservation =
      (volume.prod Measure.count).withDensity (phObservedDensity h₀ g r) := by
  have := isProbabilityMeasure_phEventLaw hcont hnn hH hr
  have hT : IsFiniteMeasure (volume.withDensity fun t => ENNReal.ofReal (phDensity h₀ r t)) :=
    inferInstanceAs (IsFiniteMeasure (phEventLaw h₀ r))
  have hm : Measurable (phDensity h₀ r) :=
    (measurable_phDensity_uncurry hcont).comp (measurable_const.prodMk measurable_id)
  rw [phEventLaw, map_censoredObservation_prod_withDensity hm hg]
  congr 1
  funext z
  rw [phObservedDensity]
  congr 3
  funext t
  rw [← phEventLaw, phEventLaw_real_Ioi hcont hnn hH hr, phEventSurvival]

/-- The observed pair has a probability law under the hypotheses of
`map_censoredObservation_phEventLaw`. -/
theorem isProbabilityMeasure_withDensity_phObservedDensity (hcont : Continuous h₀)
    (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u) (hH : Tendsto (cumHazard h₀) atTop atTop) {r : ℝ} (hr : 0 < r)
    {g : ℝ → ℝ} (hg : Measurable g)
    [IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal (g t))] :
    IsProbabilityMeasure ((volume.prod Measure.count).withDensity (phObservedDensity h₀ g r)) := by
  have := isProbabilityMeasure_phEventLaw hcont hnn hH hr
  rw [← map_censoredObservation_phEventLaw hcont hnn hH hr hg]
  exact (Measure.isProbabilityMeasure_map_iff measurable_censoredObservation.aemeasurable).2
    inferInstance

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The **observation kernel** of a proportional hazards arm with relative hazard `ρ` and
censoring density `g`: the law of the observed pair given the covariates `x`, Lebesgue measure
times the counting measure with density `phObservedDensity h₀ g (ρ x)`. -/
noncomputable def phObservedKernel (h₀ g : ℝ → ℝ) (ρ : 𝒳 → ℝ) : Kernel 𝒳 (ℝ × Bool) :=
  Kernel.withDensity (Kernel.const 𝒳 (volume.prod Measure.count))
    fun x z => phObservedDensity h₀ g (ρ x) z

theorem measurable_phObservedDensity_comp (hcont : Continuous h₀) {g : ℝ → ℝ}
    (hg : Measurable g) {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) :
    Measurable (Function.uncurry fun x z => phObservedDensity h₀ g (ρ x) z) :=
  (measurable_phObservedDensity_uncurry hcont hg).comp
    ((hρ.comp measurable_fst).prodMk measurable_snd)

theorem phObservedKernel_apply (hcont : Continuous h₀) {g : ℝ → ℝ} (hg : Measurable g)
    {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (x : 𝒳) :
    phObservedKernel h₀ g ρ x =
      (volume.prod Measure.count).withDensity (phObservedDensity h₀ g (ρ x)) := by
  rw [phObservedKernel, Kernel.withDensity_apply _ (measurable_phObservedDensity_comp hcont hg hρ)]
  rfl

/-- **The observation kernel is the law of the observed pair**: given the covariates `x`, it is
the law of `(min T C, 1{T ≤ C})` for independent `T ∼ phEventLaw h₀ (ρ x)` and `C` with density
`g`. -/
theorem phObservedKernel_eq_map (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {g : ℝ → ℝ} (hg : Measurable g)
    [IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal (g t))] {ρ : 𝒳 → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x) (x : 𝒳) :
    phObservedKernel h₀ g ρ x =
      ((phEventLaw h₀ (ρ x)).prod (volume.withDensity fun t => ENNReal.ofReal (g t))).map
        censoredObservation := by
  rw [phObservedKernel_apply hcont hg hρ, map_censoredObservation_phEventLaw hcont hnn hH (hρ0 x)
    hg]

theorem isMarkovKernel_phObservedKernel (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {g : ℝ → ℝ} (hg : Measurable g)
    [IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal (g t))] {ρ : 𝒳 → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x) : IsMarkovKernel (phObservedKernel h₀ g ρ) :=
  ⟨fun x => by
    rw [phObservedKernel_apply hcont hg hρ]
    exact isProbabilityMeasure_withDensity_phObservedDensity hcont hnn hH (hρ0 x) hg⟩

/-! ### The integrated censored contribution of the reconstructed arm -/

theorem phEventSurvival_mem_Icc (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    0 < phEventSurvival h₀ r t ∧ phEventSurvival h₀ r t ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hr
    (cumHazard_nonneg hnn (le_max_right t 0))))⟩

/-- The event time density at a time `t > 0` is at most `h₀(t) e^{-1} / H₀(t)` where
`H₀(t) > 0`, whatever the relative hazard `r`. -/
theorem phDensity_le (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u) (r : ℝ) {t : ℝ} (ht : 0 < t)
    (hHt : 0 < cumHazard h₀ t) : phDensity h₀ r t ≤ h₀ t * Real.exp (-1) / cumHazard h₀ t := by
  rw [phDensity, ite_eq_left ht]
  have h1 := Real.mul_exp_neg_le_exp_neg_one (r * cumHazard h₀ t)
  rw [le_div_iff₀ hHt]
  calc r * h₀ t * Real.exp (-(r * cumHazard h₀ t)) * cumHazard h₀ t
      = h₀ t * (r * cumHazard h₀ t * Real.exp (-(r * cumHazard h₀ t))) := by ring
    _ ≤ h₀ t * Real.exp (-1) := mul_le_mul_of_nonneg_left h1 (hnn t ht.le)

/-- The **censored contribution** `f(t | x)^δ S(t | x)^(1 - δ)` of an observation `(t, δ)` of a
patient with relative hazard `r`. -/
noncomputable def phCensoredContribution (h₀ : ℝ → ℝ) (r : ℝ) (z : ℝ × Bool) : ℝ :=
  censoredContribution (phDensity h₀ r) (phEventSurvival h₀ r) z.1 z.2

theorem phCensoredContribution_nonneg (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u) {r : ℝ} (hr : 0 ≤ r)
    (z : ℝ × Bool) : 0 ≤ phCensoredContribution h₀ r z := by
  unfold phCensoredContribution censoredContribution
  split_ifs
  · exact phDensity_nonneg hnn hr _
  · exact (phEventSurvival_mem_Icc hnn hr _).1.le

/-- **The integrated censored likelihood of the reconstructed arm is finite.** For a continuous
baseline hazard, nonnegative at nonnegative times, a measurable positive relative hazard `ρ`, a
covariate probability law `F_B` and an observation `(t, δ)` with `t > 0` and `H₀(t) > 0`, the
contribution `x ↦ f(t | x)^δ S(t | x)^(1 - δ)` is integrable under `F_B`, and its integral lies
in `[0, h₀(t) e^{-1} / H₀(t)]` at an event and in `[0, 1]` at a censoring. The bound does not
depend on the relative hazard: no integrability of the covariates is needed. -/
theorem integral_phCensoredContribution_le (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x) (F : Measure 𝒳)
    [IsProbabilityMeasure F] {z : ℝ × Bool} (ht : 0 < z.1) (hHt : 0 < cumHazard h₀ z.1) :
    Integrable (fun x => phCensoredContribution h₀ (ρ x) z) F ∧
      0 ≤ ∫ x, phCensoredContribution h₀ (ρ x) z ∂F ∧
      ∫ x, phCensoredContribution h₀ (ρ x) z ∂F ≤
        if z.2 then h₀ z.1 * Real.exp (-1) / cumHazard h₀ z.1 else 1 := by
  have hH := continuous_cumHazard (h₀ := h₀) fun a b => hcont.intervalIntegrable a b
  have hb : ∀ x, phCensoredContribution h₀ (ρ x) z ≤
      if z.2 then h₀ z.1 * Real.exp (-1) / cumHazard h₀ z.1 else 1 := fun x => by
    unfold phCensoredContribution censoredContribution
    split_ifs
    · exact phDensity_le hnn (ρ x) ht hHt
    · exact (phEventSurvival_mem_Icc hnn (hρ0 x).le _).2
  have hm : Measurable fun x => phCensoredContribution h₀ (ρ x) z := by
    unfold phCensoredContribution censoredContribution
    split_ifs
    · exact (measurable_phDensity_uncurry hcont).comp (hρ.prodMk measurable_const)
    · unfold phEventSurvival
      exact (Continuous.measurable (by fun_prop : Continuous fun r : ℝ =>
        Real.exp (-(r * cumHazard h₀ (max z.1 0))))).comp hρ
  have hint : Integrable (fun x => phCensoredContribution h₀ (ρ x) z) F :=
    Integrable.of_bound hm.aestronglyMeasurable _ (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (phCensoredContribution_nonneg hnn (hρ0 x).le z)]
      exact hb x)
  refine ⟨hint, integral_nonneg fun x => phCensoredContribution_nonneg hnn (hρ0 x).le z, ?_⟩
  calc ∫ x, phCensoredContribution h₀ (ρ x) z ∂F
      ≤ ∫ _x, (if z.2 then h₀ z.1 * Real.exp (-1) / cumHazard h₀ z.1 else 1) ∂F :=
        integral_mono hint (integrable_const _) hb
    _ = _ := by simp

/-- **The integrated density of a patient of the reconstructed arm factors.** The density
`∫ L(x; z) F_B(dx)` of an observation `z = (t, δ)` of the reconstructed arm, `t > 0`,
`H₀(t) > 0`, is the integrated censored contribution `∫ f(t | x)^δ S(t | x)^(1 - δ) F_B(dx)`
times the censoring factor `G(t)^δ g(t)^(1 - δ)`, which does not depend on the covariates. -/
theorem lintegral_phObservedDensity (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 < ρ x) (F : Measure 𝒳)
    [IsProbabilityMeasure F] (g : ℝ → ℝ) {z : ℝ × Bool} (ht : 0 < z.1)
    (hHt : 0 < cumHazard h₀ z.1) :
    ∫⁻ x, phObservedDensity h₀ g (ρ x) z ∂F =
      ENNReal.ofReal (∫ x, phCensoredContribution h₀ (ρ x) z ∂F) *
        ENNReal.ofReal (censoringContribution (censoringSurvival g) g z.1 z.2) := by
  have h := integral_phCensoredContribution_le hcont hnn hρ hρ0 F ht hHt
  have e : ∀ x, phObservedDensity h₀ g (ρ x) z =
      ENNReal.ofReal (phCensoredContribution h₀ (ρ x) z) *
        ENNReal.ofReal (censoringContribution (censoringSurvival g) g z.1 z.2) := fun x =>
    ENNReal.ofReal_mul (phCensoredContribution_nonneg hnn (hρ0 x).le z)
  simp_rw [e]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ofReal_integral_eq_lintegral_ofReal h.1
    (Eventually.of_forall fun x => phCensoredContribution_nonneg hnn (hρ0 x).le z)]

end Observed

/-! ### The joint likelihood -/

section Joint

variable {h₀ : ℝ → ℝ} {p : ℕ}

/-- **The joint likelihood of the individual arm and the reconstructed arm.** Let both arms
follow the proportional hazards model with the multilevel linear predictor: a patient with
covariates `x` in arm `k` of study `j` has event time law `phEventLaw h₀ (exp(η_{jk}(x)))`, for a
continuous baseline hazard `h₀`, nonnegative at nonnegative times, with `H₀ → ∞`; censoring is
independent with the probability density `g_A` in arm `A` and `g_B` in arm `B`. The `n_A`
patients of the individual arm (`k_A` in study `j_A`) have the observed covariates `x_i` and
independent observed pairs. The `n_B` patients of the reconstructed arm (`k_B` in study `j_B`) are
independent pairs (covariates, observed pair) with covariates drawn from `F_B`, of which only the
observed pairs are seen. The two arms are independent. Then the observed data have density
`∏ᵢ L_A(x_i; y_i) ∏ᵢ ∫ L_B(x; z_i) F_B(dx)` with respect to the product of Lebesgue measure
times the counting measure, `L = phObservedDensity` (the censored contribution times the
censoring factor; `lintegral_phObservedDensity` factors the integrated term). -/
theorem map_unanchoredSurvival_eq_withDensity {J K : Type*} (M : MultilevelModel J K p)
    (jA jB : J) (kA kB : K) (hcont : Continuous h₀) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hH : Tendsto (cumHazard h₀) atTop atTop) {gA gB : ℝ → ℝ} (hgA : Measurable gA)
    (hgB : Measurable gB)
    [IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal (gA t))]
    [IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal (gB t))]
    {nA nB : ℕ} (xA : Fin nA → Fin p → ℝ) (FB : Measure (Fin p → ℝ)) [IsProbabilityMeasure FB] :
    (Measure.pi fun i => ((phEventLaw h₀ (Real.exp (M.eta (M.μ jA) kA (xA i)))).prod
        (volume.withDensity fun t => ENNReal.ofReal (gA t))).map censoredObservation).prod
      ((Measure.pi fun _ : Fin nB =>
          FB ⊗ₘ phObservedKernel h₀ gB fun x => Real.exp (M.eta (M.μ jB) kB x)).map
        fun z i => (z i).2) =
    ((Measure.pi fun _ : Fin nA => volume.prod Measure.count).prod
        (Measure.pi fun _ : Fin nB => volume.prod Measure.count)).withDensity fun y =>
      (∏ i, phObservedDensity h₀ gA (Real.exp (M.eta (M.μ jA) kA (xA i))) (y.1 i)) *
        ∏ i, ∫⁻ x, phObservedDensity h₀ gB (Real.exp (M.eta (M.μ jB) kB x)) (y.2 i) ∂FB := by
  set ν : Measure (ℝ × Bool) := volume.prod Measure.count with hν
  have hρB : Measurable fun x => Real.exp (M.eta (M.μ jB) kB x) :=
    (M.continuous_eta _ _).measurable.exp
  have hmA : ∀ r, Measurable (phObservedDensity h₀ gA r) := fun r =>
    (measurable_phObservedDensity_uncurry hcont hgA).comp (measurable_const.prodMk measurable_id)
  have hA : (Measure.pi fun i => ((phEventLaw h₀ (Real.exp (M.eta (M.μ jA) kA (xA i)))).prod
      (volume.withDensity fun t => ENNReal.ofReal (gA t))).map censoredObservation) =
      (Measure.pi fun _ : Fin nA => ν).withDensity fun y =>
        ∏ i, phObservedDensity h₀ gA (Real.exp (M.eta (M.μ jA) kA (xA i))) (y i) := by
    have e : ∀ i, ((phEventLaw h₀ (Real.exp (M.eta (M.μ jA) kA (xA i)))).prod
        (volume.withDensity fun t => ENNReal.ofReal (gA t))).map censoredObservation =
        ν.withDensity (phObservedDensity h₀ gA (Real.exp (M.eta (M.μ jA) kA (xA i)))) :=
      fun i => map_censoredObservation_phEventLaw hcont hnn hH (Real.exp_pos _) hgA
    have : ∀ i, SigmaFinite (ν.withDensity
        (phObservedDensity h₀ gA (Real.exp (M.eta (M.μ jA) kA (xA i))))) := fun i => by
      have := isProbabilityMeasure_withDensity_phObservedDensity hcont hnn hH
        (Real.exp_pos (M.eta (M.μ jA) kA (xA i))) hgA
      infer_instance
    simp_rw [e]
    exact pi_withDensity ν (fun i => phObservedDensity h₀ gA (Real.exp (M.eta (M.μ jA) kA (xA i))))
      fun i => hmA _
  have := isMarkovKernel_phObservedKernel hcont hnn hH hgB hρB fun x => Real.exp_pos _
  have hB := map_pi_compProd_eq_withDensity (fun _ : Fin nB => FB) ν
    (fun _ => phObservedKernel h₀ gB fun x => Real.exp (M.eta (M.μ jB) kB x))
    (fun _ x z => phObservedDensity h₀ gB (Real.exp (M.eta (M.μ jB) kB x)) z)
    (fun _ => measurable_phObservedDensity_comp hcont hgB hρB)
    (fun _ => Eventually.of_forall fun x => phObservedKernel_apply hcont hgB hρB x)
  rw [hA, hB, prod_withDensity]
  · exact Finset.measurable_prod _ fun i _ => (hmA _).comp (measurable_pi_apply i)
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_phObservedDensity_comp hcont hgB hρB).lintegral_prod_left'.comp
        (measurable_pi_apply i)

end Joint

/-! ### An exponential baseline with a two valued covariate -/

section Instance

theorem tendsto_cumHazard_one : Tendsto (cumHazard fun _ : ℝ => (1 : ℝ)) atTop atTop := by
  have e : cumHazard (fun _ : ℝ => (1 : ℝ)) = id := by funext u; simp [cumHazard]
  rw [e]
  exact tendsto_id

theorem linearRelativeHazard_log_two_zero :
    linearRelativeHazard 0 ![Real.log 2] ![0] = 1 := by
  simp [linearRelativeHazard, dotProduct]

theorem linearRelativeHazard_log_two_one :
    linearRelativeHazard 0 ![Real.log 2] ![1] = 2 := by
  simp [linearRelativeHazard, dotProduct, Real.exp_log]

/-- **Instance: unit baseline hazard, covariate taking the values `0` and `1` with probability
`1/2`, log hazard ratio `log 2`.** The relative hazards are `1` and `2`. At an observed time
`t > 0`: the event time law of the relative hazard `2` has `P(T > t) = e^{-2t}`; the integrated
censored contribution is `(e^{-t} + e^{-2t}) / 2` at a censoring and `(e^{-t} + 2 e^{-2t}) / 2` at
an event, and the latter is at most `e^{-1} / t` (`integral_phCensoredContribution_le`). -/
theorem phLikelihood_instance {t : ℝ} (ht : 0 < t) :
    (phEventLaw (fun _ => 1) 2).real (Ioi t) = Real.exp (-(2 * t)) ∧
      ∫ x, phCensoredContribution (fun _ => 1) (linearRelativeHazard 0 ![Real.log 2] x)
          (t, false) ∂twoAtomLaw ![0] ![1] (1 / 2) = (Real.exp (-t) + Real.exp (-(2 * t))) / 2 ∧
      ∫ x, phCensoredContribution (fun _ => 1) (linearRelativeHazard 0 ![Real.log 2] x)
          (t, true) ∂twoAtomLaw ![0] ![1] (1 / 2) =
        (Real.exp (-t) + 2 * Real.exp (-(2 * t))) / 2 ∧
      ∫ x, phCensoredContribution (fun _ => 1) (linearRelativeHazard 0 ![Real.log 2] x)
          (t, true) ∂twoAtomLaw ![0] ![1] (1 / 2) ≤ Real.exp (-1) / t := by
  have hc : cumHazard (fun _ : ℝ => (1 : ℝ)) = id := by funext u; simp [cumHazard]
  have hmax : max t 0 = t := max_eq_left ht.le
  have := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  have hb := integral_phCensoredContribution_le (h₀ := fun _ => 1) continuous_const
    (fun _ _ => zero_le_one) (continuous_linearRelativeHazard 0 ![Real.log 2]).measurable
    (linearRelativeHazard_pos 0 ![Real.log 2]) (twoAtomLaw ![0] ![1] (1 / 2)) (z := (t, true))
    ht (by rw [hc]; exact ht)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [phEventLaw_real_Ioi continuous_const (fun _ _ => zero_le_one) tendsto_cumHazard_one
      two_pos, hc, hmax, id]
  · rw [integral_twoAtomLaw (by norm_num) (by norm_num), linearRelativeHazard_log_two_zero,
      linearRelativeHazard_log_two_one]
    simp only [phCensoredContribution, censoredContribution, Bool.false_eq_true, ↓reduceIte,
      phEventSurvival, hc, hmax, id]
    ring_nf
  · rw [integral_twoAtomLaw (by norm_num) (by norm_num), linearRelativeHazard_log_two_zero,
      linearRelativeHazard_log_two_one]
    simp only [phCensoredContribution, censoredContribution, ↓reduceIte, phDensity,
      ite_eq_left ht, hc, id]
    ring_nf
  · have h := hb.2.2
    simp only [↓reduceIte, hc, id, one_mul] at h
    exact h

theorem exponentialPDFReal_of_nonneg' {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPDFReal r x = r * Real.exp (-(r * x)) := by
  rw [exponentialPDFReal, gammaPDFReal, ite_eq_left hx, Real.rpow_one, Real.Gamma_one, sub_self,
    Real.rpow_zero]
  ring

/-- **Instance: the observed pair under exponential censoring.** With `h₀ = 1`, relative hazard
`2` and a unit exponential censoring time, the observed pair has density `phObservedDensity`,
equal at `(t, δ)`, `t > 0`, to `2 e^{-3t}` at an event and `e^{-3t}` at a censoring, the density
of `censoredDensity_expMeasure` with rates `2` and `1`. For the reconstructed arm with the two
valued covariate of `phLikelihood_instance`, the integrated density at an event is
`((e^{-t} + 2 e^{-2t}) / 2) e^{-t}` (`lintegral_phObservedDensity`). -/
theorem phObserved_instance {t : ℝ} (ht : 0 < t) :
    ((phEventLaw (fun _ => 1) 2).prod (expMeasure 1)).map censoredObservation =
        (volume.prod Measure.count).withDensity
          (phObservedDensity (fun _ => 1) (exponentialPDFReal 1) 2) ∧
      phObservedDensity (fun _ => 1) (exponentialPDFReal 1) 2 (t, true) =
        ENNReal.ofReal (2 * Real.exp (-(3 * t))) ∧
      phObservedDensity (fun _ => 1) (exponentialPDFReal 1) 2 (t, false) =
        ENNReal.ofReal (Real.exp (-(3 * t))) ∧
      ∫⁻ x, phObservedDensity (fun _ => 1) (exponentialPDFReal 1)
          (linearRelativeHazard 0 ![Real.log 2] x) (t, true) ∂twoAtomLaw ![0] ![1] (1 / 2) =
        ENNReal.ofReal ((Real.exp (-t) + 2 * Real.exp (-(2 * t))) / 2) *
          ENNReal.ofReal (Real.exp (-t)) := by
  have hc : cumHazard (fun _ : ℝ => (1 : ℝ)) = id := by funext u; simp [cumHazard]
  have := isProbabilityMeasure_expMeasure (zero_lt_one' ℝ)
  have hP : IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal
      (exponentialPDFReal 1 t)) := by rw [← expMeasure_eq_withDensity]; infer_instance
  have hG : censoringSurvival (exponentialPDFReal 1) t = Real.exp (-t) := by
    rw [censoringSurvival, ← expMeasure_eq_withDensity, expMeasure_real_Ici one_pos ht.le,
      one_mul]
  have hg : exponentialPDFReal 1 t = Real.exp (-t) := by
    rw [exponentialPDFReal_of_nonneg' ht.le, one_mul, one_mul]
  have hprob := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [expMeasure_eq_withDensity]
    exact map_censoredObservation_phEventLaw continuous_const (fun _ _ => zero_le_one)
      tendsto_cumHazard_one two_pos (measurable_exponentialPDFReal 1)
  · simp only [phObservedDensity, censoredContribution, censoringContribution, ↓reduceIte,
      phDensity, ite_eq_left ht, hc, id, hG]
    congr 1
    rw [mul_one, mul_assoc, ← Real.exp_add]
    ring_nf
  · simp only [phObservedDensity, censoredContribution, censoringContribution,
      Bool.false_eq_true, ↓reduceIte, phEventSurvival, hc, id, max_eq_left ht.le, hg]
    congr 1
    rw [← Real.exp_add]
    ring_nf
  · rw [lintegral_phObservedDensity continuous_const (fun _ _ => zero_le_one)
      (continuous_linearRelativeHazard 0 ![Real.log 2]).measurable
      (linearRelativeHazard_pos 0 ![Real.log 2]) _ _ (z := (t, true)) ht (by rw [hc]; exact ht),
      (phLikelihood_instance ht).2.2.1]
    simp only [censoringContribution, ↓reduceIte, hG]

/-- **Instance: the joint likelihood.** For the multilevel model with zero intercepts and
treatment effects and prognostic effect `log 2` of a single covariate, a unit baseline hazard,
unit exponential censoring in both arms, one patient with covariate `1` in the individual arm and
one patient of the reconstructed arm with the two valued covariate law, the observed data have
the density of `map_unanchoredSurvival_eq_withDensity`. -/
theorem jointLikelihood_instance :
    let M : MultilevelModel Unit Unit 1 :=
      { μ := fun _ => 0, β₁ := ![Real.log 2], γ := fun _ => 0, β₂ := fun _ => 0 }
    (Measure.pi fun i : Fin 1 => ((phEventLaw (fun _ => 1)
        (Real.exp (M.eta (M.μ ()) () ((fun _ => ![1]) i)))).prod
        (volume.withDensity fun t => ENNReal.ofReal (exponentialPDFReal 1 t))).map
          censoredObservation).prod
      ((Measure.pi fun _ : Fin 1 => twoAtomLaw ![0] ![1] (1 / 2) ⊗ₘ
          phObservedKernel (fun _ => 1) (exponentialPDFReal 1)
            fun x => Real.exp (M.eta (M.μ ()) () x)).map fun z i => (z i).2) =
    ((Measure.pi fun _ : Fin 1 => volume.prod Measure.count).prod
        (Measure.pi fun _ : Fin 1 => volume.prod Measure.count)).withDensity fun y =>
      (∏ i, phObservedDensity (fun _ => 1) (exponentialPDFReal 1)
          (Real.exp (M.eta (M.μ ()) () ((fun _ => ![1]) i))) (y.1 i)) *
        ∏ i, ∫⁻ x, phObservedDensity (fun _ => 1) (exponentialPDFReal 1)
          (Real.exp (M.eta (M.μ ()) () x)) (y.2 i) ∂twoAtomLaw ![0] ![1] (1 / 2) := by
  intro M
  have := isProbabilityMeasure_expMeasure (zero_lt_one' ℝ)
  have hP : IsProbabilityMeasure (volume.withDensity fun t => ENNReal.ofReal
      (exponentialPDFReal 1 t)) := by rw [← expMeasure_eq_withDensity]; infer_instance
  have hprob := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  exact map_unanchoredSurvival_eq_withDensity M () () () () continuous_const
    (fun _ _ => zero_le_one) tendsto_cumHazard_one (measurable_exponentialPDFReal 1)
    (measurable_exponentialPDFReal 1) (fun _ => ![1]) _

end Instance

end NetworkMetaRegression

end CausalInference
