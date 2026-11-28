/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.HazardMixtureGeneral
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The population hazard of a mixture with general conditional hazards

**Time scale: continuous.** A family of conditional hazards `h x` indexed by a covariate value
`x` gives the conditional curves `S x = exp (-∫₀ˢ h x)` (`hazardCurves h`). Under a finite,
nonzero covariate law `ν` the population curve is `popSurvival ν S s = ∫ S x s dν(x)`.

**Where the results hold.** The cumulative hazard is taken from the time `0`, and `popHazard`
is defined with the two sided derivative. Every result below is therefore stated at a time
`s > 0` with a neighborhood `(s - ε, s + ε) ⊆ (0, ∞)` on which the conditional hazards are
continuous and on which `h x u * S x u` is dominated by a `ν` integrable function of `x`
(`IsEnvelopedHazardAt ν h s`). Nothing is claimed at the time `0`.

## Main definitions

* `hazardCurves h x = expSurvival (cumHazard (h x))`: the conditional curves of the hazards.
* `IsEnvelopedHazardAt ν h s`: the regularity under which the population curve is
  differentiable at `s` with the derivative computed under the integral sign.
* `covSurvivorLaw ν S s`: the law of the covariates among the survivors at `s`, with density
  `S x s / ∫ S y s dν(y)` with respect to `ν`.

## Main results

* `hasDerivAt_popSurvival_hazardCurves`: the population curve has derivative
  `-∫ h x s S x s dν(x)` at `s` (dominated convergence).
* `popHazard_hazardCurves`: **the survivor weighted hazard formula**
  `popHazard ν S s = (∫ h x s S x s dν) / (∫ S x s dν)`, with a positive denominator;
  `popHazard_eq_integral_covSurvivorLaw`: the population hazard is the mean of the conditional
  hazards over the probability law `covSurvivorLaw ν S s` of the covariates among survivors.
* `popHazard_hazardCurves_mem_Icc`: almost sure bounds `a ≤ h x s ≤ b` bound the population
  hazard; `popHazard_hazardCurves_pos`.
* The proportional hazards case: `hazardCurves_mul`, `isEnvelopedHazardAt_mul`,
  `popHazard_phSurvival_cumHazard` (the right side of `popHazard_phSurvival_eq_div` from the
  general formula, without integrability of the relative hazard),
  `map_covSurvivorLaw_phSurvival` (the bridge to `Bias.HazardMixtureGeneral.survivorLaw`) and
  `popHazard_phSurvival_cumHazard_genHazard`.
* Two arms: `popHazard_ratio_hazardCurves` (the marginal hazard ratio as a ratio of two survivor
  weighted means) and `popHazard_ratio_hazardCurves_const_mul` (under a conditional hazard ratio
  `ψ`, the marginal hazard ratio is `ψ` times the ratio of the means of the same control hazard
  under two different survivor laws).

## References

* M. A. Hernán, *The hazards of hazard ratios*, Epidemiology 21 (2010).
* O. O. Aalen, R. J. Cook and K. Røysland, *Does Cox analysis of a randomized survival study
  yield a causal treatment effect?*, Lifetime Data Analysis 21 (2015).
-/

@[expose] public section

namespace CausalInference

namespace Survival

namespace ContinuousTime

open MeasureTheory Set Filter Topology Metric

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure 𝒳} {h : 𝒳 → ℝ → ℝ} {s : ℝ}

/-! ### The conditional curves of a family of hazards -/

/-- The **conditional survival curves** of a family of conditional hazards:
`S x s = exp (-∫₀ˢ h x)`. -/
noncomputable def hazardCurves (h : 𝒳 → ℝ → ℝ) (x : 𝒳) : ℝ → ℝ :=
  expSurvival (cumHazard (h x))

omit [MeasurableSpace 𝒳] in
theorem hazardCurves_apply (h : 𝒳 → ℝ → ℝ) (x : 𝒳) (u : ℝ) :
    hazardCurves h x u = Real.exp (-cumHazard (h x) u) := rfl

omit [MeasurableSpace 𝒳] in
theorem hazardCurves_pos (h : 𝒳 → ℝ → ℝ) (x : 𝒳) (u : ℝ) : 0 < hazardCurves h x u :=
  expSurvival_pos _ _

omit [MeasurableSpace 𝒳] in
/-- A hazard that is nonnegative on `[0, ∞)` gives a curve at most `1` at the time `u ≥ 0`. -/
theorem hazardCurves_le_one {x : 𝒳} (hn : ∀ v, 0 ≤ v → 0 ≤ h x v) {u : ℝ} (hu : 0 ≤ u) :
    hazardCurves h x u ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (cumHazard_nonneg hn hu))

/-- The cumulative hazard at a fixed time is measurable in the covariate. -/
theorem measurable_cumHazard_param (hm : Measurable (Function.uncurry h)) (u : ℝ) :
    Measurable fun x => cumHazard (h x) u := by
  have key : ∀ I : Set ℝ, Measurable fun x => ∫ v in I, h x v := fun I =>
    (StronglyMeasurable.integral_prod_right (f := h) (ν := volume.restrict I)
      hm.stronglyMeasurable).measurable
  simp only [cumHazard, intervalIntegral]
  exact (key _).sub (key _)

/-- The conditional curves at a fixed time are measurable in the covariate. -/
theorem measurable_hazardCurves (hm : Measurable (Function.uncurry h)) (u : ℝ) :
    Measurable fun x => hazardCurves h x u :=
  (measurable_cumHazard_param hm u).neg.exp

/-! ### The regularity condition -/

/-- **Regularity of a family of conditional hazards at the time `s`.** The hazard is jointly
measurable; `ν`-almost every conditional hazard is nonnegative on `[0, ∞)` and integrable on
every `[0, u]`; and there is a radius `0 < ε ≤ s` such that `ν`-almost every conditional hazard
is continuous on `(s - ε, s + ε)` and the products `h x u * S x u` on that interval are bounded
by a `ν` integrable function `g x` of the covariate. The interval lies in `(0, ∞)`, so the
condition forces `s > 0`. The envelope bounds the derivative `h x u * S x u` of the conditional
curve, not the hazard alone; a hazard envelope is a special case
(`IsEnvelopedHazardAt.of_hazard_le`). -/
structure IsEnvelopedHazardAt (ν : Measure 𝒳) (h : 𝒳 → ℝ → ℝ) (s : ℝ) : Prop where
  measurable : Measurable (Function.uncurry h)
  nonneg : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → 0 ≤ h x u
  intervalIntegrable : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → IntervalIntegrable (h x) volume 0 u
  envelope : ∃ ε, 0 < ε ∧ ε ≤ s ∧ ∃ g : 𝒳 → ℝ, Integrable g ν ∧ ∀ᵐ x ∂ν,
    ContinuousOn (h x) (ball s ε) ∧ ∀ u ∈ ball s ε, h x u * hazardCurves h x u ≤ g x

theorem IsEnvelopedHazardAt.pos (he : IsEnvelopedHazardAt ν h s) : 0 < s := by
  obtain ⟨ε, hε, hεs, -⟩ := he.envelope
  linarith

/-- **A hazard envelope suffices**: if `ν`-almost every conditional hazard is continuous on
`(s - ε, s + ε)` with `0 < ε ≤ s` and bounded there by `g x` with `g` integrable, the family is
regular at `s`. -/
theorem IsEnvelopedHazardAt.of_hazard_le (hm : Measurable (Function.uncurry h))
    (hn : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → 0 ≤ h x u)
    (hi : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → IntervalIntegrable (h x) volume 0 u) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε ≤ s) {g : 𝒳 → ℝ} (hg : Integrable g ν)
    (hb : ∀ᵐ x ∂ν, ContinuousOn (h x) (ball s ε) ∧ ∀ u ∈ ball s ε, h x u ≤ g x) :
    IsEnvelopedHazardAt ν h s := by
  refine ⟨hm, hn, hi, ε, hε, hεs, g, hg, ?_⟩
  filter_upwards [hn, hb] with x hnx hbx
  refine ⟨hbx.1, fun u hu => ?_⟩
  have hu0 : 0 ≤ u := by
    rw [mem_ball, Real.dist_eq, abs_lt] at hu
    linarith
  calc h x u * hazardCurves h x u ≤ h x u * 1 :=
        mul_le_mul_of_nonneg_left (hazardCurves_le_one hnx hu0) (hnx u hu0)
    _ ≤ g x := by rw [mul_one]; exact hbx.2 u hu

/-! ### The derivative of the population curve -/

/-- Under the regularity at `s`, the conditional curves at `s` are integrable under a finite
law: they take values in `(0, 1]`. -/
theorem integrable_hazardCurves [IsFiniteMeasure ν] (he : IsEnvelopedHazardAt ν h s) :
    Integrable (fun x => hazardCurves h x s) ν :=
  Integrable.of_bound (measurable_hazardCurves he.measurable s).aestronglyMeasurable 1
    (he.nonneg.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (hazardCurves_pos h x s)]
      exact hazardCurves_le_one hx he.pos.le)

/-- Under the regularity at `s`, the population curve of the conditional curves is positive at
`s` under a finite nonzero law. -/
theorem popSurvival_hazardCurves_pos [IsFiniteMeasure ν] [NeZero ν]
    (he : IsEnvelopedHazardAt ν h s) : 0 < popSurvival ν (hazardCurves h) s := by
  rw [popSurvival, integral_pos_iff_support_of_nonneg (fun x => (hazardCurves_pos h x s).le)
    (integrable_hazardCurves he)]
  have : Function.support (fun x => hazardCurves h x s) = univ :=
    eq_univ_of_forall fun x => (hazardCurves_pos h x s).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne ν)

/-- **The derivative of the population curve.** Under a finite law and the regularity
`IsEnvelopedHazardAt ν h s` (so at a time `s > 0`), the product `h x s * S x s` is integrable
and the population curve of the conditional curves `S = hazardCurves h` has derivative
`-∫ h x s S x s dν(x)` at `s`. -/
theorem hasDerivAt_popSurvival_hazardCurves [IsFiniteMeasure ν] (he : IsEnvelopedHazardAt ν h s) :
    Integrable (fun x => h x s * hazardCurves h x s) ν ∧
      HasDerivAt (popSurvival ν (hazardCurves h)) (-∫ x, h x s * hazardCurves h x s ∂ν) s := by
  obtain ⟨ε, hε, hεs, g, hg, hb⟩ := he.envelope
  have hpos : ∀ u ∈ ball s ε, 0 < u := fun u hu => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hu
    linarith
  have hmh : ∀ u, Measurable fun x => h x u := fun u =>
    he.measurable.comp (measurable_id.prodMk measurable_const)
  have hderiv : ∀ᵐ x ∂ν, ∀ u ∈ ball s ε,
      HasDerivAt (fun v => hazardCurves h x v) (-(h x u * hazardCurves h x u)) u := by
    filter_upwards [he.intervalIntegrable, hb] with x hix hbx u hu
    have hcont : ContinuousAt (h x) u := hbx.1.continuousAt (isOpen_ball.mem_nhds hu)
    have hmeas : StronglyMeasurableAtFilter (h x) (𝓝 u) :=
      hbx.1.stronglyMeasurableAtFilter isOpen_ball u hu
    exact hasDerivAt_expSurvival
      (intervalIntegral.integral_hasDerivAt_right (hix u (hpos u hu).le) hmeas hcont)
  have hbound : ∀ᵐ x ∂ν, ∀ u ∈ ball s ε, ‖-(h x u * hazardCurves h x u)‖ ≤ g x := by
    filter_upwards [he.nonneg, hb] with x hnx hbx u hu
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hnx u (hpos u hu).le) (hazardCurves_pos h x u).le)]
    exact hbx.2 u hu
  obtain ⟨hint, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun u x => hazardCurves h x u) (F' := fun u x => -(h x u * hazardCurves h x u))
    (ball_mem_nhds s hε)
    (Eventually.of_forall fun u => (measurable_hazardCurves he.measurable u).aestronglyMeasurable)
    (integrable_hazardCurves he)
    (((hmh s).mul (measurable_hazardCurves he.measurable s)).neg.aestronglyMeasurable)
    hbound hg hderiv
  refine ⟨hint.neg.congr (Eventually.of_forall fun x => by simp), ?_⟩
  rw [← integral_neg]
  exact hd

/-! ### The survivor weighted hazard formula -/

/-- **The survivor weighted hazard formula.** Under a finite nonzero law and the regularity
`IsEnvelopedHazardAt ν h s`, the population curve is positive at `s` and the population hazard
at `s` is `(∫ h x s S x s dν) / (∫ S x s dν)`. -/
theorem popHazard_hazardCurves [IsFiniteMeasure ν] [NeZero ν] (he : IsEnvelopedHazardAt ν h s) :
    0 < popSurvival ν (hazardCurves h) s ∧
      popHazard ν (hazardCurves h) s =
        (∫ x, h x s * hazardCurves h x s ∂ν) / ∫ x, hazardCurves h x s ∂ν := by
  refine ⟨popSurvival_hazardCurves_pos he, ?_⟩
  rw [popHazard, curveHazard, (hasDerivAt_popSurvival_hazardCurves he).2.deriv, neg_neg]
  rfl

/-! ### The law of the covariates among the survivors -/

/-- The **law of the covariates among the survivors** at the time `s`: the measure with density
`S x s / ∫ S y s dν(y)` with respect to the covariate law `ν`, for a family of conditional curves
`S`. -/
noncomputable def covSurvivorLaw (ν : Measure 𝒳) (S : 𝒳 → ℝ → ℝ) (s : ℝ) : Measure 𝒳 :=
  ν.withDensity fun x => ENNReal.ofReal (S x s / popSurvival ν S s)

/-- Integration against the survivor law is the survival weighted mean:
`∫ φ d(covSurvivorLaw ν S s) = (∫ φ x S x s dν) / ∫ S x s dν` when the population curve is
positive at `s`. -/
theorem integral_covSurvivorLaw {S : 𝒳 → ℝ → ℝ} (hSm : Measurable fun x => S x s)
    (hS0 : ∀ x, 0 ≤ S x s) (hpos : 0 < popSurvival ν S s) (φ : 𝒳 → ℝ) :
    ∫ x, φ x ∂covSurvivorLaw ν S s = (∫ x, φ x * S x s ∂ν) / popSurvival ν S s := by
  rw [covSurvivorLaw, integral_withDensity_eq_integral_toReal_smul
    (hSm.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (div_nonneg (hS0 _) hpos.le)]
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- The survivor law is a probability law when the curves at `s` are nonnegative and integrable
and the population curve is positive at `s`. -/
theorem isProbabilityMeasure_covSurvivorLaw {S : 𝒳 → ℝ → ℝ} (hS0 : ∀ x, 0 ≤ S x s)
    (hSi : Integrable (fun x => S x s) ν) (hpos : 0 < popSurvival ν S s) :
    IsProbabilityMeasure (covSurvivorLaw ν S s) := by
  constructor
  rw [covSurvivorLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hSi.div_const _)
      (Eventually.of_forall fun x => div_nonneg (hS0 x) hpos.le), integral_div]
  rw [show (∫ x, S x s ∂ν) = popSurvival ν S s from rfl, div_self hpos.ne']
  simp

/-- **The population hazard is the mean conditional hazard among the survivors.** Under a
finite nonzero law and the regularity `IsEnvelopedHazardAt ν h s`, the survivor law
`covSurvivorLaw ν (hazardCurves h) s` is a probability law and the population hazard at `s` is
the mean of the conditional hazards `h x s` under it. -/
theorem popHazard_eq_integral_covSurvivorLaw [IsFiniteMeasure ν] [NeZero ν]
    (he : IsEnvelopedHazardAt ν h s) :
    IsProbabilityMeasure (covSurvivorLaw ν (hazardCurves h) s) ∧
      popHazard ν (hazardCurves h) s = ∫ x, h x s ∂covSurvivorLaw ν (hazardCurves h) s := by
  obtain ⟨hpos, hform⟩ := popHazard_hazardCurves he
  have hSm := measurable_hazardCurves he.measurable s
  refine ⟨isProbabilityMeasure_covSurvivorLaw (fun x => (hazardCurves_pos h x s).le)
    (integrable_hazardCurves he) hpos, ?_⟩
  rw [integral_covSurvivorLaw hSm (fun x => (hazardCurves_pos h x s).le) hpos, hform]
  rfl

/-! ### Bounds -/

/-- **The population hazard lies between almost sure bounds of the conditional hazards**: if
`a ≤ h x s ≤ b` for `ν`-almost every `x`, then `a ≤ popHazard ν S s ≤ b`, under a finite nonzero
law and the regularity `IsEnvelopedHazardAt ν h s`. -/
theorem popHazard_hazardCurves_mem_Icc [IsFiniteMeasure ν] [NeZero ν]
    (he : IsEnvelopedHazardAt ν h s) {a b : ℝ} (hab : ∀ᵐ x ∂ν, a ≤ h x s ∧ h x s ≤ b) :
    popHazard ν (hazardCurves h) s ∈ Icc a b := by
  obtain ⟨hpos, hform⟩ := popHazard_hazardCurves he
  have hSi := integrable_hazardCurves he
  have hhS := (hasDerivAt_popSurvival_hazardCurves he).1
  have hD : (∫ x, hazardCurves h x s ∂ν) = popSurvival ν (hazardCurves h) s := rfl
  rw [hform, hD]
  constructor
  · rw [le_div_iff₀ hpos, popSurvival, ← integral_const_mul]
    refine integral_mono_ae (hSi.const_mul a) hhS (hab.mono fun x hx => ?_)
    exact mul_le_mul_of_nonneg_right hx.1 (hazardCurves_pos h x s).le
  · rw [div_le_iff₀ hpos, popSurvival, ← integral_const_mul]
    refine integral_mono_ae hhS (hSi.const_mul b) (hab.mono fun x hx => ?_)
    exact mul_le_mul_of_nonneg_right hx.2 (hazardCurves_pos h x s).le

/-- **The population hazard is positive** when `ν`-almost every conditional hazard is positive
at `s`, under a finite nonzero law and the regularity `IsEnvelopedHazardAt ν h s`. -/
theorem popHazard_hazardCurves_pos [IsFiniteMeasure ν] [NeZero ν]
    (he : IsEnvelopedHazardAt ν h s) (hpos : ∀ᵐ x ∂ν, 0 < h x s) :
    0 < popHazard ν (hazardCurves h) s := by
  obtain ⟨hS, hform⟩ := popHazard_hazardCurves he
  rw [hform]
  refine div_pos ?_ hS
  have hhS := (hasDerivAt_popSurvival_hazardCurves he).1
  rw [integral_pos_iff_support_of_nonneg_ae
    (hpos.mono fun x hx => (mul_pos hx (hazardCurves_pos h x s)).le) hhS]
  have hsub : {x | ¬ 0 < h x s}ᶜ ⊆ Function.support fun x => h x s * hazardCurves h x s :=
    fun x hx => (mul_pos (not_not.1 hx) (hazardCurves_pos h x s)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have h0 : ν {x | ¬ 0 < h x s} = 0 := ae_iff.1 hpos
  have hu := measure_univ_le_add_compl (μ := ν) {x | ¬ 0 < h x s}
  rw [h0, zero_add] at hu
  exact lt_of_lt_of_le (Measure.measure_univ_pos.2 (NeZero.ne ν)) hu

/-! ### The proportional hazards case -/

section ProportionalHazards

open Bias.HazardMixtureGeneral

omit [MeasurableSpace 𝒳] in
/-- The conditional curves of the hazards `ρ x * h₀ u` are the proportional hazards curves with
baseline cumulative hazard `cumHazard h₀`. -/
theorem hazardCurves_mul (ρ : 𝒳 → ℝ) (h₀ : ℝ → ℝ) :
    hazardCurves (fun x u => ρ x * h₀ u) = phSurvival (cumHazard h₀) ρ := by
  funext x u
  simp only [hazardCurves, expSurvival, phSurvival, cumHazard,
    intervalIntegral.integral_const_mul]

/-- `r exp (-(r c)) ≤ 1 / c` for every real `r` and `c > 0`. -/
theorem mul_exp_neg_mul_le {r c : ℝ} (hc : 0 < c) : r * Real.exp (-(r * c)) ≤ 1 / c := by
  rw [le_div_iff₀ hc]
  have h1 := Real.mul_exp_neg_le_exp_neg_one (r * c)
  have h2 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  nlinarith

/-- **Proportional hazards families are regular at every time with a positive baseline
cumulative hazard.** For a measurable relative hazard `ρ ≥ 0` (`ν`-almost surely), a measurable
baseline hazard `h₀ ≥ 0` on `[0, ∞)`, integrable on every `[0, u]` and continuous on
`(s - ε₀, s + ε₀)` with `0 < ε₀ ≤ s`, and `cumHazard h₀ s > 0`, the hazards `ρ x * h₀ u` are
regular at `s` under every finite law. No integrability of `ρ` is needed: the envelope is the
constant `C / c` with `C` a bound of `h₀` and `c` a lower bound of `cumHazard h₀` near `s`,
since `r exp (-(r c)) ≤ 1 / c`. -/
theorem isEnvelopedHazardAt_mul [IsFiniteMeasure ν] {ρ : 𝒳 → ℝ} (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x) {h₀ : ℝ → ℝ} (hm₀ : Measurable h₀) (hn₀ : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hi₀ : ∀ u, 0 ≤ u → IntervalIntegrable h₀ volume 0 u) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀s : ε₀ ≤ s) (hc₀ : ContinuousOn h₀ (ball s ε₀)) (hΛ : 0 < cumHazard h₀ s) :
    IsEnvelopedHazardAt ν (fun x u => ρ x * h₀ u) s := by
  have hs : 0 < s := hε₀.trans_le hε₀s
  -- a bound of `h₀` near `s`
  have hsub : closedBall s (ε₀ / 2) ⊆ ball s ε₀ := closedBall_subset_ball (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_closedBall s (ε₀ / 2)).exists_bound_of_continuousOn
    (hc₀.mono hsub)
  -- a lower bound of the cumulative hazard near `s`
  have hd : HasDerivAt (cumHazard h₀) (h₀ s) s :=
    intervalIntegral.integral_hasDerivAt_right (hi₀ s hs.le)
      (hc₀.stronglyMeasurableAtFilter isOpen_ball s (mem_ball_self hε₀))
      (hc₀.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε₀)))
  obtain ⟨δ, hδ, hδΛ⟩ := Metric.eventually_nhds_iff.1
    (hd.continuousAt.eventually (lt_mem_nhds (half_lt_self hΛ)))
  set c := cumHazard h₀ s / 2 with hcdef
  have hc : 0 < c := half_pos hΛ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC s (mem_closedBall_self (by linarith)))
  refine ⟨(hρ.comp measurable_fst).mul (hm₀.comp measurable_snd),
    hρ0.mono fun x hx u hu => mul_nonneg hx (hn₀ u hu),
    Eventually.of_forall fun x u hu => (hi₀ u hu).const_mul (ρ x),
    min (ε₀ / 2) δ, lt_min (by linarith) hδ, (min_le_left _ _).trans (by linarith),
    fun _ => C / c, integrable_const _, ?_⟩
  filter_upwards [hρ0] with x hx
  have hball : ball s (min (ε₀ / 2) δ) ⊆ ball s ε₀ :=
    ball_subset_ball ((min_le_left _ _).trans (by linarith))
  refine ⟨continuousOn_const.mul (hc₀.mono hball), fun u hu => ?_⟩
  have hu1 : u ∈ closedBall s (ε₀ / 2) :=
    ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hu)
  have hu2 : c < cumHazard h₀ u := hδΛ (lt_of_lt_of_le (mem_ball.1 hu) (min_le_right _ _))
  have hu0 : 0 ≤ u := by
    have := mem_closedBall.1 hu1
    rw [Real.dist_eq, abs_le] at this
    linarith
  have hCu : h₀ u ≤ C := (le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hC u hu1)
  rw [congrFun (congrFun (hazardCurves_mul ρ h₀) x) u, phSurvival]
  have hexp : ρ x * Real.exp (-(ρ x * cumHazard h₀ u)) ≤ 1 / c := by
    refine le_trans ?_ (mul_exp_neg_mul_le (r := ρ x) hc)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hx
    exact neg_le_neg (mul_le_mul_of_nonneg_left hu2.le hx)
  calc ρ x * h₀ u * Real.exp (-(ρ x * cumHazard h₀ u))
      = h₀ u * (ρ x * Real.exp (-(ρ x * cumHazard h₀ u))) := by ring
    _ ≤ C * (1 / c) :=
        mul_le_mul hCu hexp (mul_nonneg hx (Real.exp_pos _).le) hC0
    _ = C / c := by ring

/-- **The proportional hazards formula from the general one.** For a finite nonzero law, a
measurable relative hazard `ρ ≥ 0` (`ν`-almost surely) and a baseline hazard `h₀` as in
`isEnvelopedHazardAt_mul` with `cumHazard h₀ s > 0`, the survivor weighted formula gives
`popHazard ν (phSurvival Λ₀ ρ) s = (∫ ρ x h₀ s S x s dν) / (∫ S x s dν)` with
`Λ₀ = cumHazard h₀`. This is the right side of `popHazard_phSurvival_eq_div`, obtained here from
`popHazard_hazardCurves` for a finite (not only probability) law and without integrability of
`ρ`, in the case of a baseline cumulative hazard `∫₀ˢ h₀` with `h₀` continuous near `s`. -/
theorem popHazard_phSurvival_cumHazard [IsFiniteMeasure ν] [NeZero ν] {ρ : 𝒳 → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x) {h₀ : ℝ → ℝ} (hm₀ : Measurable h₀)
    (hn₀ : ∀ u, 0 ≤ u → 0 ≤ h₀ u) (hi₀ : ∀ u, 0 ≤ u → IntervalIntegrable h₀ volume 0 u)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀s : ε₀ ≤ s) (hc₀ : ContinuousOn h₀ (ball s ε₀))
    (hΛ : 0 < cumHazard h₀ s) :
    popHazard ν (phSurvival (cumHazard h₀) ρ) s =
      (∫ x, ρ x * h₀ s * phSurvival (cumHazard h₀) ρ x s ∂ν) /
        ∫ x, phSurvival (cumHazard h₀) ρ x s ∂ν := by
  have he := isEnvelopedHazardAt_mul (ν := ν) hρ hρ0 hm₀ hn₀ hi₀ hε₀ hε₀s hc₀ hΛ
  have := (popHazard_hazardCurves he).2
  rwa [hazardCurves_mul] at this

/-- **The survivor law of a proportional hazards model, bridged.** The image under the relative
hazard `ρ` of the law of the covariates among the survivors of `phSurvival Λ₀ ρ` at `s` is the
survivor law `survivorLaw (ν.map ρ) (Λ₀ s)` of the mixture of exponential laws with rate law
`ν.map ρ`, at the time `Λ₀ s`. -/
theorem map_covSurvivorLaw_phSurvival {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (Λ₀ : ℝ → ℝ) (s : ℝ) :
    (covSurvivorLaw ν (phSurvival Λ₀ ρ) s).map ρ = survivorLaw (ν.map ρ) (Λ₀ s) := by
  have hf : Measurable fun r : ℝ =>
      ENNReal.ofReal (Real.exp (-(r * Λ₀ s)) / genSurvival (ν.map ρ) (Λ₀ s)) :=
    ((Real.continuous_exp.comp (by fun_prop)).div_const _).measurable.ennreal_ofReal
  rw [survivorLaw_eq_withDensity]
  ext A hA
  rw [Measure.map_apply hρ hA, covSurvivorLaw, withDensity_apply _ (hρ hA),
    withDensity_apply _ hA, setLIntegral_map hA hf hρ, popSurvival_phSurvival hρ]
  rfl

/-- **The mean rate among survivors from the general formula.** Under the hypotheses of
`popHazard_phSurvival_cumHazard`, the population hazard is `h₀ s` times the mean rate among the
survivors `genHazard (ν.map ρ) (cumHazard h₀ s)`; this is `popHazard_phSurvival` in that case,
obtained from `popHazard_eq_integral_covSurvivorLaw` and `map_covSurvivorLaw_phSurvival`. -/
theorem popHazard_phSurvival_cumHazard_genHazard [IsFiniteMeasure ν] [NeZero ν] {ρ : 𝒳 → ℝ}
    (hρ : Measurable ρ) (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x) {h₀ : ℝ → ℝ} (hm₀ : Measurable h₀)
    (hn₀ : ∀ u, 0 ≤ u → 0 ≤ h₀ u) (hi₀ : ∀ u, 0 ≤ u → IntervalIntegrable h₀ volume 0 u)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀s : ε₀ ≤ s) (hc₀ : ContinuousOn h₀ (ball s ε₀))
    (hΛ : 0 < cumHazard h₀ s) :
    popHazard ν (phSurvival (cumHazard h₀) ρ) s =
      h₀ s * genHazard (ν.map ρ) (cumHazard h₀ s) := by
  have he := isEnvelopedHazardAt_mul (ν := ν) hρ hρ0 hm₀ hn₀ hi₀ hε₀ hε₀s hc₀ hΛ
  have h1 := (popHazard_eq_integral_covSurvivorLaw he).2
  rw [hazardCurves_mul] at h1
  rw [h1, genHazard, ← map_covSurvivorLaw_phSurvival hρ,
    integral_map (f := fun r : ℝ => r) hρ.aemeasurable aestronglyMeasurable_id,
    integral_mul_const, mul_comm]

end ProportionalHazards

/-! ### Two arms: the marginal hazard ratio -/

section TwoArms

/-- **The marginal hazard ratio as a ratio of survivor weighted means.** For two arms with
conditional hazards `h₀` (control) and `h₁` (treated), both regular at `s` under a finite nonzero
law, and `ν`-almost surely positive control hazards at `s`, the control population hazard is
positive and the marginal hazard ratio at `s` is the mean of `h₁ · s` among the survivors of the
treated arm over the mean of `h₀ · s` among the survivors of the control arm. -/
theorem popHazard_ratio_hazardCurves [IsFiniteMeasure ν] [NeZero ν] {h₀ h₁ : 𝒳 → ℝ → ℝ}
    (he₀ : IsEnvelopedHazardAt ν h₀ s) (he₁ : IsEnvelopedHazardAt ν h₁ s)
    (hpos : ∀ᵐ x ∂ν, 0 < h₀ x s) :
    0 < popHazard ν (hazardCurves h₀) s ∧
      popHazard ν (hazardCurves h₁) s / popHazard ν (hazardCurves h₀) s =
        (∫ x, h₁ x s ∂covSurvivorLaw ν (hazardCurves h₁) s) /
          ∫ x, h₀ x s ∂covSurvivorLaw ν (hazardCurves h₀) s := by
  refine ⟨popHazard_hazardCurves_pos he₀ hpos, ?_⟩
  rw [(popHazard_eq_integral_covSurvivorLaw he₀).2, (popHazard_eq_integral_covSurvivorLaw he₁).2]

omit [MeasurableSpace 𝒳] in
/-- Under a conditional hazard ratio `ψ`, the treated curves are the control curves to the
power `ψ`. -/
theorem hazardCurves_const_mul (h₀ : 𝒳 → ℝ → ℝ) (ψ : ℝ) (x : 𝒳) (u : ℝ) :
    hazardCurves (fun x u => ψ * h₀ x u) x u = hazardCurves h₀ x u ^ ψ := by
  rw [Real.rpow_def_of_pos (hazardCurves_pos h₀ x u), hazardCurves_apply, hazardCurves_apply,
    Real.log_exp, cumHazard, cumHazard, intervalIntegral.integral_const_mul]
  ring_nf

/-- **Non collapsibility of the hazard ratio: the mechanism.** Let the treated arm have the
conditional hazards `ψ h₀ x u`, a conditional hazard ratio `ψ` at every covariate value and
every time. If both arms are regular at `s` under a finite nonzero law and the control hazards
are `ν`-almost surely positive at `s`, then the mean of `h₀ · s` among the control survivors is
positive and the marginal hazard ratio at `s` is `ψ` times the ratio of the means of the same
control hazard `h₀ · s` under two survivor laws: that of the treated arm, whose curves are
`S₀ ^ ψ` (`hazardCurves_const_mul`), over that of the control arm. The marginal ratio is `ψ` only
when these two means agree. -/
theorem popHazard_ratio_hazardCurves_const_mul [IsFiniteMeasure ν] [NeZero ν]
    {h₀ : 𝒳 → ℝ → ℝ} {ψ : ℝ} (he₀ : IsEnvelopedHazardAt ν h₀ s)
    (he₁ : IsEnvelopedHazardAt ν (fun x u => ψ * h₀ x u) s) (hpos : ∀ᵐ x ∂ν, 0 < h₀ x s) :
    0 < ∫ x, h₀ x s ∂covSurvivorLaw ν (hazardCurves h₀) s ∧
      popHazard ν (hazardCurves fun x u => ψ * h₀ x u) s / popHazard ν (hazardCurves h₀) s =
        ψ * ((∫ x, h₀ x s ∂covSurvivorLaw ν (hazardCurves fun x u => ψ * h₀ x u) s) /
          ∫ x, h₀ x s ∂covSurvivorLaw ν (hazardCurves h₀) s) := by
  obtain ⟨h0pos, hratio⟩ := popHazard_ratio_hazardCurves he₀ he₁ hpos
  refine ⟨(popHazard_eq_integral_covSurvivorLaw he₀).2 ▸ h0pos, ?_⟩
  rw [hratio, integral_const_mul, mul_div_assoc]

end TwoArms

end ContinuousTime

end Survival

end CausalInference
