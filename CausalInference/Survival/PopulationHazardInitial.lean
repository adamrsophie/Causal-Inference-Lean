/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.PopulationHazardExamples
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The population hazard at the time zero

**Time scale: continuous.** The survivor weighted formula of `Survival.PopulationHazard` holds at
times `s > 0`, because `popHazard` is defined with the two sided derivative and the curves
`S x = exp (-∫₀ h x)` carry no information before `0`. At the time `0` everybody is alive,
`S x 0 = 1`, and the population hazard taken from the right is the plain average of the
conditional hazards: no survivor weighting has happened yet.

The right sided hazard `curveHazardRight S s = -S'(s+) / S s` uses
`derivWithin S (Ici s) s`; `Ici s` has unique derivatives at `s` (`uniqueDiffWithinAt_Ici`), so
the right derivative is determined, and where the curve is differentiable the right sided hazard
is the hazard (`curveHazardRight_eq_curveHazard`).

## Main definitions

* `IsEnvelopedHazardAtZero ν h`: the conditional hazards are almost surely right continuous at
  `0`, and `h x u * S x u` has a `ν` integrable envelope on some `[0, ε)`.
* `curveHazardRight S s`, `popHazardRight ν S s`: the right sided hazard of a curve and of the
  population curve.

## Main results

* `integral_mul_hazardCurves`: `∫₀ᵇ h S = 1 - S b` for a nonnegative integrable hazard.
* `hasDerivWithinAt_popSurvival_hazardCurves_zero`: the population curve has right derivative
  `-∫ h x 0 dν(x)` at `0` (dominated convergence).
* `popHazardRight_hazardCurves`: at a time `s > 0` with `IsEnvelopedHazardAt ν h s`, the right
  sided population hazard is `popHazard`.
* `popHazardRight_hazardCurves_zero`: at `0` under a probability law it is `∫ h x 0 dν(x)`;
  `covSurvivorLaw_hazardCurves_zero`: the survivor law at `0` is the covariate law.
* `popHazardRight_ratio_hazardCurves_const_mul_zero`: under a conditional hazard ratio `ψ` the
  right sided marginal hazard ratio at `0` is `ψ`; `popHazardRight_ratio_phSurvival`: in a
  proportional hazards model with a nonconstant relative hazard it is `ψ` at `0` and not `ψ` at
  positive times.
* Finite mixtures: `popHazardRight_stratumLaw`, `popHazardRight_stratumLaw_zero`,
  `popHazardRight_ratio_stratumLaw_zero` (the bridge to `mixHazard_ratio_zero`).
* Instances: `popHazardRight_ratio_phModel_strataLaw` (`phModel`: right sided population
  hazards `3/2` and `3` at `0`, ratio `2`, against `9/5` at `log 2`), with the ratio `2` also
  from the general statement (`popHazardRight_ratio_phModel_strataLaw_zero`), and
  `popHazardRight_nonPH`
  (`nonPHHazard`: `1/2` at `0`, `3/2` at `1`).

## References

* M. A. Hernán, *The hazards of hazard ratios*, Epidemiology 21 (2010).
* O. O. Aalen, R. J. Cook and K. Røysland, *Does Cox analysis of a randomized survival study
  yield a causal treatment effect?*, Lifetime Data Analysis 21 (2015).
-/

@[expose] public section

namespace CausalInference

namespace Survival

namespace ContinuousTime

open MeasureTheory Set Filter Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳] {ν : Measure 𝒳} {h : 𝒳 → ℝ → ℝ}

/-! ### The conditional curves at and right after the time `0` -/

omit [MeasurableSpace 𝒳] in
/-- Everybody is alive at the time `0`: every conditional curve is `1` there. -/
theorem hazardCurves_zero (h : 𝒳 → ℝ → ℝ) (x : 𝒳) : hazardCurves h x 0 = 1 := by
  simp [hazardCurves_apply, cumHazard]

/-- Under a finite law the population curve at the time `0` is the total mass of the law. -/
theorem popSurvival_hazardCurves_zero (ν : Measure 𝒳) [IsFiniteMeasure ν] (h : 𝒳 → ℝ → ℝ) :
    popSurvival ν (hazardCurves h) 0 = ν.real univ := by
  simp [popSurvival, hazardCurves_zero]

/-- `u ↦ exp (-u)` is `1` Lipschitz on `[0, ∞)`. -/
theorem lipschitzOnWith_exp_neg_Ici : LipschitzOnWith 1 (fun u => Real.exp (-u)) (Ici 0) := by
  refine Convex.lipschitzOnWith_of_nnNorm_hasDerivWithin_le (convex_Ici 0)
    (f' := fun u => -Real.exp (-u)) (fun u _ => ?_) fun u hu => ?_
  · exact ((hasDerivAt_neg u).exp.congr_deriv (by ring)).hasDerivWithinAt
  · rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, abs_neg,
      abs_of_pos (Real.exp_pos _), NNReal.coe_one]
    exact Real.exp_le_one_iff.mpr (by simpa using hu)

omit [MeasurableSpace 𝒳] in
/-- **The probability of an event by the time `b`**: for a hazard that is nonnegative on
`[0, ∞)` and integrable on `[0, b]`, `∫₀ᵇ h S = 1 - S b` with `S = exp (-∫₀ h)`. The hazard need
not be continuous: `S` is absolutely continuous on `[0, b]`, with derivative `-h S` almost
everywhere. -/
theorem integral_mul_hazardCurves {x : 𝒳} (hn : ∀ v, 0 ≤ v → 0 ≤ h x v) {b : ℝ} (hb : 0 ≤ b)
    (hi : IntervalIntegrable (h x) volume 0 b) :
    ∫ t in (0 : ℝ)..b, h x t * hazardCurves h x t = 1 - hazardCurves h x b := by
  have hac : AbsolutelyContinuousOnInterval (cumHazard (h x)) 0 b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hmaps : MapsTo (cumHazard (h x)) (uIcc 0 b) (Ici 0) := fun t ht => by
    rw [uIcc_of_le hb] at ht
    exact cumHazard_nonneg hn ht.1
  have hftc := (lipschitzOnWith_exp_neg_Ici.comp_absolutelyContinuousOnInterval hmaps
    hac).integral_deriv_eq_sub
  have hderiv : ∀ᵐ t, t ∈ uIoc 0 b →
      deriv ((fun u => Real.exp (-u)) ∘ cumHazard (h x)) t =
        -(h x t * hazardCurves h x t) := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht htI
    have htI' : t ∈ uIcc 0 b := uIoc_subset_uIcc htI
    have hd := (ht htI' 0 (by rw [uIcc_of_le hb]; exact ⟨le_rfl, hb⟩)).neg.exp
    rw [Function.comp_def]
    refine hd.deriv.trans ?_
    rw [hazardCurves_apply, cumHazard, Pi.neg_apply]
    ring
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_neg] at hftc
  simp only [Function.comp_apply] at hftc
  have h0 : Real.exp (-cumHazard (h x) 0) = 1 := by simp [cumHazard]
  rw [h0] at hftc
  rw [hazardCurves_apply]
  linarith

omit [MeasurableSpace 𝒳] in
/-- **The right derivative of a conditional curve at the time `0`**: a measurable hazard that is
right continuous at `0` gives a curve `exp (-∫₀ h)` with right derivative `-h 0` at `0`. -/
theorem hasDerivWithinAt_hazardCurves_zero {x : 𝒳} (hm : Measurable (h x))
    (hc : ContinuousWithinAt (h x) (Ici 0) 0) :
    HasDerivWithinAt (hazardCurves h x) (-h x 0) (Ici 0) 0 := by
  have hd : HasDerivWithinAt (cumHazard (h x)) (h x 0) (Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right IntervalIntegrable.refl (t := Ioi 0)
      hm.stronglyMeasurable.stronglyMeasurableAtFilter (hc.mono Ioi_subset_Ici_self)
  have := hd.neg.exp
  have h0 : Real.exp ((-cumHazard (h x)) 0) = 1 := by simp [cumHazard]
  rw [h0, one_mul] at this
  exact this

/-! ### The regularity condition at the time `0` -/

/-- **Regularity of a family of conditional hazards at the time `0`, from the right.** The
hazard is jointly measurable; `ν`-almost every conditional hazard is nonnegative on `[0, ∞)`
and integrable on every `[0, u]`; and there is a radius `ε > 0` such that `ν`-almost every
conditional hazard is right continuous at `0` and the products `h x u * S x u` on `[0, ε)` are
bounded by a `ν` integrable function `g x` of the covariate, with `S = hazardCurves h`. Nothing
is asked at negative times, and no continuity is asked at positive times. The envelope bounds
the derivative `h x u * S x u` of the conditional curve; a hazard envelope is a special case
(`IsEnvelopedHazardAtZero.of_hazard_le`). -/
structure IsEnvelopedHazardAtZero (ν : Measure 𝒳) (h : 𝒳 → ℝ → ℝ) : Prop where
  measurable : Measurable (Function.uncurry h)
  nonneg : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → 0 ≤ h x u
  intervalIntegrable : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → IntervalIntegrable (h x) volume 0 u
  envelope : ∃ ε, 0 < ε ∧ ∃ g : 𝒳 → ℝ, Integrable g ν ∧ ∀ᵐ x ∂ν,
    ContinuousWithinAt (h x) (Ici 0) 0 ∧ ∀ u ∈ Ico 0 ε, h x u * hazardCurves h x u ≤ g x

/-- **A hazard envelope suffices**: if `ν`-almost every conditional hazard is right continuous
at `0` and bounded on `[0, ε)` by `g x` with `g` integrable and `ε > 0`, the family is regular
at the time `0`. -/
theorem IsEnvelopedHazardAtZero.of_hazard_le (hm : Measurable (Function.uncurry h))
    (hn : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → 0 ≤ h x u)
    (hi : ∀ᵐ x ∂ν, ∀ u, 0 ≤ u → IntervalIntegrable (h x) volume 0 u) {ε : ℝ} (hε : 0 < ε)
    {g : 𝒳 → ℝ} (hg : Integrable g ν)
    (hb : ∀ᵐ x ∂ν, ContinuousWithinAt (h x) (Ici 0) 0 ∧ ∀ u ∈ Ico 0 ε, h x u ≤ g x) :
    IsEnvelopedHazardAtZero ν h := by
  refine ⟨hm, hn, hi, ε, hε, g, hg, ?_⟩
  filter_upwards [hn, hb] with x hnx hbx
  refine ⟨hbx.1, fun u hu => ?_⟩
  calc h x u * hazardCurves h x u ≤ h x u * 1 :=
        mul_le_mul_of_nonneg_left (hazardCurves_le_one hnx hu.1) (hnx u hu.1)
    _ ≤ g x := by rw [mul_one]; exact hbx.2 u hu

/-- Under the regularity at `0` the conditional hazards at `0` are `ν` integrable: they lie
between `0` and the envelope. -/
theorem IsEnvelopedHazardAtZero.integrable (he : IsEnvelopedHazardAtZero ν h) :
    Integrable (fun x => h x 0) ν := by
  obtain ⟨ε, hε, g, hg, hb⟩ := he.envelope
  refine hg.mono' (he.measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    ?_
  filter_upwards [he.nonneg, hb] with x hnx hbx
  have := hbx.2 0 ⟨le_rfl, hε⟩
  rw [hazardCurves_zero, mul_one] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (hnx 0 le_rfl)]
  exact this

/-! ### The right derivative of the population curve at the time `0` -/

/-- **The right derivative of the population curve at the time `0`.** Under a finite law and the
regularity `IsEnvelopedHazardAtZero ν h`, the conditional hazards at `0` are integrable and the
population curve of `S = hazardCurves h` has right derivative `-∫ h x 0 dν(x)` at `0`: since
`S x 0 = 1`, the survivor weighting `h x 0 * S x 0` is no weighting at all. The proof is
dominated convergence for the difference quotients `(S x u - 1) / u`, which the envelope bounds
through `1 - S x u = ∫₀ᵘ h x S x` (`integral_mul_hazardCurves`). -/
theorem hasDerivWithinAt_popSurvival_hazardCurves_zero [IsFiniteMeasure ν]
    (he : IsEnvelopedHazardAtZero ν h) :
    Integrable (fun x => h x 0) ν ∧
      HasDerivWithinAt (popSurvival ν (hazardCurves h)) (-∫ x, h x 0 ∂ν) (Ici 0) 0 := by
  obtain ⟨ε, hε, g, hg, hb⟩ := he.envelope
  have hmx : ∀ x, Measurable (h x) := fun x =>
    he.measurable.comp (measurable_const.prodMk measurable_id)
  have hmS := measurable_hazardCurves he.measurable
  have hint : ∀ t, 0 ≤ t → Integrable (fun x => hazardCurves h x t) ν := fun t ht =>
    Integrable.of_bound (hmS t).aestronglyMeasurable 1 (he.nonneg.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (hazardCurves_pos h x t)]
      exact hazardCurves_le_one hx ht)
  refine ⟨he.integrable, ?_⟩
  rw [hasDerivWithinAt_iff_tendsto_slope, ← integral_neg]
  refine (tendsto_integral_filter_of_dominated_convergence
    (F := fun s' x => slope (fun t => hazardCurves h x t) 0 s') g ?_ ?_ hg ?_).congr' ?_
  · exact Eventually.of_forall fun s' => by
      simp only [slope_def_field]
      exact (((hmS s').sub (hmS 0)).div_const _).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε)] with s' hs' hs'ε
    filter_upwards [he.nonneg, he.intervalIntegrable, hb] with x hnx hix hbx
    have hs0 : 0 < s' := lt_of_le_of_ne hs'.1 (Ne.symm hs'.2)
    rw [slope_def_field, hazardCurves_zero, sub_zero, Real.norm_eq_abs, abs_div,
      abs_of_pos hs0, div_le_iff₀ hs0]
    have hI := integral_mul_hazardCurves hnx hs0.le (hix s' hs0.le)
    have hle : ‖∫ t in (0 : ℝ)..s', h x t * hazardCurves h x t‖ ≤ g x * |s' - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
        rw [uIoc_of_le hs0.le] at ht
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (hnx t ht.1.le) (hazardCurves_pos h x t).le)]
        exact hbx.2 t ⟨ht.1.le, ht.2.trans_lt hs'ε⟩
    rw [hI, Real.norm_eq_abs, sub_zero, abs_of_pos hs0] at hle
    rw [abs_sub_comm]
    exact hle
  · filter_upwards [hb] with x hbx
    exact hasDerivWithinAt_iff_tendsto_slope.mp (hasDerivWithinAt_hazardCurves_zero (hmx x) hbx.1)
  · filter_upwards [self_mem_nhdsWithin] with s' hs'
    simp only [slope_def_field]
    rw [integral_div, integral_sub (hint s' hs'.1) (hint 0 le_rfl), popSurvival, popSurvival]

/-! ### The right sided hazard -/

/-- The **right sided hazard of a curve** at the time `s`: `-S'(s+) / S(s)`, with the right
derivative `derivWithin S (Ici s) s`. It does not look at the curve before `s`, so at the time
`0` it does not depend on the curve at negative times. It is a genuine hazard where `S` has a
right derivative and is positive; the results below say so. -/
noncomputable def curveHazardRight (S : ℝ → ℝ) (s : ℝ) : ℝ := -derivWithin S (Ici s) s / S s

/-- The **right sided population hazard**: the right sided hazard of the population curve. -/
noncomputable def popHazardRight (ν : Measure 𝒳) (S : 𝒳 → ℝ → ℝ) (s : ℝ) : ℝ :=
  curveHazardRight (popSurvival ν S) s

/-- Where the curve is differentiable, the right sided hazard is the hazard: `Ici s` has unique
derivatives at `s`. -/
theorem curveHazardRight_eq_curveHazard {S : ℝ → ℝ} {s : ℝ} (hS : DifferentiableAt ℝ S s) :
    curveHazardRight S s = curveHazard S s := by
  rw [curveHazardRight, curveHazard, hS.derivWithin (uniqueDiffWithinAt_Ici s)]

/-- Where the population curve is differentiable, the right sided population hazard is the
population hazard `popHazard`. -/
theorem popHazardRight_eq_popHazard {S : 𝒳 → ℝ → ℝ} {s : ℝ}
    (hS : DifferentiableAt ℝ (popSurvival ν S) s) : popHazardRight ν S s = popHazard ν S s :=
  curveHazardRight_eq_curveHazard hS

/-- **The bridge at positive times.** Under a finite law and the regularity
`IsEnvelopedHazardAt ν h s` (so at a time `s > 0`), the right sided population hazard at `s` is
the population hazard `popHazard`, given by the survivor weighted formula
`popHazard_hazardCurves`. -/
theorem popHazardRight_hazardCurves [IsFiniteMeasure ν] {s : ℝ} (he : IsEnvelopedHazardAt ν h s) :
    popHazardRight ν (hazardCurves h) s = popHazard ν (hazardCurves h) s :=
  popHazardRight_eq_popHazard (hasDerivAt_popSurvival_hazardCurves he).2.differentiableAt

/-- **The population hazard at the time `0` is the plain average of the conditional
hazards.** Under a probability law and the regularity `IsEnvelopedHazardAtZero ν h`, the
conditional hazards at `0` are integrable and the right sided population hazard at `0` is
`∫ h x 0 dν(x)`. Everybody is alive at `0`, so the survivor weights `S x 0` of the formula at
positive times (`popHazard_hazardCurves`) are all `1`. -/
theorem popHazardRight_hazardCurves_zero [IsProbabilityMeasure ν]
    (he : IsEnvelopedHazardAtZero ν h) :
    Integrable (fun x => h x 0) ν ∧ popHazardRight ν (hazardCurves h) 0 = ∫ x, h x 0 ∂ν := by
  obtain ⟨hi, hd⟩ := hasDerivWithinAt_popSurvival_hazardCurves_zero he
  refine ⟨hi, ?_⟩
  rw [popHazardRight, curveHazardRight, hd.derivWithin (uniqueDiffWithinAt_Ici 0), neg_neg,
    popSurvival_hazardCurves_zero, probReal_univ, div_one]

/-- The time `0` under a finite nonzero law: the population curve at `0` is the positive total
mass `ν.real univ`, and the right sided population hazard at `0` is the mean
`(∫ h x 0 dν) / ν.real univ` of the conditional hazards. -/
theorem popHazardRight_hazardCurves_zero_eq_div [IsFiniteMeasure ν] [NeZero ν]
    (he : IsEnvelopedHazardAtZero ν h) :
    0 < popSurvival ν (hazardCurves h) 0 ∧
      popHazardRight ν (hazardCurves h) 0 = (∫ x, h x 0 ∂ν) / ν.real univ := by
  obtain ⟨-, hd⟩ := hasDerivWithinAt_popSurvival_hazardCurves_zero he
  rw [popSurvival_hazardCurves_zero]
  refine ⟨measureReal_univ_pos, ?_⟩
  rw [popHazardRight, curveHazardRight, hd.derivWithin (uniqueDiffWithinAt_Ici 0), neg_neg,
    popSurvival_hazardCurves_zero]

/-- **At the time `0` the survivors are the whole population**: under a probability law the law
of the covariates among the survivors at `0` is the covariate law itself. -/
theorem covSurvivorLaw_hazardCurves_zero [IsProbabilityMeasure ν] (h : 𝒳 → ℝ → ℝ) :
    covSurvivorLaw ν (hazardCurves h) 0 = ν := by
  rw [covSurvivorLaw, popSurvival_hazardCurves_zero, probReal_univ]
  simp [hazardCurves_zero]

/-! ### Two arms at the time `0` -/

/-- Under a conditional hazard ratio `ψ ≥ 1`, the regularity at `0` of the control hazards gives
that of the treated hazards: the treated curves `S₀ ^ ψ` are at most the control curves `S₀`. -/
theorem IsEnvelopedHazardAtZero.const_mul {h₀ : 𝒳 → ℝ → ℝ} (he : IsEnvelopedHazardAtZero ν h₀)
    {ψ : ℝ} (hψ : 1 ≤ ψ) : IsEnvelopedHazardAtZero ν (fun x u => ψ * h₀ x u) := by
  obtain ⟨ε, hε, g, hg, hb⟩ := he.envelope
  have hψ0 : 0 ≤ ψ := zero_le_one.trans hψ
  refine ⟨he.measurable.const_mul ψ, he.nonneg.mono fun x hx u hu => mul_nonneg hψ0 (hx u hu),
    he.intervalIntegrable.mono fun x hx u hu => (hx u hu).const_mul ψ, ε, hε,
    fun x => ψ * g x, hg.const_mul ψ, ?_⟩
  filter_upwards [he.nonneg, hb] with x hnx hbx
  refine ⟨continuousWithinAt_const.mul hbx.1, fun u hu => ?_⟩
  rw [hazardCurves_const_mul]
  have hS := hazardCurves_pos h₀ x u
  have hS1 := hazardCurves_le_one hnx hu.1
  have hpow : hazardCurves h₀ x u ^ ψ ≤ hazardCurves h₀ x u := by
    calc hazardCurves h₀ x u ^ ψ ≤ hazardCurves h₀ x u ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hS hS1 hψ
      _ = hazardCurves h₀ x u := Real.rpow_one _
  calc ψ * h₀ x u * hazardCurves h₀ x u ^ ψ ≤ ψ * (h₀ x u * hazardCurves h₀ x u) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (hnx u hu.1)) hψ0
    _ ≤ ψ * g x := mul_le_mul_of_nonneg_left (hbx.2 u hu) hψ0

/-- **At the time `0` the marginal hazard ratio is the conditional one.** Let the treated arm
have the conditional hazards `ψ h₀ x u`. If both arms are regular at `0` under a probability law
and the mean control hazard at `0` is positive, then the right sided control population hazard
at `0` is positive and the right sided marginal hazard ratio at `0` is exactly `ψ`. At positive
times the marginal ratio is `ψ` times a ratio of means of `h₀` under two different survivor laws
(`popHazard_ratio_hazardCurves_const_mul`), and it differs from `ψ` in general
(`popHazard_ratio_lt`, `lt_popHazard_ratio`, `popHazardRight_ratio_phSurvival`); at `0` the two
survivor laws are both the covariate law (`covSurvivorLaw_hazardCurves_zero`). -/
theorem popHazardRight_ratio_hazardCurves_const_mul_zero [IsProbabilityMeasure ν]
    {h₀ : 𝒳 → ℝ → ℝ} {ψ : ℝ} (he₀ : IsEnvelopedHazardAtZero ν h₀)
    (he₁ : IsEnvelopedHazardAtZero ν (fun x u => ψ * h₀ x u)) (hpos : 0 < ∫ x, h₀ x 0 ∂ν) :
    0 < popHazardRight ν (hazardCurves h₀) 0 ∧
      popHazardRight ν (hazardCurves fun x u => ψ * h₀ x u) 0 /
        popHazardRight ν (hazardCurves h₀) 0 = ψ := by
  rw [(popHazardRight_hazardCurves_zero he₀).2, (popHazardRight_hazardCurves_zero he₁).2,
    integral_const_mul, mul_div_assoc, div_self hpos.ne', mul_one]
  exact ⟨hpos, rfl⟩

/-! ### Proportional hazards at the time `0` and at positive times -/

section ProportionalHazards

open Bias.HazardMixtureGeneral EffectMeasure

/-- **Proportional hazards families are regular at the time `0`.** For a measurable,
`ν` integrable relative hazard `ρ ≥ 0` (`ν`-almost surely) and a measurable baseline hazard
`h₀ ≥ 0` on `[0, ∞)`, integrable on every `[0, u]` and right continuous at `0`, the hazards
`ρ x * h₀ u` are regular at `0`: near `0` the baseline is below `h₀ 0 + 1`, so `ρ x (h₀ 0 + 1)`
is a hazard envelope. -/
theorem isEnvelopedHazardAtZero_mul {ρ : 𝒳 → ℝ} (hρ : Measurable ρ) (hρi : Integrable ρ ν)
    (hρ0 : ∀ᵐ x ∂ν, 0 ≤ ρ x) {h₀ : ℝ → ℝ} (hm₀ : Measurable h₀) (hn₀ : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hi₀ : ∀ u, 0 ≤ u → IntervalIntegrable h₀ volume 0 u)
    (hc₀ : ContinuousWithinAt h₀ (Ici 0) 0) :
    IsEnvelopedHazardAtZero ν (fun x u => ρ x * h₀ u) := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
    (hc₀.eventually (gt_mem_nhds (lt_add_one (h₀ 0))))
  refine IsEnvelopedHazardAtZero.of_hazard_le
    ((hρ.comp measurable_fst).mul (hm₀.comp measurable_snd))
    (hρ0.mono fun x hx u hu => mul_nonneg hx (hn₀ u hu))
    (Eventually.of_forall fun x u hu => (hi₀ u hu).const_mul (ρ x)) (mem_Ioi.1 hε)
    (g := fun x => ρ x * (h₀ 0 + 1)) (hρi.mul_const _) ?_
  filter_upwards [hρ0] with x hx
  exact ⟨continuousWithinAt_const.mul hc₀,
    fun u hu => mul_le_mul_of_nonneg_left (le_of_lt (hsub hu)) hx⟩

/-- **Non collapsibility of the hazard ratio starts after the time `0`.** In a proportional
hazards model with a measurable, `ν` integrable relative hazard `ρ` that is `ν`-almost surely
positive and not `ν`-almost surely constant, a conditional hazard ratio `ψ > 0` with `ψ ≠ 1`, and
a baseline hazard `h₀` as in `isEnvelopedHazardAtZero_mul` with `h₀ 0 > 0`, under a probability
law:
* at the time `0` the right sided control population hazard is positive and the right sided
  marginal hazard ratio is exactly `ψ`;
* at every time `s` where `cumHazard h₀` has derivative `h₀ s > 0` and `cumHazard h₀ s > 0`,
  the right sided control population hazard is positive and the right sided marginal hazard
  ratio differs from `ψ` (`popHazard_pos`, `popHazard_ratio_lt`, `lt_popHazard_ratio`; the
  population curve is differentiable there, so the right sided hazards are the hazards
  `popHazard`). -/
theorem popHazardRight_ratio_phSurvival [IsProbabilityMeasure ν] {ρ : 𝒳 → ℝ}
    (hρ : Measurable ρ) (hρi : Integrable ρ ν) (hρ0 : ∀ᵐ x ∂ν, 0 < ρ x)
    (hnc : ¬ ∃ c, ∀ᵐ x ∂ν, ρ x = c) {ψ : ℝ} (hψ0 : 0 < ψ) (hψ1 : ψ ≠ 1) {h₀ : ℝ → ℝ}
    (hm₀ : Measurable h₀) (hn₀ : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (hi₀ : ∀ u, 0 ≤ u → IntervalIntegrable h₀ volume 0 u)
    (hc₀ : ContinuousWithinAt h₀ (Ici 0) 0) (hh₀ : 0 < h₀ 0) :
    (0 < popHazardRight ν (phSurvival (cumHazard h₀) ρ) 0 ∧
      popHazardRight ν (phSurvival (cumHazard h₀) fun x => ψ * ρ x) 0 /
        popHazardRight ν (phSurvival (cumHazard h₀) ρ) 0 = ψ) ∧
      ∀ s, HasDerivAt (cumHazard h₀) (h₀ s) s → 0 < cumHazard h₀ s → 0 < h₀ s →
        0 < popHazardRight ν (phSurvival (cumHazard h₀) ρ) s ∧
        popHazardRight ν (phSurvival (cumHazard h₀) fun x => ψ * ρ x) s /
          popHazardRight ν (phSurvival (cumHazard h₀) ρ) s ≠ ψ := by
  have hψρ : ∀ᵐ x ∂ν, 0 < ψ * ρ x := hρ0.mono fun x hx => mul_pos hψ0 hx
  constructor
  · have he₀ := isEnvelopedHazardAtZero_mul (ν := ν) hρ hρi
      (hρ0.mono fun x hx => hx.le) hm₀ hn₀ hi₀ hc₀
    have he₁ := isEnvelopedHazardAtZero_mul (ν := ν) (hρ.const_mul ψ) (hρi.const_mul ψ)
      (hψρ.mono fun x hx => hx.le) hm₀ hn₀ hi₀ hc₀
    have e₀ : phSurvival (cumHazard h₀) ρ = hazardCurves (fun x u => ρ x * h₀ u) :=
      (hazardCurves_mul ρ h₀).symm
    have e₁ : phSurvival (cumHazard h₀) (fun x => ψ * ρ x) =
        hazardCurves (fun x u => ψ * ρ x * h₀ u) := (hazardCurves_mul _ h₀).symm
    have hI : 0 < ∫ x, ρ x ∂ν := integral_pos_of_ae_pos hρi hρ0
    rw [e₀, e₁, (popHazardRight_hazardCurves_zero he₀).2, (popHazardRight_hazardCurves_zero he₁).2,
      integral_mul_const, integral_mul_const, integral_const_mul]
    exact ⟨mul_pos hI hh₀, by field_simp⟩
  · intro s hΛ hΛs hhs
    have hd : ∀ r : 𝒳 → ℝ, Measurable r → (∀ᵐ x ∂ν, 0 < r x) →
        DifferentiableAt ℝ (popSurvival ν (phSurvival (cumHazard h₀) r)) s := fun r hr hr0 => by
      rw [popSurvival_phSurvival hr]
      exact ((hasDerivAt_genSurvival
        (ae_nonneg_map hr (hr0.mono fun x hx => hx.le)) hΛs).comp s hΛ).differentiableAt
    rw [popHazardRight_eq_popHazard (hd _ (hρ.const_mul ψ) hψρ),
      popHazardRight_eq_popHazard (hd ρ hρ hρ0)]
    refine ⟨popHazard_pos hρ hρ0 hΛ hΛs hhs, ?_⟩
    rcases lt_or_gt_of_ne hψ1 with h | h
    · exact (lt_popHazard_ratio hρ hρ0 hnc hψ0 h hΛ hΛs hhs).ne'
    · exact (popHazard_ratio_lt hρ hρ0 hnc h hΛ hΛs hhs).ne

end ProportionalHazards

/-! ### Finite mixtures of constant hazards -/

section Finite

open Bias.HazardMixture EffectMeasure

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The cumulative hazard of the unit hazard is the identity. -/
theorem cumHazard_const_one_eq_id : cumHazard (fun _ => (1 : ℝ)) = id := by
  funext u
  simp [cumHazard]

/-- **The bridge to finite mixtures.** For a finite stratifier with weights `p` and constant
stratum hazards `r`, the population curve is the smooth mixture `mixSurvival p r`, so the right
sided population hazard is the mixture hazard `mixHazard p r` at every time. -/
theorem popHazardRight_stratumLaw {p : V → ℝ} (hp : IsWeights p) (r : V → ℝ) (t : ℝ) :
    popHazardRight (stratumLaw p) (phSurvival id r) t = mixHazard p r t := by
  have hS : popSurvival (stratumLaw p) (phSurvival id r) = mixSurvival p r :=
    funext fun s => popSurvival_stratumLaw hp.1 r id s
  have hd : DifferentiableAt ℝ (popSurvival (stratumLaw p) (phSurvival id r)) t := by
    rw [hS]
    exact (hasDerivAt_mixSurvival p r t).differentiableAt
  rw [popHazardRight_eq_popHazard hd, popHazard_stratumLaw hp]

/-- **The time `0` formula on a finite mixture.** With weights `p` and nonnegative constant
stratum hazards `r`, the general formula `popHazardRight_hazardCurves_zero` gives the right
sided population hazard `∑ p v r v` at `0`, the plain average of the stratum hazards, and so the
mixture hazard `mixHazard p r 0` is that average. -/
theorem popHazardRight_stratumLaw_zero {p : V → ℝ} (hp : IsWeights p) {r : V → ℝ}
    (hr : ∀ v, 0 ≤ r v) :
    popHazardRight (stratumLaw p) (phSurvival id r) 0 = ∑ v, p v * r v ∧
      mixHazard p r 0 = ∑ v, p v * r v := by
  have := isProbabilityMeasure_stratumLaw hp
  have he := isEnvelopedHazardAtZero_mul (ν := stratumLaw p) (ρ := r) (measurable_of_finite r)
    (integrable_stratumLaw p r) (Eventually.of_forall hr) measurable_const
    (fun _ _ => zero_le_one) (fun _ _ => intervalIntegrable_const) continuousWithinAt_const
  have e : phSurvival id r = hazardCurves (fun v _ => r v * 1) := by
    rw [hazardCurves_mul, cumHazard_const_one_eq_id]
  have h1 : popHazardRight (stratumLaw p) (phSurvival id r) 0 = ∑ v, p v * r v := by
    rw [e, (popHazardRight_hazardCurves_zero he).2, integral_stratumLaw hp.1, standardizedRisk]
    simp
  exact ⟨h1, (popHazardRight_stratumLaw hp r 0).symm.trans h1⟩

/-- **The ratio at `0` on a finite mixture, bridged.** With positive stratum hazards `r` for the
control arm and `ψ r` for the treated arm, the right sided marginal hazard ratio at `0` is `ψ`;
this is `mixHazard_ratio_zero` through `popHazardRight_stratumLaw`. The denominator is the
mixture hazard at `0`, positive by `mixHazard_pos`. -/
theorem popHazardRight_ratio_stratumLaw_zero {p : V → ℝ} (hp : IsWeights p) {r : V → ℝ}
    (hr : ∀ v, 0 < r v) (ψ : ℝ) :
    popHazardRight (stratumLaw p) (phSurvival id fun v => ψ * r v) 0 /
      popHazardRight (stratumLaw p) (phSurvival id r) 0 = ψ := by
  rw [popHazardRight_stratumLaw hp, popHazardRight_stratumLaw hp]
  exact mixHazard_ratio_zero hp hr ψ

end Finite

/-! ### Instances -/

section Instances

open IndirectComparison EffectMeasure

/-- The curves of the arm `a` of `phModel` with the unit baseline are the curves of the
constant conditional hazards `exp (η_a(x))`. -/
theorem phCurve_phModel_eq_hazardCurves (a : Bool) :
    phCurve phModel id a = hazardCurves (fun x _ => Real.exp (phModel.predictor a x) * 1) := by
  rw [hazardCurves_mul, cumHazard_const_one_eq_id]
  rfl

/-- Both arms of `phModel` are regular at the time `0` under `strataLaw`. -/
theorem isEnvelopedHazardAtZero_phModel (a : Bool) :
    IsEnvelopedHazardAtZero strataLaw (fun x _ => Real.exp (phModel.predictor a x) * 1) :=
  isEnvelopedHazardAtZero_mul (measurable_predictor phModel a).exp
    ((integrable_map_measure (measurable_predictor phModel a).exp.aestronglyMeasurable
      (measurable_of_finite strataCov).aemeasurable).2 (integrable_stratumLaw _ _))
    (Eventually.of_forall fun _ => (Real.exp_pos _).le) measurable_const
    (fun _ _ => zero_le_one) (fun _ _ => intervalIntegrable_const) continuousWithinAt_const

/-- Both arms of `phModel` are regular at the time `log 2` under `strataLaw`. -/
theorem isEnvelopedHazardAt_phModel_log_two (a : Bool) :
    IsEnvelopedHazardAt strataLaw (fun x _ => Real.exp (phModel.predictor a x) * 1)
      (Real.log 2) :=
  isEnvelopedHazardAt_mul (measurable_predictor phModel a).exp
    (Eventually.of_forall fun _ => (Real.exp_pos _).le) measurable_const
    (fun _ _ => zero_le_one) (fun _ _ => intervalIntegrable_const) log_two_pos' le_rfl
    continuousOn_const (by rw [cumHazard_const_one_eq_id]; exact log_two_pos')

/-- **`phModel` at the time `0`: the plain averages.** Under `strataLaw` the right sided
population hazards at `0` are the averages `(1 + 2) / 2 = 3/2` (control) and
`(2 + 4) / 2 = 3` (treated) of the stratum hazards. -/
theorem popHazardRight_phModel_strataLaw_zero (a : Bool) :
    popHazardRight strataLaw (phCurve phModel id a) 0 = if a then 3 else 3 / 2 := by
  rw [phCurve_phModel_eq_hazardCurves,
    (popHazardRight_hazardCurves_zero (isEnvelopedHazardAtZero_phModel a)).2,
    integral_strataLaw_eq ((measurable_predictor phModel a).exp.mul_const 1)]
  simp only [exp_phModel_predictor]
  cases a <;> norm_num [phRate]

/-- **`phModel`: the marginal hazard ratio is `2` at the time `0` and `9/5` at the time
`log 2`.** The conditional hazard ratio is `2` in both strata. At `0` the right sided population
hazards under `strataLaw` are `3/2` and `3`, with ratio `2`; at `log 2` the right sided
population hazards are the population hazards `4/3` and `12/5` (`popHazard_phModel_strataLaw`),
with ratio `9/5` (`logHazardRatio_marginal_example`). -/
theorem popHazardRight_ratio_phModel_strataLaw :
    popHazardRight strataLaw (phCurve phModel id false) 0 = 3 / 2 ∧
      popHazardRight strataLaw (phCurve phModel id true) 0 = 3 ∧
      popHazardRight strataLaw (phCurve phModel id true) 0 /
        popHazardRight strataLaw (phCurve phModel id false) 0 = 2 ∧
      popHazardRight strataLaw (phCurve phModel id true) (Real.log 2) /
        popHazardRight strataLaw (phCurve phModel id false) (Real.log 2) = 9 / 5 := by
  have h0 := popHazardRight_phModel_strataLaw_zero false
  have h1 := popHazardRight_phModel_strataLaw_zero true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h0 h1
  refine ⟨h0, h1, by rw [h0, h1]; norm_num, ?_⟩
  rw [phCurve_phModel_eq_hazardCurves, phCurve_phModel_eq_hazardCurves,
    popHazardRight_hazardCurves (isEnvelopedHazardAt_phModel_log_two true),
    popHazardRight_hazardCurves (isEnvelopedHazardAt_phModel_log_two false),
    ← phCurve_phModel_eq_hazardCurves, ← phCurve_phModel_eq_hazardCurves]
  exact logHazardRatio_marginal_example.2.2.2.1

/-- In `phModel` the treated hazards are twice the control hazards at every covariate value. -/
theorem phModel_hazard_true_eq_two_mul :
    (fun x (_ : ℝ) => Real.exp (phModel.predictor true x) * 1) =
      fun x u => 2 * (fun x (_ : ℝ) => Real.exp (phModel.predictor false x) * 1) x u := by
  funext x u
  simp only [phModel, AnchoredModel.predictor, anchoredPredictor, ite_true, Bool.false_eq_true,
    ite_false, Real.exp_add, Real.exp_log two_pos, Real.exp_zero]
  simp only [mul_comm (x _) (Real.log 2)]
  ring

/-- **The general statement applies to `phModel`**: with `ψ = 2`, both arms regular at `0`
(`IsEnvelopedHazardAtZero.const_mul`) and the mean control hazard `3/2 > 0` at `0`,
`popHazardRight_ratio_hazardCurves_const_mul_zero` gives the right sided marginal hazard ratio
`2` at the time `0`. -/
theorem popHazardRight_ratio_phModel_strataLaw_zero :
    popHazardRight strataLaw (phCurve phModel id true) 0 /
      popHazardRight strataLaw (phCurve phModel id false) 0 = 2 := by
  have he₀ := isEnvelopedHazardAtZero_phModel false
  have hpos : 0 < ∫ x, Real.exp (phModel.predictor false x) * 1 ∂strataLaw := by
    have h := (popHazardRight_hazardCurves_zero he₀).2
    rw [← phCurve_phModel_eq_hazardCurves, popHazardRight_phModel_strataLaw_zero] at h
    rw [← h]
    norm_num
  have := (popHazardRight_ratio_hazardCurves_const_mul_zero he₀
    (he₀.const_mul one_le_two) hpos).2
  rw [← phModel_hazard_true_eq_two_mul, ← phCurve_phModel_eq_hazardCurves,
    ← phCurve_phModel_eq_hazardCurves] at this
  exact this

/-- The model `nonPHHazard` is regular at the time `0` under `halfLaw`: the hazards are
continuous and at most `2` on `[0, 1)`. -/
theorem isEnvelopedHazardAtZero_nonPH : IsEnvelopedHazardAtZero halfLaw nonPHHazard := by
  refine IsEnvelopedHazardAtZero.of_hazard_le (g := fun _ => 2)
    (measurable_from_prod_countable_right fun b => (continuous_nonPHHazard b).measurable)
    (Eventually.of_forall fun b u hu => ?_)
    (Eventually.of_forall fun b u _ => (continuous_nonPHHazard b).intervalIntegrable _ _)
    one_pos (integrable_const _)
    (Eventually.of_forall fun b => ⟨(continuous_nonPHHazard b).continuousWithinAt,
      fun u hu => ?_⟩)
  · cases b
    · simp [nonPHHazard]
    · simp only [nonPHHazard, ite_true]
      linarith
  · cases b
    · simp only [nonPHHazard, Bool.false_eq_true, ite_false]
      norm_num
    · simp only [nonPHHazard, ite_true]
      linarith [hu.2]

/-- **The model that is not proportional hazards at the time `0`.** With the conditional hazards
`2 u` and `1` of two equally likely strata, the right sided population hazard at `0` is the
average `(0 + 1) / 2 = 1/2` of the conditional hazards at `0`; at the time `1` it is the
population hazard `3/2` (`popHazard_nonPH_one`). -/
theorem popHazardRight_nonPH :
    popHazardRight halfLaw (hazardCurves nonPHHazard) 0 = 1 / 2 ∧
      popHazardRight halfLaw (hazardCurves nonPHHazard) 1 = 3 / 2 := by
  refine ⟨?_, ?_⟩
  · rw [(popHazardRight_hazardCurves_zero isEnvelopedHazardAtZero_nonPH).2, integral_halfLaw]
    norm_num [nonPHHazard]
  · rw [popHazardRight_hazardCurves (isEnvelopedHazardAt_nonPH one_pos), popHazard_nonPH_one]

end Instances

end ContinuousTime

end Survival

end CausalInference
