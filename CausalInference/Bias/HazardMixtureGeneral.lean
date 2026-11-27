/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Bias.HazardMixture
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Hazards of general mixtures of exponential laws

**Time scale: continuous.** A population whose individual hazards are constant rates `r`
distributed according to a probability law `ν` on `ℝ` with `ν`-almost every rate nonnegative.
`CausalInference.Bias.HazardMixture` treats finite mixtures; this file treats an arbitrary law.

## Main definitions

* `genSurvival ν t = ∫ exp (-(r t)) dν(r)`: the population survival.
* `survivorLaw ν t`: the law of the rate among the survivors at `t`, with density
  `exp (-(r t)) / S(t)` with respect to `ν` (`survivorLaw_eq_withDensity`). It is Mathlib's
  exponentially tilted measure `ν.tilted (t * negRate ·)` with `negRate r = -r`.
* `genHazard ν t = ∫ r d(survivorLaw ν t)(r)`: the mean rate among the survivors.
* `genCumHazard ν t = -log S(t)`.

## Main results

* `genSurvival_pos`, `isProbabilityMeasure_survivorLaw` (for `t ≥ 0`), `genHazard_eq_div`
  (`h(t) = ∫ r exp (-(r t)) dν / S(t)`), `hasDerivAt_genSurvival` (for `t > 0`,
  `S'(t) = -∫ r exp (-(r t)) dν`), hence `genHazard_eq_neg_deriv_div` (`h = -S' / S`) and
  `hasDerivAt_genCumHazard` (`H' = h`). For `t > 0` the integrand `r exp (-(r t))` is bounded on
  the nonnegative rates, so no moment assumption is needed; the differentiation under the
  integral is Mathlib's theory of the moment generating function of `-r`. At `t = 0` a finite
  first moment gives the right derivative `S'(0+) = -∫ r dν`
  (`hasDerivWithinAt_genSurvival_zero`).
* `hasDerivAt_genHazard`: `h'(t) = -Var(r)` under the survivor law at `t`, for `t > 0`.
* `genHazard_antitoneOn`, `genHazard_strictAntiOn`: the hazard is nonincreasing on `(0, ∞)`,
  and strictly decreasing unless the rate is `ν`-almost surely constant.
  `genHazard_const_iff`: the hazard is constant on `(0, ∞)` if and only if the rate is
  `ν`-almost surely constant, that is (`ae_eq_const_iff_eq_dirac`) `ν` is a point mass.
* `genSurvival_finMix`, `genHazard_finMix`, `variance_survivorLaw_finMix`: for a finite weighted
  sum of point masses `finMix p r` the survival, the hazard and the variance among survivors
  are `mixSurvival`, `mixHazard` and the variance of `hasDerivAt_mixHazard_eq_neg_var`.
* `genCumHazard_attenuation`: multiplying every rate by `ψ > 1` gives, at every `t > 0`,
  `0 < H₀(t) < H₁(t) < ψ H₀(t)` when the rate is not almost surely constant; `H₁(t) = H₀(ψ t)`
  is `genSurvival_map_mul`.

## Source

NICE DSU Technical Support Document 2, S. Dias, N. J. Welton, A. J. Sutton, A. E. Ades (2011,
last updated 2016), Section 3.1: in populations with constant but heterogeneous rates the
average hazard decreases over time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace CausalInference

namespace Bias

namespace HazardMixtureGeneral

open HazardMixture EffectMeasure

variable {ν : Measure ℝ} {t : ℝ}

/-- Minus the rate, `negRate r = -r`: the random variable whose moment generating function is
the survival function. -/
def negRate (r : ℝ) : ℝ := -r

/-- The survival function of the mixture with rate law `ν`: `S(t) = ∫ exp (-(r t)) dν(r)`. -/
noncomputable def genSurvival (ν : Measure ℝ) (t : ℝ) : ℝ := ∫ r, Real.exp (-(r * t)) ∂ν

/-- The law of the rate among the survivors at time `t`: the measure with density
`exp (-(r t)) / S(t)` with respect to `ν`, written as Mathlib's tilted measure. -/
noncomputable def survivorLaw (ν : Measure ℝ) (t : ℝ) : Measure ℝ := ν.tilted (t * negRate ·)

/-- The population hazard: the mean rate among the survivors at time `t`. -/
noncomputable def genHazard (ν : Measure ℝ) (t : ℝ) : ℝ := ∫ r, r ∂(survivorLaw ν t)

/-- The population cumulative hazard `H(t) = -log S(t)`. -/
noncomputable def genCumHazard (ν : Measure ℝ) (t : ℝ) : ℝ := -Real.log (genSurvival ν t)

theorem exp_mul_negRate (t r : ℝ) : Real.exp (t * negRate r) = Real.exp (-(r * t)) := by
  rw [negRate]; ring_nf

/-- The survival function is the moment generating function of `-r`. -/
theorem genSurvival_eq_mgf (ν : Measure ℝ) (t : ℝ) : genSurvival ν t = mgf negRate ν t := by
  simp only [genSurvival, mgf, exp_mul_negRate]

/-- The survivor law has density `exp (-(r t)) / S(t)` with respect to `ν`. -/
theorem survivorLaw_eq_withDensity (ν : Measure ℝ) (t : ℝ) :
    survivorLaw ν t =
      ν.withDensity fun r => ENNReal.ofReal (Real.exp (-(r * t)) / genSurvival ν t) := by
  simp only [survivorLaw, Measure.tilted, exp_mul_negRate, genSurvival]

/-- For `t ≥ 0` and nonnegative rates the integrand `exp (-(r t))` lies in `(0, 1]`, so it is
integrable for a finite `ν`. -/
theorem integrable_exp_neg [IsFiniteMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 ≤ t) :
    Integrable (fun r => Real.exp (-(r * t))) ν := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hν] with r hr
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have := mul_nonneg hr ht
  linarith

/-- Every `t > 0` is in the interior of the set where the moment generating function of `-r` is
finite. -/
theorem mem_interior_integrableExpSet [IsFiniteMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 < t) :
    t ∈ interior (integrableExpSet negRate ν) := by
  have hsub : Ioi (0 : ℝ) ⊆ integrableExpSet negRate ν := fun s (hs : 0 < s) => by
    simp only [integrableExpSet, mem_ofPred_eq, exp_mul_negRate]
    exact integrable_exp_neg hν hs.le
  exact interior_mono hsub (by rw [interior_Ioi]; exact ht)

/-- The survival is positive for `t ≥ 0`. -/
theorem genSurvival_pos [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 ≤ t) :
    0 < genSurvival ν t :=
  integral_exp_pos (integrable_exp_neg hν ht)

/-- Everybody is alive at time `0`: `S(0) = 1`. -/
theorem genSurvival_zero [IsProbabilityMeasure ν] : genSurvival ν 0 = 1 := by
  simp [genSurvival]

/-- For `t ≥ 0` the survivor law is a probability measure. -/
theorem isProbabilityMeasure_survivorLaw [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r)
    (ht : 0 ≤ t) : IsProbabilityMeasure (survivorLaw ν t) :=
  isProbabilityMeasure_tilted (by simpa only [exp_mul_negRate] using integrable_exp_neg hν ht)

/-- The hazard is the density over the survival: `h(t) = ∫ r exp (-(r t)) dν / S(t)`. -/
theorem genHazard_eq_div (ν : Measure ℝ) (t : ℝ) :
    genHazard ν t = (∫ r, r * Real.exp (-(r * t)) ∂ν) / genSurvival ν t := by
  rw [genHazard, survivorLaw, integral_tilted]
  simp_rw [exp_mul_negRate, smul_eq_mul]
  rw [← integral_div]
  congr 1
  funext r
  rw [genSurvival]
  ring

/-- For `t > 0` the survival is differentiable with `S'(t) = -∫ r exp (-(r t)) dν`. -/
theorem hasDerivAt_genSurvival [IsFiniteMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 < t) :
    HasDerivAt (genSurvival ν) (-∫ r, r * Real.exp (-(r * t)) ∂ν) t := by
  have h := hasDerivAt_mgf (mem_interior_integrableExpSet hν ht)
  rw [show genSurvival ν = mgf negRate ν from funext (genSurvival_eq_mgf ν)]
  convert h using 1
  rw [← integral_neg]
  congr 1
  funext r
  simp only [exp_mul_negRate]
  rw [negRate]
  ring

/-- **The hazard is `-S'/S`** for `t > 0`. -/
theorem genHazard_eq_neg_deriv_div [IsFiniteMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 < t) :
    genHazard ν t = -deriv (genSurvival ν) t / genSurvival ν t := by
  rw [(hasDerivAt_genSurvival hν ht).deriv, neg_neg, genHazard_eq_div]

/-- The hazard is minus the derivative of the cumulant generating function of `-r`. -/
theorem genHazard_eq_neg_deriv_cgf [IsFiniteMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 < t) :
    genHazard ν t = -deriv (cgf negRate ν) t := by
  rw [← integral_tilted_mul_self (mem_interior_integrableExpSet hν ht), genHazard, survivorLaw,
    ← integral_neg]
  simp [negRate]

/-- The cumulative hazard is an antiderivative of the hazard on `(0, ∞)`: `H' = h`. -/
theorem hasDerivAt_genCumHazard [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 < t) :
    HasDerivAt (genCumHazard ν) (genHazard ν t) t := by
  have hint := mem_interior_integrableExpSet hν ht
  rw [genHazard_eq_neg_deriv_cgf hν ht,
    show genCumHazard ν = fun s => -cgf negRate ν s from
      funext fun s => by rw [genCumHazard, genSurvival_eq_mgf, cgf]]
  exact (analyticAt_cgf hint).differentiableAt.hasDerivAt.neg

/-- `r ↦ r` is `-negRate`. -/
theorem id_eq_neg_negRate : (fun r : ℝ => r) = -negRate := by
  funext r; simp [negRate]

/-- **The derivative of the hazard is minus the variance of the rate among survivors**: for
`t > 0`, `h'(t) = -Var(r)` under `survivorLaw ν t`. Equivalently, the second derivative of
`log S` is that variance. -/
theorem hasDerivAt_genHazard [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 < t) :
    HasDerivAt (genHazard ν) (-Var[fun r => r; survivorLaw ν t]) t := by
  have hint := mem_interior_integrableExpSet hν ht
  have hd : HasDerivAt (deriv (cgf negRate ν)) (iteratedDeriv 2 (cgf negRate ν) t) t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (analyticAt_cgf hint).deriv.differentiableAt.hasDerivAt
  rw [id_eq_neg_negRate, variance_neg, survivorLaw, variance_tilted_mul hint]
  refine hd.neg.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with s hs
  exact genHazard_eq_neg_deriv_cgf hν hs

/-- The hazard is nonnegative at every time: it is a mean of nonnegative rates. -/
theorem genHazard_nonneg (hν : ∀ᵐ r ∂ν, 0 ≤ r) :
    0 ≤ genHazard ν t :=
  integral_nonneg_of_ae ((tilted_absolutelyContinuous ν _).ae_le hν)

/-- **The hazard is nonincreasing on `(0, ∞)`** (NICE DSU TSD 2, Section 3.1). -/
theorem genHazard_antitoneOn [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) :
    AntitoneOn (genHazard ν) (Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun s hs => (hasDerivAt_genHazard hν hs).continuousAt.continuousWithinAt)
    (fun s hs => ?_) (fun s hs => ?_)
  · rw [interior_Ioi] at hs
    exact (hasDerivAt_genHazard hν hs).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi] at hs
    rw [(hasDerivAt_genHazard hν hs).deriv, neg_nonpos]
    exact variance_nonneg _ _

/-- Unless the rate is `ν`-almost surely constant, its variance among the survivors is positive
at every `t > 0`. -/
theorem variance_survivorLaw_pos [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) (ht : 0 < t)
    (hnc : ¬ ∃ c, ∀ᵐ r ∂ν, r = c) : 0 < Var[fun r => r; survivorLaw ν t] := by
  rcases (variance_nonneg (fun r : ℝ => r) (survivorLaw ν t)).eq_or_lt with h | h
  · exfalso
    apply hnc
    have := isProbabilityMeasure_survivorLaw hν ht.le
    have hm : MemLp (fun r : ℝ => r) 2 (survivorLaw ν t) := by
      have := memLp_tilted_mul (mem_interior_integrableExpSet hν ht) 2
      rw [id_eq_neg_negRate]
      exact_mod_cast this.neg
    have hi : Integrable (fun r => Real.exp (t * negRate r)) ν := by
      simpa only [exp_mul_negRate] using integrable_exp_neg hν ht.le
    exact ⟨_, (absolutelyContinuous_tilted hi).ae_le
      (ae_eq_integral_of_variance_eq_zero hm h.symm)⟩
  · exact h

/-- **The hazard is strictly decreasing on `(0, ∞)`** unless the rate is `ν`-almost surely
constant. -/
theorem genHazard_strictAntiOn [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r)
    (hnc : ¬ ∃ c, ∀ᵐ r ∂ν, r = c) : StrictAntiOn (genHazard ν) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun s hs => (hasDerivAt_genHazard hν hs).continuousAt.continuousWithinAt) fun s hs => ?_
  rw [interior_Ioi] at hs
  rw [(hasDerivAt_genHazard hν hs).deriv, neg_lt_zero]
  exact variance_survivorLaw_pos hν hs hnc

/-- An almost surely constant rate `c` gives the constant hazard `c` at every `t ≥ 0`. -/
theorem genHazard_eq_of_ae_eq [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) {c : ℝ}
    (hc : ∀ᵐ r ∂ν, r = c) (ht : 0 ≤ t) : genHazard ν t = c := by
  have := isProbabilityMeasure_survivorLaw hν ht
  have h : (fun r : ℝ => r) =ᵐ[survivorLaw ν t] fun _ => c :=
    (tilted_absolutelyContinuous ν _).ae_le hc
  rw [genHazard, integral_congr_ae h, integral_const]
  simp

/-- **The dichotomy**: the hazard is constant on `(0, ∞)` if and only if the rate is
`ν`-almost surely constant. -/
theorem genHazard_const_iff [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) :
    (∃ c, ∀ t, 0 < t → genHazard ν t = c) ↔ ∃ c, ∀ᵐ r ∂ν, r = c := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra hnc
    have := genHazard_strictAntiOn hν hnc (show (1 : ℝ) ∈ Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num)
    rw [hc 1 one_pos, hc 2 two_pos] at this
    exact lt_irrefl _ this
  · rintro ⟨c, hc⟩
    exact ⟨c, fun t ht => genHazard_eq_of_ae_eq hν hc ht.le⟩

/-- For a probability measure on `ℝ`, an almost surely constant rate means a point mass. -/
theorem ae_eq_const_iff_eq_dirac [IsProbabilityMeasure ν] (c : ℝ) :
    (∀ᵐ r ∂ν, r = c) ↔ ν = Measure.dirac c := by
  constructor
  · intro h
    ext s hs
    rw [Measure.dirac_apply' _ hs]
    by_cases hc : c ∈ s
    · rw [Set.indicator_of_mem hc, Pi.one_apply, ← prob_compl_eq_zero_iff hs]
      exact measure_mono_null (t := {r | ¬ r = c})
        (fun r (hr : r ∈ sᶜ) (hrc : r = c) => hr (hrc ▸ hc)) (ae_iff.1 h)
    · rw [Set.indicator_of_notMem hc]
      exact measure_mono_null (t := {r | ¬ r = c})
        (fun r (hr : r ∈ s) (hrc : r = c) => hc (hrc ▸ hr)) (ae_iff.1 h)
  · rintro rfl
    simp

/-- **The right derivative of the survival at `0`** under a finite first moment of the rate:
`S'(0+) = -∫ r dν`, so the hazard at the origin is the mean rate. The quotient
`(exp (-(r s)) - 1) / s` is dominated by `r` for `s > 0` and nonnegative `r`. -/
theorem hasDerivWithinAt_genSurvival_zero [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r)
    (h1 : Integrable (fun r => r) ν) :
    HasDerivWithinAt (genSurvival ν) (-∫ r, r ∂ν) (Ici 0) 0 := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici,
    hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))]
  set F : ℝ → ℝ → ℝ := fun s r => s⁻¹ • (Real.exp (-(r * (0 + s))) - Real.exp (-(r * 0)))
    with hF
  have hlim : Tendsto (fun s => ∫ r, F s r ∂ν) (𝓝[>] 0) (𝓝 (∫ r, -r ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := fun r => r) ?_ ?_ h1 ?_
    · exact Eventually.of_forall fun s => Continuous.aestronglyMeasurable (by fun_prop)
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      filter_upwards [hν] with r hr
      simp only [hF, zero_add, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul]
      have hx := Real.add_one_le_exp (-(r * s))
      have hle : Real.exp (-(r * s)) ≤ 1 := Real.exp_le_one_iff.2 (by
        have := mul_nonneg hr hs.le; linarith)
      rw [Real.norm_eq_abs, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hs.le)
        (by linarith)), ← mul_neg, inv_mul_le_iff₀ hs]
      linarith
    · refine ae_of_all _ fun r => ?_
      have hd : HasDerivAt (fun s => Real.exp (-(r * s))) (-r) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).const_mul r).neg.exp
        convert this using 1
        · rfl
        · change -r = Real.exp (-(r * 0)) * -(r * 1)
          simp
      exact hd.tendsto_slope_zero_right
  rw [integral_neg] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hi : Integrable (fun r => Real.exp (-(r * s))) ν := integrable_exp_neg hν hs.le
  simp only [hF, slope, genSurvival, zero_add, mul_zero, neg_zero, Real.exp_zero, sub_zero,
    vsub_eq_sub, smul_eq_mul]
  rw [integral_const_mul, integral_sub hi (integrable_const 1), integral_const]

/-! ### Finite mixtures -/

section Finite

variable {ι : Type*} [Fintype ι]

/-- The finite mixture `∑ i, p i δ_{r i}` of point masses at the rates `r i`. -/
noncomputable def finMix (p r : ι → ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac (r i)

/-- Integrals against `finMix p r` are weighted sums. -/
theorem integral_finMix {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (r : ι → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(finMix p r) = ∑ i, p i * f (r i) := by
  rw [finMix, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Weights forming a distribution give a probability measure. -/
theorem isProbabilityMeasure_finMix {p : ι → ℝ} (hp : IsWeights p) (r : ι → ℝ) :
    IsProbabilityMeasure (finMix p r) := by
  constructor
  simp only [finMix, sum_apply, smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp.1 i), hp.2, ENNReal.ofReal_one]

/-- Rates nonnegative on the strata of positive weight give almost surely nonnegative rates. -/
theorem ae_nonneg_finMix {p r : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < p i → 0 ≤ r i) :
    ∀ᵐ x ∂(finMix p r), 0 ≤ x := by
  rw [ae_iff]
  simp only [finMix, sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases (hp i).eq_or_lt with h | h
  · rw [← h, ENNReal.ofReal_zero, zero_mul]
  · simp [Measure.dirac_apply, Set.indicator, hr i h]

/-- The general survival of a finite mixture is `mixSurvival`. -/
theorem genSurvival_finMix {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (r : ι → ℝ) (t : ℝ) :
    genSurvival (finMix p r) t = mixSurvival p r t := by
  rw [genSurvival, integral_finMix hp]
  rfl

/-- The general hazard of a finite mixture is `mixHazard`. -/
theorem genHazard_finMix {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (r : ι → ℝ) (t : ℝ) :
    genHazard (finMix p r) t = mixHazard p r t := by
  rw [genHazard_eq_div, integral_finMix hp, genSurvival_finMix hp, mixHazard, mixDensity]
  simp only [mul_assoc]

/-- The variance among survivors of a finite mixture is the variance of
`hasDerivAt_mixHazard_eq_neg_var`, under the survivor weights `survivorWeight p r t`. -/
theorem variance_survivorLaw_finMix {p r : ι → ℝ} (hp : IsWeights p)
    (hr : ∀ i, 0 < p i → 0 ≤ r i) (ht : 0 < t) :
    Var[fun x => x; survivorLaw (finMix p r) t] =
      ∑ i, survivorWeight p r t i * r i ^ 2 - (∑ i, survivorWeight p r t i * r i) ^ 2 := by
  have := isProbabilityMeasure_finMix hp r
  have h1 := hasDerivAt_genHazard (ae_nonneg_finMix hp.1 hr) ht
  rw [show genHazard (finMix p r) = mixHazard p r from funext (genHazard_finMix hp.1 r)] at h1
  have := h1.unique (hasDerivAt_mixHazard_eq_neg_var hp r t)
  linarith

end Finite

/-! ### A proportional effect on every rate -/

/-- Multiplying every rate by `ψ` (the law of `ψ r`) rescales time: `S₁(t) = S₀(ψ t)`. -/
theorem genSurvival_map_mul (ν : Measure ℝ) (ψ t : ℝ) :
    genSurvival (ν.map (fun r => ψ * r)) t = genSurvival ν (ψ * t) := by
  rw [genSurvival, integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [genSurvival]
  congr 1
  funext r
  ring_nf

/-- The cumulative hazard of the treated arm: `H₁(t) = H₀(ψ t)`. -/
theorem genCumHazard_map_mul (ν : Measure ℝ) (ψ t : ℝ) :
    genCumHazard (ν.map (fun r => ψ * r)) t = genCumHazard ν (ψ * t) := by
  rw [genCumHazard, genCumHazard, genSurvival_map_mul]

/-- The survival is continuous on `[0, ∞)` (dominated by `1`). -/
theorem continuousOn_genSurvival [IsFiniteMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r) :
    ContinuousOn (genSurvival ν) (Ici 0) := by
  change ContinuousOn (fun s => ∫ r, Real.exp (-(r * s)) ∂ν) (Ici 0)
  refine continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
    (fun s _ => Continuous.aestronglyMeasurable (by fun_prop)) (fun s hs => ?_)
    (integrable_const 1)
    (ae_of_all _ fun r => (by fun_prop : Continuous fun s => Real.exp (-(r * s))).continuousOn)
  filter_upwards [hν] with r hr
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have := mul_nonneg hr (show (0 : ℝ) ≤ s from hs)
  linarith

/-- **Attenuation of the cumulative hazard ratio for a general rate law** (NICE DSU TSD 3,
Section 1.1.5, aggregation bias). Every rate is multiplied by `ψ > 1` under treatment (the
treated rate law is the image of `ν` under `r ↦ ψ r`), so the conditional hazard ratio is `ψ`
at every time. If the rate is not `ν`-almost surely constant (in particular not almost surely
zero), then at every `t > 0`, `0 < H₀(t) < H₁(t) < ψ H₀(t)`: the marginal cumulative hazard
ratio lies strictly between `1` and `ψ`. This is the general form of
`HazardMixture.mixCumHazard_attenuation_of_nonneg`. -/
theorem genCumHazard_attenuation [IsProbabilityMeasure ν] (hν : ∀ᵐ r ∂ν, 0 ≤ r)
    (hnc : ¬ ∃ c, ∀ᵐ r ∂ν, r = c) {ψ : ℝ} (hψ : 1 < ψ) (ht : 0 < t) :
    0 < genCumHazard ν t ∧ genCumHazard ν t < genCumHazard (ν.map (fun r => ψ * r)) t ∧
      genCumHazard (ν.map (fun r => ψ * r)) t < ψ * genCumHazard ν t := by
  rw [genCumHazard_map_mul]
  have hHc : ContinuousOn (genCumHazard ν) (Ici 0) :=
    ((continuousOn_genSurvival hν).log fun s hs => (genSurvival_pos hν hs).ne').neg
  have hanti := genHazard_strictAntiOn hν hnc
  have hpos : ∀ s, 0 < s → 0 < genHazard ν s := fun s hs =>
    lt_of_le_of_lt (genHazard_nonneg hν)
      (hanti (show s ∈ Ioi 0 from hs) (show 2 * s ∈ Ioi 0 from mem_Ioi.2 (by linarith))
        (by linarith))
  have hmono : StrictMonoOn (genCumHazard ν) (Ici 0) :=
    strictMonoOn_of_deriv_pos (convex_Ici 0) hHc fun s hs => by
      rw [interior_Ici] at hs
      rw [(hasDerivAt_genCumHazard hν hs).deriv]
      exact hpos s hs
  have h0 : genCumHazard ν 0 = 0 := by
    rw [genCumHazard, genSurvival_zero, Real.log_one, neg_zero]
  have hψt : t < ψ * t := by nlinarith
  refine ⟨?_, hmono (mem_Ici.2 ht.le) (mem_Ici.2 (by nlinarith)) hψt, ?_⟩
  · have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht
    rwa [h0] at this
  -- `g s = ψ H₀(s) - H₀(ψ s)` vanishes at `0` and increases on `(0, t)`.
  set g : ℝ → ℝ := fun s => ψ * genCumHazard ν s - genCumHazard ν (ψ * s) with hg
  have hg' : ∀ s, 0 < s → HasDerivAt g (ψ * genHazard ν s - ψ * genHazard ν (ψ * s)) s := by
    intro s hs
    have h2 := (hasDerivAt_genCumHazard hν (show 0 < ψ * s by nlinarith)).comp s
      ((hasDerivAt_id s).const_mul ψ)
    convert ((hasDerivAt_genCumHazard hν hs).const_mul ψ).sub h2 using 1
    · rfl
    · simp only [mul_one]; ring
  have hgc : ContinuousOn g (Icc 0 t) := by
    refine (continuousOn_const.mul (hHc.mono Icc_subset_Ici_self)).sub ?_
    refine hHc.comp (continuousOn_const.mul continuousOn_id) fun s hs => ?_
    exact mem_Ici.2 (by have := hs.1; nlinarith)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g _ ht hgc fun s hs => hg' s hs.1
  have hc0 : 0 < c := hc.1
  have hpos' : 0 < ψ * genHazard ν c - ψ * genHazard ν (ψ * c) := by
    have : genHazard ν (ψ * c) < genHazard ν c :=
      hanti (show c ∈ Ioi 0 from hc0) (show ψ * c ∈ Ioi 0 from mem_Ioi.2 (by nlinarith))
        (by nlinarith)
    nlinarith
  have hg0 : g 0 = 0 := by simp only [hg, mul_zero, h0, sub_zero]
  rw [hg0, sub_zero, sub_zero, eq_div_iff ht.ne'] at hslope
  have : 0 < g t := by rw [← hslope]; positivity
  simp only [hg] at this
  linarith

end HazardMixtureGeneral

end Bias

end CausalInference
