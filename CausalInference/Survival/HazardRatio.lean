/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Comparison
public import CausalInference.Bias.HazardRatio
public import CausalInference.Measures.Collapsibility
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Proportional hazards, non-collapsibility of the hazard ratio, and duration of effect

**Time scale: discrete.** As in the rest of `CausalInference.Survival`, event times are
`T : Ω → ℕ`, the survival is `S k = P(T > k)` and the hazard is `h k = P(T = k | T ≥ k)`
(`CausalInference.Survival.Basic`); the comparison of two arms uses `hazardRatio`
(`CausalInference.Survival.Comparison`). The non-collapsibility results use the two-period
binary-frailty model of `CausalInference.Bias.HazardRatio`. The continuous-time results on
mixtures of exponential laws are in `CausalInference.Bias.HazardMixture`.

## Main results

* Proportional hazards. `survival_eq_rpow_iff`: when `S₀ k > 0`, `S₁ m = S₀ m ^ c` for all
  `m ≤ k` if and only if `1 - h₁ m = (1 - h₀ m) ^ c` for all `m ≤ k`: in discrete time the
  power relation between the survival curves is proportionality of the interval cumulative
  hazards `-log (1 - h)`, not a constant ratio of the hazards `h`.
  `one_sub_eq_rpow_iff_cloglog` restates it on the complementary log-log scale where
  `0 < h < 1`. `PropHazardsExample.constant_hazardRatio_no_power`: two laws on `{1, 2, 3}`
  with hazard ratio `1/2` at times `1` and `2` (every time `m ≤ 2` with positive reference
  hazard), and no exponent `c` with `S₁ m = S₀ m ^ c` for `m ≤ 2`; at time `3` both hazards are
  `1`, since the laws put all remaining mass there.
  `PropHazardsExample.logLogistic_fullGrid`: the log-logistic laws `S₀(k) = 1 / (1 + k)` and
  `S₁(k) = 1 / (1 + 2 k)` on the full grid `k : ℕ` (`llTime_survival`) have hazard ratio
  `2 (k + 1) / (1 + 2 k)` at every `k ≥ 1`, which is `4/3` at time `1`, `6/5` at time `2` and
  tends to `1`, and have no exponent `c`: an accelerated failure time family without
  proportional hazards. `llTime_hazardRatio`, `tendsto_llTime_hazardRatio` and
  `llTime_hazardRatio_ne` give the closed form `φ (k + 1) / (1 + φ k)`, its limit `1` and its
  nonconstancy for every acceleration factor `φ > 0`, `φ ≠ 1`.
  `PropHazardsExample.logLogistic_hazardRatio_varies` is the version with three-point laws
  that agree with these through time `2`.
* Duration of treatment effect. `survival_mul_eq_of_hazard_eq`: if the hazards agree after
  `t₀`, then `S₁ k * S₀ t₀ = S₀ k * S₁ t₀` for `k ≥ t₀` (the survival ratio is frozen at its
  value at `t₀`; ratio form `survival_div_eq_of_hazard_eq`). `sum_survival_sub_of_hazard_eq`:
  the area between the curves over `t₀, …, K` is `(S₁ t₀ / S₀ t₀ - 1) ∑ S₀`;
  `hasSum_survival_sub_of_hazard_eq` is the unbounded horizon version under summable reference
  survival (the lifetime mean gain accrued from `t₀` on).
  `survival_mul_le_of_hazard_le` and `survival_le_of_maintained`: a maintained effect (hazard
  at most the reference after `t₀`) gives at least the survival of a stopped one;
  `tsum_survival_lt_of_maintained`: strictly larger lifetime survival when the maintained
  hazard is strictly lower in some period reached with positive probability.
  `PropHazardsExample.duration_not_identified`: two treated laws that agree up to `t₀ = 1` and
  differ afterwards, so follow-up to `t₀` does not determine the duration of the effect.
* Non-collapsibility. With a common stratum hazard ratio `ψ` at both periods and a frailty
  independent of treatment (`phRisk`): `hazard1_phRisk` (`h₁(1) = ψ h₀(1)`),
  `stratumHazard2_phRisk` (`h₁(2 | u) = ψ h₀(2 | u)` in each stratum), and
  `hazard2_phRisk_eq_iff` (`h₁(2) = ψ h₀(2)` if and only if `ψ = 1`, or the frailty leaves the
  period `1` risk unchanged, or it leaves the period `2` risk unchanged). These are
  multiplicative identities, true also at a zero reference hazard; the hazard ratio forms with
  positive reference hazards are `hazard1_phRisk_ratio`, `stratumHazard2_phRisk_ratio` and
  `hazard2_phRisk_ratio_eq_iff`. `hazard2_phRisk_isCollapsible_iff`: the same condition
  characterizes `EffectMeasure.IsCollapsible` for the period `2` hazard ratio.
  `frailtyHazard2_eq_iff`: with a finite frailty, the period `2` identity holds if and only if
  `ψ = 1` or the two period risks have zero covariance under the frailty law
  (`frailtyCov_bool` recovers the binary exceptions, `PropHazardsExample.zeroCov_example`
  shows they do not extend to three levels).
  `PropHazardsExample.noncollapsible_example`: stratum hazard ratio `1/2` at both periods,
  marginal hazard ratio `1/2` at period `1` and `329/578` at period `2`.
  `PropHazardsExample.groupedPH_noncollapsible`: on the survival-power scale, a common
  conditional power `2` in each frailty stratum, with marginal period `1` survivals `5/16` and
  `1/2`, and `5/16 ≠ (1/2) ^ 2`.
* Scale-dependent effect modification. `cumHazard` (`H = -log S`), `cumHazard_succ_sub`
  (its increment is `-log (1 - h)`), and `cloglogRatio_eq_iff`: in a model additive in two
  binary covariates on the log cumulative hazard scale with time-varying coefficients (stated
  as a multiplicative model for the cumulative hazard; `log_multiplicative_cumHazard` gives the
  log-linear reading under positive multipliers), the
  grouped-time hazard ratio for one covariate over an interval does not depend on the other
  if and only if one of the two coefficients is constant over that interval
  (`incrementRatio_eq_iff` is the algebra). `PropHazardsExample.scaleDependence_example`: four
  laws satisfying the model with both coefficients changing, for which the ratio depends on the
  other covariate.

The notion of hazard ratio differs between the sections. The power relation section shows
that in discrete time proportional hazards in the sense of `S₁ = S₀ ^ c` is not a constant
ratio of the hazards `h`. The non-collapsibility section uses the ratio of the discrete
hazards themselves (`hazardRatio`, `hazard1`, `hazard2`): a common stratum ratio `ψ` of the
period risks. Its period `1` collapsibility holds because the period `1` hazard is a risk; for
a common power `c` on the survival scale even period `1` is not collapsible
(`PropHazardsExample.groupedPH_noncollapsible`).

## Sources

* NICE DSU Technical Support Document 14, N. Latimer, *Survival analysis for economic
  evaluations alongside clinical trials: extrapolation with patient-level data* (2011, updated
  2013), Section 2.9 (a single hazard ratio requires proportional hazards; the duration of
  treatment effect assumption should be justified) and Section 4.1.3 (without a stated
  duration of effect the trial hazard ratio is implicitly assumed to last for the whole model
  horizon).
* NICE DSU Technical Support Document 19, B. Woods, E. Sideris, S. Palmer, N. Latimer,
  M. Soares (2017), on partitioned survival analysis, Section 3.2.5 (equal hazards between
  arms from a time point on).
* NICE DSU Technical Support Document 21, M. J. Rutherford, P. C. Lambert, M. J. Sweeting,
  B. Pennington, M. J. Crowther, K. R. Abrams, N. R. Latimer, *Flexible methods for survival
  analysis* (2020), Section 3.2.3 (with multiple time-dependent effects the hazard ratio for one
  covariate depends on another without an interaction) and Section 5.2.1 (data simulated with
  disease-specific survival `S_d(t) = S_d0(t) ^ exp(Z β)` conditional on a frailty `Z`, the
  display immediately above Equation 17; Equation 17 itself gives the baseline Weibull
  mixture `S_d0`).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Fine Point 4.3
  (collapsibility) and Technical Point 8.1 (the selection bias built into hazard ratios).
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace Survival

variable {Ω₀ Ω₁ : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
  {μ₀ : Measure Ω₀} {μ₁ : Measure Ω₁} [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
  {T₀ : Ω₀ → ℕ} {T₁ : Ω₁ → ℕ}

namespace PropHazards

section Recursion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → ℕ}

/-- The one-step recursion `S (k + 1) = S k * (1 - h (k + 1))`, valid at every time. -/
theorem survival_succ (hT : Measurable T) (k : ℕ) :
    survival μ T (k + 1) = survival μ T k * (1 - hazard μ T (k + 1)) := by
  rw [survival_eq_atRisk_mul hT (k + 1), atRisk_succ]

/-- At time `0`: `S 0 = 1 - h 0`. -/
theorem survival_zero_eq (hT : Measurable T) : survival μ T 0 = 1 - hazard μ T 0 := by
  rw [survival_eq_atRisk_mul hT 0, atRisk_zero, one_mul]

/-- One minus a hazard is nonnegative. -/
theorem one_sub_hazard_nonneg (k : ℕ) : 0 ≤ 1 - hazard μ T k :=
  sub_nonneg.2 (hazard_le_one k)

end Recursion

/-- **Proportional hazards in discrete time: the power relation** (NICE DSU TSD 14, Section 2.9).
For `c : ℝ` and a horizon `k` with `S₀ k > 0`, the survival curves satisfy `S₁ m = S₀ m ^ c` at
every `m ≤ k` if and only if one minus the hazards satisfy `1 - h₁ m = (1 - h₀ m) ^ c` at every
`m ≤ k`. The condition is on the interval survival probabilities `1 - h`, equivalently on the
interval cumulative hazards `-log (1 - h)`, which are proportional with factor `c`; it is not
a constant ratio `h₁ / h₀` of the hazards (`PropHazardsExample.constant_hazardRatio_no_power`).
Since `S₀ k > 0`, every `S₀ m`, `m ≤ k`, is positive, so no conventional hazard value enters. -/
theorem survival_eq_rpow_iff (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) (c : ℝ) (k : ℕ)
    (hS₀ : 0 < survival μ₀ T₀ k) :
    (∀ m ≤ k, 1 - hazard μ₁ T₁ m = (1 - hazard μ₀ T₀ m) ^ c) ↔
      ∀ m ≤ k, survival μ₁ T₁ m = survival μ₀ T₀ m ^ c := by
  have hpos : ∀ m ≤ k, 0 < survival μ₀ T₀ m := fun m hm =>
    lt_of_lt_of_le hS₀ (survival_antitone hm)
  constructor
  · intro h m hm
    induction m with
    | zero => rw [survival_zero_eq hT₀, survival_zero_eq hT₁, h 0 hm]
    | succ m ih =>
      rw [survival_succ hT₀, survival_succ hT₁, ih (by omega), h (m + 1) hm,
        Real.mul_rpow (survival_nonneg m) (one_sub_hazard_nonneg _)]
  · intro h m hm
    rcases m with _ | m
    · rw [← survival_zero_eq hT₀, ← survival_zero_eq hT₁, h 0 hm]
    · have e₁ := h (m + 1) hm
      have e₀ := h m (by omega)
      rw [survival_succ hT₀, survival_succ hT₁, e₀,
        Real.mul_rpow (survival_nonneg m) (one_sub_hazard_nonneg _)] at e₁
      exact mul_left_cancel₀ (Real.rpow_pos_of_pos (hpos m (by omega)) c).ne' e₁

/-- **The complementary log-log form** of the power relation at one time: for hazards strictly
between `0` and `1` and `c > 0`, `1 - y = (1 - x) ^ c` if and only if
`log (-log (1 - y)) = log c + log (-log (1 - x))`, that is, the grouped-time hazards differ by
the constant `log c` on the complementary log-log scale. At a zero hazard the left side reads
`log (-log 1) = log 0`, a conventional value, which is why `survival_eq_rpow_iff` is stated in
the power form. -/
theorem one_sub_eq_rpow_iff_cloglog {x y c : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y)
    (hy1 : y < 1) (hc : 0 < c) :
    1 - y = (1 - x) ^ c ↔
      Real.log (-Real.log (1 - y)) = Real.log c + Real.log (-Real.log (1 - x)) := by
  have hlx : 0 < -Real.log (1 - x) := neg_pos.2 (Real.log_neg (by linarith) (by linarith))
  have hly : 0 < -Real.log (1 - y) := neg_pos.2 (Real.log_neg (by linarith) (by linarith))
  rw [Real.rpow_def_of_pos (by linarith), ← Real.log_mul hc.ne' hlx.ne']
  constructor
  · intro h
    rw [h, Real.log_exp]
    ring_nf
  · intro h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.2 hly) (Set.mem_Ioi.2 (mul_pos hc hlx)) h
    rw [← Real.exp_log (show 0 < 1 - y by linarith)]
    congr 1
    linarith

end PropHazards

namespace PropHazardsExample

open ComparisonExample

/-- Arm `0` of the proportional hazards example: masses `1/2, 3/8, 1/8` at times `1, 2, 3`;
hazards `1/2` at time `1` and `3/4` at time `2`. -/
noncomputable def phArm₀ : Measure ℕ := threePoint (1 / 2) (3 / 8) (1 / 8)

/-- Arm `1` of the proportional hazards example: masses `1/4, 9/32, 15/32` at times `1, 2, 3`;
hazards `1/4` at time `1` and `3/8` at time `2`, half those of arm `0`. -/
noncomputable def phArm₁ : Measure ℕ := threePoint (1 / 4) (9 / 32) (15 / 32)

/-- The masses of `phArm₀`. -/
theorem phArm₀_real (s : Set ℕ) : phArm₀.real s =
    s.indicator (fun _ => 1 / 2) 1 + s.indicator (fun _ => 3 / 8) 2 +
      s.indicator (fun _ => 1 / 8) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

/-- The masses of `phArm₁`. -/
theorem phArm₁_real (s : Set ℕ) : phArm₁.real s =
    s.indicator (fun _ => 1 / 4) 1 + s.indicator (fun _ => 9 / 32) 2 +
      s.indicator (fun _ => 15 / 32) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

instance : IsProbabilityMeasure phArm₀ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure phArm₁ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Reference arm of the log-logistic example: the log-logistic survival `S(t) = 1 / (1 + t)`
(shape `1`) sampled on the grid, `S 1 = 1/2` and `S 2 = 1/3`; masses `1/2, 1/6, 1/3` at times
`1, 2, 3`. -/
noncomputable def llArm₀ : Measure ℕ := threePoint (1 / 2) (1 / 6) (1 / 3)

/-- Treated arm of the log-logistic example: `S(t) = 1 / (1 + 2 t)`, the reference law with
acceleration factor `2` (`S₁(t) = S₀(2 t)`), sampled on the grid, `S 1 = 1/3` and `S 2 = 1/5`;
masses `2/3, 2/15, 1/5` at times `1, 2, 3`. -/
noncomputable def llArm₁ : Measure ℕ := threePoint (2 / 3) (2 / 15) (1 / 5)

/-- The masses of `llArm₀`. -/
theorem llArm₀_real (s : Set ℕ) : llArm₀.real s =
    s.indicator (fun _ => 1 / 2) 1 + s.indicator (fun _ => 1 / 6) 2 +
      s.indicator (fun _ => 1 / 3) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

/-- The masses of `llArm₁`. -/
theorem llArm₁_real (s : Set ℕ) : llArm₁.real s =
    s.indicator (fun _ => 2 / 3) 1 + s.indicator (fun _ => 2 / 15) 2 +
      s.indicator (fun _ => 1 / 5) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

instance : IsProbabilityMeasure llArm₀ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure llArm₁ :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **An accelerated failure time family has no single hazard ratio** (NICE DSU TSD 14,
Section 2.9: log-logistic models "do not produce a single hazard ratio"). Two log-logistic
laws of shape `1` with acceleration factor `2`, sampled on the grid through time `2`: the
hazard ratio is `4/3` at time `1` and `6/5` at time `2`, and there is no exponent `c` with
`S₁ m = S₀ m ^ c` for `m ≤ 2`, so the proportional hazards relation of `survival_eq_rpow_iff`
fails. (From `(1/2) ^ c = 1/3` one gets `c > 3/2`, hence `(1/3) ^ c < 1/5`.) -/
theorem logLogistic_hazardRatio_varies :
    hazardRatio llArm₁ id llArm₀ id 1 = 4 / 3 ∧ hazardRatio llArm₁ id llArm₀ id 2 = 6 / 5 ∧
      ¬ ∃ c : ℝ, ∀ m ≤ 2, survival llArm₁ id m = survival llArm₀ id m ^ c := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hazardRatio, hazard, atRisk, llArm₀_real, llArm₁_real, id,
      Set.indicator_apply, Set.mem_ofPred_eq]
    norm_num
  · simp only [hazardRatio, hazard, atRisk, llArm₀_real, llArm₁_real, id,
      Set.indicator_apply, Set.mem_ofPred_eq]
    norm_num
  · rintro ⟨c, hc⟩
    have h1 := hc 1 (by norm_num)
    have h2 := hc 2 le_rfl
    simp only [survival, llArm₀_real, llArm₁_real, id, Set.indicator_apply,
      Set.mem_ofPred_eq] at h1 h2
    norm_num at h1 h2
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow] at h1 h2
    have h1' : (2 : ℝ) ^ c = 3 := by
      have := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) c
      field_simp at h1; linarith
    have h2' : (3 : ℝ) ^ c = 5 := by
      have := Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num) c
      field_simp at h2; linarith
    have hc : 3 / 2 < c := by
      by_contra hle
      push Not at hle
      have hm : (2 : ℝ) ^ c ≤ 2 ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      have hsq : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
        rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
      have : (3 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 :=
        calc (3 : ℝ) ^ 2 = ((2 : ℝ) ^ c) ^ 2 := by rw [h1']
          _ ≤ _ := pow_le_pow_left₀ (by positivity) hm 2
      rw [hsq] at this
      norm_num at this
    have hm : (3 : ℝ) ^ (3 / 2 : ℝ) < 3 ^ c := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hc
    have hsq : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 27 := by
      rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
    have : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 < (5 : ℝ) ^ 2 := by
      rw [← h2']; exact pow_lt_pow_left₀ hm (by positivity) (by norm_num)
    rw [hsq] at this
    norm_num at this

/-- **A constant hazard ratio is not proportional hazards in discrete time.** The hazard ratio
of `phArm₁` versus `phArm₀` is `1/2` at every time `m ≤ 2` at which the reference hazard is
positive, yet there is no exponent `c` with `S₁ m = S₀ m ^ c` for all `m ≤ 2`: the first
condition at `m = 1` forces `(1/2) ^ c = 3/4`, and then `S₀ 2 ^ c = ((1/2) ^ c) ^ 3 = 27/64`,
while `S₁ 2 = 15/32`. -/
theorem constant_hazardRatio_no_power :
    (∀ m ≤ 2, 0 < hazard phArm₀ id m → hazardRatio phArm₁ id phArm₀ id m = 1 / 2) ∧
      ¬ ∃ c : ℝ, ∀ m ≤ 2, survival phArm₁ id m = survival phArm₀ id m ^ c := by
  refine ⟨fun m hm => ?_, ?_⟩
  · rcases m with _ | _ | _ | m
    all_goals try (simp only [hazardRatio, hazard, atRisk, phArm₀_real, phArm₁_real, id,
      Set.indicator_apply, Set.mem_ofPred_eq]; norm_num; done)
    omega
  · rintro ⟨c, hc⟩
    have h1 := hc 1 (by norm_num)
    have h2 := hc 2 le_rfl
    simp only [survival, phArm₀_real, phArm₁_real, id, Set.indicator_apply,
      Set.mem_ofPred_eq] at h1 h2
    norm_num at h1 h2
    have h8 : (1 / 8 : ℝ) = (1 / 2) ^ (3 : ℕ) := by norm_num
    rw [h8, ← Real.rpow_natCast_mul (by norm_num), mul_comm,
      Real.rpow_mul_natCast (by norm_num), ← h1] at h2
    norm_num at h2

end PropHazardsExample

namespace PropHazards

/-! ### Duration of treatment effect -/

/-- **A smaller hazard after `t₀` keeps the survival ratio from falling.** If, at every time
`m` with `t₀ < m ≤ k` at which both arms have positive at-risk probability, the hazard of arm
`1` is at most that of arm `0`, then `S₀ k * S₁ t₀ ≤ S₁ k * S₀ t₀`: the survival ratio
`S₁ / S₀` at `k` is at least its value at `t₀`. Times at which an arm has at-risk probability
zero impose no condition. -/
theorem survival_mul_le_of_hazard_le (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) {t₀ k : ℕ}
    (hk : t₀ ≤ k)
    (h : ∀ m, t₀ < m → m ≤ k → 0 < atRisk μ₀ T₀ m → 0 < atRisk μ₁ T₁ m →
      hazard μ₁ T₁ m ≤ hazard μ₀ T₀ m) :
    survival μ₀ T₀ k * survival μ₁ T₁ t₀ ≤ survival μ₁ T₁ k * survival μ₀ T₀ t₀ := by
  induction k, hk using Nat.le_induction with
  | base => rw [mul_comm]
  | succ k hk ih =>
    have ih' := ih fun m h1 h2 => h m h1 (by omega)
    rw [survival_succ hT₀, survival_succ hT₁]
    have hS₀ := survival_nonneg (μ := μ₀) (T := T₀) k
    have hS₁ := survival_nonneg (μ := μ₁) (T := T₁) k
    have ht₀ := survival_nonneg (μ := μ₀) (T := T₀) t₀
    have ht₁ := survival_nonneg (μ := μ₁) (T := T₁) t₀
    have hq₀ := one_sub_hazard_nonneg (μ := μ₀) (T := T₀) (k + 1)
    have hq₁ := one_sub_hazard_nonneg (μ := μ₁) (T := T₁) (k + 1)
    rcases hS₀.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, zero_mul]; positivity
    rcases hS₁.eq_or_lt with h1 | h1
    · have : survival μ₀ T₀ k * survival μ₁ T₁ t₀ ≤ 0 := by rw [← h1, zero_mul] at ih'; exact ih'
      have : survival μ₀ T₀ k * (1 - hazard μ₀ T₀ (k + 1)) * survival μ₁ T₁ t₀ ≤ 0 := by
        nlinarith
      have : 0 ≤ survival μ₁ T₁ k * (1 - hazard μ₁ T₁ (k + 1)) * survival μ₀ T₀ t₀ := by
        positivity
      linarith
    have hh := h (k + 1) (by omega) le_rfl (by rw [atRisk_succ]; exact h0)
      (by rw [atRisk_succ]; exact h1)
    calc survival μ₀ T₀ k * (1 - hazard μ₀ T₀ (k + 1)) * survival μ₁ T₁ t₀
        = survival μ₀ T₀ k * survival μ₁ T₁ t₀ * (1 - hazard μ₀ T₀ (k + 1)) := by ring
      _ ≤ survival μ₁ T₁ k * survival μ₀ T₀ t₀ * (1 - hazard μ₀ T₀ (k + 1)) :=
          mul_le_mul_of_nonneg_right ih' hq₀
      _ ≤ survival μ₁ T₁ k * survival μ₀ T₀ t₀ * (1 - hazard μ₁ T₁ (k + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = survival μ₁ T₁ k * (1 - hazard μ₁ T₁ (k + 1)) * survival μ₀ T₀ t₀ := by ring

/-- **Duration of treatment effect: the effect stops at `t₀`** (NICE DSU TSD 14, Sections 4.1.3
and 2.9; TSD 19, Section 3.2.5). If the hazards of the two arms agree at every time `m` with
`t₀ < m ≤ k` at which both arms have positive at-risk probability, then
`S₁ k * S₀ t₀ = S₀ k * S₁ t₀`: the survival ratio `S₁ / S₀` stays at its value at `t₀`. -/
theorem survival_mul_eq_of_hazard_eq (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) {t₀ k : ℕ}
    (hk : t₀ ≤ k)
    (h : ∀ m, t₀ < m → m ≤ k → 0 < atRisk μ₀ T₀ m → 0 < atRisk μ₁ T₁ m →
      hazard μ₁ T₁ m = hazard μ₀ T₀ m) :
    survival μ₁ T₁ k * survival μ₀ T₀ t₀ = survival μ₀ T₀ k * survival μ₁ T₁ t₀ :=
  le_antisymm
    (survival_mul_le_of_hazard_le hT₁ hT₀ hk fun m h1 h2 a₁ a₀ => (h m h1 h2 a₀ a₁).ge)
    (survival_mul_le_of_hazard_le hT₀ hT₁ hk fun m h1 h2 a₀ a₁ => (h m h1 h2 a₀ a₁).le)

/-- The ratio form of `survival_mul_eq_of_hazard_eq`: if `S₀ k > 0` (hence `S₀ t₀ > 0`), then
`S₁ k / S₀ k = S₁ t₀ / S₀ t₀`. -/
theorem survival_div_eq_of_hazard_eq (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) {t₀ k : ℕ}
    (hk : t₀ ≤ k) (hS : 0 < survival μ₀ T₀ k)
    (h : ∀ m, t₀ < m → m ≤ k → 0 < atRisk μ₀ T₀ m → 0 < atRisk μ₁ T₁ m →
      hazard μ₁ T₁ m = hazard μ₀ T₀ m) :
    survival μ₁ T₁ k / survival μ₀ T₀ k = survival μ₁ T₁ t₀ / survival μ₀ T₀ t₀ := by
  have ht := lt_of_lt_of_le hS (survival_antitone hk)
  rw [div_eq_div_iff hS.ne' ht.ne', survival_mul_eq_of_hazard_eq hT₀ hT₁ hk h, mul_comm]

/-- **The survival gain after an effect that stops at `t₀`.** Under the hypothesis of
`survival_mul_eq_of_hazard_eq` up to the horizon `K`, with `S₀ t₀ > 0`, the area between the
survival curves over the periods `t₀, …, K` is the survival ratio at `t₀`, minus one, times the
area under the reference curve:
`∑_{k = t₀}^{K} (S₁ k - S₀ k) = (S₁ t₀ / S₀ t₀ - 1) * ∑_{k = t₀}^{K} S₀ k`. This is a restricted
(finite horizon) sum; nothing is claimed about the infinite horizon. -/
theorem sum_survival_sub_of_hazard_eq (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) {t₀ K : ℕ}
    (ht : 0 < survival μ₀ T₀ t₀)
    (h : ∀ m, t₀ < m → m ≤ K → 0 < atRisk μ₀ T₀ m → 0 < atRisk μ₁ T₁ m →
      hazard μ₁ T₁ m = hazard μ₀ T₀ m) :
    ∑ k ∈ Finset.Icc t₀ K, (survival μ₁ T₁ k - survival μ₀ T₀ k) =
      (survival μ₁ T₁ t₀ / survival μ₀ T₀ t₀ - 1) * ∑ k ∈ Finset.Icc t₀ K, survival μ₀ T₀ k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  have e := survival_mul_eq_of_hazard_eq hT₀ hT₁ hk1 fun m h1 h2 => h m h1 (h2.trans hk2)
  field_simp
  linarith

/-- **A maintained effect gives at least the gain of a stopped effect.** Two laws for arm `1`:
`(ν, T)` with hazards equal to those of arm `0` after `t₀` (the effect stops), and `(ν', T')`
with hazards at most those of arm `0` after `t₀` (the effect is maintained, for instance a
hazard ratio below one). If the two laws have the same survival at `t₀` and `S₀ t₀ > 0`, then
the maintained scenario has at least the survival of the stopped one at every `k ≥ t₀`. -/
theorem survival_le_of_maintained {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {ν : Measure Ω} {ν' : Measure Ω'} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {T : Ω → ℕ} {T' : Ω' → ℕ} (hT₀ : Measurable T₀) (hT : Measurable T) (hT' : Measurable T')
    {t₀ k : ℕ} (hk : t₀ ≤ k) (ht : 0 < survival μ₀ T₀ t₀)
    (heq : survival ν T t₀ = survival ν' T' t₀)
    (hstop : ∀ m, t₀ < m → m ≤ k → 0 < atRisk μ₀ T₀ m → 0 < atRisk ν T m →
      hazard ν T m = hazard μ₀ T₀ m)
    (hmaint : ∀ m, t₀ < m → m ≤ k → 0 < atRisk μ₀ T₀ m → 0 < atRisk ν' T' m →
      hazard ν' T' m ≤ hazard μ₀ T₀ m) :
    survival ν T k ≤ survival ν' T' k := by
  have e := survival_mul_eq_of_hazard_eq hT₀ hT hk hstop
  have l := survival_mul_le_of_hazard_le hT₀ hT' hk hmaint
  rw [← heq] at l
  exact le_of_mul_le_mul_right (by linarith) ht

/-- **The lifetime survival gain after an effect that stops at `t₀`.** If the hazards of the two
arms agree at every time `m > t₀` at which both arms have positive at-risk probability,
`S₀ t₀ > 0`, and the reference survival is summable, then the gains `S₁ k - S₀ k`, `k ≥ t₀`, are
summable with sum `(S₁ t₀ / S₀ t₀ - 1) * ∑_{k ≥ t₀} S₀ k`. Since `∑_k P(T > k)` is the mean of
`T`, this is the gain in mean survival time accrued from `t₀` on over an unbounded horizon;
`sum_survival_sub_of_hazard_eq` is the restricted version. -/
theorem hasSum_survival_sub_of_hazard_eq (hT₀ : Measurable T₀) (hT₁ : Measurable T₁) {t₀ : ℕ}
    (ht : 0 < survival μ₀ T₀ t₀)
    (h : ∀ m, t₀ < m → 0 < atRisk μ₀ T₀ m → 0 < atRisk μ₁ T₁ m →
      hazard μ₁ T₁ m = hazard μ₀ T₀ m)
    (hsum : Summable (survival μ₀ T₀)) :
    HasSum (fun k => survival μ₁ T₁ (t₀ + k) - survival μ₀ T₀ (t₀ + k))
      ((survival μ₁ T₁ t₀ / survival μ₀ T₀ t₀ - 1) * ∑' k, survival μ₀ T₀ (t₀ + k)) := by
  have hs : Summable (fun k => survival μ₀ T₀ (t₀ + k)) :=
    ((summable_nat_add_iff t₀).2 hsum).congr fun k => by rw [add_comm]
  convert hs.hasSum.mul_left (survival μ₁ T₁ t₀ / survival μ₀ T₀ t₀ - 1) using 1
  funext k
  have e := survival_mul_eq_of_hazard_eq hT₀ hT₁ (Nat.le_add_right t₀ k)
    fun m h1 _ => h m h1
  field_simp
  linarith

/-- **A maintained effect gives a strictly larger lifetime survival than a stopped one.** Under
the hypotheses of `survival_le_of_maintained` at every horizon, with summable reference survival
and summable survival of the maintained scenario, if in some period `m₁ > t₀` that the
maintained scenario reaches with positive probability its hazard is strictly below the
reference hazard, then `∑_{k ≥ t₀} S k < ∑_{k ≥ t₀} S' k` for the stopped law `S` and the
maintained law `S'`. -/
theorem tsum_survival_lt_of_maintained {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {ν : Measure Ω} {ν' : Measure Ω'} [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    {T : Ω → ℕ} {T' : Ω' → ℕ} (hT₀ : Measurable T₀) (hT : Measurable T) (hT' : Measurable T')
    {t₀ : ℕ} (ht : 0 < survival μ₀ T₀ t₀) (heq : survival ν T t₀ = survival ν' T' t₀)
    (hstop : ∀ m, t₀ < m → 0 < atRisk μ₀ T₀ m → 0 < atRisk ν T m →
      hazard ν T m = hazard μ₀ T₀ m)
    (hmaint : ∀ m, t₀ < m → 0 < atRisk μ₀ T₀ m → 0 < atRisk ν' T' m →
      hazard ν' T' m ≤ hazard μ₀ T₀ m)
    {m₁ : ℕ} (hm₁ : t₀ < m₁) (hr₁ : 0 < atRisk ν' T' m₁)
    (hlt : hazard ν' T' m₁ < hazard μ₀ T₀ m₁)
    (hsum : Summable (survival μ₀ T₀)) (hsum' : Summable (survival ν' T')) :
    ∑' k, survival ν T (t₀ + k) < ∑' k, survival ν' T' (t₀ + k) := by
  have hle : ∀ k, t₀ ≤ k → survival ν T k ≤ survival ν' T' k := fun k hk =>
    survival_le_of_maintained hT₀ hT hT' hk ht heq (fun m h1 _ => hstop m h1)
      (fun m h1 _ => hmaint m h1)
  -- summability of the stopped scenario from the frozen ratio
  have hd := hasSum_survival_sub_of_hazard_eq hT₀ hT ht hstop hsum
  have hs₀ : Summable (fun k => survival μ₀ T₀ (t₀ + k)) :=
    ((summable_nat_add_iff t₀).2 hsum).congr fun k => by rw [add_comm]
  have hsS : Summable (fun k => survival ν T (t₀ + k)) :=
    (hd.summable.add hs₀).congr fun k => by ring
  have hsS' : Summable (fun k => survival ν' T' (t₀ + k)) :=
    ((summable_nat_add_iff t₀).2 hsum').congr fun k => by rw [add_comm]
  -- the strict inequality in period `m₁`
  obtain ⟨k, rfl⟩ : ∃ k, m₁ = k + 1 := ⟨m₁ - 1, by omega⟩
  have hS'k : 0 < survival ν' T' k := by rwa [atRisk_succ] at hr₁
  have h0pos : 0 < atRisk μ₀ T₀ (k + 1) := by
    rcases (atRisk_nonneg (μ := μ₀) (T := T₀) (k + 1)).eq_or_lt with h | h
    · have : hazard μ₀ T₀ (k + 1) = 0 := by rw [hazard, ← h, div_zero]
      linarith [hazard_nonneg (μ := ν') (T := T') (k + 1)]
    · exact h
  have hstrict : survival ν T (k + 1) < survival ν' T' (k + 1) := by
    have hq₀ := one_sub_hazard_nonneg (μ := μ₀) (T := T₀) (k + 1)
    have hstep : survival ν T (k + 1) ≤ survival ν' T' k * (1 - hazard μ₀ T₀ (k + 1)) := by
      rw [survival_succ hT]
      rcases (survival_nonneg (μ := ν) (T := T) k).eq_or_lt with h | h
      · rw [← h, zero_mul]; positivity
      · rw [hstop (k + 1) hm₁ h0pos (by rw [atRisk_succ]; exact h)]
        exact mul_le_mul_of_nonneg_right (hle k (by omega)) hq₀
    rw [survival_succ hT']
    calc survival ν T (k + 1) ≤ survival ν' T' k * (1 - hazard μ₀ T₀ (k + 1)) := hstep
      _ < survival ν' T' k * (1 - hazard ν' T' (k + 1)) :=
          mul_lt_mul_of_pos_left (by linarith) hS'k
  refine Summable.tsum_lt_tsum (i := k + 1 - t₀) (fun j => hle _ (Nat.le_add_right t₀ j)) ?_
    hsS hsS'
  rw [show t₀ + (k + 1 - t₀) = k + 1 by omega]
  exact hstrict

end PropHazards

namespace PropHazards

/-! ### Non-collapsibility of the hazard ratio -/

open Bias.HazardRatio

/-- Stratum risks with a common stratum hazard ratio `ψ`: in the frailty stratum `u` the
untreated risk is `c u` and the treated risk `ψ * c u`. The hazard ratio here is the ratio of
discrete-time hazards (period risks among those at risk), as in `hazardRatio`; it is not the
power relation of `survival_eq_rpow_iff`. -/
def phRisk (ψ : ℝ) (c : Bool → ℝ) (a u : Bool) : ℝ := if a then ψ * c u else c u

variable (pA pU : Bool → ℝ) (ψ : ℝ) (b₁ b₂ : Bool → ℝ)

/-- At period `1` the hazard ratio is collapsible: with a common stratum hazard ratio `ψ` and a
frailty independent of treatment, the marginal period `1` hazards satisfy the multiplicative
identity `h₁ = ψ * h₀`. It also holds when the reference hazard is zero, where no hazard ratio
is defined; the ratio form with a positive reference hazard is `hazard1_phRisk_ratio`. -/
theorem hazard1_phRisk (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u) :
    hazard1 pA pU (phRisk ψ b₁) true = ψ * hazard1 pA pU (phRisk ψ b₁) false := by
  have := hA true; have := hA false; have := hU true; have := hU false
  simp only [hazard1, dead1Mass, armMass, phRisk, Fintype.sum_bool, ite_true,
    Bool.false_eq_true, ite_false]
  field_simp

/-- Within each frailty stratum the period `2` hazards satisfy the multiplicative identity
`h₁(2 | u) = ψ * h₀(2 | u)`. The ratio form, which needs a positive reference stratum hazard,
is `stratumHazard2_phRisk_ratio`. -/
theorem stratumHazard2_phRisk (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hs : ∀ a u, 0 < 1 - phRisk ψ b₁ a u) (u : Bool) :
    stratumHazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) true u =
      ψ * stratumHazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false u := by
  have h : ∀ a, pA a * pU u * (1 - phRisk ψ b₁ a u) ≠ 0 := fun a => by
    have := hA a; have := hU u; have := hs a u; positivity
  rw [stratumHazard2_eq _ _ _ _ _ _ (h true), stratumHazard2_eq _ _ _ _ _ _ (h false)]
  simp [phRisk]

/-- **The period `1` hazard ratio**, ratio form of `hazard1_phRisk`: when the reference
period `1` hazard is positive, `h₁(1) / h₀(1) = ψ`. -/
theorem hazard1_phRisk_ratio (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (h0 : 0 < hazard1 pA pU (phRisk ψ b₁) false) :
    hazard1 pA pU (phRisk ψ b₁) true / hazard1 pA pU (phRisk ψ b₁) false = ψ := by
  rw [hazard1_phRisk pA pU ψ b₁ hA hU, mul_div_assoc, div_self h0.ne', mul_one]

/-- **The stratum period `2` hazard ratio**, ratio form of `stratumHazard2_phRisk`: in a
stratum `u` with positive untreated period `2` risk `b₂ u` (the reference stratum hazard), the
stratum hazard ratio is `ψ`. -/
theorem stratumHazard2_phRisk_ratio (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hs : ∀ a u, 0 < 1 - phRisk ψ b₁ a u) (u : Bool) (hb : 0 < b₂ u) :
    stratumHazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) true u /
      stratumHazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false u = ψ := by
  have h : pA false * pU u * (1 - phRisk ψ b₁ false u) ≠ 0 := by
    have := hA false; have := hU u; have := hs false u; positivity
  have e : stratumHazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false u = b₂ u := by
    rw [stratumHazard2_eq _ _ _ _ _ _ h]; simp [phRisk]
  rw [stratumHazard2_phRisk pA pU ψ b₁ b₂ hA hU hs u, mul_div_assoc, e, div_self hb.ne',
    mul_one]

/-- The difference `h₁(2) - ψ h₀(2)` of the marginal period `2` hazards factors as
`ψ (c₂ 1 - c₂ 0) (w 1 1 - w 0 1)`, with `w a 1` the share of the stratum `U = 1` among the
period `1` survivors of arm `a`. -/
theorem hazard2_phRisk_sub (h1 : surv1Mass pA pU (phRisk ψ b₁) true ≠ 0)
    (h0 : surv1Mass pA pU (phRisk ψ b₁) false ≠ 0) :
    hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) true -
        ψ * hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false =
      ψ * (b₂ true - b₂ false) * (frailtyWeight pA pU (phRisk ψ b₁) true true -
        frailtyWeight pA pU (phRisk ψ b₁) false true) := by
  have hw : ∀ a, surv1Mass pA pU (phRisk ψ b₁) a ≠ 0 →
      frailtyWeight pA pU (phRisk ψ b₁) a false =
        1 - frailtyWeight pA pU (phRisk ψ b₁) a true := fun a ha => by
    rw [eq_sub_iff_add_eq, add_comm, frailtyWeight_add _ _ _ a ha]
  rw [hazard2_eq_weighted, hazard2_eq_weighted]
  simp only [Fintype.sum_bool, hw true h1, hw false h0, phRisk, ite_true, Bool.false_eq_true,
    ite_false]
  ring

/-- The survivors' frailty shares differ between the arms by
`pA 1 pA 0 pU 1 pU 0 (1 - ψ) (c₁ 1 - c₁ 0) / (P(A = 1, Y1 = 0) P(A = 0, Y1 = 0))`. -/
theorem frailtyWeight_phRisk_sub (h1 : surv1Mass pA pU (phRisk ψ b₁) true ≠ 0)
    (h0 : surv1Mass pA pU (phRisk ψ b₁) false ≠ 0) :
    frailtyWeight pA pU (phRisk ψ b₁) true true - frailtyWeight pA pU (phRisk ψ b₁) false true =
      pA true * pA false * pU true * pU false * ((1 - ψ) * (b₁ true - b₁ false)) /
        (surv1Mass pA pU (phRisk ψ b₁) true * surv1Mass pA pU (phRisk ψ b₁) false) := by
  rw [frailtyWeight, frailtyWeight, div_sub_div _ _ h1 h0]
  congr 1
  simp only [surv1Mass, Fintype.sum_bool, phRisk, ite_true, Bool.false_eq_true, ite_false]
  ring

/-- **Non-collapsibility of the hazard ratio, multiplicative form** (NICE DSU TSD 21, Section 5.2.1,
simulates data with survival conditional on a frailty `Z` equal to a power of a baseline survival,
the display immediately above Equation 17, while the fitted models are marginal; the conditional
model here is the ratio of period risks, not the survival power, for which see
`PropHazardsExample.groupedPH_noncollapsible`). In the two-period model of
`CausalInference.Bias.HazardRatio` with a frailty `U` independent of treatment, positive arm and
frailty probabilities, positive period `1` survival in every cell, and a common stratum hazard ratio
`ψ > 0` at both periods (untreated stratum risks `c₁ u`, `c₂ u`; treated `ψ * c₁ u`, `ψ * c₂ u`),
the marginal period `1` hazard ratio is `ψ` when the reference hazard is positive
(`hazard1_phRisk_ratio`), and the marginal period `2` hazards satisfy the multiplicative identity
`h₁(2) = ψ * h₀(2)` if and only if `ψ = 1` (no effect), or the frailty does not change the period
`1` risk (`c₁ 1 = c₁ 0`), or it does not change the period `2` risk (`c₂ 1 = c₂ 0`). With a positive
reference hazard at period `2` this is a statement about the hazard ratio
(`hazard2_phRisk_ratio_eq_iff`): in every other case the marginal hazard ratio differs from the
common stratum hazard ratio at period `2`. These exceptions are special to a binary frailty; for a
finite frailty the condition is a zero covariance of the two period risks (`frailtyHazard2_eq_iff`).
-/
theorem hazard2_phRisk_eq_iff (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u) (hψ : 0 < ψ)
    (hs : ∀ a u, 0 < 1 - phRisk ψ b₁ a u) :
    hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) true =
        ψ * hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false ↔
      ψ = 1 ∨ b₁ true = b₁ false ∨ b₂ true = b₂ false := by
  have hS := surv1Mass_pos pA pU (phRisk ψ b₁) hA hU hs
  rw [← sub_eq_zero, hazard2_phRisk_sub _ _ _ _ _ (hS true).ne' (hS false).ne',
    frailtyWeight_phRisk_sub _ _ _ _ (hS true).ne' (hS false).ne']
  have hP : pA true * pA false * pU true * pU false ≠ 0 := by
    have := hA true; have := hA false; have := hU true; have := hU false; positivity
  have hD : surv1Mass pA pU (phRisk ψ b₁) true * surv1Mass pA pU (phRisk ψ b₁) false ≠ 0 :=
    mul_ne_zero (hS true).ne' (hS false).ne'
  simp only [mul_eq_zero, div_eq_zero_iff, hψ.ne', hP, hD, sub_eq_zero, false_or, or_false]
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-- **Non-collapsibility of the period `2` hazard ratio**, ratio form of
`hazard2_phRisk_eq_iff`: with a positive reference hazard at period `2`,
`h₁(2) / h₀(2) = ψ` if and only if `ψ = 1`, `c₁ 1 = c₁ 0`, or `c₂ 1 = c₂ 0`. -/
theorem hazard2_phRisk_ratio_eq_iff (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u) (hψ : 0 < ψ)
    (hs : ∀ a u, 0 < 1 - phRisk ψ b₁ a u)
    (h0 : 0 < hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false) :
    hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) true /
        hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false = ψ ↔
      ψ = 1 ∨ b₁ true = b₁ false ∨ b₂ true = b₂ false := by
  rw [div_eq_iff h0.ne', hazard2_phRisk_eq_iff pA pU ψ b₁ b₂ hA hU hψ hs]

/-- **The period `2` hazard ratio is collapsible exactly in the degenerate cases**, in the
sense of `EffectMeasure.IsCollapsible` (Hernán and Robins, Fine Point 4.3) applied to the
period `2` risks among the period `1` survivors, whose stratum distributions are the survivors'
frailty shares `frailtyWeight a`. With positive untreated period `2` risks, every stratum hazard
ratio is `ψ`, and the marginal ratio `h₁(2) / h₀(2)` is a weighted average of them if and only
if `ψ = 1`, `c₁ 1 = c₁ 0`, or `c₂ 1 = c₂ 0`. Unlike the risk ratio with a stratifier
independent of treatment (`riskRatio_isCollapsible`), the hazard ratio is not collapsible,
because the survivors' frailty distributions differ between the arms. -/
theorem hazard2_phRisk_isCollapsible_iff (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hψ : 0 < ψ) (hs : ∀ a u, 0 < 1 - phRisk ψ b₁ a u) (hb₂ : ∀ u, 0 < b₂ u) :
    EffectMeasure.IsCollapsible (fun x y => x / y) EffectMeasure.riskRatioDom
        (frailtyWeight pA pU (phRisk ψ b₁) true) (frailtyWeight pA pU (phRisk ψ b₁) false)
        (phRisk ψ b₂ true) (phRisk ψ b₂ false) ↔
      ψ = 1 ∨ b₁ true = b₁ false ∨ b₂ true = b₂ false := by
  have hS := surv1Mass_pos pA pU (phRisk ψ b₁) hA hU hs
  have hwpos : ∀ a u, 0 < frailtyWeight pA pU (phRisk ψ b₁) a u := fun a u =>
    div_pos (by have := hA a; have := hU u; have := hs a u; positivity) (hS a)
  have hW : ∀ a, EffectMeasure.IsWeights (frailtyWeight pA pU (phRisk ψ b₁) a) := fun a =>
    ⟨fun u => (hwpos a u).le, by rw [Fintype.sum_bool]; exact frailtyWeight_add _ _ _ a (hS a).ne'⟩
  have hstd : ∀ a, EffectMeasure.standardizedRisk (frailtyWeight pA pU (phRisk ψ b₁) a)
      (phRisk ψ b₂ a) = hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) a := fun a =>
    (hazard2_eq_weighted _ _ _ _ a).symm
  have hratio : ∀ v, phRisk ψ b₂ true v / phRisk ψ b₂ false v = ψ := fun v => by
    simp [phRisk, (hb₂ v).ne']
  have h0pos : 0 < hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false := by
    rw [← hstd]
    exact Finset.sum_pos (fun u _ => mul_pos (hwpos _ u) (by simp [phRisk, hb₂ u]))
      Finset.univ_nonempty
  have key : ∀ w : Bool → ℝ, EffectMeasure.IsWeights w →
      ∑ v, w v * (phRisk ψ b₂ true v / phRisk ψ b₂ false v) = ψ := fun w hw => by
    simp only [hratio, ← Finset.sum_mul, hw.2, one_mul]
  rw [← hazard2_phRisk_eq_iff pA pU ψ b₁ b₂ hA hU hψ hs, EffectMeasure.IsCollapsible]
  simp only [hstd]
  constructor
  · rintro ⟨w, hw, -, he⟩
    rw [key w hw, div_eq_iff h0pos.ne'] at he
    exact he
  · intro h
    refine ⟨_, hW false, fun v _ => ⟨hwpos true v, hwpos false v, ?_⟩, ?_⟩
    · simp [EffectMeasure.riskRatioDom, phRisk, hb₂ v]
    · rw [key _ (hW false), h, mul_div_assoc, div_self h0pos.ne', mul_one]

end PropHazards

namespace PropHazards

/-! ### Finite frailty: the covariance criterion -/

section FiniteFrailty

open Bias.HazardRatio

variable {ι : Type*} [Fintype ι]

/-- The covariance `Cov_π(x, y) = ∑ π x y - (∑ π x) (∑ π y)` of two functions of the frailty
under the weights `π`; it is a covariance when `π` is a distribution. -/
def frailtyCov (π x y : ι → ℝ) : ℝ :=
  ∑ u, π u * x u * y u - (∑ u, π u * x u) * ∑ u, π u * y u

/-- The marginal period `2` hazard of an arm whose stratum risks are `κ * b₁ u` at period `1`
and `κ * b₂ u` at period `2`, with frailty law `π` independent of treatment:
`∑ π u (1 - κ b₁ u) κ b₂ u / ∑ π u (1 - κ b₁ u)`, the period `2` deaths among the period `1`
survivors. The untreated arm is `κ = 1`, the treated arm `κ = ψ`. -/
noncomputable def frailtyHazard2 (π b₁ b₂ : ι → ℝ) (κ : ℝ) : ℝ :=
  (∑ u, π u * (1 - κ * b₁ u) * (κ * b₂ u)) / ∑ u, π u * (1 - κ * b₁ u)

/-- **Non-collapsibility of the hazard ratio with a finite frailty.** For a frailty law `π`
(summing to one) on a finite set, a common stratum hazard ratio `ψ ≠ 0` at both periods, and
positive survivor mass after period `1` in both arms (nonzero denominators), the marginal
period `2` hazards satisfy `h₁(2) = ψ * h₀(2)` if and only if `ψ = 1` or the two period risks
are uncorrelated under `π`: `Cov_π(b₁, b₂) = 0`. The identity behind it is
`h₁(2) - ψ h₀(2) ∝ ψ (1 - ψ) Cov_π(b₁, b₂)`. -/
theorem frailtyHazard2_eq_iff (π b₁ b₂ : ι → ℝ) {ψ : ℝ} (hπ : ∑ u, π u = 1) (hψ : ψ ≠ 0)
    (h1 : ∑ u, π u * (1 - ψ * b₁ u) ≠ 0) (h0 : ∑ u, π u * (1 - 1 * b₁ u) ≠ 0) :
    frailtyHazard2 π b₁ b₂ ψ = ψ * frailtyHazard2 π b₁ b₂ 1 ↔
      ψ = 1 ∨ frailtyCov π b₁ b₂ = 0 := by
  have hs : ∀ κ : ℝ, ∑ u, π u * (1 - κ * b₁ u) = 1 - κ * ∑ u, π u * b₁ u := fun κ => by
    have : ∀ u, π u * (1 - κ * b₁ u) = π u - κ * (π u * b₁ u) := fun u => by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hπ]
  have hn : ∀ κ : ℝ, ∑ u, π u * (1 - κ * b₁ u) * (κ * b₂ u) =
      κ * ∑ u, π u * b₂ u - κ ^ 2 * ∑ u, π u * b₁ u * b₂ u := fun κ => by
    have : ∀ u, π u * (1 - κ * b₁ u) * (κ * b₂ u) =
        κ * (π u * b₂ u) - κ ^ 2 * (π u * b₁ u * b₂ u) := fun u => by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hs] at h1 h0
  unfold frailtyHazard2 frailtyCov
  rw [hs, hs, hn, hn, mul_div_assoc', div_eq_div_iff h1 h0]
  set E1 := ∑ u, π u * b₁ u
  set E2 := ∑ u, π u * b₂ u
  set E12 := ∑ u, π u * b₁ u * b₂ u
  constructor
  · intro h
    have : ψ * ((1 - ψ) * (E12 - E1 * E2)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hψ
    rcases mul_eq_zero.1 h' with h' | h'
    · exact Or.inl (by linarith)
    · exact Or.inr h'
  · rintro (rfl | h)
    · ring
    · linear_combination (ψ * (1 - ψ)) * h

/-- The binary frailty model of `CausalInference.Bias.HazardRatio` is the case `ι = Bool` of
`frailtyHazard2`: with `pA a ≠ 0`, the period `2` hazard of arm `a` under `phRisk ψ` is
`frailtyHazard2 pU b₁ b₂ κ` with `κ = ψ` for the treated and `κ = 1` for the untreated. -/
theorem hazard2_phRisk_eq_frailtyHazard2 (pA pU : Bool → ℝ) (ψ : ℝ) (b₁ b₂ : Bool → ℝ)
    (a : Bool) (ha : pA a ≠ 0) :
    hazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) a =
      frailtyHazard2 pU b₁ b₂ (if a then ψ else 1) := by
  have e1 : ∀ r : Bool → ℝ, ∀ u, phRisk ψ r a u = (if a then ψ else 1) * r u := fun r u => by
    cases a <;> simp [phRisk]
  simp only [hazard2, dead2Mass, surv1Mass, frailtyHazard2, e1]
  have : ∀ f : Bool → ℝ, ∑ u, pA a * pU u * f u = pA a * ∑ u, pU u * f u := fun f => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
  have h2 : ∑ u, pA a * pU u * (1 - (if a then ψ else 1) * b₁ u) *
      ((if a then ψ else 1) * b₂ u) =
      pA a * ∑ u, pU u * (1 - (if a then ψ else 1) * b₁ u) * ((if a then ψ else 1) * b₂ u) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
  rw [h2, this, mul_div_mul_left _ _ ha]

/-- With a binary frailty and weights summing to one, the covariance of two risks is
`π 1 π 0 (x 1 - x 0) (y 1 - y 0)`: it vanishes exactly when `π` is degenerate or one of the
risks does not depend on the frailty. With `frailtyHazard2_eq_iff` this gives back the
exceptional cases of `hazard2_phRisk_eq_iff`. -/
theorem frailtyCov_bool (π x y : Bool → ℝ) (hπ : π true + π false = 1) :
    frailtyCov π x y = π true * π false * (x true - x false) * (y true - y false) := by
  have : π false = 1 - π true := by linarith
  simp only [frailtyCov, Fintype.sum_bool, this]
  ring

end FiniteFrailty

end PropHazards

namespace PropHazardsExample

open Bias.HazardRatio PropHazards

/-- Untreated stratum risks of the non-collapsibility example: `1/10` with `U = 1`, `1/2`
with `U = 0`, at both periods. -/
noncomputable def ncRisk (u : Bool) : ℝ := if u then 1 / 10 else 1 / 2

/-- **Numerical non-collapsibility.** Fair treatment and frailty, untreated stratum risks
`1/10` (`U = 1`) and `1/2` (`U = 0`) at both periods, and a common stratum hazard ratio `1/2`.
The marginal hazard ratio is `1/2` at period `1` and `329/578` (about `0.57`) at period `2`,
although it is `1/2` in each stratum at both periods: it moves toward `1` over time. -/
theorem noncollapsible_example :
    hazard1 exHalf exHalf (phRisk (1 / 2) ncRisk) true /
        hazard1 exHalf exHalf (phRisk (1 / 2) ncRisk) false = 1 / 2 ∧
      hazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) true /
        hazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) false =
          329 / 578 ∧
      ∀ u, stratumHazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) true u /
        stratumHazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) false u =
          1 / 2 := by
  refine ⟨?_, ?_, fun u => ?_⟩
  · norm_num [hazard1, dead1Mass, armMass, exHalf, phRisk, ncRisk, Fintype.sum_bool]
  · norm_num [hazard2, dead2Mass, surv1Mass, exHalf, phRisk, ncRisk, Fintype.sum_bool]
  · cases u <;> norm_num [stratumHazard2, exHalf, phRisk, ncRisk]

/-- Uniform law on three frailty levels. -/
noncomputable def triWeight (_ : Fin 3) : ℝ := 1 / 3

/-- Untreated period `1` risks on three frailty levels: `1/10, 1/5, 3/10`. -/
noncomputable def triRisk₁ : Fin 3 → ℝ := ![1 / 10, 1 / 5, 3 / 10]

/-- Untreated period `2` risks on three frailty levels: `1/5, 2/5, 1/5`. -/
noncomputable def triRisk₂ : Fin 3 → ℝ := ![1 / 5, 2 / 5, 1 / 5]

/-- **The binary exceptions do not extend to three frailty levels.** Both period risks depend
on the frailty, yet their covariance under the uniform law is zero, so with the common stratum
hazard ratio `1/2` the marginal period `2` hazards still satisfy `h₁(2) = (1/2) h₀(2)`
(`frailtyHazard2_eq_iff`), and the reference hazard is positive. -/
theorem zeroCov_example :
    triRisk₁ 0 ≠ triRisk₁ 1 ∧ triRisk₂ 0 ≠ triRisk₂ 1 ∧ frailtyCov triWeight triRisk₁ triRisk₂ = 0 ∧
      0 < frailtyHazard2 triWeight triRisk₁ triRisk₂ 1 ∧
      frailtyHazard2 triWeight triRisk₁ triRisk₂ (1 / 2) =
        1 / 2 * frailtyHazard2 triWeight triRisk₁ triRisk₂ 1 := by
  refine ⟨by norm_num [triRisk₁], by norm_num [triRisk₂], ?_, ?_, ?_⟩ <;>
    norm_num [frailtyCov, frailtyHazard2, triWeight, triRisk₁, triRisk₂, Fin.sum_univ_three]

/-- Period `1` risks of the survival-power example. Untreated: `3/4` with `U = 0` and `1/4`
with `U = 1` (period `1` survival `1/4` and `3/4`). Treated: `15/16` and `7/16` (survival
`1/16` and `9/16`, the squares). -/
noncomputable def gpRisk (a u : Bool) : ℝ :=
  if a then (if u then 7 / 16 else 15 / 16) else (if u then 1 / 4 else 3 / 4)

/-- **Grouped proportional hazards on the survival-power scale are not collapsible** (the
conditional model of NICE DSU TSD 21, Section 5.2.1, display above Equation 17: survival given
the frailty is a power of a baseline survival). In the two-period model with a fair treatment
and a fair frailty independent of treatment, the period `1` survival of the treated is the
square of that of the untreated in each frailty stratum, `1 - r₁(1, u) = (1 - r₁(0, u)) ^ 2`.
The marginal period `1` survival `P(Y1 = 0 | A = a)` is `5/16` in the treated and `1/2` in the
untreated, and `5/16 ≠ (1/2) ^ 2 = 1/4`: the marginal survival curves do not satisfy the power
relation with the common conditional power `2`. -/
theorem groupedPH_noncollapsible :
    (∀ u, 1 - gpRisk true u = (1 - gpRisk false u) ^ (2 : ℝ)) ∧
      surv1Mass exHalf exHalf gpRisk true / armMass exHalf exHalf true = 5 / 16 ∧
      surv1Mass exHalf exHalf gpRisk false / armMass exHalf exHalf false = 1 / 2 ∧
      surv1Mass exHalf exHalf gpRisk true / armMass exHalf exHalf true ≠
        (surv1Mass exHalf exHalf gpRisk false / armMass exHalf exHalf false) ^ (2 : ℝ) := by
  refine ⟨fun u => ?_, ?_, ?_, ?_⟩
  · cases u <;> norm_num [gpRisk, Real.rpow_two]
  all_goals norm_num [surv1Mass, armMass, exHalf, gpRisk, Fintype.sum_bool, Real.rpow_two]

end PropHazardsExample

namespace PropHazards

/-! ### Scale-dependent effect modification on the log cumulative hazard scale -/

section CumHazard

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → ℕ}

/-- The discrete-time cumulative hazard `H k = -log S k`. -/
noncomputable def cumHazard (μ : Measure Ω) (T : Ω → ℕ) (k : ℕ) : ℝ :=
  -Real.log (survival μ T k)

/-- The increment of the cumulative hazard over interval `k + 1` is the grouped-time hazard
`-log (1 - h (k + 1))`, when `S (k + 1) > 0`. -/
theorem cumHazard_succ_sub (hT : Measurable T) (k : ℕ) (hS : 0 < survival μ T (k + 1)) :
    cumHazard μ T (k + 1) - cumHazard μ T k = -Real.log (1 - hazard μ T (k + 1)) := by
  have hk : 0 < survival μ T k := lt_of_lt_of_le hS (survival_antitone k.le_succ)
  have hq : 0 < 1 - hazard μ T (k + 1) := by
    rw [survival_succ hT] at hS
    exact pos_of_mul_pos_right hS hk.le
  rw [cumHazard, cumHazard, survival_succ hT, Real.log_mul hk.ne' hq.ne']
  ring

end CumHazard

/-- **The log-linear reading of the multiplicative cumulative hazard model**: when `G`, `B`, `C`
are positive, `H(x, z) = G B^x C^z` (with `x, z` binary) satisfies
`log H(x, z) = log G + x log B + z log C`. -/
theorem log_multiplicative_cumHazard {G B C : ℝ} (hG : 0 < G) (hB : 0 < B) (hC : 0 < C)
    (x z : Bool) :
    Real.log (G * (if x then B else 1) * (if z then C else 1)) =
      Real.log G + (if x then Real.log B else 0) + (if z then Real.log C else 0) := by
  cases x <;> cases z <;> simp [Real.log_mul, hG.ne', hB.ne', hC.ne']

/-- The algebra behind `cloglogRatio_eq_iff`: for `G, g ≠ 0` and nonzero denominators,
`(G B - g b) / (G - g) = (G B C - g b c) / (G C - g c)` if and only if `B = b` or `C = c`. -/
theorem incrementRatio_eq_iff {G g B b C c : ℝ} (hG : G ≠ 0) (hg : g ≠ 0) (h0 : G - g ≠ 0)
    (h1 : G * C - g * c ≠ 0) :
    (G * B - g * b) / (G - g) = (G * B * C - g * b * c) / (G * C - g * c) ↔ B = b ∨ C = c := by
  rw [div_eq_div_iff h0 h1]
  constructor
  · intro h
    have : G * g * ((B - b) * (C - c)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (mul_ne_zero hG hg)
    · rcases mul_eq_zero.1 h' with h' | h'
      · exact Or.inl (sub_eq_zero.1 h')
      · exact Or.inr (sub_eq_zero.1 h')
  · rintro (rfl | rfl) <;> ring

/-- **Scale-dependent effect modification** (NICE DSU TSD 21, Section 3.2.3: with several
time-dependent effects, the hazard ratio for one covariate depends on the value of another
even without an interaction term), in discrete time. Four laws, indexed by two binary
covariates `x` and `z`, follow a model that is additive on the log cumulative hazard scale
at times `k` and `k + 1`:
`log H(j | x, z) = log G_j + x log B_j + z log C_j`, that is
`H(k | x, z) = G₀ B₀^x C₀^z` and `H(k + 1 | x, z) = G₁ B₁^x C₁^z`, with no `x z` term. The
hazard ratio for `x` over interval `k + 1` on the grouped-time (complementary log-log) scale,
`-log (1 - h(k + 1 | 1, z)) / -log (1 - h(k + 1 | 0, z))`, is the same for `z = 1` and `z = 0`
if and only if the effect of `x` does not change over the interval (`B₁ = B₀`) or the effect of
`z` does not (`C₁ = C₀`). The statement is for the multiplicative cumulative hazard model: the
hypotheses allow `B_j = 0` or `C_j = 0`, where `log H` is not defined. The log-linear reading
`log H = log G + x log B + z log C` holds when every multiplier is positive
(`log_multiplicative_cumHazard`). The positivity hypotheses make `H = -log S`, the grouped-time
hazards `-log (1 - h)` and the two ratios genuine. -/
theorem cloglogRatio_eq_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Bool → Bool → Measure Ω)
    [∀ x z, IsProbabilityMeasure (μ x z)] (T : Bool → Bool → Ω → ℕ)
    (hT : ∀ x z, Measurable (T x z)) (k : ℕ) {G₀ G₁ B₀ B₁ C₀ C₁ : ℝ} (hG₀ : 0 < G₀)
    (hG₁ : 0 < G₁)
    (hk : ∀ x z, cumHazard (μ x z) (T x z) k =
      G₀ * (if x then B₀ else 1) * (if z then C₀ else 1))
    (hk₁ : ∀ x z, cumHazard (μ x z) (T x z) (k + 1) =
      G₁ * (if x then B₁ else 1) * (if z then C₁ else 1))
    (hS : ∀ x z, 0 < survival (μ x z) (T x z) (k + 1))
    (hh : ∀ z, 0 < hazard (μ false z) (T false z) (k + 1)) :
    -Real.log (1 - hazard (μ true true) (T true true) (k + 1)) /
        -Real.log (1 - hazard (μ false true) (T false true) (k + 1)) =
      -Real.log (1 - hazard (μ true false) (T true false) (k + 1)) /
        -Real.log (1 - hazard (μ false false) (T false false) (k + 1)) ↔
      B₁ = B₀ ∨ C₁ = C₀ := by
  have e : ∀ x z, -Real.log (1 - hazard (μ x z) (T x z) (k + 1)) =
      G₁ * (if x then B₁ else 1) * (if z then C₁ else 1) -
        G₀ * (if x then B₀ else 1) * (if z then C₀ else 1) := fun x z => by
    rw [← cumHazard_succ_sub (hT x z) k (hS x z), hk, hk₁]
  have hpos : ∀ z, 0 < -Real.log (1 - hazard (μ false z) (T false z) (k + 1)) := fun z => by
    have h1 : hazard (μ false z) (T false z) (k + 1) ≤ 1 := hazard_le_one _
    have h2 : 1 - hazard (μ false z) (T false z) (k + 1) ≠ 0 := by
      intro h0
      have := survival_succ (μ := μ false z) (hT false z) k
      rw [h0, mul_zero] at this
      exact (hS false z).ne' this
    exact neg_pos.2 (Real.log_neg (lt_of_le_of_ne (sub_nonneg.2 h1) (Ne.symm h2))
      (by linarith [hh z]))
  have d0 := hpos false
  have d1 := hpos true
  rw [e] at d0 d1
  simp only [e, ite_true, Bool.false_eq_true, ite_false, mul_one] at d0 d1 ⊢
  rw [eq_comm, incrementRatio_eq_iff hG₁.ne' hG₀.ne' d0.ne' d1.ne']

end PropHazards

namespace PropHazardsExample

open ComparisonExample

/-- Reference arm of the duration example: masses `1/2, 1/4, 1/4` at times `1, 2, 3`;
hazards `1/2` at times `1` and `2`. -/
noncomputable def durRef : Measure ℕ := threePoint (1 / 2) (1 / 4) (1 / 4)

/-- Treated arm whose effect stops after time `1`: hazards `1/4` at time `1` and `1/2` at
time `2`. -/
noncomputable def durStop : Measure ℕ := threePoint (1 / 4) (3 / 8) (3 / 8)

/-- Treated arm whose effect is maintained: hazards `1/4` at times `1` and `2`, a hazard ratio
`1/2` at times `1` and `2`. At time `3` the laws `durRef`, `durStop`, `durMaint` put all their
remaining mass, so every hazard there is `1`; the example is about times up to `2`. -/
noncomputable def durMaint : Measure ℕ := threePoint (1 / 4) (3 / 16) (9 / 16)

/-- The masses of `durRef`. -/
theorem durRef_real (s : Set ℕ) : durRef.real s =
    s.indicator (fun _ => 1 / 2) 1 + s.indicator (fun _ => 1 / 4) 2 +
      s.indicator (fun _ => 1 / 4) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

/-- The masses of `durStop`. -/
theorem durStop_real (s : Set ℕ) : durStop.real s =
    s.indicator (fun _ => 1 / 4) 1 + s.indicator (fun _ => 3 / 8) 2 +
      s.indicator (fun _ => 3 / 8) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

/-- The masses of `durMaint`. -/
theorem durMaint_real (s : Set ℕ) : durMaint.real s =
    s.indicator (fun _ => 1 / 4) 1 + s.indicator (fun _ => 3 / 16) 2 +
      s.indicator (fun _ => 9 / 16) 3 :=
  threePoint_real (by norm_num) (by norm_num) (by norm_num) s

instance : IsProbabilityMeasure durRef :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure durStop :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

instance : IsProbabilityMeasure durMaint :=
  isProbabilityMeasure_threePoint (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The duration of the treatment effect is not determined by follow-up to `t₀`.** With
follow-up to `t₀ = 1`, the two treated scenarios are indistinguishable: same survival and same
hazard at times `0` and `1` (hazard ratio `1/2` against the reference arm at time `1`). After
`t₀` the effect stops in `durStop` (hazard `1/2`, equal to the reference) and is maintained in
`durMaint` (hazard `1/4`, hazard ratio `1/2`), and the survivals at time `2` are `3/8` and
`9/16`. The stopped scenario keeps the survival ratio of time `1`:
`S(2) / S_ref(2) = (3/8) / (1/4) = (3/4) / (1/2)`. -/
theorem duration_not_identified :
    (∀ m ≤ 1, survival durStop id m = survival durMaint id m ∧
      hazard durStop id m = hazard durMaint id m) ∧
      hazardRatio durStop id durRef id 1 = 1 / 2 ∧
      hazard durStop id 2 = hazard durRef id 2 ∧ hazardRatio durMaint id durRef id 2 = 1 / 2 ∧
      survival durStop id 2 = 3 / 8 ∧ survival durMaint id 2 = 9 / 16 ∧
      survival durStop id 2 / survival durRef id 2 =
        survival durStop id 1 / survival durRef id 1 := by
  refine ⟨fun m hm => ?_, ?_⟩
  · rcases m with _ | _ | m
    all_goals try (simp only [hazard, survival, atRisk, durStop_real, durMaint_real, id,
      Set.indicator_apply, Set.mem_ofPred_eq]; norm_num; done)
    omega
  · simp only [hazardRatio, hazard, survival, atRisk, durRef_real, durStop_real, durMaint_real,
      id, Set.indicator_apply, Set.mem_ofPred_eq]
    norm_num

end PropHazardsExample

namespace PropHazardsExample

open ComparisonExample PropHazards

/-- Survival at time `2` in the arm `(x, z)` of the scale-dependence example: `1/4`, `1/16`,
`1/16` and `1/256` for `(x, z) = (0, 0), (1, 0), (0, 1), (1, 1)`. -/
noncomputable def sdTail (x z : Bool) : ℝ :=
  if x then (if z then 1 / 256 else 1 / 16) else (if z then 1 / 16 else 1 / 4)

/-- `0 < q ≤ 1/2` for the survival `q` at time `2`. -/
theorem sdTail_bounds (x z : Bool) : 0 < sdTail x z ∧ sdTail x z ≤ 1 / 2 := by
  cases x <;> cases z <;> norm_num [sdTail]

/-- The arm `(x, z)` of the scale-dependence example: masses `1/2, 1/2 - q, q` at times
`1, 2, 3` with `q = sdTail x z`, so that `S 1 = 1/2` and `S 2 = q` in every arm. -/
noncomputable def sdArm (x z : Bool) : Measure ℕ :=
  threePoint (1 / 2) (1 / 2 - sdTail x z) (sdTail x z)

/-- The masses of `sdArm x z`. -/
theorem sdArm_real (x z : Bool) (s : Set ℕ) : (sdArm x z).real s =
    s.indicator (fun _ => 1 / 2) 1 + s.indicator (fun _ => 1 / 2 - sdTail x z) 2 +
      s.indicator (fun _ => sdTail x z) 3 :=
  threePoint_real (by norm_num) (by linarith [(sdTail_bounds x z).2]) (sdTail_bounds x z).1.le s

instance (x z : Bool) : IsProbabilityMeasure (sdArm x z) :=
  isProbabilityMeasure_threePoint (by norm_num) (by linarith [(sdTail_bounds x z).2])
    (sdTail_bounds x z).1.le (by ring)

/-- **The scale-dependent modification of `cloglogRatio_eq_iff` occurs.** Four laws with
`S 1 = 1/2` in every arm and `S 2 = 1/4, 1/16, 1/16, 1/256` for
`(x, z) = (0, 0), (1, 0), (0, 1), (1, 1)` follow the model of `cloglogRatio_eq_iff` with
`H(1 | x, z) = log 2` and `H(2 | x, z) = 2 log 2 * 2 ^ x * 2 ^ z`: additive in `x` and `z` on
the log cumulative hazard scale, with no interaction term, and with both coefficients changing
between times `1` and `2`. The grouped-time hazard ratio for `x` over interval `2` is then
different for `z = 1` and `z = 0`. -/
theorem scaleDependence_example :
    -Real.log (1 - hazard (sdArm true true) id 2) / -Real.log (1 - hazard (sdArm false true) id 2)
      ≠ -Real.log (1 - hazard (sdArm true false) id 2) /
        -Real.log (1 - hazard (sdArm false false) id 2) := by
  have hS1 : ∀ x z, survival (sdArm x z) id 1 = 1 / 2 := fun x z => by
    simp only [survival, sdArm_real, id, Set.indicator_apply, Set.mem_ofPred_eq]
    norm_num
  have hS2 : ∀ x z, survival (sdArm x z) id 2 = sdTail x z := fun x z => by
    simp only [survival, sdArm_real, id, Set.indicator_apply, Set.mem_ofPred_eq]
    norm_num
  have hl : ∀ n : ℕ, Real.log ((2 : ℝ) ^ n)⁻¹ = -(n * Real.log 2) := fun n => by
    rw [Real.log_inv, Real.log_pow]
  have hG : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro h
  have key := (cloglogRatio_eq_iff sdArm (fun _ _ => id) (fun _ _ => measurable_id) 1
    (G₀ := Real.log 2) (G₁ := 2 * Real.log 2) (B₀ := 1) (B₁ := 2) (C₀ := 1) (C₁ := 2) hG
    (by positivity) (fun x z => ?_) (fun x z => ?_) (fun x z => ?_) (fun z => ?_)).1 h
  · norm_num at key
  · rw [cumHazard, hS1, one_div, Real.log_inv, neg_neg]
    simp
  · rw [cumHazard, hS2]
    cases x <;> cases z
    · rw [show sdTail false false = ((2 : ℝ) ^ 2)⁻¹ by norm_num [sdTail], hl]; norm_num
    · rw [show sdTail false true = ((2 : ℝ) ^ 4)⁻¹ by norm_num [sdTail], hl]; norm_num; ring
    · rw [show sdTail true false = ((2 : ℝ) ^ 4)⁻¹ by norm_num [sdTail], hl]; norm_num; ring
    · rw [show sdTail true true = ((2 : ℝ) ^ 8)⁻¹ by norm_num [sdTail], hl]; norm_num; ring
  · rw [hS2]; exact (sdTail_bounds x z).1
  · have hb := sdTail_bounds false z
    simp only [hazard, atRisk, sdArm_real, id, Set.indicator_apply, Set.mem_ofPred_eq]
    cases z <;> norm_num [sdTail]

end PropHazardsExample

namespace PropHazardsExample

open Filter Topology

/-- The sample space of the full-grid log-logistic example: the uniform law on `(0, 1]`. -/
noncomputable def llSpace : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance : IsProbabilityMeasure llSpace := ⟨by simp [llSpace]⟩

/-- The event time of the full-grid log-logistic example with acceleration factor `φ`:
`T u = ⌊(1/u - 1)/φ⌋₊ + 1`. For `φ > 0` its survival is `S(k) = 1 / (1 + φ k)` at every
`k : ℕ` (`llTime_survival`): the log-logistic survival of shape `1` and scale `1/φ` on the full
grid. -/
noncomputable def llTime (φ u : ℝ) : ℕ := ⌊(1 / u - 1) / φ⌋₊ + 1

theorem measurable_llTime (φ : ℝ) : Measurable (llTime φ) :=
  (Measurable.of_discrete (f := fun n : ℕ => n + 1)).comp
    (Nat.measurable_floor.comp (((measurable_const.div measurable_id).sub_const 1).div_const φ))

/-- For `u ∈ (0, 1]`: `k < T u` if and only if `u ≤ 1 / (1 + φ k)`. -/
theorem lt_llTime_iff {φ u : ℝ} (hφ : 0 < φ) (hu0 : 0 < u) (hu1 : u ≤ 1) (k : ℕ) :
    k < llTime φ u ↔ u ≤ 1 / (1 + φ * k) := by
  have hx : 0 ≤ (1 / u - 1) / φ :=
    div_nonneg (sub_nonneg.2 (by rw [le_div_iff₀ hu0]; linarith)) hφ.le
  have hd : 0 < 1 + φ * k := by positivity
  rw [llTime, Nat.lt_succ_iff, Nat.le_floor_iff hx, le_div_iff₀ hφ, le_div_iff₀ hd,
    le_sub_iff_add_le, le_div_iff₀ hu0]
  constructor <;> intro h <;> nlinarith

/-- **The full-grid log-logistic survival**: `S(k) = 1 / (1 + φ k)` for every `k : ℕ`. -/
theorem llTime_survival {φ : ℝ} (hφ : 0 < φ) (k : ℕ) :
    survival llSpace (llTime φ) k = 1 / (1 + φ * k) := by
  have hd : 0 < 1 + φ * k := by positivity
  have hc : 1 / (1 + φ * k) ≤ 1 := (div_le_one hd).2 (by nlinarith [k.cast_nonneg (α := ℝ)])
  have hset : {u | k < llTime φ u} ∩ Set.Ioc 0 1 = Set.Ioc 0 (1 / (1 + φ * k)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨h, hu0, hu1⟩; exact ⟨hu0, (lt_llTime_iff hφ hu0 hu1 k).1 h⟩
    · rintro ⟨hu0, hu⟩; exact ⟨(lt_llTime_iff hφ hu0 (hu.trans hc) k).2 hu, hu0, hu.trans hc⟩
  rw [survival, llSpace, measureReal_def, Measure.restrict_apply' measurableSet_Ioc, hset,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)]

/-- The hazard of the full-grid log-logistic law at time `k + 1`: `φ / (1 + φ (k + 1))`. -/
theorem llTime_hazard {φ : ℝ} (hφ : 0 < φ) (k : ℕ) :
    hazard llSpace (llTime φ) (k + 1) = φ / (1 + φ * (k + 1)) := by
  rw [hazard, measureReal_eq_atRisk_sub (measurable_llTime φ), atRisk_succ, atRisk_succ,
    llTime_survival hφ, llTime_survival hφ]
  push_cast
  have : 0 < 1 + φ * k := by positivity
  have : 0 < 1 + φ * (k + 1) := by positivity
  field_simp
  ring

/-- **The period hazard ratio of two log-logistic laws in closed form.** The law with
acceleration factor `φ > 0` against the reference law (`φ = 1`): at every time `k ≥ 1` the hazard
ratio is `φ (k + 1) / (1 + φ k)`. At `k = 0` both hazards are zero. -/
theorem llTime_hazardRatio {φ : ℝ} (hφ : 0 < φ) (k : ℕ) (hk : 1 ≤ k) :
    hazardRatio llSpace (llTime φ) llSpace (llTime 1) k = φ * (k + 1) / (1 + φ * k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [hazardRatio, llTime_hazard hφ, llTime_hazard one_pos]
  push_cast
  have : 0 < 1 + φ * (j + 1) := by positivity
  have : (0 : ℝ) < 1 + 1 * (j + 1) := by positivity
  field_simp
  ring

/-- **The log-logistic hazard ratio tends to one**: for every `φ > 0`, the period hazard ratio
`h_φ(k) / h_1(k)` tends to `1` as `k → ∞`. -/
theorem tendsto_llTime_hazardRatio {φ : ℝ} (hφ : 0 < φ) :
    Tendsto (hazardRatio llSpace (llTime φ) llSpace (llTime 1)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => 1 + (φ - 1) / (1 + φ * k)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hφ)))
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [llTime_hazardRatio hφ k hk]
  have : 0 < 1 + φ * k := by positivity
  field_simp
  ring

/-- **The log-logistic hazard ratio is not constant**: for `φ > 0`, `φ ≠ 1`, the hazard ratios
at times `1` and `2`, `2 φ / (1 + φ)` and `3 φ / (1 + 2 φ)`, differ. -/
theorem llTime_hazardRatio_ne {φ : ℝ} (hφ : 0 < φ) (h1 : φ ≠ 1) :
    hazardRatio llSpace (llTime φ) llSpace (llTime 1) 1 ≠
      hazardRatio llSpace (llTime φ) llSpace (llTime 1) 2 := by
  rw [llTime_hazardRatio hφ 1 le_rfl, llTime_hazardRatio hφ 2 (by norm_num)]
  push_cast
  intro h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have : φ * (φ - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · exact hφ.ne' h'
  · exact h1 (by linarith)

/-- No exponent `c` gives `(1/2) ^ c = 1/3` and `(1/3) ^ c = 1/5`: the first forces `c > 3/2`,
hence `(1/3) ^ c < 1/5`. -/
theorem no_rpow_half_third {c : ℝ} (h1 : (1 / 2 : ℝ) ^ c = 1 / 3)
    (h2 : (1 / 3 : ℝ) ^ c = 1 / 5) : False := by
  rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow] at h1 h2
  have h1' : (2 : ℝ) ^ c = 3 := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) c
    field_simp at h1; linarith
  have h2' : (3 : ℝ) ^ c = 5 := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 3 by norm_num) c
    field_simp at h2; linarith
  have hc : 3 / 2 < c := by
    by_contra hle
    push Not at hle
    have hm : (2 : ℝ) ^ c ≤ 2 ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
    have hsq : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
      rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
    have : (3 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 :=
      calc (3 : ℝ) ^ 2 = ((2 : ℝ) ^ c) ^ 2 := by rw [h1']
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hm 2
    rw [hsq] at this
    norm_num at this
  have hm : (3 : ℝ) ^ (3 / 2 : ℝ) < 3 ^ c := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hc
  have hsq : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 27 := by
    rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
  have : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 < (5 : ℝ) ^ 2 := by
    rw [← h2']; exact pow_lt_pow_left₀ hm (by positivity) (by norm_num)
  rw [hsq] at this
  norm_num at this

/-- **An accelerated failure time family on the full grid has no single hazard ratio** (NICE
DSU TSD 14, Section 2.9). The log-logistic laws `S₀(k) = 1 / (1 + k)` and `S₁(k) = 1 / (1 + 2 k)`
at every `k : ℕ`: the hazard ratio at time `k ≥ 1` is `2 (k + 1) / (1 + 2 k)`, equal to `4/3` at
time `1` and `6/5` at time `2`, and tends to `1`; there is no exponent `c` with
`S₁ m = S₀ m ^ c` for `m ≤ 2`. -/
theorem logLogistic_fullGrid :
    (∀ k : ℕ, 1 ≤ k → hazardRatio llSpace (llTime 2) llSpace (llTime 1) k =
      2 * (k + 1) / (1 + 2 * k)) ∧
      hazardRatio llSpace (llTime 2) llSpace (llTime 1) 1 = 4 / 3 ∧
      hazardRatio llSpace (llTime 2) llSpace (llTime 1) 2 = 6 / 5 ∧
      Tendsto (hazardRatio llSpace (llTime 2) llSpace (llTime 1)) atTop (𝓝 1) ∧
      ¬ ∃ c : ℝ, ∀ m ≤ 2, survival llSpace (llTime 2) m = survival llSpace (llTime 1) m ^ c := by
  refine ⟨fun k hk => llTime_hazardRatio two_pos k hk, ?_, ?_,
    tendsto_llTime_hazardRatio two_pos, ?_⟩
  · rw [llTime_hazardRatio two_pos 1 le_rfl]; norm_num
  · rw [llTime_hazardRatio two_pos 2 (by norm_num)]; norm_num
  · rintro ⟨c, hc⟩
    have h1 := hc 1 (by norm_num)
    have h2 := hc 2 le_rfl
    rw [llTime_survival two_pos, llTime_survival one_pos] at h1 h2
    norm_num at h1 h2
    exact no_rpow_half_third (c := c) h1.symm h2.symm

end PropHazardsExample

end Survival

end CausalInference
