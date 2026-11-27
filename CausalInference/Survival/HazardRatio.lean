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
  `0 < h < 1`. `PropHazardsExample.constant_hazardRatio_no_power`: a hazard ratio equal to
  `1/2` at every time with positive reference hazard, and no exponent `c` at all with
  `S₁ = S₀ ^ c`. `PropHazardsExample.logLogistic_hazardRatio_varies`: two log-logistic laws
  with acceleration factor `2`, sampled on the grid, have hazard ratio `4/3` at time `1` and
  `6/5` at time `2` and no exponent `c`: an accelerated failure time family without
  proportional hazards.
* Duration of treatment effect. `survival_mul_eq_of_hazard_eq`: if the hazards agree after
  `t₀`, then `S₁ k * S₀ t₀ = S₀ k * S₁ t₀` for `k ≥ t₀` (the survival ratio is frozen at its
  value at `t₀`; ratio form `survival_div_eq_of_hazard_eq`). `sum_survival_sub_of_hazard_eq`:
  the area between the curves over `t₀, …, K` is `(S₁ t₀ / S₀ t₀ - 1) ∑ S₀`.
  `survival_mul_le_of_hazard_le` and `survival_le_of_maintained`: a maintained effect (hazard
  at most the reference after `t₀`) gives at least the survival of a stopped one.
  `PropHazardsExample.duration_not_identified`: two treated laws that agree up to `t₀ = 1` and
  differ afterwards, so follow-up to `t₀` does not determine the duration of the effect.
* Non-collapsibility. With a common stratum hazard ratio `ψ` at both periods and a frailty
  independent of treatment (`phRisk`): `hazard1_phRisk` (the marginal period `1` hazard ratio
  is `ψ`), `stratumHazard2_phRisk` (the stratum period `2` hazard ratios are `ψ`),
  `hazard2_phRisk_eq_iff` (the marginal period `2` hazard ratio equals `ψ` if and only if
  `ψ = 1`, or the frailty leaves the period `1` risk unchanged, or it leaves the period `2`
  risk unchanged), and `hazard2_phRisk_isCollapsible_iff` (the same condition characterizes
  `EffectMeasure.IsCollapsible` for the period `2` hazard ratio).
  `PropHazardsExample.noncollapsible_example`: stratum hazard ratio `1/2` at both periods,
  marginal hazard ratio `1/2` at period `1` and `329/578` at period `2`.
* Scale-dependent effect modification. `cumHazard` (`H = -log S`), `cumHazard_succ_sub`
  (its increment is `-log (1 - h)`), and `cloglogRatio_eq_iff`: in a model additive in two
  binary covariates on the log cumulative hazard scale with time-varying coefficients, the
  grouped-time hazard ratio for one covariate over an interval does not depend on the other
  if and only if one of the two coefficients is constant over that interval
  (`incrementRatio_eq_iff` is the algebra). `PropHazardsExample.scaleDependence_example`: four
  laws satisfying the model with both coefficients changing, for which the ratio depends on the
  other covariate.

The notion of hazard ratio differs between the sections. The power relation section shows
that in discrete time proportional hazards in the sense of `S₁ = S₀ ^ c` is not a constant
ratio of the hazards `h`. The non-collapsibility section uses the ratio of the discrete
hazards themselves (`hazardRatio`, `hazard1`, `hazard2`): a common stratum ratio `ψ` of the
period risks. Its period `1` collapsibility holds because the period `1` hazard is a risk; the
corresponding statement for a common power `c` on the survival scale is not treated.

## Sources

* NICE DSU Technical Support Document 14, N. Latimer, *Survival analysis for economic
  evaluations alongside clinical trials: extrapolation with patient-level data* (2011, updated
  2013), Section 2.9 (a single hazard ratio requires proportional hazards; the duration of
  treatment effect assumption should be justified) and Section 4.1.3 (without a stated
  duration of effect the trial hazard ratio is implicitly assumed to last for the whole model
  horizon).
* NICE DSU Technical Support Document 19, H. Woods, E. Sideris, S. Palmer, N. Latimer,
  M. Soares (2017), on partitioned survival analysis, Section 3.2.5 (equal hazards between
  arms from a time point on).
* NICE DSU Technical Support Document 21, M. J. Rutherford, P. C. Lambert, M. J. Sweeting,
  B. Pennington, M. J. Crowther, K. R. Abrams, N. R. Latimer, *Flexible methods for survival
  analysis* (2020), Section 3.2.3 (with multiple time-dependent effects the hazard ratio for one
  covariate depends on another without an interaction) and Section 5.2.1, Equation 17 (data
  simulated under proportional hazards conditional on a frailty `Z`).
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
frailty independent of treatment, the marginal period `1` hazards satisfy `h₁ = ψ * h₀`. -/
theorem hazard1_phRisk (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u) :
    hazard1 pA pU (phRisk ψ b₁) true = ψ * hazard1 pA pU (phRisk ψ b₁) false := by
  have := hA true; have := hA false; have := hU true; have := hU false
  simp only [hazard1, dead1Mass, armMass, phRisk, Fintype.sum_bool, ite_true,
    Bool.false_eq_true, ite_false]
  field_simp

/-- Within each frailty stratum the period `2` hazard ratio is `ψ`. -/
theorem stratumHazard2_phRisk (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hs : ∀ a u, 0 < 1 - phRisk ψ b₁ a u) (u : Bool) :
    stratumHazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) true u =
      ψ * stratumHazard2 pA pU (phRisk ψ b₁) (phRisk ψ b₂) false u := by
  have h : ∀ a, pA a * pU u * (1 - phRisk ψ b₁ a u) ≠ 0 := fun a => by
    have := hA a; have := hU u; have := hs a u; positivity
  rw [stratumHazard2_eq _ _ _ _ _ _ (h true), stratumHazard2_eq _ _ _ _ _ _ (h false)]
  simp [phRisk]

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

/-- **Non-collapsibility of the hazard ratio** (NICE DSU TSD 21, Section 5.2.1, Equation 17,
generates conditional proportional hazards given a frailty while the fitted models are
marginal). In the two-period model of `CausalInference.Bias.HazardRatio` with a frailty `U`
independent of treatment, positive arm and frailty probabilities, positive period `1` survival
in every cell, and a common stratum hazard ratio `ψ > 0` at both periods (untreated stratum
risks `c₁ u`, `c₂ u`; treated `ψ * c₁ u`, `ψ * c₂ u`), the marginal period `1` hazard ratio is
`ψ` (`hazard1_phRisk`), and the marginal period `2` hazards satisfy `h₁(2) = ψ * h₀(2)` if and
only if `ψ = 1` (no effect), or the frailty does not change the period `1` risk
(`c₁ 1 = c₁ 0`), or it does not change the period `2` risk (`c₂ 1 = c₂ 0`). In every other
case the marginal hazard ratio differs from the common stratum hazard ratio at period `2` and
is not constant in time. -/
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
`z` does not (`C₁ = C₀`). The positivity hypotheses make every logarithm and every ratio a
genuine one. -/
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
`1/2` throughout. -/
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

end Survival

end CausalInference
