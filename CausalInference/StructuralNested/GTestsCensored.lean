/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.GTestsExamples
public import CausalInference.Survival.Recensoring

/-!
# Rank-based g-statistics with right censoring

The statistics of `CausalInference.StructuralNested.GTest` on right-censored samples: each
patient is a pair `(x, δ)` of an observed time and an event indicator. The risk set at `t` counts
every patient with `x ≥ t`; the events at `t` count the patients with `x = t` and `δ = true`. The
sum runs over the distinct observed times; times with no event contribute zero.

## Main definitions

* `GTest.atRiskC`, `GTest.deathsC`, `GTest.oeC`, `GTest.weightedLogRankC`, `GTest.logRankC`:
  the censored versions of the counts and statistics.
* `GTest.propOnTreatment`, `GTest.switchWeight`, `GTest.switchWeighted`: a weighted log-rank
  statistic whose weight at `t` is the difference between the two arms of the proportions of the
  patients at risk who are on the experimental treatment at `t`.
* `GTest.recensoredGStat`, `GTest.naiveGStat`: a censored statistic evaluated, at a candidate
  `ψ`, on the recensored records (`CensoredTrial.recensored`) or on the transformed times with
  the original event indicators (`CensoredTrial.naive`).

## Main results

* `weightedLogRankC_uncensored`: when every indicator is `true` the censored statistic is the
  uncensored one of `GTest`.
* `weightedLogRankC_swap`: antisymmetry; `weightedLogRankC_eq_zero_of_equiv`: zero for equal
  samples.
* `switchWeighted_swap`: the switching-weighted statistic is **symmetric**, not antisymmetric,
  under swapping the arms: the weight changes sign together with observed minus expected.
* `switchWeighted_eq_zero_of_equiv`: zero for equal samples.
* `absSwitchWeighted_swap`, `absSwitchWeighted_eq_zero_of_equiv`: the unsigned reading (absolute
  value of the difference of proportions) is antisymmetric and zero for equal samples;
  `SwitchExample.abs_sign_pattern`: it has the sign pattern of the log-rank statistic there.
* `switchGStat`: the switching-weighted g-statistic at a candidate `ψ`, on the recensored
  candidate records with the treatment status `statusAt ψ` on the scale of `U(ψ)`;
  `switchGStat_congr`: a function of the observed records `CensoredTrial.pathRecord` and `ψ`;
  `switchGStat_eq_of_constant`: with paths that are empty or the whole follow-up it is
  `switchWeighted` with constant status.
* `SwitchExample.sign_pattern`: on the candidate untreated times of
  `GTestExample.NoRoot` the log-rank statistic is positive at `ψ = log (1/4)` and negative at
  `ψ = log 2`, while the switching-weighted statistic is negative and positive.
* `recensoredGStat_congr`: the recensored g-statistic depends only on the observed records of the
  sampled patients and on `ψ`.
* `RecensoringExample.differ`: a trial with two patients in which the log-rank statistic on the
  recensored records is `0` and on the naive records `-1/2`, at the true parameter.

## The weights of Bowden et al.

TSD 24, Section 4.2.1.1, describes these weights only as "derived from the proportions of trial
participants on the experimental treatment in each trial arm over time". `switchWeight` is a
reading of that description, not a formula printed in the document: the proportion on the
experimental treatment among those at risk in the experimental arm minus the same proportion in
the control arm. In a g-test the statistic is computed on the time scale of the candidate
untreated times `U(ψ)`, so the risk sets are those of the candidate untreated times at `ψ` and
the treatment status at a time `u` of that scale is the status at the original time `s` with
`untreatedTime ψ A s = u`; the weight then depends on `ψ`. `switchWeighted` takes the samples
and the status functions on the scale on which it is computed, so in a g-test both are those at
the candidate `ψ`.

## Sources

N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16* (2014), Appendix A;
H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24* (2024),
Sections 4.2.1 and 4.2.1.1.
-/

@[expose] public section

open Finset

namespace CausalInference

namespace StructuralNested

namespace GTest

variable {m n : ℕ}

/-- The observed times of a censored sample. -/
def times (S : Fin m → ℝ × Bool) : Fin m → ℝ := fun i ↦ (S i).1

open Classical in
/-- The number at risk at `t` in a censored sample: the patients with observed time `≥ t`. -/
noncomputable def atRiskC (S : Fin m → ℝ × Bool) (t : ℝ) : ℕ := #{i | t ≤ (S i).1}

open Classical in
/-- The number of events at `t` in a censored sample: observed time `t` and indicator `true`. -/
noncomputable def deathsC (S : Fin m → ℝ × Bool) (t : ℝ) : ℕ :=
  #{i | (S i).1 = t ∧ (S i).2 = true}

/-- Observed minus expected events in the experimental arm at `t`, for censored samples. -/
noncomputable def oeC (E : Fin m → ℝ × Bool) (C : Fin n → ℝ × Bool) (t : ℝ) : ℝ :=
  deathsC E t - (deathsC E t + deathsC C t) * atRiskC E t / (atRiskC E t + atRiskC C t)

/-- **The weighted log-rank statistic for censored samples**, summed over the distinct observed
times. -/
noncomputable def weightedLogRankC (W : ℝ → ℝ) (E : Fin m → ℝ × Bool) (C : Fin n → ℝ × Bool) :
    ℝ :=
  ∑ t ∈ eventTimes (times E) (times C), W t * oeC E C t

/-- **The log-rank statistic for censored samples.** -/
noncomputable def logRankC (E : Fin m → ℝ × Bool) (C : Fin n → ℝ × Bool) : ℝ :=
  weightedLogRankC (fun _ ↦ 1) E C

/-- An uncensored sample as a censored one: every indicator is `true`. -/
def uncensored (S : Fin m → ℝ) : Fin m → ℝ × Bool := fun i ↦ (S i, true)

theorem atRiskC_eq (S : Fin m → ℝ × Bool) (t : ℝ) : atRiskC S t = atRisk (times S) t := rfl

theorem deathsC_uncensored (S : Fin m → ℝ) (t : ℝ) : deathsC (uncensored S) t = deaths S t := by
  simp [deathsC, deaths, uncensored]

/-- **Reduction to the uncensored statistic** when every indicator is `true`. -/
theorem weightedLogRankC_uncensored (W : ℝ → ℝ) (E : Fin m → ℝ) (C : Fin n → ℝ) :
    weightedLogRankC W (uncensored E) (uncensored C) = weightedLogRank W E C := by
  simp only [weightedLogRankC, weightedLogRank, oeC, oe, deathsC_uncensored, atRiskC_eq]
  rfl

theorem logRankC_uncensored (E : Fin m → ℝ) (C : Fin n → ℝ) :
    logRankC (uncensored E) (uncensored C) = logRank E C :=
  weightedLogRankC_uncensored _ E C

theorem deathsC_le_atRiskC (S : Fin m → ℝ × Bool) (t : ℝ) : deathsC S t ≤ atRiskC S t := by
  classical
  unfold deathsC atRiskC
  exact card_le_card fun i ↦ by
    simp only [mem_filter, mem_univ, true_and]; rintro ⟨h, -⟩; rw [h]

theorem oeC_swap (E : Fin m → ℝ × Bool) (C : Fin n → ℝ × Bool) (t : ℝ) :
    oeC C E t = -oeC E C t := by
  unfold oeC
  by_cases h : (atRiskC E t : ℝ) + atRiskC C t = 0
  · have h1 := Nat.cast_nonneg (α := ℝ) (atRiskC E t)
    have h2 := Nat.cast_nonneg (α := ℝ) (atRiskC C t)
    have hE : atRiskC E t = 0 := by exact_mod_cast (show (atRiskC E t : ℝ) = 0 by linarith)
    have hC : atRiskC C t = 0 := by exact_mod_cast (show (atRiskC C t : ℝ) = 0 by linarith)
    have dE := Nat.eq_zero_of_le_zero (hE ▸ deathsC_le_atRiskC E t)
    have dC := Nat.eq_zero_of_le_zero (hC ▸ deathsC_le_atRiskC C t)
    simp [hE, hC, dE, dC]
  · have h' : (atRiskC C t : ℝ) + atRiskC E t ≠ 0 := by rwa [add_comm]
    field_simp
    ring

/-- **Antisymmetry with censoring.** -/
theorem weightedLogRankC_swap (W : ℝ → ℝ) (E : Fin m → ℝ × Bool) (C : Fin n → ℝ × Bool) :
    weightedLogRankC W C E = -weightedLogRankC W E C := by
  rw [weightedLogRankC, weightedLogRankC, eventTimes_swap, ← sum_neg_distrib]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [oeC_swap, mul_neg]

/-- **Equal censored samples give zero.** If `C (σ i) = E i` for a bijection `σ` (same times and
same indicators), every weighted log-rank statistic is zero. -/
theorem weightedLogRankC_eq_zero_of_equiv (W : ℝ → ℝ) (E : Fin m → ℝ × Bool)
    (C : Fin n → ℝ × Bool) (σ : Fin m ≃ Fin n) (hσ : ∀ i, C (σ i) = E i) :
    weightedLogRankC W E C = 0 := by
  classical
  have hr : ∀ t, atRiskC C t = atRiskC E t := fun t ↦
    (card_equiv σ fun i ↦ by simp [hσ]).symm
  have hd : ∀ t, deathsC C t = deathsC E t := fun t ↦
    (card_equiv σ fun i ↦ by simp [hσ]).symm
  refine sum_eq_zero fun t _ ↦ ?_
  rw [oeC, hr, hd]
  by_cases h : atRiskC E t = 0
  · simp [h, Nat.eq_zero_of_le_zero (h ▸ deathsC_le_atRiskC E t)]
  · have : (atRiskC E t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h
    have : (atRiskC E t : ℝ) + atRiskC E t ≠ 0 := by positivity
    field_simp
    ring

/-! ### Weights from the proportions on the experimental treatment -/

open Classical in
/-- The number of patients at risk at `t` who are on the experimental treatment at `t`. -/
noncomputable def onTreatment (S : Fin m → ℝ × Bool) (Z : Fin m → ℝ → Bool) (t : ℝ) : ℕ :=
  #{i | t ≤ (S i).1 ∧ Z i t = true}

/-- The proportion of the patients at risk at `t` who are on the experimental treatment at `t`
(status `Z i t`); `0` if nobody is at risk. -/
noncomputable def propOnTreatment (S : Fin m → ℝ × Bool) (Z : Fin m → ℝ → Bool) (t : ℝ) : ℝ :=
  (onTreatment S Z t : ℝ) / atRiskC S t

/-- The weight at `t`: the proportion on the experimental treatment among those at risk in the
experimental arm minus that in the control arm. This is a reading of the description of the
weights of Bowden et al. in TSD 24, Section 4.2.1.1, not a formula printed there. The signed
weight loses the direction of the comparison: the resulting statistic is symmetric in the arms
(`switchWeighted_swap`), so its sign does not say which arm does better. The unsigned reading
`absSwitchWeight` keeps it (`absSwitchWeighted_swap`). -/
noncomputable def switchWeight (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) (t : ℝ) : ℝ :=
  propOnTreatment E ZE t - propOnTreatment C ZC t

/-- The weighted log-rank statistic with the weights `switchWeight`. -/
noncomputable def switchWeighted (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) : ℝ :=
  weightedLogRankC (switchWeight E ZE C ZC) E C

/-- **Symmetry, not antisymmetry.** Swapping the arms (with their treatment status) changes the
sign of the weight and of observed minus expected, so the statistic is unchanged. -/
theorem switchWeighted_swap (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) :
    switchWeighted C ZC E ZE = switchWeighted E ZE C ZC := by
  rw [switchWeighted, switchWeighted, weightedLogRankC, weightedLogRankC, eventTimes_swap]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [oeC_swap, switchWeight, switchWeight]
  ring

/-- **Equal samples give zero**, whatever the treatment status. -/
theorem switchWeighted_eq_zero_of_equiv (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) (σ : Fin m ≃ Fin n)
    (hσ : ∀ i, C (σ i) = E i) : switchWeighted E ZE C ZC = 0 :=
  weightedLogRankC_eq_zero_of_equiv _ E C σ hσ

/-- With equal samples and equal treatment status the weight itself is zero. -/
theorem switchWeight_eq_zero_of_equiv (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) (σ : Fin m ≃ Fin n)
    (hσ : ∀ i, C (σ i) = E i) (hZ : ∀ i, ZC (σ i) = ZE i) (t : ℝ) :
    switchWeight E ZE C ZC t = 0 := by
  classical
  have hr : atRiskC C t = atRiskC E t := (card_equiv σ fun i ↦ by simp [hσ]).symm
  have hn : onTreatment C ZC t = onTreatment E ZE t :=
    (card_equiv σ fun i ↦ by simp [hσ, hZ]).symm
  rw [switchWeight, propOnTreatment, propOnTreatment, hr, hn, sub_self]

/-- **The unsigned reading of the weights**: the absolute value of the difference between the two
arms of the proportions on the experimental treatment among those at risk. This is also a
reading of the description in TSD 24, Section 4.2.1.1, not a formula printed there. -/
noncomputable def absSwitchWeight (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) (t : ℝ) : ℝ :=
  |propOnTreatment E ZE t - propOnTreatment C ZC t|

/-- The weighted log-rank statistic with the weights `absSwitchWeight`. -/
noncomputable def absSwitchWeighted (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) : ℝ :=
  weightedLogRankC (absSwitchWeight E ZE C ZC) E C

/-- **The unsigned version is antisymmetric**: its weight does not depend on the order of the
arms, so swapping the arms changes the sign of the statistic. -/
theorem absSwitchWeighted_swap (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) :
    absSwitchWeighted C ZC E ZE = -absSwitchWeighted E ZE C ZC := by
  have hw : absSwitchWeight C ZC E ZE = absSwitchWeight E ZE C ZC :=
    funext fun _ ↦ abs_sub_comm _ _
  rw [absSwitchWeighted, absSwitchWeighted, hw, weightedLogRankC_swap]

/-- The unsigned version is zero for equal samples, whatever the treatment status. -/
theorem absSwitchWeighted_eq_zero_of_equiv (E : Fin m → ℝ × Bool) (ZE : Fin m → ℝ → Bool)
    (C : Fin n → ℝ × Bool) (ZC : Fin n → ℝ → Bool) (σ : Fin m ≃ Fin n)
    (hσ : ∀ i, C (σ i) = E i) : absSwitchWeighted E ZE C ZC = 0 :=
  weightedLogRankC_eq_zero_of_equiv _ E C σ hσ

/-- The switching-weighted statistics use the treatment status only at the event times at which
the patient is at risk. -/
theorem onTreatment_congr {S : Fin m → ℝ × Bool} {Z Z' : Fin m → ℝ → Bool} {t : ℝ}
    (h : ∀ i, t ≤ (S i).1 → Z i t = Z' i t) : onTreatment S Z t = onTreatment S Z' t := by
  classical
  unfold onTreatment
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun hi ↦ by rw [h i hi]

theorem switchWeighted_congr_status {E : Fin m → ℝ × Bool} {ZE ZE' : Fin m → ℝ → Bool}
    {C : Fin n → ℝ × Bool} {ZC ZC' : Fin n → ℝ → Bool}
    (hE : ∀ t ∈ eventTimes (times E) (times C), ∀ i, t ≤ (E i).1 → ZE i t = ZE' i t)
    (hC : ∀ t ∈ eventTimes (times E) (times C), ∀ j, t ≤ (C j).1 → ZC j t = ZC' j t) :
    switchWeighted E ZE C ZC = switchWeighted E ZE' C ZC' := by
  rw [switchWeighted, switchWeighted, weightedLogRankC, weightedLogRankC]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [switchWeight, switchWeight, propOnTreatment, propOnTreatment, propOnTreatment,
    propOnTreatment, onTreatment_congr (hE t ht), onTreatment_congr (hC t ht)]

theorem atRiskC_eq_sum (S : Fin m → ℝ × Bool) (t : ℝ) :
    (atRiskC S t : ℝ) = ∑ i, if t ≤ (S i).1 then 1 else 0 := by
  classical
  rw [atRiskC, card_filter]; push_cast; rfl

theorem deathsC_eq_sum (S : Fin m → ℝ × Bool) (t : ℝ) :
    (deathsC S t : ℝ) = ∑ i, if (S i).1 = t ∧ (S i).2 = true then 1 else 0 := by
  classical
  rw [deathsC, card_filter]; push_cast; rfl

theorem onTreatment_eq_sum (S : Fin m → ℝ × Bool) (Z : Fin m → ℝ → Bool) (t : ℝ) :
    (onTreatment S Z t : ℝ) = ∑ i, if t ≤ (S i).1 ∧ Z i t = true then 1 else 0 := by
  classical
  rw [onTreatment, card_filter]; push_cast; rfl

namespace SwitchExample

/-- The candidate untreated times of `GTestExample.NoRoot` at `ψ = log (1/4)`, uncensored. -/
noncomputable def expLow : Fin 2 → ℝ × Bool := ![(1 / 4, true), (1 / 2, true)]

/-- The candidate untreated times of `GTestExample.NoRoot` at `ψ = log 2`, uncensored. -/
noncomputable def expHigh : Fin 2 → ℝ × Bool := ![(2, true), (4, true)]

/-- The control patient of `GTestExample.NoRoot`. -/
noncomputable def ctrl : Fin 1 → ℝ × Bool := ![(1, true)]

/-- Treatment status: the first experimental patient is on the experimental treatment, the
second is not; the control patient is on it (a switcher). -/
def statusE : Fin 2 → ℝ → Bool := ![fun _ ↦ true, fun _ ↦ false]

/-- The control patient switched to the experimental treatment. -/
def statusC : Fin 1 → ℝ → Bool := ![fun _ ↦ true]

theorem expLow_eq : (fun i ↦ (untreated (Real.log (1 / 4)) (GTestExample.NoRoot.expSample i),
    true)) = expLow := by
  funext i
  fin_cases i <;> norm_num [untreated, GTestExample.NoRoot.expSample, expLow,
    Real.exp_log (show (0 : ℝ) < 1 / 4 by norm_num)]

theorem expHigh_eq : (fun i ↦ (untreated (Real.log 2) (GTestExample.NoRoot.expSample i),
    true)) = expHigh := by
  funext i
  fin_cases i <;> norm_num [untreated, GTestExample.NoRoot.expSample, expHigh,
    Real.exp_log (show (0 : ℝ) < 2 by norm_num)]

theorem ctrl_eq (ψ : ℝ) :
    (fun j ↦ (untreated ψ (GTestExample.NoRoot.ctrlSample j), true)) = ctrl := by
  funext j
  fin_cases j
  simp [untreated, GTestExample.NoRoot.ctrlSample, ctrl]

theorem logRank_low : logRankC expLow ctrl = 5 / 6 := by
  rw [logRankC, weightedLogRankC, sum_eventTimes_eq]
  simp only [oeC, atRiskC_eq_sum, deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_two,
    Fin.sum_univ_one, times, expLow, ctrl]
  norm_num

theorem logRank_high : logRankC expHigh ctrl = -2 / 3 := by
  rw [logRankC, weightedLogRankC, sum_eventTimes_eq]
  simp only [oeC, atRiskC_eq_sum, deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_two,
    Fin.sum_univ_one, times, expHigh, ctrl]
  norm_num

theorem switch_low : switchWeighted expLow statusE ctrl statusC = -2 / 3 := by
  rw [switchWeighted, weightedLogRankC, sum_eventTimes_eq]
  simp only [switchWeight, propOnTreatment, onTreatment_eq_sum, oeC, atRiskC_eq_sum,
    deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_two, Fin.sum_univ_one, times, expLow, ctrl,
    statusE, statusC]
  norm_num

theorem switch_high : switchWeighted expHigh statusE ctrl statusC = 1 / 3 := by
  rw [switchWeighted, weightedLogRankC, sum_eventTimes_eq]
  simp only [switchWeight, propOnTreatment, onTreatment_eq_sum, oeC, atRiskC_eq_sum,
    deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_two, Fin.sum_univ_one, times, expHigh, ctrl,
    statusE, statusC]
  norm_num

theorem abs_low : absSwitchWeighted expLow statusE ctrl statusC = 2 / 3 := by
  rw [absSwitchWeighted, weightedLogRankC, sum_eventTimes_eq]
  simp only [absSwitchWeight, propOnTreatment, onTreatment_eq_sum, oeC, atRiskC_eq_sum,
    deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_two, Fin.sum_univ_one, times, expLow, ctrl,
    statusE, statusC]
  norm_num [abs_div]

theorem abs_high : absSwitchWeighted expHigh statusE ctrl statusC = -1 / 3 := by
  rw [absSwitchWeighted, weightedLogRankC, sum_eventTimes_eq]
  simp only [absSwitchWeight, propOnTreatment, onTreatment_eq_sum, oeC, atRiskC_eq_sum,
    deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_two, Fin.sum_univ_one, times, expHigh, ctrl,
    statusE, statusC]
  norm_num [abs_div]

/-- **The unsigned version keeps the direction.** On the same samples it is positive at
`ψ = log (1/4)` and negative at `ψ = log 2`, with the sign pattern of the log-rank statistic,
where the signed version has the opposite pattern (`sign_pattern`). -/
theorem abs_sign_pattern :
    0 < absSwitchWeighted expLow statusE ctrl statusC ∧
      absSwitchWeighted expHigh statusE ctrl statusC < 0 := by
  rw [abs_low, abs_high]
  norm_num

/-- **A different sign pattern.** At `ψ = log (1/4)` and `ψ = log 2` the log-rank statistic is
positive then negative, the switching-weighted statistic negative then positive. -/
theorem sign_pattern :
    0 < logRankC expLow ctrl ∧ logRankC expHigh ctrl < 0 ∧
      switchWeighted expLow statusE ctrl statusC < 0 ∧
      0 < switchWeighted expHigh statusE ctrl statusC := by
  rw [logRank_low, logRank_high, switch_low, switch_high]
  norm_num

end SwitchExample

/-! ### The g-statistic with recensoring -/

section Recensoring

variable {Ω : Type*}

/-- The g-statistic on recensored records: a censored two-sample statistic evaluated at `ψ` on
the recensored records of the sampled experimental patients `pE` and control patients `pC`. -/
noncomputable def recensoredGStat (stat : (Fin m → ℝ × Bool) → (Fin n → ℝ × Bool) → ℝ)
    (M : CensoredTrial Ω) (pE : Fin m → Ω) (pC : Fin n → Ω) (ψ : ℝ) : ℝ :=
  stat (fun i ↦ M.recensored ψ (pE i)) (fun j ↦ M.recensored ψ (pC j))

/-- The g-statistic without recensoring: the transformed follow-up with the original event
indicators. -/
noncomputable def naiveGStat (stat : (Fin m → ℝ × Bool) → (Fin n → ℝ × Bool) → ℝ)
    (M : CensoredTrial Ω) (pE : Fin m → Ω) (pC : Fin n → Ω) (ψ : ℝ) : ℝ :=
  stat (fun i ↦ M.naive ψ (pE i)) (fun j ↦ M.naive ψ (pC j))

/-- **The recensored g-statistic is a function of the observed data and `ψ`.** Two samples
(possibly from different trials) whose patients have the same observed records give the same
value, whatever their latent survival and untreated times. -/
theorem recensoredGStat_congr {Ω' : Type*} (stat : (Fin m → ℝ × Bool) → (Fin n → ℝ × Bool) → ℝ)
    {M : CensoredTrial Ω} {M' : CensoredTrial Ω'} {pE : Fin m → Ω} {pC : Fin n → Ω}
    {pE' : Fin m → Ω'} {pC' : Fin n → Ω'} (hE : ∀ i, M.observed (pE i) = M'.observed (pE' i))
    (hC : ∀ j, M.observed (pC j) = M'.observed (pC' j)) (ψ : ℝ) :
    recensoredGStat stat M pE pC ψ = recensoredGStat stat M' pE' pC' ψ := by
  have key : ∀ ω ω', M.observed ω = M'.observed ω' → M.recensored ψ ω = M'.recensored ψ ω' :=
    fun ω ω' h ↦ by
      rw [congrFun (CensoredTrial.recensored_eq_comp_observed M ψ) ω,
        congrFun (CensoredTrial.recensored_eq_comp_observed M' ψ) ω', Function.comp_apply,
        Function.comp_apply, h]
  have e1 : (fun i ↦ M.recensored ψ (pE i)) = fun i ↦ M'.recensored ψ (pE' i) :=
    funext fun i ↦ key _ _ (hE i)
  have e2 : (fun j ↦ M.recensored ψ (pC j)) = fun j ↦ M'.recensored ψ (pC' j) :=
    funext fun j ↦ key _ _ (hC j)
  rw [recensoredGStat, recensoredGStat, e1, e2]

/-! ### The switching-weighted g-statistic at a candidate `ψ` -/

open Classical in
/-- **Treatment status on the scale of the candidate untreated time.** A patient with observed
treatment path `B` is on the experimental treatment at the time `u` of the scale of `U(ψ)` when
`u = untreatedTime ψ B s` for an original time `s ∈ B`. For a measurable path that `s` is unique,
since `untreatedTime ψ B` is strictly increasing (`untreatedTime_strictMono`). The status is
defined here directly from the path. -/
noncomputable def statusAt (ψ : ℝ) (B : Set ℝ) (u : ℝ) : Bool :=
  decide (∃ s ∈ B, untreatedTime ψ B s = u)

/-- The candidate record at `ψ` of an observed record `(x, δ, B, c)`: follow-up `x`, event
indicator `δ`, observed treatment path `B` and administrative censoring time `c`. It is the
recensored record, computed with the time `timeOn B x` on treatment. -/
noncomputable def candidateRecord (ψ : ℝ) (r : ℝ × Bool × Set ℝ × ℝ) : ℝ × Bool :=
  recensorData ψ r.1 r.2.1 (timeOn r.2.2.1 r.1) r.2.2.2

/-- **The switching-weighted g-statistic at a candidate `ψ`**: the statistic `switchWeighted` on
the candidate records, with the risk sets of the candidate records and the treatment status
`statusAt ψ` on the scale of `U(ψ)`. It is defined on the observed records, so it is a function
of the observed records and `ψ`. -/
noncomputable def switchGStat (E : Fin m → ℝ × Bool × Set ℝ × ℝ)
    (C : Fin n → ℝ × Bool × Set ℝ × ℝ) (ψ : ℝ) : ℝ :=
  switchWeighted (fun i ↦ candidateRecord ψ (E i)) (fun i ↦ statusAt ψ (E i).2.2.1)
    (fun j ↦ candidateRecord ψ (C j)) (fun j ↦ statusAt ψ (C j).2.2.1)

/-- The observed record of a patient of a censored trial: follow-up, event indicator, treatment
path up to the follow-up, administrative censoring time. Every component is observed. -/
noncomputable def _root_.CausalInference.StructuralNested.CensoredTrial.pathRecord
    (M : CensoredTrial Ω) (ω : Ω) : ℝ × Bool × Set ℝ × ℝ :=
  (M.obsTime ω, M.event ω, M.A ω ∩ Set.Iic (M.obsTime ω), M.C ω)

/-- **The switching-weighted g-statistic is a function of the observed records and `ψ`.** -/
theorem switchGStat_congr {Ω' : Type*} {M : CensoredTrial Ω} {M' : CensoredTrial Ω'}
    {pE : Fin m → Ω} {pC : Fin n → Ω} {pE' : Fin m → Ω'} {pC' : Fin n → Ω'}
    (hE : ∀ i, M.pathRecord (pE i) = M'.pathRecord (pE' i))
    (hC : ∀ j, M.pathRecord (pC j) = M'.pathRecord (pC' j)) (ψ : ℝ) :
    switchGStat (fun i ↦ M.pathRecord (pE i)) (fun j ↦ M.pathRecord (pC j)) ψ =
      switchGStat (fun i ↦ M'.pathRecord (pE' i)) (fun j ↦ M'.pathRecord (pC' j)) ψ := by
  simp only [hE, hC]

theorem timeOn_inter_Iic (A : Set ℝ) {x : ℝ} (hx : 0 ≤ x) :
    timeOn (A ∩ Set.Iic x) x = timeOn A x := by
  unfold timeOn
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [Set.uIcc_of_le hx] at hs
  by_cases h : s ∈ A <;> simp [h, hs.2]

/-- The candidate record of the observed record is the recensored record of the trial. -/
theorem candidateRecord_pathRecord {M : CensoredTrial Ω} (hwf : M.WellFormed) (ψ : ℝ) (ω : Ω) :
    candidateRecord ψ (M.pathRecord ω) = M.recensored ψ ω := by
  have hx : 0 ≤ M.obsTime ω := le_min (hwf.T_nonneg ω) (hwf.C_nonneg ω)
  simp only [candidateRecord, CensoredTrial.pathRecord, CensoredTrial.recensored,
    CensoredTrial.obsTimeOn, timeOn_inter_Iic _ hx]

theorem statusAt_empty (ψ u : ℝ) : statusAt ψ ∅ u = false := by
  simp [statusAt]

/-- A patient on the experimental treatment throughout follow-up `(0, x]` is on it at every time
`u ∈ (0, exp ψ x]` of the candidate scale. -/
theorem statusAt_Ioc {ψ x u : ℝ} (hu : 0 < u) (hux : u ≤ Real.exp ψ * x) :
    statusAt ψ (Set.Ioc 0 x) u = true := by
  have he := Real.exp_pos ψ
  have hs0 : 0 < u / Real.exp ψ := div_pos hu he
  have hsx : u / Real.exp ψ ≤ x := (div_le_iff₀' he).2 hux
  simp only [statusAt, decide_eq_true_eq]
  refine ⟨u / Real.exp ψ, ⟨hs0, hsx⟩, ?_⟩
  rw [untreatedTime_eq measurableSet_Ioc, show Set.Ioc (0 : ℝ) x = onTreatmentPath 0 x from rfl,
    timeOn_onTreatmentPath le_rfl (hs0.le.trans hsx) hs0.le, min_eq_right hsx,
    min_eq_left hs0.le]
  field_simp
  ring

/-- The candidate time of a record that is never treated (`b = false`, path `∅`) or treated
throughout follow-up (`b = true`, path `(0, x]`) is positive and, if treated, at most
`exp ψ x`. -/
theorem candidateRecord_bounds (ψ : ℝ) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (δ b : Bool) :
    0 < (candidateRecord ψ (x, δ, if b then Set.Ioc 0 x else ∅, c)).1 ∧
      (b = true → (candidateRecord ψ (x, δ, if b then Set.Ioc 0 x else ∅, c)).1 ≤
        Real.exp ψ * x) := by
  have he := Real.exp_pos ψ
  have hD : 0 < recensoringTime ψ c := lt_min hc (mul_pos he hc)
  cases b
  · have : timeOn (∅ : Set ℝ) x = 0 := by simp [timeOn]
    simp only [candidateRecord, recensorData, Bool.false_eq_true, ite_false, this, mul_zero,
      sub_zero, add_zero]
    exact ⟨lt_min hx hD, fun h ↦ h.elim⟩
  · have : timeOn (Set.Ioc (0 : ℝ) x) x = x := by
      rw [show Set.Ioc (0 : ℝ) x = onTreatmentPath 0 x from rfl,
        timeOn_onTreatmentPath le_rfl hx.le hx.le, min_self, min_eq_left hx.le, sub_zero]
    simp only [candidateRecord, recensorData, ite_true, this, sub_self, zero_add]
    exact ⟨lt_min (mul_pos he hx) hD, fun _ ↦ min_le_left _ _⟩

/-- **Reduction to `switchWeighted` with constant status.** If every patient is either never
treated (path `∅`) or treated throughout follow-up (path `(0, x]`), with positive follow-up and
censoring times, the g-statistic is `switchWeighted` on the candidate records with the constant
status `b_i` of each patient (the case of `SwitchExample`). -/
theorem switchGStat_eq_of_constant (E : Fin m → ℝ × Bool × Set ℝ × ℝ)
    (C : Fin n → ℝ × Bool × Set ℝ × ℝ) (ψ : ℝ) (bE : Fin m → Bool) (bC : Fin n → Bool)
    (hE : ∀ i, (E i).2.2.1 = if bE i then Set.Ioc 0 (E i).1 else ∅)
    (hC : ∀ j, (C j).2.2.1 = if bC j then Set.Ioc 0 (C j).1 else ∅)
    (hEx : ∀ i, 0 < (E i).1) (hCx : ∀ j, 0 < (C j).1)
    (hEc : ∀ i, 0 < (E i).2.2.2) (hCc : ∀ j, 0 < (C j).2.2.2) :
    switchGStat E C ψ = switchWeighted (fun i ↦ candidateRecord ψ (E i)) (fun i _ ↦ bE i)
      (fun j ↦ candidateRecord ψ (C j)) (fun j _ ↦ bC j) := by
  -- every record is of the stated form
  have fE : ∀ i, E i = ((E i).1, (E i).2.1, if bE i then Set.Ioc 0 (E i).1 else ∅, (E i).2.2.2) :=
    fun i ↦ by rw [← hE i]
  have fC : ∀ j, C j = ((C j).1, (C j).2.1, if bC j then Set.Ioc 0 (C j).1 else ∅, (C j).2.2.2) :=
    fun j ↦ by rw [← hC j]
  -- the status of one record at a positive time at which it is at risk
  have key : ∀ (r : ℝ × Bool × Set ℝ × ℝ) (b : Bool),
      r.2.2.1 = (if b then Set.Ioc 0 r.1 else ∅) → 0 < r.1 → 0 < r.2.2.2 → ∀ t, 0 < t →
        t ≤ (candidateRecord ψ r).1 → statusAt ψ r.2.2.1 t = b := by
    rintro ⟨x, δ, B, c⟩ b hB hx hc t ht htr
    simp only at hB hx hc ⊢
    subst hB
    cases b
    · exact statusAt_empty ψ t
    · exact statusAt_Ioc ht (htr.trans ((candidateRecord_bounds ψ hx hc δ true).2 rfl))
  -- every event time is positive
  have hpos : ∀ t ∈ eventTimes (times fun i ↦ candidateRecord ψ (E i))
      (times fun j ↦ candidateRecord ψ (C j)), 0 < t := by
    intro t ht
    classical
    simp only [eventTimes, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      times] at ht
    rcases ht with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [fE i]; exact (candidateRecord_bounds ψ (hEx i) (hEc i) _ _).1
    · rw [fC j]; exact (candidateRecord_bounds ψ (hCx j) (hCc j) _ _).1
  exact switchWeighted_congr_status
    (fun t ht i hi ↦ key (E i) (bE i) (hE i) (hEx i) (hEc i) t (hpos t ht) hi)
    (fun t ht j hj ↦ key (C j) (bC j) (hC j) (hCx j) (hCc j) t (hpos t ht) hj)

end Recensoring

namespace RecensoringExample

open Set

/-- Two patients. The experimental patient (`true`) is on the experimental treatment throughout,
dies at `6` and is censored at `10`; the control patient (`false`) is never treated, dies at
`2` and is censored at `3`. The time ratio is `1/2`. -/
noncomputable def trial : CensoredTrial Bool where
  R ω := ω
  T ω := if ω then 6 else 2
  A ω := if ω then univ else ∅
  C ω := if ω then 10 else 3
  U ω := if ω then 3 else 2

theorem wellFormed : trial.WellFormed where
  measurableSet_path ω := by cases ω <;> simp [trial]
  T_nonneg ω := by cases ω <;> norm_num [trial]
  C_nonneg ω := by cases ω <;> norm_num [trial]

theorem pathModel : trial.PathModel (Real.log (1 / 2)) := by
  intro ω
  cases ω
  · simp [trial, untreatedTime_empty]
  · simp only [trial, ite_true, untreatedTime_univ, Real.exp_log (show (0 : ℝ) < 1 / 2 by
      norm_num)]
    norm_num

theorem recensored_true : trial.recensored (Real.log (1 / 2)) true = (3, true) := by
  rw [CensoredTrial.recensored_eq wellFormed pathModel]
  norm_num [censorAt, CensoredTrial.recensTime, recensoringTime, trial,
    Real.exp_log (show (0 : ℝ) < 1 / 2 by norm_num)]

theorem recensored_false : trial.recensored (Real.log (1 / 2)) false = (3 / 2, false) := by
  rw [CensoredTrial.recensored_eq wellFormed pathModel]
  norm_num [censorAt, CensoredTrial.recensTime, recensoringTime, trial,
    Real.exp_log (show (0 : ℝ) < 1 / 2 by norm_num)]

theorem naive_true : trial.naive (Real.log (1 / 2)) true = (3, true) := by
  rw [CensoredTrial.naive_eq wellFormed pathModel]
  norm_num [censorAt, CensoredTrial.naiveCensTime, untreatedTime_univ, trial,
    Real.exp_log (show (0 : ℝ) < 1 / 2 by norm_num)]

theorem naive_false : trial.naive (Real.log (1 / 2)) false = (2, true) := by
  rw [CensoredTrial.naive_eq wellFormed pathModel]
  norm_num [censorAt, CensoredTrial.naiveCensTime, untreatedTime_empty, trial]

theorem recensored_stat :
    recensoredGStat logRankC trial ![true] ![false] (Real.log (1 / 2)) = 0 := by
  have e1 : (fun i : Fin 1 ↦ trial.recensored (Real.log (1 / 2)) (![true] i)) = ![(3, true)] := by
    funext i; fin_cases i; exact recensored_true
  have e2 : (fun j : Fin 1 ↦ trial.recensored (Real.log (1 / 2)) (![false] j)) =
      ![(3 / 2, false)] := by
    funext j; fin_cases j; exact recensored_false
  rw [recensoredGStat, e1, e2, logRankC, weightedLogRankC, sum_eventTimes_eq]
  simp only [oeC, atRiskC_eq_sum, deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_one, times]
  norm_num

theorem naive_stat :
    naiveGStat logRankC trial ![true] ![false] (Real.log (1 / 2)) = -1 / 2 := by
  have e1 : (fun i : Fin 1 ↦ trial.naive (Real.log (1 / 2)) (![true] i)) = ![(3, true)] := by
    funext i; fin_cases i; exact naive_true
  have e2 : (fun j : Fin 1 ↦ trial.naive (Real.log (1 / 2)) (![false] j)) = ![(2, true)] := by
    funext j; fin_cases j; exact naive_false
  rw [naiveGStat, e1, e2, logRankC, weightedLogRankC, sum_eventTimes_eq]
  simp only [oeC, atRiskC_eq_sum, deathsC_eq_sum, deaths_eq_sum, Fin.sum_univ_one, times]
  norm_num

/-- **Recensoring changes the statistic at the true parameter.** The control patient's event at
the untreated time `2` lies beyond the recensoring time `3/2` and is discarded by recensoring;
the naive analysis keeps it. -/
theorem differ :
    recensoredGStat logRankC trial ![true] ![false] (Real.log (1 / 2)) ≠
      naiveGStat logRankC trial ![true] ![false] (Real.log (1 / 2)) := by
  rw [recensored_stat, naive_stat]
  norm_num

end RecensoringExample

end GTest

end StructuralNested

end CausalInference
