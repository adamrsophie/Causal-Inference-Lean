/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Discrete-time survival: survival, risk, hazard and the product formula

An event time `T : Ω → ℕ` on a probability space `(Ω, μ)`, with time measured in discrete
intervals. We define

* `survival μ T k = P(T > k)`, the survival at time `k`;
* `risk μ T k = 1 - P(T > k) = P(T ≤ k)`, the risk (cumulative incidence) at time `k`;
* `atRisk μ T k = P(T ≥ k)`, the probability of being still at risk at the start of interval
  `k`; for `k ≥ 1` this is `P(T > k - 1)`;
* `hazard μ T k = P(T = k) / P(T ≥ k)`, the discrete-time hazard `P(T = k | T ≥ k)`. For
  `k ≥ 1` this is the book's `P(T = k | T > k - 1)`; at `k = 0` it is `P(T = 0)` for a
  probability measure, since everybody is at risk at time `0`. It is a genuine conditional
  probability only when `0 < atRisk μ T k`; every result below that uses a hazard as a
  conditional probability carries that positivity hypothesis.

## Main results

* `survival_antitone`, `risk_monotone`: survival is nonincreasing and risk nondecreasing.
* Range: `hazard_nonneg`, `hazard_le_one`, `survival_nonneg`, `survival_le_one`,
  `risk_nonneg`, `risk_le_one`, `atRisk_nonneg`, `atRisk_le_one`; and `hazard_zero`:
  `h 0 = P(T = 0)`.
* `measureReal_eq_hazard_mul_atRisk`: `P(T = k) = h k * P(T ≥ k)`; when the at-risk event is
  null, both sides are zero because the event `T = k` is contained in it (no division by zero
  is used to get the left side).
* `survival_eq_atRisk_mul`: `S k = P(T ≥ k) * (1 - h k)`.
* `survival_eq_prod_one_sub_hazard`: the product formula
  `S k = ∏_{m = 0}^{k} (1 - h m)` whenever `P(T ≥ k) > 0`; then every factor is one minus a
  genuine conditional probability. `survival_eq_prod_Icc` is the book's form
  `S k = ∏_{m = 1}^{k} (1 - h m)` when `P(T = 0) = 0` (everybody is alive at time `0`) and
  `P(T ≥ k) > 0`; `survival_eq_prod_Icc_filter` is the same at every horizon `k`, with the
  product over the times `1 ≤ m ≤ k` with `P(T ≥ m) > 0`.
* `exists_hazard_eq_one_of_survival_eq_zero`: if `S k = 0` then some `m ≤ k` has positive
  at-risk probability and hazard exactly `1`. So once survival reaches zero, the product
  formula has a genuine zero factor; `survival_eq_prod_one_sub_hazard_of_survival_eq_zero`
  states the product formula in that case, where the later factors are irrelevant.
* `survival_eq_prod_one_sub_hazard'`: the product formula for every `k`, with the reading of
  the factors at times of at-risk probability zero explained in its docstring.
* `risk_eq_measureReal_le`: `1 - S k = P(T ≤ k)`.
* `risk_eq_sum_hazard_mul_atRisk`: `1 - S k = ∑_{m = 0}^{k} h m * P(T ≥ m)`;
  `risk_eq_sum_Icc`: `1 - S k = ∑_{m = 1}^{k} h m * S (m - 1)` when `P(T = 0) = 0`.
* `hazard_one_eq_risk_one`: when `P(T = 0) = 0` the hazard at time `1` is the risk at time `1`.
* `map_eq_of_hazard_eq`: hazards at the times with positive at-risk probability determine
  the law of `T`; `hazard_eq_of_map_eq`: conversely, the law of `T` determines the hazards.

## Source

M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Chapter 17, Sections 17.1
(survival, risk and hazard) and 17.2 (from hazards to risks: the product formula).
-/

@[expose] public section

open MeasureTheory

namespace CausalInference

namespace Survival

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The survival at time `k`: `S k = P(T > k)`. -/
noncomputable def survival (μ : Measure Ω) (T : Ω → ℕ) (k : ℕ) : ℝ :=
  μ.real {ω | k < T ω}

/-- The risk, or cumulative incidence, at time `k`: `1 - P(T > k)`, which equals
`P(T ≤ k)` for a probability measure (`risk_eq_measureReal_le`). -/
noncomputable def risk (μ : Measure Ω) (T : Ω → ℕ) (k : ℕ) : ℝ :=
  1 - survival μ T k

/-- The probability of being at risk at the start of interval `k`: `P(T ≥ k)`. For `k ≥ 1`
this is `P(T > k - 1) = S (k - 1)` (`atRisk_succ`). -/
noncomputable def atRisk (μ : Measure Ω) (T : Ω → ℕ) (k : ℕ) : ℝ :=
  μ.real {ω | k ≤ T ω}

/-- The discrete-time hazard at time `k`: `h k = P(T = k) / P(T ≥ k)`, the probability
`P(T = k | T ≥ k)` of the event in interval `k` among those who had not had it before `k`.
For `k ≥ 1` the conditioning event `T ≥ k` is `T > k - 1`, so `h k = P(T = k | T > k - 1)` as
in the book; at `k = 0` the conditioning event is the whole space and, for a probability
measure, `h 0 = P(T = 0)` (`hazard_zero`). It is a conditional probability only when
`0 < atRisk μ T k`; at other times its value is the conventional `0` and no result uses it as
a probability. -/
noncomputable def hazard (μ : Measure Ω) (T : Ω → ℕ) (k : ℕ) : ℝ :=
  μ.real {ω | T ω = k} / atRisk μ T k

variable {μ : Measure Ω} {T : Ω → ℕ}

theorem atRisk_succ (k : ℕ) : atRisk μ T (k + 1) = survival μ T k := by
  simp only [atRisk, survival, Nat.succ_le_iff]

theorem atRisk_zero [IsProbabilityMeasure μ] : atRisk μ T 0 = 1 := by
  simp [atRisk]

/-- The hazard at time `0` is the probability of the event at time `0`: `h 0 = P(T = 0)`. -/
theorem hazard_zero [IsProbabilityMeasure μ] : hazard μ T 0 = μ.real {ω | T ω = 0} := by
  rw [hazard, atRisk_zero, div_one]

theorem survival_nonneg (k : ℕ) : 0 ≤ survival μ T k := measureReal_nonneg

theorem atRisk_nonneg (k : ℕ) : 0 ≤ atRisk μ T k := measureReal_nonneg

theorem hazard_nonneg (k : ℕ) : 0 ≤ hazard μ T k :=
  div_nonneg measureReal_nonneg measureReal_nonneg

theorem survival_le_one [IsProbabilityMeasure μ] (k : ℕ) : survival μ T k ≤ 1 :=
  measureReal_le_one

theorem atRisk_le_one [IsProbabilityMeasure μ] (k : ℕ) : atRisk μ T k ≤ 1 :=
  measureReal_le_one

theorem risk_nonneg [IsProbabilityMeasure μ] (k : ℕ) : 0 ≤ risk μ T k :=
  sub_nonneg.2 (survival_le_one k)

theorem risk_le_one (k : ℕ) : risk μ T k ≤ 1 :=
  sub_le_self _ (survival_nonneg k)

variable [IsFiniteMeasure μ]

/-- Survival is nonincreasing in time. -/
theorem survival_antitone : Antitone (survival μ T) := by
  intro j k hjk
  exact measureReal_mono fun ω (h : k < T ω) => lt_of_le_of_lt hjk h

/-- The at-risk probability is nonincreasing in time. -/
theorem atRisk_antitone : Antitone (atRisk μ T) := by
  intro j k hjk
  exact measureReal_mono fun ω (h : k ≤ T ω) => le_trans hjk h

theorem survival_le_atRisk (k : ℕ) : survival μ T k ≤ atRisk μ T k :=
  measureReal_mono fun ω (h : k < T ω) => h.le

theorem measureReal_eq_le_atRisk (k : ℕ) : μ.real {ω | T ω = k} ≤ atRisk μ T k :=
  measureReal_mono fun ω (h : T ω = k) => h.ge

/-- The hazard is at most one: `P(T = k) ≤ P(T ≥ k)`. So `0 ≤ 1 - h k` at every time. -/
theorem hazard_le_one (k : ℕ) : hazard μ T k ≤ 1 :=
  div_le_one_of_le₀ (measureReal_eq_le_atRisk k) (atRisk_nonneg k)

/-- Risk is nondecreasing in time. -/
theorem risk_monotone : Monotone (risk μ T) := by
  intro j k hjk
  have := survival_antitone (μ := μ) (T := T) hjk
  simp only [risk]
  linarith

/-- `P(T = k) = h k * P(T ≥ k)` for every `k`. If `P(T ≥ k) = 0` then also `P(T = k) = 0`
since `{T = k} ⊆ {T ≥ k}`, so both sides vanish for that reason, whatever the conventional
value of the hazard. -/
theorem measureReal_eq_hazard_mul_atRisk (k : ℕ) :
    μ.real {ω | T ω = k} = hazard μ T k * atRisk μ T k := by
  rcases (measureReal_nonneg : 0 ≤ atRisk μ T k).eq_or_lt with h | h
  all_goals change _ = μ.real {ω | T ω = k} / atRisk μ T k * atRisk μ T k
  · have h0 : μ.real {ω | T ω = k} = 0 :=
      le_antisymm (h ▸ measureReal_eq_le_atRisk k) measureReal_nonneg
    rw [h0, zero_div, zero_mul]
  · exact (div_mul_cancel₀ _ h.ne').symm

/-- Every event defined by a property of a measurable `T : Ω → ℕ` is measurable. -/
theorem measurableSet_setOf_of_discrete {S : Type*} {T : Ω → S} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (hT : Measurable T) (p : S → Prop) :
    MeasurableSet {ω | p (T ω)} :=
  hT (MeasurableSet.of_discrete (s := {x | p x}))

variable (hT : Measurable T)
include hT

/-- `P(T ≥ k) = P(T = k) + P(T > k)`. -/
theorem atRisk_eq_add (k : ℕ) :
    atRisk μ T k = μ.real {ω | T ω = k} + survival μ T k := by
  have hset : {ω | k ≤ T ω} = {ω | T ω = k} ∪ {ω | k < T ω} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_union]; omega
  rw [atRisk, hset, measureReal_union _ (measurableSet_setOf_of_discrete hT (k < ·))]
  · rfl
  · exact Set.disjoint_left.2 fun ω (h1 : T ω = k) (h2 : k < T ω) => by omega

/-- `S k = P(T ≥ k) * (1 - h k)`, valid for every `k` (when `P(T ≥ k) = 0` both sides are
zero, the right side through the factor `P(T ≥ k)`). -/
theorem survival_eq_atRisk_mul (k : ℕ) :
    survival μ T k = atRisk μ T k * (1 - hazard μ T k) := by
  have h1 := atRisk_eq_add (μ := μ) hT k
  have h2 := measureReal_eq_hazard_mul_atRisk (μ := μ) (T := T) k
  linarith

/-- `P(T = k) = P(T ≥ k) - P(T ≥ k + 1)`. -/
theorem measureReal_eq_atRisk_sub (k : ℕ) :
    μ.real {ω | T ω = k} = atRisk μ T k - atRisk μ T (k + 1) := by
  rw [atRisk_succ, atRisk_eq_add hT k]; ring

omit [IsFiniteMeasure μ]
variable [IsProbabilityMeasure μ]

/-- The risk is the probability of an event by time `k`: `1 - P(T > k) = P(T ≤ k)`. -/
theorem risk_eq_measureReal_le (k : ℕ) : risk μ T k = μ.real {ω | T ω ≤ k} := by
  have h := probReal_compl_eq_one_sub (μ := μ) (measurableSet_setOf_of_discrete hT (k < ·))
  have hset : {ω | k < T ω}ᶜ = {ω | T ω ≤ k} := by ext ω; simp
  rw [hset] at h
  rw [risk, survival, h]

/-- The product formula, unconditional form: `S k = ∏_{m = 0}^{k} (1 - h m)` for every `k`.
At a time `m` with `P(T ≥ m) = 0` the factor `1 - h m` is a conventional value, not one minus
a conditional probability; such factors occur only after survival has reached zero, and then
an earlier factor is a genuine zero (`exists_hazard_eq_one_of_survival_eq_zero`), so the
conventional values do not affect the product. When `P(T ≥ k) > 0` no such factor occurs:
see `survival_eq_prod_one_sub_hazard`. -/
theorem survival_eq_prod_one_sub_hazard' (k : ℕ) :
    survival μ T k = ∏ m ∈ Finset.range (k + 1), (1 - hazard μ T m) := by
  induction k with
  | zero => simp [survival_eq_atRisk_mul hT 0, atRisk_zero]
  | succ k ih =>
    rw [Finset.prod_range_succ, ← ih, survival_eq_atRisk_mul hT (k + 1), atRisk_succ]

/-- The product formula of Hernán and Robins (Section 17.2):
`S k = ∏_{m = 0}^{k} (1 - h m)` when the at-risk probability `P(T ≥ k)` is positive. In that
case every at-risk probability `P(T ≥ m)`, `m ≤ k`, is positive (first conjunct), so each
factor is one minus a genuine conditional probability `P(T = m | T ≥ m)`. -/
theorem survival_eq_prod_one_sub_hazard (k : ℕ) (hk : 0 < atRisk μ T k) :
    (∀ m ≤ k, 0 < atRisk μ T m) ∧
      survival μ T k = ∏ m ∈ Finset.range (k + 1), (1 - hazard μ T m) :=
  ⟨fun _ hm => lt_of_lt_of_le hk (atRisk_antitone hm), survival_eq_prod_one_sub_hazard' hT k⟩

/-- Once survival reaches zero, the product formula has a genuine zero factor: if `S k = 0`
then there is a time `m ≤ k` with positive at-risk probability `P(T ≥ m) > 0` and hazard
`P(T = m | T ≥ m) = 1`. -/
theorem exists_hazard_eq_one_of_survival_eq_zero {k : ℕ} (hk : survival μ T k = 0) :
    ∃ m ≤ k, 0 < atRisk μ T m ∧ hazard μ T m = 1 := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, by simp [atRisk_zero], ?_⟩
    have := survival_eq_atRisk_mul (μ := μ) hT 0
    rw [hk, atRisk_zero] at this
    linarith
  | succ k ih =>
    rcases (measureReal_nonneg : 0 ≤ atRisk μ T (k + 1)).eq_or_lt with h | h
    · obtain ⟨m, hm, hpos, hh⟩ := ih (by rw [← atRisk_succ]; exact h.symm)
      exact ⟨m, hm.trans k.le_succ, hpos, hh⟩
    · refine ⟨k + 1, le_rfl, h, ?_⟩
      have := survival_eq_atRisk_mul (μ := μ) hT (k + 1)
      rw [hk] at this
      have h1 : 1 - hazard μ T (k + 1) = 0 := by
        rcases mul_eq_zero.1 this.symm with h' | h'
        · exact absurd h' h.ne'
        · exact h'
      linarith

/-- The product formula when survival has reached zero: if `S k = 0` then the product
`∏_{m = 0}^{k} (1 - h m)` is zero as well, because it contains the factor `1 - h m = 0` at a
time `m` with positive at-risk probability (`exists_hazard_eq_one_of_survival_eq_zero`). -/
theorem survival_eq_prod_one_sub_hazard_of_survival_eq_zero {k : ℕ}
    (hk : survival μ T k = 0) :
    survival μ T k = ∏ m ∈ Finset.range (k + 1), (1 - hazard μ T m) := by
  obtain ⟨m, hm, -, hh⟩ := exists_hazard_eq_one_of_survival_eq_zero hT hk
  rw [hk, eq_comm]
  exact Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_of_le hm)) (by rw [hh, sub_self])

/-- The product formula in the book's indexing: if nobody has the event at time `0`
(`P(T = 0) = 0`, so `S 0 = 1`) and `P(T ≥ k) > 0`, then `S k = ∏_{m = 1}^{k} (1 - h m)`,
where each factor is one minus the genuine conditional probability
`h m = P(T = m | T > m - 1)`. -/
theorem survival_eq_prod_Icc (h0 : μ.real {ω | T ω = 0} = 0) (k : ℕ)
    (hk : 0 < atRisk μ T k) :
    survival μ T k = ∏ m ∈ Finset.Icc 1 k, (1 - hazard μ T m) := by
  rw [(survival_eq_prod_one_sub_hazard hT k hk).2]
  clear hk
  induction k with
  | zero => simp [hazard, h0]
  | succ k ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]

open Classical in
/-- The product formula in the book's indexing at every horizon: if nobody has the event at
time `0` (`P(T = 0) = 0`), then for every `k`,
`S k = ∏ (1 - h m)` over the times `1 ≤ m ≤ k` with positive at-risk probability
`P(T ≥ m) > 0`. Every factor is one minus a genuine conditional probability
`h m = P(T = m | T > m - 1)`; no conventional hazard value enters. When `S k = 0` the product
contains a genuine zero factor, the first time at which the hazard is `1`
(`exists_hazard_eq_one_of_survival_eq_zero`). -/
theorem survival_eq_prod_Icc_filter (h0 : μ.real {ω | T ω = 0} = 0) (k : ℕ) :
    survival μ T k =
      ∏ m ∈ (Finset.Icc 1 k).filter (fun m => 0 < atRisk μ T m), (1 - hazard μ T m) := by
  rcases (survival_nonneg (μ := μ) (T := T) k).eq_or_lt with hS | hS
  · obtain ⟨m, hm, hpos, hh⟩ := exists_hazard_eq_one_of_survival_eq_zero hT hS.symm
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · rw [hazard_zero, h0] at hh; exact absurd hh zero_ne_one
      · exact hm1
    rw [← hS, eq_comm]
    exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hm1, hm⟩, hpos⟩)
      (by rw [hh, sub_self])
  · have hk : 0 < atRisk μ T k := lt_of_lt_of_le hS (survival_le_atRisk k)
    rw [Finset.filter_true_of_mem fun m hm =>
      lt_of_lt_of_le hk (atRisk_antitone (Finset.mem_Icc.1 hm).2)]
    exact survival_eq_prod_Icc hT h0 k hk

/-- Risk as a cumulative sum of hazards: `1 - S k = ∑_{m = 0}^{k} h m * P(T ≥ m)`. Each term
equals `P(T = m)` (`measureReal_eq_hazard_mul_atRisk`); a term with `P(T ≥ m) = 0` is zero
because `P(T = m) = 0`, not because of a convention. -/
theorem risk_eq_sum_hazard_mul_atRisk (k : ℕ) :
    risk μ T k = ∑ m ∈ Finset.range (k + 1), hazard μ T m * atRisk μ T m := by
  simp only [← measureReal_eq_hazard_mul_atRisk]
  induction k with
  | zero =>
    have := atRisk_eq_add (μ := μ) hT 0
    rw [atRisk_zero] at this
    simp only [risk, zero_add, Finset.range_one, Finset.sum_singleton]
    linarith
  | succ k ih =>
    have h1 := atRisk_eq_add (μ := μ) hT (k + 1)
    rw [atRisk_succ] at h1
    rw [Finset.sum_range_succ, ← ih]
    simp only [risk]
    linarith

/-- Risk as a cumulative sum, the book's indexing: if `P(T = 0) = 0` then
`1 - S k = ∑_{m = 1}^{k} h m * S (m - 1)`. -/
theorem risk_eq_sum_Icc (h0 : μ.real {ω | T ω = 0} = 0) (k : ℕ) :
    risk μ T k = ∑ m ∈ Finset.Icc 1 k, hazard μ T m * survival μ T (m - 1) := by
  rw [risk_eq_sum_hazard_mul_atRisk hT]
  induction k with
  | zero => simp [hazard, h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel,
      atRisk_succ]

/-- When nobody has the event at time `0`, the hazard at time `1` equals the risk at time `1`:
`h 1 = P(T ≤ 1)`, since everybody is at risk at time `1`. -/
theorem hazard_one_eq_risk_one (h0 : μ.real {ω | T ω = 0} = 0) :
    hazard μ T 1 = risk μ T 1 := by
  have e0 := atRisk_eq_add (μ := μ) hT 0
  have e1 := atRisk_eq_add (μ := μ) hT 1
  rw [atRisk_zero, h0, zero_add, ← atRisk_succ] at e0
  rw [hazard, ← e0, div_one, risk]
  linarith

omit [IsProbabilityMeasure μ] hT in
/-- The law of `T` determines the hazards: two event times with the same distribution have
the same hazard at every time. The identity is between the expressions
`P(T = k) / P(T ≥ k)` as defined, and it holds because numerators and denominators agree
separately; at a time with `P(T ≥ k) = 0` both sides are the conventional value `0`, and only
at times of positive at-risk probability is it an equality of conditional probabilities. -/
theorem hazard_eq_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} {T' : Ω' → ℕ}
    (hT : Measurable T) (hT' : Measurable T') (h : μ.map T = ν.map T') (k : ℕ) :
    hazard μ T k = hazard ν T' k := by
  have key : ∀ p : ℕ → Prop, μ.real {ω | p (T ω)} = ν.real {ω | p (T' ω)} := fun p => by
    have h1 := map_measureReal_apply (μ := μ) hT (MeasurableSet.of_discrete (s := {x | p x}))
    have h2 := map_measureReal_apply (μ := ν) hT' (MeasurableSet.of_discrete (s := {x | p x}))
    rw [h] at h1
    exact h1.symm.trans h2
  exact congrArg₂ (· / ·) (key (· = k)) (key (k ≤ ·))

omit [IsProbabilityMeasure μ] in
/-- Hazards determine the law of `T`: if `μ` and `ν` are probability measures and the hazards
of `T` and `T'` agree at every time at which `T` has positive at-risk probability, then `T`
and `T'` have the same distribution. Times with `P(T ≥ k) = 0` impose no condition, and the
proof never uses the conventional value of a hazard: it propagates `P(T ≥ k + 1) =
P(T ≥ k) * (1 - h k)`, which at such times reads `0 = 0`. -/
theorem map_eq_of_hazard_eq [IsProbabilityMeasure μ] {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {T' : Ω' → ℕ} (hT' : Measurable T')
    (h : ∀ k, 0 < atRisk μ T k → hazard μ T k = hazard ν T' k) : μ.map T = ν.map T' := by
  have hR : ∀ k, atRisk μ T k = atRisk ν T' k := by
    intro k
    induction k with
    | zero => rw [atRisk_zero, atRisk_zero]
    | succ k ih =>
      rw [atRisk_succ, atRisk_succ, survival_eq_atRisk_mul hT, survival_eq_atRisk_mul hT', ← ih]
      rcases (measureReal_nonneg : 0 ≤ atRisk μ T k).eq_or_lt with h0 | h0
      · rw [show atRisk μ T k = 0 from h0.symm, zero_mul, zero_mul]
      · rw [h k h0]
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.map_apply hT (measurableSet_singleton k),
    Measure.map_apply hT' (measurableSet_singleton k), ← measureReal_eq_measureReal_iff]
  exact (measureReal_eq_atRisk_sub hT k).trans
    (by rw [hR, hR]; exact (measureReal_eq_atRisk_sub hT' k).symm)

end Survival

end CausalInference
