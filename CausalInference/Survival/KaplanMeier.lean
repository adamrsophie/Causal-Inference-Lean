/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The finite-sample Kaplan-Meier estimator

A data set of `n` individuals, each recorded as `(X i, Δ i) : ℕ × Bool`: the follow-up time
and whether the event was observed at that time (`Δ i = true`) or the individual was censored
(`Δ i = false`). With the at-risk count `R m = #{i | X i ≥ m}` and the event count
`E m = #{i | X i = m, Δ i = true}`, the Kaplan-Meier (product-limit) estimator is

  `KM k = ∏_{m = 0}^{k} (1 - E m / R m)`,

the product formula of `CausalInference.Survival.Basic` with each hazard replaced by the
proportion of events among those at risk.

## Main results

* `kaplanMeier_eq_survivorFraction`: without censoring (`Δ i = true` for all `i`) and with
  `n > 0`, the Kaplan-Meier estimator equals the empirical survival fraction
  `#{i | X i > k} / n` at every time `k`.
* `atRiskCount_pos_of_le`: a positive at-risk count at `k` gives positive at-risk counts, hence
  positive denominators, at every earlier time.

Variance estimation (Greenwood's formula) and sampling properties are not treated.

## Source

M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Chapter 17, Section 17.2
(the Kaplan-Meier, or product-limit, estimator) and Section 17.3 (without censoring the
survival can be estimated by the fraction of survivors).
-/

@[expose] public section

namespace CausalInference

namespace Survival

variable {n : ℕ}

/-- The number at risk at time `m`: individuals whose follow-up time is at least `m`. -/
def atRiskCount (d : Fin n → ℕ × Bool) (m : ℕ) : ℕ :=
  (Finset.univ.filter fun i => m ≤ (d i).1).card

/-- The number of observed events at time `m`. -/
def eventCount (d : Fin n → ℕ × Bool) (m : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (d i).1 = m ∧ (d i).2 = true).card

/-- The number of individuals whose follow-up time exceeds `k`. -/
def survivorCount (d : Fin n → ℕ × Bool) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun i => k < (d i).1).card

/-- The Kaplan-Meier estimator at time `k`: `∏_{m = 0}^{k} (1 - E m / R m)`. A factor with
`R m = 0` takes the conventional value `1`. -/
noncomputable def kaplanMeier (d : Fin n → ℕ × Bool) (k : ℕ) : ℝ :=
  ∏ m ∈ Finset.range (k + 1), (1 - (eventCount d m : ℝ) / atRiskCount d m)

theorem atRiskCount_succ (d : Fin n → ℕ × Bool) (k : ℕ) :
    atRiskCount d (k + 1) = survivorCount d k := by
  simp only [atRiskCount, survivorCount, Nat.succ_le_iff]

theorem atRiskCount_zero (d : Fin n → ℕ × Bool) : atRiskCount d 0 = n := by
  simp [atRiskCount]

/-- Without censoring, those at risk at `m` either have the event at `m` or survive past `m`:
`R m = E m + #{i | X i > m}`. -/
theorem atRiskCount_eq_add (d : Fin n → ℕ × Bool) (hd : ∀ i, (d i).2 = true) (m : ℕ) :
    atRiskCount d m = eventCount d m + survivorCount d m := by
  simp only [atRiskCount, eventCount, survivorCount, Finset.card_filter, hd, and_true,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

/-- The at-risk count is nonincreasing; in particular `R k > 0` gives `R m > 0` for every
`m ≤ k`, so every factor of `KM k` then has a positive denominator. -/
theorem atRiskCount_pos_of_le (d : Fin n → ℕ × Bool) {m k : ℕ} (hmk : m ≤ k)
    (hk : 0 < atRiskCount d k) : 0 < atRiskCount d m :=
  lt_of_lt_of_le hk (Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hmk.trans hi)

/-- Without censoring the Kaplan-Meier estimator is the empirical survival fraction: if every
event is observed (`Δ i = true`) and `n > 0`, then `KM k = #{i | X i > k} / n` for every `k`.
When `R k > 0` all denominators are positive (`atRiskCount_pos_of_le`). When `R k = 0` the
survivor fraction is `0`; the proof shows that the product is `0` because a partial product
`KM m` reaches `0` (at the first `m` with no survivors past `m`, where `R m > 0`), so the
conventional factors with `R m = 0` do not affect the value. -/
theorem kaplanMeier_eq_survivorFraction (d : Fin n → ℕ × Bool) (hd : ∀ i, (d i).2 = true)
    (hn : 0 < n) (k : ℕ) :
    kaplanMeier d k = (survivorCount d k : ℝ) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  induction k with
  | zero =>
    have h := atRiskCount_eq_add d hd 0
    rw [atRiskCount_zero] at h
    have h' : (n : ℝ) = eventCount d 0 + survivorCount d 0 := by exact_mod_cast h
    rw [kaplanMeier, Finset.prod_range_one, atRiskCount_zero]
    field_simp
    linarith
  | succ k ih =>
    rw [kaplanMeier, Finset.prod_range_succ, ← kaplanMeier, ih, atRiskCount_succ]
    have h := atRiskCount_eq_add d hd (k + 1)
    rw [atRiskCount_succ] at h
    rcases Nat.eq_zero_or_pos (survivorCount d k) with h0 | h0
    · have : survivorCount d (k + 1) = 0 := by omega
      rw [h0, this]
      simp
    · have h0' : (0 : ℝ) < survivorCount d k := Nat.cast_pos.2 h0
      have h' : (survivorCount d k : ℝ) = eventCount d (k + 1) + survivorCount d (k + 1) := by
        exact_mod_cast h
      field_simp
      linarith

end Survival

end CausalInference
