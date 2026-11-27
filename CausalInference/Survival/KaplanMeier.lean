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
public import CausalInference.Survival.Censoring

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
* `kaplanMeier_ne_survivorFraction_censored`: with censoring the identity fails; one
  individual censored at time `1` and one with the event at time `2` give `KM 1 = 1` while the
  fraction followed beyond time `1` is `1/2`.
* `kaplanMeier_nonneg`, `kaplanMeier_le_one`, `kaplanMeier_antitone`: the estimator lies in the
  unit interval and is nonincreasing in time.
* `kaplanMeier_eq_productLimit`: the estimator is the product-limit functional
  `CausalInference.Survival.productLimit` of the empirical law `empiricalLaw d`
  `= n⁻¹ ∑_i δ_{(X i, Δ i)}`, a probability measure when `n > 0`.
* `kaplanMeier_eq_survival_of_hazard_eq`: through that identity, the identification theorem
  `productLimit_map_observed_eq_survival_of_hazard_eq` applies to the estimator: when the
  empirical law equals the observed-data law of a model satisfying its hypotheses, the
  estimator equals the survival.

Variance estimation (Greenwood's formula) and sampling properties are not treated.

## Source

M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), Chapter 17, Section 17.2
(the Kaplan-Meier, or product-limit, estimator) and Section 17.3 (without censoring the
survival can be estimated by the fraction of survivors).
-/

@[expose] public section

open MeasureTheory

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

/-- The number of observed events never exceeds the number at risk. -/
theorem eventCount_le_atRiskCount (d : Fin n → ℕ × Bool) (m : ℕ) :
    eventCount d m ≤ atRiskCount d m :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.1.ge

/-- Each factor `1 - E m / R m` of the estimator lies in the unit interval. -/
theorem one_sub_eventCount_div_mem (d : Fin n → ℕ × Bool) (m : ℕ) :
    0 ≤ 1 - (eventCount d m : ℝ) / atRiskCount d m ∧
      1 - (eventCount d m : ℝ) / atRiskCount d m ≤ 1 :=
  ⟨sub_nonneg.2 (div_le_one_of_le₀ (by exact_mod_cast eventCount_le_atRiskCount d m)
      (Nat.cast_nonneg _)),
    sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))⟩

theorem kaplanMeier_nonneg (d : Fin n → ℕ × Bool) (k : ℕ) : 0 ≤ kaplanMeier d k :=
  Finset.prod_nonneg fun m _ => (one_sub_eventCount_div_mem d m).1

theorem kaplanMeier_le_one (d : Fin n → ℕ × Bool) (k : ℕ) : kaplanMeier d k ≤ 1 :=
  Finset.prod_le_one₀ (fun m _ => (one_sub_eventCount_div_mem d m).1)
    fun m _ => (one_sub_eventCount_div_mem d m).2

/-- The Kaplan-Meier estimator is nonincreasing in time. -/
theorem kaplanMeier_antitone (d : Fin n → ℕ × Bool) : Antitone (kaplanMeier d) :=
  antitone_nat_of_succ_le fun k => by
    rw [kaplanMeier, Finset.prod_range_succ, ← kaplanMeier]
    exact mul_le_of_le_one_right (kaplanMeier_nonneg d k) (one_sub_eventCount_div_mem d _).2

/-- The empirical law of the data set: `n⁻¹ ∑_i δ_{(X i, Δ i)}`, a law of the observed data
`(X, Δ)`. It is a probability measure when `n > 0` (`isProbabilityMeasure_empiricalLaw`). -/
noncomputable def empiricalLaw (d : Fin n → ℕ × Bool) : Measure (ℕ × Bool) :=
  (n : ENNReal)⁻¹ • ∑ i, Measure.dirac (d i)

open Classical in
/-- The empirical probability of a set is the fraction of records in it. -/
theorem empiricalLaw_real (d : Fin n → ℕ × Bool) (s : Set (ℕ × Bool)) :
    (empiricalLaw d).real s = ((Finset.univ.filter fun i => d i ∈ s).card : ℝ) / n := by
  simp only [empiricalLaw, measureReal_def, smul_apply, sum_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, Finset.sum_boole, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [div_eq_inv_mul]

theorem isProbabilityMeasure_empiricalLaw (d : Fin n → ℕ × Bool) (hn : 0 < n) :
    IsProbabilityMeasure (empiricalLaw d) := by
  refine ⟨?_⟩
  simp only [empiricalLaw, smul_apply, sum_apply, measure_univ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

/-- The Kaplan-Meier estimator is the product-limit functional of the empirical law:
`KM k = productLimit (empiricalLaw d) k`. The empirical probability of an observed event at
`m` is `E m / n` and that of follow-up time at least `m` is `R m / n`, and the factors `1 / n`
cancel. This is an identity between the expressions as defined: at a time with `R m = 0` both
factors are the conventional `1`, since both ratios are `0 / 0`. (For `n = 0` both sides are
the empty-data value `1`.) -/
theorem kaplanMeier_eq_productLimit (d : Fin n → ℕ × Bool) (k : ℕ) :
    kaplanMeier d k = productLimit (empiricalLaw d) k := by
  refine Finset.prod_congr rfl fun m _ => ?_
  have hE : (empiricalLaw d).real {x | x.1 = m ∧ x.2 = true} = (eventCount d m : ℝ) / n := by
    rw [empiricalLaw_real, eventCount]; congr 3; ext; simp
  have hR : (empiricalLaw d).real {x | m ≤ x.1} = (atRiskCount d m : ℝ) / n := by
    rw [empiricalLaw_real, atRiskCount]; congr 3; ext; simp
  rw [observedHazard, hE, hR]
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · simp [eventCount, atRiskCount, Nat.cast_eq_zero.1 hn]
  · rw [div_div_div_cancel_right₀ hn]

/-- The identification theorem transferred to the estimator: if the empirical law of the data
equals the observed-data law `μ.map (observed T C)` of a model in which, at every time `m ≤ k`
with `P(T ≥ m, C ≥ m) > 0`, the hazard among those at risk and uncensored equals the true
hazard, and `P(T ≥ k, C ≥ k) > 0`, then the Kaplan-Meier estimator equals the survival
`P(T > k)`. This is an algebraic statement about the plug-in; it says nothing about sampling
variability. -/
theorem kaplanMeier_eq_survival_of_hazard_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T C : Ω → ℕ} (hT : Measurable T) (hC : Measurable C)
    (d : Fin n → ℕ × Bool) (hd : empiricalLaw d = μ.map (observed T C)) (k : ℕ)
    (hk : 0 < μ.real {ω | k ≤ T ω ∧ k ≤ C ω})
    (h : ∀ m ≤ k, 0 < μ.real {ω | m ≤ T ω ∧ m ≤ C ω} →
      μ.real {ω | T ω = m ∧ m ≤ C ω} / μ.real {ω | m ≤ T ω ∧ m ≤ C ω} = hazard μ T m) :
    kaplanMeier d k = survival μ T k := by
  rw [kaplanMeier_eq_productLimit, hd]
  exact productLimit_map_observed_eq_survival_of_hazard_eq hT hC k hk h

/-- A data set with censoring: one individual censored at time `1` and one with the event at
time `2`. -/
def censoredData : Fin 2 → ℕ × Bool := ![(1, false), (2, true)]

/-- With censoring the Kaplan-Meier estimator is not the survivor fraction: for `censoredData`,
both individuals are at risk at time `1` and no event is observed by then, so `KM 1 = 1`,
while the fraction of individuals followed beyond time `1` is `1/2`. So the hypothesis
`∀ i, Δ i = true` of `kaplanMeier_eq_survivorFraction` cannot be dropped. -/
theorem kaplanMeier_ne_survivorFraction_censored :
    (censoredData 0).2 = false ∧ kaplanMeier censoredData 1 = 1 ∧
      (survivorCount censoredData 1 : ℝ) / 2 = 1 / 2 := by
  have e0 : eventCount censoredData 0 = 0 := by decide
  have e1 : eventCount censoredData 1 = 0 := by decide
  have s1 : survivorCount censoredData 1 = 1 := by decide
  refine ⟨rfl, ?_, ?_⟩
  · simp [kaplanMeier, Finset.prod_range_succ, e0, e1]
  · rw [s1]; norm_num

end Survival

end CausalInference
