/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.RPSFTMCounterexamples

/-!
# Rank-based g-statistics for the RPSFTM

The test statistics that g-estimation evaluates at each candidate `ψ` (TSD 16, Appendix A,
"RPSFTM": a log-rank or Wilcoxon test; TSD 24, Section 4.2.1.1, "Weighted log-rank test for
RPSFTM"), on a finite sample of uncensored times: an experimental sample `E : Fin m → ℝ` and a
control sample `C : Fin n → ℝ`. Every observation is an event (no censoring). Tied times are
handled in the usual way: at a distinct event time `t` with `d(t)` events among `n(t)` patients
at risk, the expected number of events in the experimental arm is `d(t) n_E(t) / n(t)`, the mean
of the hypergeometric law. The documents print no formula for these statistics; the definitions
here are the standard ones.

## Main definitions

* `GTest.atRisk S t`, `GTest.deaths S t`: the number at risk (`S_i ≥ t`) and the number of events
  (`S_i = t`) at time `t`.
* `GTest.eventTimes E C`: the distinct event times of the pooled sample.
* `GTest.oe E C t = d_E(t) - d(t) n_E(t) / n(t)`: observed minus expected events in the
  experimental arm at `t`.
* `GTest.weightedLogRank W E C = Σ_t W t (d_E(t) - d(t) n_E(t) / n(t))`, with a weight `W t` per
  event time; `GTest.logRank` (weight `1`), `GTest.gehan` (weight `n(t)`, the Wilcoxon or Gehan
  statistic), and `GTest.riskWeighted g` (weight `g (n_E(t)) (n_C(t))`, a function of the risk set
  sizes).
* `GTest.mannWhitney E C = Σ_{i, j} sign (E_i - C_j)`.
* `GTest.gStat stat E C ψ`: a statistic applied to the candidate untreated times
  `T^c + exp ψ T^e` of samples of pairs `(T^c, T^e)`.

## Main results

* `weightedLogRank_swap`: antisymmetry, swapping the arms changes the sign.
* `weightedLogRank_eq_zero_of_equiv`: the statistic is zero when the two arms have the same
  multiset of times (a bijection `σ` between the samples with `C (σ i) = E i`).
* `riskWeighted_congr_order`: a risk-set weighted statistic depends only on the order pattern of
  the pooled sample; `riskWeighted_comp_strictMono`: it is invariant under strictly increasing
  transformations of the times, so it is a function of the ranks only.
* `gStat_congr_order`: as a function of `ψ`, the g-statistic is constant on every set of `ψ` with
  the same order of the pooled candidate untreated times; it changes only where two candidate
  untreated times cross. So it is piecewise constant and an exact root need not exist (see
  `CausalInference.StructuralNested.GTestExample`).
* `gehan_eq_neg_mannWhitney`: without censoring the Gehan statistic is minus the Mann-Whitney
  statistic; `gStat_gehan_eq_neg_wilcoxon` relates it to
  `CausalInference.StructuralNested.RPSFTMCounterexample.Wilcoxon.stat`.

The weights of Bowden et al. (TSD 24, Section 4.2.1.1) are described in the document only as
"derived from the proportions of trial participants on the experimental treatment in each trial
arm over time", which does not determine a formula; they are not defined here, but any such
weights are an instance of `weightedLogRank`.

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

open Classical in
/-- The number of patients of the sample `S` at risk at time `t`: those with `S_i ≥ t`. -/
noncomputable def atRisk {m : ℕ} (S : Fin m → ℝ) (t : ℝ) : ℕ := #{i | t ≤ S i}

open Classical in
/-- The number of events of the sample `S` at time `t`: those with `S_i = t`. -/
noncomputable def deaths {m : ℕ} (S : Fin m → ℝ) (t : ℝ) : ℕ := #{i | S i = t}

open Classical in
/-- The distinct event times of the pooled sample. -/
noncomputable def eventTimes {m n : ℕ} (E : Fin m → ℝ) (C : Fin n → ℝ) : Finset ℝ :=
  univ.image E ∪ univ.image C

variable {m n : ℕ}

/-- Observed minus expected events in the experimental arm at time `t`:
`d_E(t) - (d_E(t) + d_C(t)) n_E(t) / (n_E(t) + n_C(t))`. -/
noncomputable def oe (E : Fin m → ℝ) (C : Fin n → ℝ) (t : ℝ) : ℝ :=
  deaths E t - (deaths E t + deaths C t) * atRisk E t / (atRisk E t + atRisk C t)

/-- **The weighted log-rank statistic** with weight `W t` at each event time:
`Σ_t W t (d_E(t) - d(t) n_E(t) / n(t))`. -/
noncomputable def weightedLogRank (W : ℝ → ℝ) (E : Fin m → ℝ) (C : Fin n → ℝ) : ℝ :=
  ∑ t ∈ eventTimes E C, W t * oe E C t

/-- **The log-rank statistic**: every event time has weight `1`. -/
noncomputable def logRank (E : Fin m → ℝ) (C : Fin n → ℝ) : ℝ :=
  weightedLogRank (fun _ ↦ 1) E C

/-- The weight of the Gehan (Wilcoxon) statistic: the number at risk `n(t)`. -/
noncomputable def gehanWeight (E : Fin m → ℝ) (C : Fin n → ℝ) (t : ℝ) : ℝ :=
  atRisk E t + atRisk C t

/-- **The Gehan (Wilcoxon) statistic**: each event time is weighted by the number at risk. -/
noncomputable def gehan (E : Fin m → ℝ) (C : Fin n → ℝ) : ℝ :=
  weightedLogRank (gehanWeight E C) E C

/-- A weighted log-rank statistic whose weight is a function `g` of the risk set sizes of the two
arms. The log-rank and Gehan statistics are instances (`logRank_eq_riskWeighted`,
`gehan_eq_riskWeighted`). -/
noncomputable def riskWeighted (g : ℕ → ℕ → ℝ) (E : Fin m → ℝ) (C : Fin n → ℝ) : ℝ :=
  weightedLogRank (fun t ↦ g (atRisk E t) (atRisk C t)) E C

theorem logRank_eq_riskWeighted (E : Fin m → ℝ) (C : Fin n → ℝ) :
    logRank E C = riskWeighted (fun _ _ ↦ 1) E C := rfl

theorem gehan_eq_riskWeighted (E : Fin m → ℝ) (C : Fin n → ℝ) :
    gehan E C = riskWeighted (fun a b ↦ (a : ℝ) + b) E C := rfl

/-- **The Mann-Whitney statistic** `Σ_{i, j} sign (E_i - C_j)`. -/
noncomputable def mannWhitney (E : Fin m → ℝ) (C : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, Real.sign (E i - C j)

/-! ### Elementary facts -/

theorem deaths_le_atRisk (S : Fin m → ℝ) (t : ℝ) : deaths S t ≤ atRisk S t := by
  classical
  unfold deaths atRisk
  exact card_le_card fun i ↦ by simp only [mem_filter, mem_univ, true_and]; intro h; rw [h]

theorem mem_eventTimes_left (E : Fin m → ℝ) (C : Fin n → ℝ) (i : Fin m) :
    E i ∈ eventTimes E C := by
  classical
  simp [eventTimes]

theorem mem_eventTimes_right (E : Fin m → ℝ) (C : Fin n → ℝ) (j : Fin n) :
    C j ∈ eventTimes E C := by
  classical
  simp [eventTimes]

/-- If nobody is at risk at `t`, there are no events at `t`. -/
theorem deaths_eq_zero_of_atRisk (S : Fin m → ℝ) {t : ℝ} (h : atRisk S t = 0) :
    deaths S t = 0 :=
  Nat.eq_zero_of_le_zero (h ▸ deaths_le_atRisk S t)

/-- **Sum over the events of one arm.** For any `G`,
`Σ_{t ∈ eventTimes} d_E(t) G t = Σ_i G (E_i)`. -/
theorem sum_deaths_left (E : Fin m → ℝ) (C : Fin n → ℝ) (G : ℝ → ℝ) :
    ∑ t ∈ eventTimes E C, (deaths E t : ℝ) * G t = ∑ i, G (E i) := by
  classical
  rw [← sum_fiberwise_of_maps_to' (s := univ) (t := eventTimes E C) (g := E)
    (fun i _ ↦ mem_eventTimes_left E C i) G]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [sum_const, nsmul_eq_mul, deaths]

/-- The same for the control arm. -/
theorem sum_deaths_right (E : Fin m → ℝ) (C : Fin n → ℝ) (G : ℝ → ℝ) :
    ∑ t ∈ eventTimes E C, (deaths C t : ℝ) * G t = ∑ j, G (C j) := by
  classical
  rw [← sum_fiberwise_of_maps_to' (s := univ) (t := eventTimes E C) (g := C)
    (fun j _ ↦ mem_eventTimes_right E C j) G]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [sum_const, nsmul_eq_mul, deaths]

/-- At an event time some patient has the event. -/
theorem deaths_add_pos {E : Fin m → ℝ} {C : Fin n → ℝ} {t : ℝ} (ht : t ∈ eventTimes E C) :
    (0 : ℝ) < deaths E t + deaths C t := by
  classical
  simp only [eventTimes, mem_union, mem_image, mem_univ, true_and] at ht
  rcases ht with ⟨i, hi⟩ | ⟨j, hj⟩
  · have : 0 < deaths E t := card_pos.2 ⟨i, by simp [hi]⟩
    have := Nat.cast_pos (α := ℝ).2 this
    positivity
  · have : 0 < deaths C t := card_pos.2 ⟨j, by simp [hj]⟩
    have := Nat.cast_pos (α := ℝ).2 this
    positivity

/-- **Sum over event times as a sum over patients.** For any `F`,
`Σ_{t ∈ eventTimes} F t = Σ_i F (E_i) / d(E_i) + Σ_j F (C_j) / d(C_j)`, with `d` the number of
events in the pooled sample. -/
theorem sum_eventTimes_eq (E : Fin m → ℝ) (C : Fin n → ℝ) (F : ℝ → ℝ) :
    ∑ t ∈ eventTimes E C, F t =
      ∑ i, F (E i) / (deaths E (E i) + deaths C (E i)) +
        ∑ j, F (C j) / (deaths E (C j) + deaths C (C j)) := by
  rw [← sum_deaths_left E C (fun t ↦ F t / (deaths E t + deaths C t)),
    ← sum_deaths_right E C (fun t ↦ F t / (deaths E t + deaths C t)), ← sum_add_distrib]
  refine sum_congr rfl fun t ht ↦ ?_
  have := deaths_add_pos ht
  field_simp

/-! ### Antisymmetry and equal samples -/

theorem eventTimes_swap (E : Fin m → ℝ) (C : Fin n → ℝ) : eventTimes C E = eventTimes E C := by
  classical
  simp only [eventTimes]
  exact union_comm _ _

/-- Observed minus expected in the control arm is minus that in the experimental arm. -/
theorem oe_swap (E : Fin m → ℝ) (C : Fin n → ℝ) (t : ℝ) : oe C E t = -oe E C t := by
  unfold oe
  by_cases h : (atRisk E t : ℝ) + atRisk C t = 0
  · have hE : atRisk E t = 0 := by
      have := Nat.cast_nonneg (α := ℝ) (atRisk E t)
      have := Nat.cast_nonneg (α := ℝ) (atRisk C t)
      exact_mod_cast (show (atRisk E t : ℝ) = 0 by linarith)
    have hC : atRisk C t = 0 := by
      have := Nat.cast_nonneg (α := ℝ) (atRisk E t)
      have := Nat.cast_nonneg (α := ℝ) (atRisk C t)
      exact_mod_cast (show (atRisk C t : ℝ) = 0 by linarith)
    simp [hE, hC, deaths_eq_zero_of_atRisk _ hE, deaths_eq_zero_of_atRisk _ hC]
  · have h' : (atRisk C t : ℝ) + atRisk E t ≠ 0 := by rwa [add_comm]
    field_simp
    ring

/-- **Antisymmetry.** Swapping the arms changes the sign of every weighted log-rank statistic. -/
theorem weightedLogRank_swap (W : ℝ → ℝ) (E : Fin m → ℝ) (C : Fin n → ℝ) :
    weightedLogRank W C E = -weightedLogRank W E C := by
  rw [weightedLogRank, weightedLogRank, eventTimes_swap, ← sum_neg_distrib]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [oe_swap, mul_neg]

theorem logRank_swap (E : Fin m → ℝ) (C : Fin n → ℝ) : logRank C E = -logRank E C :=
  weightedLogRank_swap _ E C

theorem gehan_swap (E : Fin m → ℝ) (C : Fin n → ℝ) : gehan C E = -gehan E C := by
  have : gehanWeight C E = gehanWeight E C := by funext t; simp only [gehanWeight]; ring
  rw [gehan, gehan, this, weightedLogRank_swap]

/-- **Equal samples give zero.** If the control sample is a relabeling of the experimental one,
`C (σ i) = E i` for a bijection `σ`, every weighted log-rank statistic is zero. -/
theorem weightedLogRank_eq_zero_of_equiv (W : ℝ → ℝ) (E : Fin m → ℝ) (C : Fin n → ℝ)
    (σ : Fin m ≃ Fin n) (hσ : ∀ i, C (σ i) = E i) : weightedLogRank W E C = 0 := by
  classical
  have hr : ∀ t, atRisk C t = atRisk E t := fun t ↦
    (card_equiv σ fun i ↦ by simp [hσ]).symm
  have hd : ∀ t, deaths C t = deaths E t := fun t ↦
    (card_equiv σ fun i ↦ by simp [hσ]).symm
  refine sum_eq_zero fun t _ ↦ ?_
  rw [oe, hr, hd]
  by_cases h : atRisk E t = 0
  · simp [h, deaths_eq_zero_of_atRisk _ h]
  · have : (atRisk E t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h
    have : (atRisk E t : ℝ) + atRisk E t ≠ 0 := by positivity
    field_simp
    ring

/-! ### Dependence on the ranks only -/

/-- The pooled sample, indexed by `Fin m ⊕ Fin n`. -/
def pool (E : Fin m → ℝ) (C : Fin n → ℝ) : Fin m ⊕ Fin n → ℝ := Sum.elim E C

/-- Two pooled samples have the same order pattern. -/
def SameOrder (E : Fin m → ℝ) (C : Fin n → ℝ) (E' : Fin m → ℝ) (C' : Fin n → ℝ) : Prop :=
  ∀ a b, pool E C a ≤ pool E C b ↔ pool E' C' a ≤ pool E' C' b

/-- A risk-set weighted statistic written as a sum over patients. -/
theorem riskWeighted_eq_sum (g : ℕ → ℕ → ℝ) (E : Fin m → ℝ) (C : Fin n → ℝ) :
    riskWeighted g E C =
      ∑ i, g (atRisk E (E i)) (atRisk C (E i)) * oe E C (E i) /
          (deaths E (E i) + deaths C (E i)) +
        ∑ j, g (atRisk E (C j)) (atRisk C (C j)) * oe E C (C j) /
          (deaths E (C j) + deaths C (C j)) :=
  sum_eventTimes_eq E C _

/-- **A risk-set weighted statistic depends only on the order pattern** of the pooled sample. -/
theorem riskWeighted_congr_order (g : ℕ → ℕ → ℝ) {E E' : Fin m → ℝ} {C C' : Fin n → ℝ}
    (h : SameOrder E C E' C') : riskWeighted g E C = riskWeighted g E' C' := by
  classical
  -- all counts at the time of a pooled patient `a` depend on the pattern only
  have kE : ∀ a, (∀ i, pool E C a ≤ E i ↔ pool E' C' a ≤ E' i) ∧
      (∀ i, E i = pool E C a ↔ E' i = pool E' C' a) := fun a ↦
    ⟨fun i ↦ h a (Sum.inl i), fun i ↦ by
      rw [le_antisymm_iff, le_antisymm_iff]
      exact and_congr (h (Sum.inl i) a) (h a (Sum.inl i))⟩
  have kC : ∀ a, (∀ j, pool E C a ≤ C j ↔ pool E' C' a ≤ C' j) ∧
      (∀ j, C j = pool E C a ↔ C' j = pool E' C' a) := fun a ↦
    ⟨fun j ↦ h a (Sum.inr j), fun j ↦ by
      rw [le_antisymm_iff, le_antisymm_iff]
      exact and_congr (h (Sum.inr j) a) (h a (Sum.inr j))⟩
  have cnt : ∀ a, atRisk E (pool E C a) = atRisk E' (pool E' C' a) ∧
      atRisk C (pool E C a) = atRisk C' (pool E' C' a) ∧
      deaths E (pool E C a) = deaths E' (pool E' C' a) ∧
      deaths C (pool E C a) = deaths C' (pool E' C' a) := fun a ↦ by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [atRisk]; congr 1; ext i; simp only [mem_filter, mem_univ, true_and]
      exact (kE a).1 i
    · simp only [atRisk]; congr 1; ext i; simp only [mem_filter, mem_univ, true_and]
      exact (kC a).1 i
    · simp only [deaths]; congr 1; ext i; simp only [mem_filter, mem_univ, true_and]
      exact (kE a).2 i
    · simp only [deaths]; congr 1; ext i; simp only [mem_filter, mem_univ, true_and]
      exact (kC a).2 i
  have term : ∀ a, g (atRisk E (pool E C a)) (atRisk C (pool E C a)) * oe E C (pool E C a) /
      (deaths E (pool E C a) + deaths C (pool E C a)) =
      g (atRisk E' (pool E' C' a)) (atRisk C' (pool E' C' a)) * oe E' C' (pool E' C' a) /
      (deaths E' (pool E' C' a) + deaths C' (pool E' C' a)) := fun a ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := cnt a
    simp only [oe, h1, h2, h3, h4]
  rw [riskWeighted_eq_sum, riskWeighted_eq_sum]
  congr 1
  · exact sum_congr rfl fun i _ ↦ term (Sum.inl i)
  · exact sum_congr rfl fun j _ ↦ term (Sum.inr j)

/-- **Invariance under strictly increasing transformations.** A risk-set weighted statistic (in
particular the log-rank and Gehan statistics) is a function of the ranks of the pooled sample. -/
theorem riskWeighted_comp_strictMono (g : ℕ → ℕ → ℝ) (E : Fin m → ℝ) (C : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : StrictMono f) : riskWeighted g (f ∘ E) (f ∘ C) = riskWeighted g E C := by
  refine riskWeighted_congr_order g fun a b ↦ ?_
  cases a <;> cases b <;> simp [pool, hf.le_iff_le]

theorem logRank_comp_strictMono (E : Fin m → ℝ) (C : Fin n → ℝ) {f : ℝ → ℝ}
    (hf : StrictMono f) : logRank (f ∘ E) (f ∘ C) = logRank E C :=
  riskWeighted_comp_strictMono (fun _ _ ↦ 1) E C hf

theorem gehan_comp_strictMono (E : Fin m → ℝ) (C : Fin n → ℝ) {f : ℝ → ℝ}
    (hf : StrictMono f) : gehan (f ∘ E) (f ∘ C) = gehan E C :=
  riskWeighted_comp_strictMono (fun a b ↦ (a : ℝ) + b) E C hf

/-! ### Gehan and Mann-Whitney -/

/-- `#{j | t ≤ C_j}` as a sum of indicators. -/
theorem atRisk_eq_sum (S : Fin m → ℝ) (t : ℝ) :
    (atRisk S t : ℝ) = ∑ i, if t ≤ S i then 1 else 0 := by
  classical
  rw [atRisk, card_filter]; push_cast; rfl

/-- `#{i | S_i = t}` as a sum of indicators. -/
theorem deaths_eq_sum (S : Fin m → ℝ) (t : ℝ) :
    (deaths S t : ℝ) = ∑ i, if S i = t then 1 else 0 := by
  classical
  rw [deaths, card_filter]; push_cast; rfl

/-- **Without censoring the Gehan statistic is minus the Mann-Whitney statistic**:
`gehan E C = -Σ_{i, j} sign (E_i - C_j)`. -/
theorem gehan_eq_neg_mannWhitney (E : Fin m → ℝ) (C : Fin n → ℝ) :
    gehan E C = -mannWhitney E C := by
  have hterm : ∀ t, gehanWeight E C t * oe E C t =
      (deaths E t : ℝ) * atRisk C t - (deaths C t : ℝ) * atRisk E t := fun t ↦ by
    unfold gehanWeight oe
    by_cases h : (atRisk E t : ℝ) + atRisk C t = 0
    · have hE : atRisk E t = 0 := by
        have := Nat.cast_nonneg (α := ℝ) (atRisk E t)
        have := Nat.cast_nonneg (α := ℝ) (atRisk C t)
        exact_mod_cast (show (atRisk E t : ℝ) = 0 by linarith)
      have hC : atRisk C t = 0 := by
        have := Nat.cast_nonneg (α := ℝ) (atRisk E t)
        have := Nat.cast_nonneg (α := ℝ) (atRisk C t)
        exact_mod_cast (show (atRisk C t : ℝ) = 0 by linarith)
      simp [hE, hC]
    · field_simp
      ring
  rw [gehan, weightedLogRank]
  simp only [hterm, sum_sub_distrib]
  rw [sum_deaths_left E C (fun t ↦ (atRisk C t : ℝ)),
    sum_deaths_right E C (fun t ↦ (atRisk E t : ℝ))]
  simp only [atRisk_eq_sum, mannWhitney]
  rw [sum_comm (s := (univ : Finset (Fin n))), ← sum_sub_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_sub_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  rcases lt_trichotomy (E i) (C j) with hlt | heq | hgt
  · simp [Real.sign_of_neg (show E i - C j < 0 by linarith), hlt.le, not_le.2 hlt]
  · simp [heq, Real.sign_zero]
  · simp [Real.sign_of_pos (show 0 < E i - C j by linarith), hgt.le, not_le.2 hgt]

/-! ### g-statistics as functions of `ψ` -/

/-- The candidate untreated time `T^c + exp ψ T^e` of a patient with data `(T^c, T^e)`. -/
noncomputable def untreated (ψ : ℝ) (p : ℝ × ℝ) : ℝ := p.1 + Real.exp ψ * p.2

/-- A g-statistic: a two-sample statistic evaluated at the candidate untreated times of the
experimental and control samples of pairs `(T^c, T^e)`. -/
noncomputable def gStat (stat : (Fin m → ℝ) → (Fin n → ℝ) → ℝ) (E : Fin m → ℝ × ℝ)
    (C : Fin n → ℝ × ℝ) (ψ : ℝ) : ℝ :=
  stat (fun i ↦ untreated ψ (E i)) (fun j ↦ untreated ψ (C j))

/-- **The g-statistic is piecewise constant in `ψ`.** For a risk-set weighted statistic, two
values `ψ`, `ψ'` at which the pooled candidate untreated times are in the same order give the
same value. So the statistic changes only at values of `ψ` where two candidate untreated times
cross. -/
theorem gStat_congr_order (g : ℕ → ℕ → ℝ) (E : Fin m → ℝ × ℝ) (C : Fin n → ℝ × ℝ) {ψ ψ' : ℝ}
    (h : SameOrder (fun i ↦ untreated ψ (E i)) (fun j ↦ untreated ψ (C j))
      (fun i ↦ untreated ψ' (E i)) (fun j ↦ untreated ψ' (C j))) :
    gStat (riskWeighted g) E C ψ = gStat (riskWeighted g) E C ψ' :=
  riskWeighted_congr_order g h

/-- The Gehan g-statistic is minus the Wilcoxon (Mann-Whitney) g-statistic
`RPSFTMCounterexample.Wilcoxon.stat`. -/
theorem gStat_gehan_eq_neg_wilcoxon (E : Fin m → ℝ × ℝ) (C : Fin n → ℝ × ℝ) (ψ : ℝ) :
    gStat gehan E C ψ = -RPSFTMCounterexample.Wilcoxon.stat E C ψ := by
  rw [gStat, gehan_eq_neg_mannWhitney]; rfl

end GTest

end StructuralNested

end CausalInference
