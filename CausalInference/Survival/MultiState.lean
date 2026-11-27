/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Discrete-time multi-state models and the illness-death model

A cohort moves in discrete periods through finitely many alive states `S` and one absorbing
death state.

## Main definitions

* `occupancy π P t s`: the proportion of the cohort in alive state `s` at the start of period
  `t`, with initial distribution `π` and one-period transition probabilities `P s s'` between
  alive states. The probability of death in a period from state `s` is
  `deathProb P s = 1 - ∑ s', P s s'`.
* `aliveMass`, `deathMass`, `deathHazard`: the proportion alive at the start of period `t`,
  the proportion dying in period `t`, and the marginal death hazard (deaths in the period
  among those alive at its start).
* `stateShare π P t s`: the distribution of the alive states among those alive at the start of
  period `t`.
* `deathLaw π P N`: the law on `ℕ` of the death period, truncated at a horizon `N` (the value
  `N` stands for being alive at the start of period `N`), as a measure, so that the library's
  `hazard` and `survival` of `Survival/Basic.lean` apply to it.
* The illness-death model (`progFree`, `progressed`): alive states `false` (progression free)
  and `true` (progressed); per period, a progression-free patient progresses with
  probability `a` and dies with probability `b`, and a progressed patient dies with
  probability `c`.

## Main results

* `aliveMass_succ`: the cohort is conserved: `aliveMass (t + 1) = aliveMass t - deathMass t`.
* `deathHazard_eq_sum_stateShare`, `deathHazard_eq_sum_stateShare_of_pos`: the marginal death
  hazard is the average of the state-specific death probabilities weighted by the occupancy
  shares among the living; when the alive mass is positive and every row of transition
  probabilities sums to at most one, the weights are a probability distribution and the hazard
  lies in `[0, 1]`.
* `hazard_deathLaw`, `survival_deathLaw`: for `t < N`, the discrete hazard `P(T = t | T ≥ t)`
  of the death period is the marginal death hazard, and `P(T > t)` is `aliveMass (t + 1)`.
* `illnessDeath_hazard_eq`: in the illness-death model,
  `h t = (b * P₁ t + c * P₂ t) / (P₁ t + P₂ t)` with `P₁ = progFree`, `P₂ = progressed`;
  `illnessDeath_hazard_deathLaw`: this is the library's `hazard` of the death period, and
  `illnessDeath_hazard_deathLaw_of_pos`: with positive alive mass it is the conditional
  probability `P(T = t | T ≥ t)` and lies in `[0, 1]`.
* `illnessDeath_tendsto_hazard`: with constant transition probabilities, `0 < a`,
  `a + b < 1` and `c ≤ 1`, the marginal death hazard converges to `min c (a + b)`.
  `illnessDeath_tendsto_hazard_of_valid`: with `0 ≤ b` and `0 ≤ c` the hazards and the limit
  lie in `[0, 1]`. `illnessDeath_hazard_monotone`: if `b ≤ c` it is nondecreasing.
* `illnessDeath_limit_ne`: a model in which the limit is not the progressed death
  probability `c`.

## Source

NICE Decision Support Unit, Technical Support Document 19, B. Woods, E. Sideris, S. Palmer,
N. Latimer and M. Soares, *Partitioned survival analysis for decision modelling in health care:
a critical review* (2017), Section 2.3 (Figure 3, the three-state model of advanced cancer, and
state membership by cohort simulation in discrete time) and Section 4.1.2
(Figure 4: with constant transition hazards and progression prognostic of death, the hazard of
death "would initially increase ... but then level off once all patients had progressed (the
hazard levels off at the hazard of death for progressed patients, `h₂₃`)"). The document works
in continuous time; this file is the discrete-time analogue with per-period probabilities.
The level reached is `min c (a + b)`: it is `c` exactly when `c ≤ a + b`. If instead
`a + b < c`, the progressed share among the living stays bounded away from one and the hazard
levels off at `a + b` (`illnessDeath_limit_ne`); the document's sentence is conditional on all
patients coming to reside in the progressed state, which is what fails in that case.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CausalInference

namespace Survival

namespace MultiState

variable {S : Type*} [Fintype S] (π : S → ℝ) (P : S → S → ℝ)

/-- The occupancy of alive state `s` at the start of period `t`: `occupancy π P 0 = π` and
`occupancy π P (t + 1) s' = ∑ s, occupancy π P t s * P s s'`. -/
def occupancy : ℕ → S → ℝ
  | 0 => π
  | t + 1 => fun s' => ∑ s, occupancy t s * P s s'

/-- The probability of death in one period from alive state `s`: `1 - ∑ s', P s s'`. -/
def deathProb (s : S) : ℝ := 1 - ∑ s', P s s'

/-- The proportion of the cohort alive at the start of period `t`. -/
def aliveMass (t : ℕ) : ℝ := ∑ s, occupancy π P t s

/-- The proportion of the cohort dying in period `t`: `∑ s, occupancy t s * deathProb s`. -/
def deathMass (t : ℕ) : ℝ := ∑ s, occupancy π P t s * deathProb P s

/-- The marginal death hazard in period `t`: the deaths in period `t` among those alive at its
start, `deathMass t / aliveMass t`. It is a conditional probability only when
`0 < aliveMass t`. -/
noncomputable def deathHazard (t : ℕ) : ℝ := deathMass π P t / aliveMass π P t

/-- The share of alive state `s` among those alive at the start of period `t`. -/
noncomputable def stateShare (t : ℕ) (s : S) : ℝ := occupancy π P t s / aliveMass π P t

theorem occupancy_succ (t : ℕ) (s' : S) :
    occupancy π P (t + 1) s' = ∑ s, occupancy π P t s * P s s' := rfl

/-- Conservation of the cohort: those alive at the start of period `t + 1` are those alive at
the start of period `t` minus those who died in period `t`. -/
theorem aliveMass_succ (t : ℕ) :
    aliveMass π P (t + 1) = aliveMass π P t - deathMass π P t := by
  simp only [aliveMass, deathMass, occupancy_succ, deathProb, mul_sub, mul_one,
    Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-- Occupancies are nonnegative for a nonnegative initial distribution and nonnegative
transition probabilities. -/
theorem occupancy_nonneg (hπ : ∀ s, 0 ≤ π s) (hP : ∀ s s', 0 ≤ P s s') (t : ℕ) (s : S) :
    0 ≤ occupancy π P t s := by
  induction t generalizing s with
  | zero => exact hπ s
  | succ t ih => exact Finset.sum_nonneg fun s' _ => mul_nonneg (ih s') (hP s' s)

/-- Death masses are nonnegative when the occupancies are and every row of transition
probabilities sums to at most one. -/
theorem deathMass_nonneg (hπ : ∀ s, 0 ≤ π s) (hP : ∀ s s', 0 ≤ P s s')
    (hrow : ∀ s, ∑ s', P s s' ≤ 1) (t : ℕ) : 0 ≤ deathMass π P t :=
  Finset.sum_nonneg fun s _ =>
    mul_nonneg (occupancy_nonneg π P hπ hP t s) (sub_nonneg.2 (hrow s))

theorem aliveMass_nonneg (hπ : ∀ s, 0 ≤ π s) (hP : ∀ s s', 0 ≤ P s s') (t : ℕ) :
    0 ≤ aliveMass π P t :=
  Finset.sum_nonneg fun s _ => occupancy_nonneg π P hπ hP t s

/-- The marginal death hazard is the average of the state-specific death probabilities
weighted by the shares of the states among the living. As an algebraic identity it also holds
when the alive mass is zero (both sides are then `0` by the convention `x / 0 = 0`); the
probability reading is `deathHazard_eq_sum_stateShare_of_pos`. -/
theorem deathHazard_eq_sum_stateShare (t : ℕ) :
    deathHazard π P t = ∑ s, stateShare π P t s * deathProb P s := by
  simp only [deathHazard, deathMass, stateShare, div_mul_eq_mul_div, ← Finset.sum_div]

/-- The probability form of `deathHazard_eq_sum_stateShare`: for a nonnegative initial
distribution and nonnegative transition probabilities whose rows sum to at most one, when the
alive mass at the start of period `t` is positive, the state shares among the living are
nonnegative and sum to one, the marginal death hazard is their average of the state-specific
death probabilities, and it lies in `[0, 1]`. -/
theorem deathHazard_eq_sum_stateShare_of_pos (hπ : ∀ s, 0 ≤ π s) (hP : ∀ s s', 0 ≤ P s s')
    (hrow : ∀ s, ∑ s', P s s' ≤ 1) (t : ℕ) (ht : 0 < aliveMass π P t) :
    (∀ s, 0 ≤ stateShare π P t s) ∧ ∑ s, stateShare π P t s = 1 ∧
      deathHazard π P t = ∑ s, stateShare π P t s * deathProb P s ∧
      0 ≤ deathHazard π P t ∧ deathHazard π P t ≤ 1 := by
  have hd := deathMass_nonneg π P hπ hP hrow t
  have hle : deathMass π P t ≤ aliveMass π P t := by
    have := aliveMass_nonneg π P hπ hP (t + 1)
    rw [aliveMass_succ] at this
    linarith
  refine ⟨fun s => div_nonneg (occupancy_nonneg π P hπ hP t s) ht.le, ?_,
    deathHazard_eq_sum_stateShare π P t, div_nonneg hd ht.le, (div_le_one ht).2 hle⟩
  simp only [stateShare, ← Finset.sum_div]
  exact div_self ht.ne'

/-- Telescoping: the deaths in periods `t, ..., N - 1` plus those alive at the start of period
`N` are those alive at the start of period `t`. -/
theorem sum_Ico_deathMass_add_aliveMass {t N : ℕ} (h : t ≤ N) :
    ∑ s ∈ Finset.Ico t N, deathMass π P s + aliveMass π P N = aliveMass π P t := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, aliveMass_succ]
    linarith

/-! ### The law of the death period -/

/-- The mass that `deathLaw π P N` gives to the period `t`: the death mass for `t < N`, the
alive mass at the start of period `N` for `t = N`, and `0` after `N`. -/
noncomputable def deathLawMass (N t : ℕ) : ℝ :=
  if t < N then deathMass π P t else if t = N then aliveMass π P N else 0

/-- The law of the death period `T` of a member of the cohort, truncated at the horizon `N`:
`P(T = t) = deathMass t` for `t < N` and `P(T = N) = aliveMass N`, where `T = N` stands for
being alive at the start of period `N`. -/
noncomputable def deathLaw (N : ℕ) : Measure ℕ :=
  ∑ t ∈ Finset.range (N + 1), ENNReal.ofReal (deathLawMass π P N t) • Measure.dirac t

variable (hπ : ∀ s, 0 ≤ π s) (hP : ∀ s s', 0 ≤ P s s') (hrow : ∀ s, ∑ s', P s s' ≤ 1)
include hπ hP hrow

theorem deathLawMass_nonneg (N t : ℕ) : 0 ≤ deathLawMass π P N t := by
  unfold deathLawMass
  split_ifs
  · exact deathMass_nonneg π P hπ hP hrow t
  · exact aliveMass_nonneg π P hπ hP N
  · exact le_rfl

/-- The probability that `deathLaw π P N` gives to a set `A` of periods. -/
theorem deathLaw_real (N : ℕ) (A : Set ℕ) :
    (deathLaw π P N).real A =
      ∑ t ∈ Finset.range (N + 1), A.indicator (deathLawMass π P N) t := by
  rw [measureReal_def, deathLaw, FunLike.coe_sum, Finset.sum_apply]
  rw [ENNReal.toReal_sum (fun t _ => by by_cases h : t ∈ A <;> simp [h])]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t ∈ A <;>
    simp [h, ENNReal.toReal_ofReal (deathLawMass_nonneg π P hπ hP hrow N t)]

/-- For `t < N`, the probability of death in period `t` under `deathLaw π P N` is the death
mass of period `t`. -/
theorem deathLaw_real_eq {N t : ℕ} (ht : t < N) :
    (deathLaw π P N).real {x | x = t} = deathMass π P t := by
  rw [deathLaw_real π P hπ hP hrow]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_ite_eq', Finset.mem_range]
  simp [deathLawMass, ht, Nat.lt_succ_of_lt ht]

/-- For `t ≤ N`, the probability of being alive at the start of period `t` under
`deathLaw π P N` is the alive mass at the start of period `t`. -/
theorem deathLaw_real_le {N t : ℕ} (ht : t ≤ N) :
    (deathLaw π P N).real {x | t ≤ x} = aliveMass π P t := by
  rw [deathLaw_real π P hπ hP hrow]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [← Finset.sum_filter, Finset.range_eq_Ico, Finset.Ico_filter_le, max_eq_right (Nat.zero_le t),
    Finset.sum_Ico_succ_top ht, ← sum_Ico_deathMass_add_aliveMass π P ht]
  congr 1
  · refine Finset.sum_congr rfl fun s hs => ?_
    simp [deathLawMass, (Finset.mem_Ico.1 hs).2]
  · simp [deathLawMass]

/-- `deathLaw π P N` is a probability measure when `π` is a probability distribution on the
alive states. -/
theorem isProbabilityMeasure_deathLaw (hπ1 : ∑ s, π s = 1) (N : ℕ) :
    IsProbabilityMeasure (deathLaw π P N) := by
  have h := deathLaw_real_le π P hπ hP hrow (Nat.zero_le N)
  simp only [zero_le, Set.ofPred_true] at h
  refine ⟨(ENNReal.toReal_eq_one_iff _).1 ?_⟩
  rw [← measureReal_def, h, aliveMass]
  exact hπ1

/-- The discrete hazard of the death period, `P(T = t | T ≥ t)` in the sense of
`Survival.hazard`, is the marginal death hazard of the cohort, for every period `t` before the
horizon. The identity holds because numerators and denominators agree separately; when the
alive mass at the start of period `t` is zero both sides are the conventional value `0`, and
only when it is positive is it an equality of conditional probabilities. Together with
`deathHazard_eq_sum_stateShare_of_pos` this says that the hazard of the death time is the
occupancy-weighted average of the state-specific death probabilities. -/
theorem hazard_deathLaw {N t : ℕ} (ht : t < N) :
    hazard (deathLaw π P N) id t = deathHazard π P t := by
  simp only [hazard, atRisk, id]
  rw [deathLaw_real_eq π P hπ hP hrow ht, deathLaw_real_le π P hπ hP hrow ht.le]
  rfl

/-- The survival `P(T > t)` of the death period is the alive mass at the start of period
`t + 1`, for every period `t` before the horizon. -/
theorem survival_deathLaw {N t : ℕ} (ht : t < N) :
    survival (deathLaw π P N) id t = aliveMass π P (t + 1) := by
  simp only [survival, id, ← Nat.succ_le_iff]
  exact deathLaw_real_le π P hπ hP hrow ht

omit hπ hP hrow

/-! ### The illness-death model -/

/-- The initial distribution of the illness-death model: everybody starts progression free
(state `false`); state `true` is the progressed state. -/
def idInit (s : Bool) : ℝ := if s then 0 else 1

/-- The one-period transition probabilities of the illness-death model between the alive
states: a progression-free patient stays progression free with probability `1 - a - b` and
progresses with probability `a` (and dies with probability `b`); a progressed patient stays
progressed with probability `1 - c` (and dies with probability `c`); there is no return from
progression. -/
def idTrans (a b c : ℝ) : Bool → Bool → ℝ
  | false, false => 1 - a - b
  | false, true => a
  | true, false => 0
  | true, true => 1 - c

/-- The progression-free proportion `P₁ t` of the cohort at the start of period `t`. -/
def progFree (a b c : ℝ) (t : ℕ) : ℝ := occupancy idInit (idTrans a b c) t false

/-- The progressed (and alive) proportion `P₂ t` of the cohort at the start of period `t`. -/
def progressed (a b c : ℝ) (t : ℕ) : ℝ := occupancy idInit (idTrans a b c) t true

/-- The marginal death hazard (overall survival hazard) of the illness-death model in period
`t`. -/
noncomputable def idHazard (a b c : ℝ) (t : ℕ) : ℝ := deathHazard idInit (idTrans a b c) t

/-- The ratio `P₂ t / P₁ t` of progressed to progression-free patients among the living. -/
noncomputable def progRatio (a b c : ℝ) (t : ℕ) : ℝ := progressed a b c t / progFree a b c t

variable (a b c : ℝ)

theorem deathProb_idTrans_false : deathProb (idTrans a b c) false = b := by
  simp only [deathProb, Fintype.sum_bool, idTrans]; ring

theorem deathProb_idTrans_true : deathProb (idTrans a b c) true = c := by
  simp only [deathProb, Fintype.sum_bool, idTrans]; ring

theorem progFree_zero : progFree a b c 0 = 1 := rfl

theorem progressed_zero : progressed a b c 0 = 0 := rfl

theorem progFree_succ (t : ℕ) : progFree a b c (t + 1) = (1 - a - b) * progFree a b c t := by
  simp only [progFree, occupancy_succ, Fintype.sum_bool, idTrans]; ring

theorem progressed_succ (t : ℕ) :
    progressed a b c (t + 1) = a * progFree a b c t + (1 - c) * progressed a b c t := by
  simp only [progressed, progFree, occupancy_succ, Fintype.sum_bool, idTrans]; ring

theorem progFree_eq (t : ℕ) : progFree a b c t = (1 - a - b) ^ t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [progFree_succ, ih, pow_succ, mul_comm]

/-- The marginal death hazard of the illness-death model is the occupancy-weighted average
`h t = (b * P₁ t + c * P₂ t) / (P₁ t + P₂ t)` of the death probabilities from the
progression-free and the progressed states. -/
theorem illnessDeath_hazard_eq (t : ℕ) :
    idHazard a b c t =
      (b * progFree a b c t + c * progressed a b c t) /
        (progFree a b c t + progressed a b c t) := by
  rw [idHazard, deathHazard, deathMass, aliveMass, Fintype.sum_bool, Fintype.sum_bool,
    deathProb_idTrans_true, deathProb_idTrans_false, progFree, progressed]
  ring

variable {a b c}

theorem progFree_pos (hab : a + b < 1) (t : ℕ) : 0 < progFree a b c t := by
  rw [progFree_eq]; exact pow_pos (by linarith) t

theorem progressed_nonneg (ha : 0 ≤ a) (hab : a + b < 1) (hc : c ≤ 1) (t : ℕ) :
    0 ≤ progressed a b c t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [progressed_succ]
    have := progFree_pos (c := c) hab t
    have : 0 ≤ 1 - c := by linarith
    positivity

theorem progRatio_nonneg (ha : 0 ≤ a) (hab : a + b < 1) (hc : c ≤ 1) (t : ℕ) :
    0 ≤ progRatio a b c t :=
  div_nonneg (progressed_nonneg ha hab hc t) (progFree_pos hab t).le

/-- The recursion of the ratio `R t = P₂ t / P₁ t`:
`R (t + 1) = (a + (1 - c) * R t) / (1 - a - b)`. -/
theorem progRatio_succ (hab : a + b < 1) (t : ℕ) :
    progRatio a b c (t + 1) = (a + (1 - c) * progRatio a b c t) / (1 - a - b) := by
  have h1 := progFree_pos (c := c) hab t
  have hx : 1 - a - b ≠ 0 := by linarith
  rw [progRatio, progRatio, progressed_succ, progFree_succ]
  field_simp

/-- The marginal death hazard in terms of the ratio `R t = P₂ t / P₁ t`:
`h t = c - (c - b) / (1 + R t)`. -/
theorem illnessDeath_hazard_eq_ratio (ha : 0 ≤ a) (hab : a + b < 1) (hc : c ≤ 1) (t : ℕ) :
    idHazard a b c t = c - (c - b) / (1 + progRatio a b c t) := by
  have h1 := progFree_pos (c := c) hab t
  have h2 := progressed_nonneg ha hab hc t
  have h3 : progFree a b c t + progressed a b c t ≠ 0 := by linarith
  rw [illnessDeath_hazard_eq, progRatio, one_add_div h1.ne', div_div_eq_mul_div]
  field_simp
  ring

/-- When `a + b < c`, the ratio has the closed form
`R t = a / (c - a - b) * (1 - ρ ^ t)` with `ρ = (1 - c) / (1 - a - b)`. -/
theorem progRatio_eq_of_lt (hab : a + b < 1) (hlt : a + b < c) (t : ℕ) :
    progRatio a b c t = a / (c - a - b) * (1 - ((1 - c) / (1 - a - b)) ^ t) := by
  have hx : 1 - a - b ≠ 0 := by linarith
  have hy : c - a - b ≠ 0 := by linarith
  induction t with
  | zero => simp [progRatio, progressed_zero]
  | succ t ih =>
    rw [progRatio_succ hab, ih, pow_succ]
    field_simp
    ring

/-- When `c ≤ a + b`, the ratio grows at least linearly: `t * (a / (1 - a - b)) ≤ R t`. -/
theorem progRatio_ge_of_le (ha : 0 ≤ a) (hab : a + b < 1) (hc : c ≤ 1) (hge : c ≤ a + b)
    (t : ℕ) : t * (a / (1 - a - b)) ≤ progRatio a b c t := by
  have hx : 0 < 1 - a - b := by linarith
  induction t with
  | zero => simp [progRatio, progressed_zero]
  | succ t ih =>
    rw [progRatio_succ hab, Nat.cast_succ, le_div_iff₀ hx]
    have hR := progRatio_nonneg ha hab hc t
    have h1 : (↑t + 1) * (a / (1 - a - b)) * (1 - a - b) = t * a + a := by field_simp
    rw [h1]
    have h2 : t * a ≤ progRatio a b c t * (1 - a - b) := by
      have := mul_le_mul_of_nonneg_right ih hx.le
      rwa [mul_assoc, div_mul_cancel₀ _ hx.ne'] at this
    nlinarith

/-- The ratio `R t = P₂ t / P₁ t` is nondecreasing: the progressed share among the living
grows over time. -/
theorem progRatio_monotone (ha : 0 ≤ a) (hab : a + b < 1) (hc : c ≤ 1) :
    Monotone (progRatio a b c) := by
  have hx : 0 < 1 - a - b := by linarith
  have key : ∀ t, progRatio a b c (t + 1) - progRatio a b c t =
      a / (1 - a - b) * ((1 - c) / (1 - a - b)) ^ t := by
    intro t
    induction t with
    | zero =>
      rw [progRatio_succ hab 0]
      simp [progRatio, progressed_zero]
    | succ t ih =>
      rw [progRatio_succ hab (t + 1), progRatio_succ hab t, pow_succ, ← mul_assoc, ← ih,
        progRatio_succ hab t]
      field_simp
      ring
  refine monotone_nat_of_le_succ fun t => ?_
  have := key t
  have : 0 ≤ a / (1 - a - b) * ((1 - c) / (1 - a - b)) ^ t := by
    have : 0 ≤ (1 - c) / (1 - a - b) := div_nonneg (by linarith) hx.le
    positivity
  linarith

/-- If death is at least as likely from the progressed state as from the progression-free
state (`b ≤ c`), the marginal death hazard of the illness-death model is nondecreasing. -/
theorem illnessDeath_hazard_monotone (ha : 0 ≤ a) (hab : a + b < 1) (hc : c ≤ 1)
    (hbc : b ≤ c) : Monotone (idHazard a b c) := by
  intro s t hst
  rw [illnessDeath_hazard_eq_ratio ha hab hc, illnessDeath_hazard_eq_ratio ha hab hc]
  have h0 := progRatio_nonneg ha hab hc s
  have h1 := progRatio_monotone ha hab hc hst
  have : (c - b) / (1 + progRatio a b c t) ≤ (c - b) / (1 + progRatio a b c s) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  linarith

/-- The level reached by the marginal death hazard of the illness-death model (TSD 19,
Section 4.1.2, Figure 4, discrete-time version). With constant per-period probabilities,
`0 < a` (progression possible), `a + b < 1` and `c ≤ 1`, the marginal death hazard
converges to `min c (a + b)`. It levels off at the progressed death probability `c` exactly
when `c ≤ a + b`; when `a + b < c` the progressed share among the living converges to
`a / (c - b) < 1` and the hazard levels off at `a + b`. This is a statement about the
algebraic recursion and needs no sign condition on `b` or `c`; the probability reading, with
`0 ≤ b` and `0 ≤ c`, is `illnessDeath_tendsto_hazard_of_valid`. -/
theorem illnessDeath_tendsto_hazard (ha : 0 < a) (hab : a + b < 1) (hc : c ≤ 1) :
    Tendsto (idHazard a b c) atTop (𝓝 (min c (a + b))) := by
  have hx : 0 < 1 - a - b := by linarith
  have hfun : idHazard a b c = fun t => c - (c - b) / (1 + progRatio a b c t) :=
    funext fun t => illnessDeath_hazard_eq_ratio ha.le hab hc t
  rw [hfun]
  rcases lt_or_ge (a + b) c with hlt | hge
  · rw [min_eq_right hlt.le]
    have hρ0 : 0 ≤ (1 - c) / (1 - a - b) := div_nonneg (by linarith) hx.le
    have hρ1 : (1 - c) / (1 - a - b) < 1 := (div_lt_one hx).2 (by linarith)
    have hR : Tendsto (progRatio a b c) atTop (𝓝 (a / (c - a - b))) := by
      have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_sub 1).const_mul
        (a / (c - a - b))
      rw [sub_zero, mul_one] at h
      exact h.congr fun t => (progRatio_eq_of_lt hab hlt t).symm
    have hy : 0 < c - a - b := by linarith
    have hden : 1 + a / (c - a - b) ≠ 0 := by positivity
    have hlim : c - (c - b) / (1 + a / (c - a - b)) = a + b := by
      have hcb : c - b ≠ 0 := by linarith
      rw [one_add_div hy.ne', show c - a - b + a = c - b by ring, div_div_cancel₀ hcb]
      ring
    rw [← hlim]
    exact tendsto_const_nhds.sub (tendsto_const_nhds.div (tendsto_const_nhds.add hR) hden)
  · rw [min_eq_left hge]
    have hR : Tendsto (progRatio a b c) atTop atTop :=
      tendsto_atTop_mono (progRatio_ge_of_le ha.le hab hc hge)
        (tendsto_natCast_atTop_atTop.atTop_mul_const (div_pos ha hx))
    have h := (tendsto_const_nhds (x := c - b)).div_atTop
      (tendsto_atTop_add_const_left _ 1 hR)
    simpa using (tendsto_const_nhds (x := c)).sub h

/-- The printed sentence "the hazard levels off at the hazard of death for progressed
patients", read unconditionally, fails when `a + b < c`: with `a = b = 1/10` and `c = 1/2` the
marginal death hazard converges to `1/5`, not to `c = 1/2`. -/
theorem illnessDeath_limit_ne :
    Tendsto (idHazard (1 / 10) (1 / 10) (1 / 2)) atTop (𝓝 (1 / 5)) ∧ (1 / 5 : ℝ) ≠ 1 / 2 := by
  refine ⟨?_, by norm_num⟩
  have h := illnessDeath_tendsto_hazard (a := 1 / 10) (b := 1 / 10) (c := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  rwa [show min (1 / 2 : ℝ) (1 / 10 + 1 / 10) = 1 / 5 by norm_num] at h

/-- The illness-death model is a valid multi-state model when `0 ≤ a`, `0 ≤ b`, `a + b ≤ 1`
and `0 ≤ c ≤ 1`: the initial distribution and the transition probabilities are nonnegative,
the initial distribution sums to one and every row sums to at most one. -/
theorem illnessDeath_valid (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) (hc0 : 0 ≤ c)
    (hc : c ≤ 1) :
    (∀ s, 0 ≤ idInit s) ∧ (∀ s s', 0 ≤ idTrans a b c s s') ∧
      (∀ s, ∑ s', idTrans a b c s s' ≤ 1) ∧ ∑ s, idInit s = 1 := by
  refine ⟨fun s => ?_, fun s s' => ?_, fun s => ?_, by simp [idInit]⟩
  · cases s <;> simp [idInit]
  · cases s <;> cases s' <;> simp only [idTrans] <;> linarith
  · cases s <;> simp only [Fintype.sum_bool, idTrans] <;> linarith

/-- In the illness-death model, the library's discrete hazard of the death period `T` (with law
`deathLaw idInit (idTrans a b c) N`, a probability measure) is the marginal death hazard
`idHazard a b c t`, for every period `t` before the horizon `N`. This is an identity of the
quotients `P(T = t) / P(T ≥ t)`: when everybody has died before period `t` both sides are the
conventional value `0`. The reading as the conditional probability `P(T = t | T ≥ t)` is
`illnessDeath_hazard_deathLaw_of_pos`. -/
theorem illnessDeath_hazard_deathLaw (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) (hc0 : 0 ≤ c)
    (hc : c ≤ 1) {N t : ℕ} (ht : t < N) :
    IsProbabilityMeasure (deathLaw idInit (idTrans a b c) N) ∧
      hazard (deathLaw idInit (idTrans a b c) N) id t = idHazard a b c t := by
  obtain ⟨h1, h2, h3, h4⟩ := illnessDeath_valid ha hb hab hc0 hc
  exact ⟨isProbabilityMeasure_deathLaw _ _ h1 h2 h3 h4 N, hazard_deathLaw _ _ h1 h2 h3 ht⟩

/-- In the illness-death model with `0 ≤ a` and `a + b < 1` somebody is alive at the start of
every period: the progression-free proportion `(1 - a - b) ^ t` is positive. -/
theorem aliveMass_idTrans_pos (ha : 0 ≤ a) (hab : a + b < 1) (hc : c ≤ 1) (t : ℕ) :
    0 < aliveMass idInit (idTrans a b c) t := by
  have h1 := progFree_pos (c := c) hab t
  have h2 := progressed_nonneg ha hab hc t
  rw [aliveMass, Fintype.sum_bool]
  change 0 < progressed a b c t + progFree a b c t
  linarith

/-- The probability form of `illnessDeath_hazard_deathLaw`: if the alive mass at the start of
period `t < N` is positive, then the death period is at risk at `t` with positive probability,
the library's hazard is the conditional probability `P(T = t | T ≥ t)` and equals
`idHazard a b c t`, and this hazard lies in `[0, 1]`. -/
theorem illnessDeath_hazard_deathLaw_of_pos (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hc0 : 0 ≤ c) (hc : c ≤ 1) {N t : ℕ} (ht : t < N)
    (hpos : 0 < aliveMass idInit (idTrans a b c) t) :
    IsProbabilityMeasure (deathLaw idInit (idTrans a b c) N) ∧
      0 < atRisk (deathLaw idInit (idTrans a b c) N) id t ∧
      hazard (deathLaw idInit (idTrans a b c) N) id t = idHazard a b c t ∧
      0 ≤ idHazard a b c t ∧ idHazard a b c t ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := illnessDeath_valid ha hb hab hc0 hc
  obtain ⟨hP, hH⟩ := illnessDeath_hazard_deathLaw ha hb hab hc0 hc ht
  obtain ⟨-, -, -, h5, h6⟩ := deathHazard_eq_sum_stateShare_of_pos _ _ h1 h2 h3 t hpos
  refine ⟨hP, ?_, hH, h5, h6⟩
  simp only [atRisk, id]
  rwa [deathLaw_real_le _ _ h1 h2 h3 ht.le]

/-- The probability reading of `illnessDeath_tendsto_hazard`. For a valid illness-death model
(`0 < a`, `0 ≤ b`, `a + b < 1`, `0 ≤ c ≤ 1`), the marginal death hazard is a probability in
every period, it converges to `min c (a + b)`, and this limit lies in `[0, 1]`. -/
theorem illnessDeath_tendsto_hazard_of_valid (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b < 1)
    (hc0 : 0 ≤ c) (hc : c ≤ 1) :
    (∀ t, 0 ≤ idHazard a b c t ∧ idHazard a b c t ≤ 1) ∧
      Tendsto (idHazard a b c) atTop (𝓝 (min c (a + b))) ∧
      0 ≤ min c (a + b) ∧ min c (a + b) ≤ 1 := by
  obtain ⟨h1, h2, h3, -⟩ := illnessDeath_valid ha.le hb hab.le hc0 hc
  refine ⟨fun t => ?_, illnessDeath_tendsto_hazard ha hab hc,
    le_min hc0 (by linarith), (min_le_left _ _).trans hc⟩
  obtain ⟨-, -, -, h5, h6⟩ := deathHazard_eq_sum_stateShare_of_pos _ _ h1 h2 h3 t
    (aliveMass_idTrans_pos ha.le hab hc t)
  exact ⟨h5, h6⟩

end MultiState

end Survival

end CausalInference
