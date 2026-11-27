/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Interference.PartialInterference
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith

/-!
# Two-stage randomization and unbiased estimation under partial interference

The design based setting of Hudgens and Halloran: potential outcomes are fixed and the only
randomness is in the assignment. Expectations are finite weighted sums.

## Main definitions

* `numWith a t`: the number of units with assignment `t` in the vector `a`.
* `completeRandomization ι k`: the allocation strategy that is uniform over the assignment
  vectors of `ι` with exactly `k` units treated.
* `FixedCount ψ t m`: with probability one exactly `m > 0` units receive `t` under `ψ`, each
  with probability `m / n`.
* `groupEstimator Y t a`: the mean observed outcome among the units of the group that received
  `t`, the estimator `Ŷ(t; ψ)` of the group average potential outcome.
* `JointDesign`: a general two-stage design, an arbitrary joint law of the arm vector `S` and
  the population assignment `A`; `JointDesign.Compatible Q strat` says that the assignment of
  each group `g` given that it is in arm `b` follows `strat b g`, with no condition on the
  dependence between groups.
* `twoStageExpect`: the expectation under two-stage randomization with independent groups; a
  first stage strategy assigns each group `g` to arm `S g`, and given `S` the groups are
  randomized independently, group `g` following the strategy `strat (S g) g`. It is the
  expectation under the joint design `productDesign P1 strat`.
* `variance`, `finitePopVar`: the variance of a statistic under a strategy and the finite
  population variance `S²` with divisor `n - 1`.
* `popEstimator`: the average of the group estimators over the groups assigned to a given arm.

## Main results

* `completeRandomization_treatProb_true`: under complete randomization of `k` among `n` units,
  every unit is treated with probability `k / n`. The proof uses only that the design is
  invariant under permutations of the units and that it treats exactly `k` units.
* `expect_groupEstimator_of_fixed`, `expect_groupEstimator_completeRandomization_true`,
  `expect_groupEstimator_completeRandomization_false`: the group estimator is unbiased for the
  group average potential outcome `ȳ(t; ψ)` within the group.
* `pairProb_of_perm_invariant`, `variance_sampleMean_of_perm_invariant`: second order
  inclusion probabilities and the variance `(1/m - 1/n) S²` of a sample mean under a
  permutation invariant fixed count design.
* `variance_groupEstimator_completeRandomization` and its `_true`, `_false` instances: under
  complete randomization and stratified interference the group estimator has variance
  `(1/m - 1/n) S²`.
* `JointDesign.expect_popEstimator` and relatives: the population estimators are unbiased under
  every two-stage design compatible with the strategies, groups being allowed to be dependent.
* `twoStageExpect_popEstimator`, `twoStageExpect_popEstimator_completeRandomization`: the
  instances for independent groups; likewise for the marginal estimators, and for the
  estimators of the direct, indirect, total and overall effects.
* `twoStageExpect_const`, `twoStageExpect_add`, `twoStageExpect_const_mul`,
  `twoStageExpect_mono`: `twoStageExpect` is an expectation.

Source: M. G. Hudgens and M. E. Halloran (2008), Toward causal inference with interference,
Journal of the American Statistical Association 103. Variance estimators and the variance of
the population estimators are not formalized.
-/

@[expose] public section

open Finset

namespace CausalInference

namespace Interference

open AllocationStrategy

variable {ι : Type*} [Fintype ι]

/-! ### Fixed number treated and complete randomization -/

/-- The number of units that receive assignment `t` in the vector `a`. -/
def numWith (a : ι → Bool) (t : Bool) : ℕ := #(univ.filter fun j ↦ a j = t)

/-- The number of units with assignment `t` is unchanged when the units are permuted. -/
theorem numWith_comp_perm (a : ι → Bool) (σ : Equiv.Perm ι) (t : Bool) :
    numWith (a ∘ σ) t = numWith a t := by
  refine card_nbij' σ σ.symm (fun x hx ↦ by simpa using hx) (fun x hx ↦ by simpa using hx)
    (fun x _ ↦ by simp) (fun x _ ↦ by simp)

/-- The units with assignment `false` are those not assigned `true`. -/
theorem numWith_false (a : ι → Bool) : numWith a false = Fintype.card ι - numWith a true := by
  have h := card_filter_add_card_filter_not (s := univ) (p := fun j ↦ a j = true)
  simp only [Bool.not_eq_true, card_univ] at h
  rw [numWith, numWith]
  omega

variable [DecidableEq ι]

/-- The expectation `∑_a ψ(a) f(a)` of a function of the assignment vector under `ψ`. -/
def expect (ψ : AllocationStrategy ι) (f : (ι → Bool) → ℝ) : ℝ := ∑ a, ψ.prob a * f a

/-- The expectation is additive. -/
theorem expect_sub (ψ : AllocationStrategy ι) (f f' : (ι → Bool) → ℝ) :
    expect ψ (fun a ↦ f a - f' a) = expect ψ f - expect ψ f' := by
  simp only [expect, mul_sub, sum_sub_distrib]

/-- If a strategy is invariant under permutations of the units and assigns `t` to exactly `m`
units with probability one, then every unit receives `t` with probability `m / n`. -/
theorem treatProb_of_perm_invariant (ψ : AllocationStrategy ι) (t : Bool) (m : ℕ)
    (hperm : ∀ (σ : Equiv.Perm ι) a, ψ.prob (a ∘ σ) = ψ.prob a)
    (hsupp : ∀ a, ψ.prob a ≠ 0 → numWith a t = m) (i : ι) :
    ψ.treatProb i t = m / Fintype.card ι := by
  have : Nonempty ι := ⟨i⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hsym : ∀ j, ψ.treatProb j t = ψ.treatProb i t := by
    intro j
    simp only [treatProb, sum_filter]
    refine Fintype.sum_bijective (fun a ↦ a ∘ Equiv.swap i j)
      (Function.Involutive.bijective fun a ↦ by funext x; simp) _ _ fun a ↦ ?_
    simp [hperm]
  have htot : ∑ j, ψ.treatProb j t = m := by
    simp only [treatProb, sum_filter]
    rw [sum_comm]
    calc ∑ a, ∑ j, (if a j = t then ψ.prob a else 0)
        = ∑ a, ψ.prob a * m := by
          refine sum_congr rfl fun a _ ↦ ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
          by_cases ha : ψ.prob a = 0
          · simp [ha]
          · rw [← hsupp a ha, numWith]
      _ = m := by rw [← sum_mul, ψ.sum_eq_one, one_mul]
  rw [eq_div_iff hn, mul_comm, ← htot]
  simp [hsym]

/-- The number of assignment vectors of `ι` with exactly `k` units treated. -/
def numVectors (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) : ℕ :=
  #(univ.filter fun a : ι → Bool ↦ numWith a true = k)

/-- There is an assignment vector with exactly `k` units treated when `k ≤ n`. -/
theorem numVectors_pos {k : ℕ} (hk : k ≤ Fintype.card ι) : 0 < numVectors ι k := by
  obtain ⟨s, -, hs⟩ := exists_subset_card_eq (s := (univ : Finset ι)) (n := k)
    (by rw [card_univ]; exact hk)
  refine card_pos.2 ⟨fun j ↦ decide (j ∈ s), mem_filter.2 ⟨mem_univ _, ?_⟩⟩
  rw [numWith, ← hs]
  congr 1
  ext j
  simp

/-- Complete randomization of `k` among the `n` units of `ι` (the allocation strategy used by
Hudgens and Halloran): the uniform distribution over the assignment vectors with exactly `k`
units treated. It requires `k ≤ n`. -/
noncomputable def completeRandomization (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ)
    (hk : k ≤ Fintype.card ι) : AllocationStrategy ι where
  prob a := if numWith a true = k then (numVectors ι k : ℝ)⁻¹ else 0
  nonneg a := by split_ifs <;> positivity
  sum_eq_one := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (numVectors_pos hk).ne')

theorem completeRandomization_perm {k : ℕ} (hk : k ≤ Fintype.card ι) (σ : Equiv.Perm ι)
    (a : ι → Bool) :
    (completeRandomization ι k hk).prob (a ∘ σ) = (completeRandomization ι k hk).prob a := by
  simp [completeRandomization, numWith_comp_perm]

theorem completeRandomization_supp {k : ℕ} (hk : k ≤ Fintype.card ι) (a : ι → Bool)
    (ha : (completeRandomization ι k hk).prob a ≠ 0) : numWith a true = k := by
  by_contra h
  exact ha (by simp [completeRandomization, h])

/-- Under complete randomization of `k` among `n` units each unit is treated with probability
`k / n`. -/
theorem completeRandomization_treatProb_true {k : ℕ} (hk : k ≤ Fintype.card ι) (i : ι) :
    (completeRandomization ι k hk).treatProb i true = k / Fintype.card ι :=
  treatProb_of_perm_invariant _ true k (completeRandomization_perm hk)
    (completeRandomization_supp hk) i

/-- Under complete randomization of `k` among `n` units each unit is a control with
probability `(n - k) / n`. -/
theorem completeRandomization_treatProb_false {k : ℕ} (hk : k ≤ Fintype.card ι) (i : ι) :
    (completeRandomization ι k hk).treatProb i false =
      ((Fintype.card ι - k : ℕ) : ℝ) / Fintype.card ι :=
  treatProb_of_perm_invariant _ false _ (completeRandomization_perm hk)
    (fun a ha ↦ by rw [numWith_false, completeRandomization_supp hk a ha]) i

/-- A strategy with a fixed number of units receiving `t`: with probability one exactly
`m > 0` units receive `t`, and each unit receives `t` with probability `m / n`. Complete
randomization has this property for `t = true` (when `0 < k`) and for `t = false` (when
`k < n`). -/
structure FixedCount (ψ : AllocationStrategy ι) (t : Bool) (m : ℕ) : Prop where
  pos : 0 < m
  supp : ∀ a, ψ.prob a ≠ 0 → numWith a t = m
  prob : ∀ j, ψ.treatProb j t = m / Fintype.card ι

/-- Under a fixed count strategy every unit receives `t` with positive probability, so every
conditional average `ȳ_j(t; ψ)` entering the group estimand is a genuine conditional mean. -/
theorem FixedCount.treatProb_pos {ψ : AllocationStrategy ι} {t : Bool} {m : ℕ}
    (h : FixedCount ψ t m) (j : ι) : 0 < ψ.treatProb j t := by
  have : Nonempty ι := ⟨j⟩
  rw [h.prob j]
  exact div_pos (Nat.cast_pos.2 h.pos) (Nat.cast_pos.2 Fintype.card_pos)

/-- A fixed count strategy lives on a nonempty set of units. -/
theorem FixedCount.nonempty {ψ : AllocationStrategy ι} {t : Bool} {m : ℕ}
    (h : FixedCount ψ t m) : Nonempty ι := by
  by_contra hι
  rw [not_nonempty_iff] at hι
  obtain ⟨a, -, ha⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (f := ψ.prob)
    (by rw [ψ.sum_eq_one]; exact one_ne_zero)
  have := h.supp a ha
  rw [numWith, univ_eq_empty, filter_empty, card_empty] at this
  exact h.pos.ne this

/-- Complete randomization of `k > 0` units treats a fixed number, `k`, of units. -/
theorem FixedCount.completeRandomization_true {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card ι) :
    FixedCount (completeRandomization ι k hk) true k :=
  ⟨hk0, completeRandomization_supp hk, completeRandomization_treatProb_true hk⟩

/-- Complete randomization of `k < n` units leaves a fixed number, `n - k`, of controls. -/
theorem FixedCount.completeRandomization_false {k : ℕ} (hk : k < Fintype.card ι) :
    FixedCount (completeRandomization ι k hk.le) false (Fintype.card ι - k) :=
  ⟨Nat.sub_pos_of_lt hk, fun a ha ↦ by rw [numWith_false, completeRandomization_supp hk.le a ha],
    completeRandomization_treatProb_false hk.le⟩

/-- Complete randomization of `k` among `n` units with `0 < k < n` is a positive strategy:
every unit is treated and is a control with positive probability. -/
theorem completeRandomization_positive {k : ℕ} (hk0 : 0 < k) (hk : k < Fintype.card ι) :
    (completeRandomization ι k hk.le).Positive := by
  intro i t
  cases t
  · exact (FixedCount.completeRandomization_false hk).treatProb_pos i
  · exact (FixedCount.completeRandomization_true hk0 hk.le).treatProb_pos i

/-! ### Unbiased estimation within a group -/

/-- The estimator `Ŷ(t; ψ)` of Hudgens and Halloran for the group average potential outcome:
the mean observed outcome `Y a j` among the units `j` with `a j = t`, where `a` is the
realized assignment vector. -/
noncomputable def groupEstimator (Y : (ι → Bool) → ι → ℝ) (t : Bool) (a : ι → Bool) : ℝ :=
  (∑ j ∈ univ.filter (fun j ↦ a j = t), Y a j) / numWith a t

/-- Unbiasedness of the group estimator: if the strategy `ψ` assigns `t` to exactly `m > 0`
units with probability one and assigns `t` to every unit with probability `m / n`, then
`E_ψ[Ŷ(t; ψ)] = ȳ(t; ψ)`. The fixed count hypothesis already makes the group nonempty
(`FixedCount.nonempty`) and every conditional average in `ȳ(t; ψ)` genuine
(`FixedCount.treatProb_pos`). -/
theorem expect_groupEstimator_of_fixed (Y : (ι → Bool) → ι → ℝ) {ψ : AllocationStrategy ι}
    {t : Bool} {m : ℕ} (h : FixedCount ψ t m) :
    expect ψ (groupEstimator Y t) = groupAvg Y ψ t := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h.pos.ne'
  have h1 : ∀ a, ψ.prob a * groupEstimator Y t a =
      (m : ℝ)⁻¹ * ∑ j, if a j = t then ψ.prob a * Y a j else 0 := by
    intro a
    by_cases ha : ψ.prob a = 0
    · simp [ha]
    · rw [groupEstimator, h.supp a ha, ← sum_filter, ← mul_sum]
      ring
  have h2 : ∀ j, (∑ a : ι → Bool, if a j = t then ψ.prob a * Y a j else 0) =
      m / Fintype.card ι * indivAvg Y ψ j t := by
    intro j
    rw [← sum_filter, ← h.prob j, treatProb_mul_indivAvg, indivSum]
  simp only [expect, h1, ← mul_sum]
  rw [sum_comm]
  simp only [h2, ← mul_sum, groupAvg, ← mul_assoc]
  congr 1
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hm', one_mul]

/-- Under complete randomization of `k` treated units with `0 < k ≤ n`, the mean outcome of
the treated is unbiased for the group average potential outcome under treatment. -/
theorem expect_groupEstimator_completeRandomization_true (Y : (ι → Bool) → ι → ℝ) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ Fintype.card ι) :
    expect (completeRandomization ι k hk) (groupEstimator Y true) =
      groupAvg Y (completeRandomization ι k hk) true :=
  expect_groupEstimator_of_fixed Y (.completeRandomization_true hk0 hk)

/-- Under complete randomization of `k` treated units with `k < n`, the mean outcome of the
controls is unbiased for the group average potential outcome under control. -/
theorem expect_groupEstimator_completeRandomization_false (Y : (ι → Bool) → ι → ℝ) {k : ℕ}
    (hk : k < Fintype.card ι) :
    expect (completeRandomization ι k hk.le) (groupEstimator Y false) =
      groupAvg Y (completeRandomization ι k hk.le) false :=
  expect_groupEstimator_of_fixed Y (.completeRandomization_false hk)

/-- The estimator of the marginal group average: the mean observed outcome of the group. -/
noncomputable def groupMarginalEstimator (Y : (ι → Bool) → ι → ℝ) (a : ι → Bool) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ j, Y a j

/-- The mean observed outcome of a nonempty group is unbiased for the marginal group average
under every allocation strategy. -/
theorem expect_groupMarginalEstimator [Nonempty ι] (Y : (ι → Bool) → ι → ℝ)
    (ψ : AllocationStrategy ι) :
    expect ψ (groupMarginalEstimator Y) = groupMarginal Y ψ := by
  simp only [expect, groupMarginalEstimator, groupMarginal, indivMarginal, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

/-! ### Stratified interference and the variance of the group estimator -/

/-- Second order inclusion probabilities: if a strategy is invariant under permutations of the
units and assigns `t` to exactly `m` units with probability one, then two distinct units both
receive `t` with probability `m (m - 1) / (n (n - 1))`. -/
theorem pairProb_of_perm_invariant (ψ : AllocationStrategy ι) (t : Bool) (m : ℕ)
    (hperm : ∀ (σ : Equiv.Perm ι) a, ψ.prob (a ∘ σ) = ψ.prob a)
    (hsupp : ∀ a, ψ.prob a ≠ 0 → numWith a t = m) {i j : ι} (hij : i ≠ j) :
    ∑ a, (if a i = t ∧ a j = t then ψ.prob a else 0) =
      m * (m - 1) / (Fintype.card ι * (Fintype.card ι - 1)) := by
  set q : ι → ℝ := fun j ↦ ∑ a, (if a i = t ∧ a j = t then ψ.prob a else 0) with hq
  have hsym : ∀ j' ∈ univ.erase i, q j' = q j := by
    intro j' hj'
    have hj'i : j' ≠ i := (mem_erase.1 hj').1
    simp only [hq]
    refine Fintype.sum_bijective (fun a ↦ a ∘ Equiv.swap j j')
      (Function.Involutive.bijective fun a ↦ by funext x; simp) _ _ fun a ↦ ?_
    have hi : Equiv.swap j j' i = i := Equiv.swap_apply_of_ne_of_ne hij hj'i.symm
    simp [hperm, hi]
  have htot : ∑ j' ∈ univ.erase i, q j' = (m - 1) * (m / Fintype.card ι) := by
    simp only [hq]
    rw [sum_comm, ← treatProb_of_perm_invariant ψ t m hperm hsupp i, treatProb, mul_sum,
      sum_filter]
    refine sum_congr rfl fun a _ ↦ ?_
    by_cases hai : a i = t
    · by_cases ha : ψ.prob a = 0
      · simp [ha]
      have hc : #((univ.filter fun j' ↦ a j' = t).erase i) + 1 = m := by
        rw [card_erase_add_one
          (mem_filter.2 ⟨mem_univ i, hai⟩ : i ∈ univ.filter fun j' ↦ a j' = t)]
        exact hsupp a ha
      have hcast : (#((univ.filter fun j' ↦ a j' = t).erase i) : ℝ) = m - 1 := by
        rw [← hc]
        push_cast
        ring
      simp only [hai, true_and, ite_true]
      rw [← sum_filter, sum_const, nsmul_eq_mul, filter_erase, hcast, mul_comm]
    · simp [hai]
  have hn : 1 < Fintype.card ι := Fintype.one_lt_card_iff.2 ⟨i, j, hij⟩
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hn1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hn
    linarith
  rw [sum_congr rfl hsym, sum_const, card_erase_of_mem (mem_univ i), card_univ, nsmul_eq_mul,
    Nat.cast_sub hn.le, Nat.cast_one] at htot
  have h2 : ((Fintype.card ι : ℝ) - 1) * q j * Fintype.card ι = (m - 1) * m := by
    rw [htot]
    field_simp
  change q j = _
  rw [eq_div_iff (mul_ne_zero hn0 hn1)]
  linear_combination h2

/-- The variance `E_ψ[(f - E_ψ f)²]` of a function of the assignment vector under `ψ`. -/
def variance (ψ : AllocationStrategy ι) (f : (ι → Bool) → ℝ) : ℝ :=
  expect ψ fun a ↦ (f a - expect ψ f) ^ 2

/-- The finite population variance `S² = (n - 1)⁻¹ ∑_j (y j - ȳ)²` of the values `y j`, where
`ȳ = n⁻¹ ∑_j y j`. It is meaningful for `n ≥ 2`. -/
noncomputable def finitePopVar (y : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) - 1)⁻¹ * ∑ j, (y j - (Fintype.card ι : ℝ)⁻¹ * ∑ i, y i) ^ 2

/-- The variance of a sample mean under a permutation invariant fixed count design. If `ψ` is
invariant under permutations of the units and assigns `t` to exactly `m` units with probability
one, `0 < m < n`, then the mean of fixed values `y j` over the units receiving `t` has variance
`(1/m - 1/n) S²`, with `S²` the finite population variance of `y`. -/
theorem variance_sampleMean_of_perm_invariant (ψ : AllocationStrategy ι) (t : Bool) {m : ℕ}
    (hperm : ∀ (σ : Equiv.Perm ι) a, ψ.prob (a ∘ σ) = ψ.prob a)
    (hsupp : ∀ a, ψ.prob a ≠ 0 → numWith a t = m) (hm0 : 0 < m) (hmn : m < Fintype.card ι)
    (y : ι → ℝ) :
    variance ψ (fun a ↦ (∑ j ∈ univ.filter (fun j ↦ a j = t), y j) / m) =
      (1 / m - 1 / Fintype.card ι) * finitePopVar y := by
  have hn1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast (show 1 < Fintype.card ι by omega)
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hn1' : (Fintype.card ι : ℝ) - 1 ≠ 0 := sub_ne_zero.2 hn1.ne'
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm0.ne'
  have hp : ∀ j, ψ.treatProb j t = m / Fintype.card ι :=
    treatProb_of_perm_invariant ψ t m hperm hsupp
  set ybar : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, y i with hybar
  set d : ι → ℝ := fun j ↦ y j - ybar with hd
  have hdsum : ∑ j, d j = 0 := by
    simp only [hd, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hybar]
    field_simp
    ring
  -- the estimator as a linear statistic
  have hlin : ∀ h : ι → ℝ, ∑ a, ψ.prob a * ∑ j, (if a j = t then h j else 0) =
      m / Fintype.card ι * ∑ j, h j := by
    intro h
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← hp j, treatProb, sum_mul, sum_filter]
    refine sum_congr rfl fun a _ ↦ ?_
    split_ifs <;> simp [mul_comm]
  have hestEq : ∀ a : ι → Bool, (∑ j ∈ univ.filter (fun j ↦ a j = t), y j) / m =
      (m : ℝ)⁻¹ * ∑ j, (if a j = t then y j else 0) := by
    intro a
    rw [sum_filter, div_eq_inv_mul]
  have hmean : expect ψ (fun a ↦ (∑ j ∈ univ.filter (fun j ↦ a j = t), y j) / m) = ybar := by
    simp only [expect, hestEq]
    calc ∑ a, ψ.prob a * ((m : ℝ)⁻¹ * ∑ j, (if a j = t then y j else 0))
        = (m : ℝ)⁻¹ * ∑ a, ψ.prob a * ∑ j, (if a j = t then y j else 0) := by
          rw [mul_sum]
          exact sum_congr rfl fun a _ ↦ by ring
      _ = ybar := by
          rw [hlin, hybar]
          field_simp
  -- the centered estimator on the support
  have hcen : ∀ a, ψ.prob a ≠ 0 →
      (∑ j ∈ univ.filter (fun j ↦ a j = t), y j) / m - ybar =
        (m : ℝ)⁻¹ * ∑ j, (if a j = t then d j else 0) := by
    intro a ha
    have hc : (#(univ.filter fun j ↦ a j = t) : ℝ) = m := by
      have := hsupp a ha
      rw [numWith] at this
      exact_mod_cast this
    rw [← sum_filter, sum_sub_distrib, sum_const, nsmul_eq_mul, hc]
    field_simp
  -- second moments
  set r : ℝ := m * (m - 1) / (Fintype.card ι * (Fintype.card ι - 1)) with hr
  have hquad : ∀ a, ψ.prob a * (∑ j, (if a j = t then d j else 0)) ^ 2 =
      ∑ i, ∑ j, d i * d j * (if a i = t ∧ a j = t then ψ.prob a else 0) := by
    intro a
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hi : a i = t
    · by_cases hj : a j = t
      · simp only [hi, hj, and_self, ite_true]
        ring
      · simp [hi, hj]
    · simp [hi]
  have hpair : ∀ i j, ∑ a, (if a i = t ∧ a j = t then ψ.prob a else 0) =
      r + if i = j then m / Fintype.card ι - r else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [and_self, ite_true, add_sub_cancel]
      rw [← sum_filter, ← treatProb, hp]
    · simp only [hij, ↓reduceIte, add_zero, hr]
      exact pairProb_of_perm_invariant ψ t m hperm hsupp hij
  have hvar : variance ψ (fun a ↦ (∑ j ∈ univ.filter (fun j ↦ a j = t), y j) / m) =
      (m : ℝ)⁻¹ ^ 2 * ((m / Fintype.card ι - r) * ∑ j, d j ^ 2) := by
    rw [variance, hmean, expect]
    have h1 : ∀ a, ψ.prob a * ((∑ j ∈ univ.filter (fun j ↦ a j = t), y j) / m - ybar) ^ 2 =
        (m : ℝ)⁻¹ ^ 2 * (ψ.prob a * (∑ j, (if a j = t then d j else 0)) ^ 2) := by
      intro a
      by_cases ha : ψ.prob a = 0
      · simp [ha]
      rw [hcen a ha]
      ring
    simp only [h1, ← mul_sum, hquad]
    congr 1
    calc ∑ a : ι → Bool, ∑ i, ∑ j, d i * d j * (if a i = t ∧ a j = t then ψ.prob a else 0)
        = ∑ i, ∑ j, d i * d j * ∑ a : ι → Bool,
            (if a i = t ∧ a j = t then ψ.prob a else 0) := by
          rw [sum_comm]
          refine sum_congr rfl fun i _ ↦ ?_
          rw [sum_comm]
          simp only [mul_sum]
      _ = ∑ i, ∑ j, (r * (d i * d j) +
            if i = j then (m / Fintype.card ι - r) * (d i * d j) else 0) := by
          simp only [hpair]
          refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
          split_ifs <;> ring
      _ = ∑ i, ∑ j, r * (d i * d j) + ∑ i, (m / Fintype.card ι - r) * (d i * d i) := by
          simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
      _ = (m / Fintype.card ι - r) * ∑ j, d j ^ 2 := by
          have h0 : ∑ i, ∑ j, r * (d i * d j) = 0 := by simp [← mul_sum, hdsum]
          rw [h0, zero_add, mul_sum]
          simp only [sq]
  rw [hvar, finitePopVar, hr]
  simp only [← hybar]
  field_simp
  ring

/-- Expectations agree for functions that agree on the support of the strategy. -/
theorem expect_congr_supp (ψ : AllocationStrategy ι) {f f' : (ι → Bool) → ℝ}
    (h : ∀ a, ψ.prob a ≠ 0 → f a = f' a) : expect ψ f = expect ψ f' := by
  refine sum_congr rfl fun a _ ↦ ?_
  by_cases ha : ψ.prob a = 0
  · simp [ha]
  · rw [h a ha]

/-- Variances agree for functions that agree on the support of the strategy. -/
theorem variance_congr_supp (ψ : AllocationStrategy ι) {f f' : (ι → Bool) → ℝ}
    (h : ∀ a, ψ.prob a ≠ 0 → f a = f' a) : variance ψ f = variance ψ f' := by
  rw [variance, variance, expect_congr_supp ψ h]
  exact expect_congr_supp ψ fun a ha ↦ by rw [h a ha]

/-- If the outcome of `j` equals `v` under every assignment vector of positive probability that
gives `j` the treatment `t`, and `t` has positive probability for `j`, then `ȳ_j(t; ψ) = v`. -/
theorem indivAvg_eq_of_const (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (j : ι)
    (t : Bool) (hp : 0 < ψ.treatProb j t) {v : ℝ}
    (hv : ∀ a, ψ.prob a ≠ 0 → a j = t → Y a j = v) : indivAvg Y ψ j t = v := by
  have hs : indivSum Y ψ j t = ψ.treatProb j t * v := by
    rw [indivSum, treatProb, sum_mul]
    refine sum_congr rfl fun a ha ↦ ?_
    by_cases h0 : ψ.prob a = 0
    · simp [h0]
    · rw [hv a h0 (mem_filter.1 ha).2]
  rw [indivAvg, hs, mul_div_cancel_left₀ _ hp.ne']

/-- Under complete randomization and stratified interference within the group, the outcome of a
unit receiving `t` is the same under every possible assignment vector, namely `ȳ_j(t; ψ)`. -/
theorem StratifiedInterference.eq_indivAvg_completeRandomization {Y : (ι → Bool) → ι → ℝ}
    (hY : StratifiedInterference (fun _ : ι ↦ ()) Y) {k : ℕ} (hk : k ≤ Fintype.card ι)
    {t : Bool} {a : ι → Bool} (ha : (completeRandomization ι k hk).prob a ≠ 0) {j : ι}
    (haj : a j = t) : Y a j = indivAvg Y (completeRandomization ι k hk) j t := by
  have hexp : ∀ b, (completeRandomization ι k hk).prob b ≠ 0 →
      stratifiedExposure (fun _ : ι ↦ ()) b j = (b j, k) := by
    intro b hb
    rw [← completeRandomization_supp hk b hb]
    simp [stratifiedExposure, numWith]
  have hpos : 0 < (completeRandomization ι k hk).treatProb j t := by
    rw [treatProb]
    exact (lt_of_le_of_ne ((completeRandomization ι k hk).nonneg a) (Ne.symm ha)).trans_le
      (single_le_sum (fun b _ ↦ (completeRandomization ι k hk).nonneg b)
        (mem_filter.2 ⟨mem_univ a, haj⟩))
  refine (indivAvg_eq_of_const Y _ j t hpos fun b hb hbj ↦ ?_).symm
  exact hY b a j (by rw [hexp b hb, hexp a ha, hbj, haj])

/-- Variance of the group estimator under stratified interference (Hudgens and Halloran). The
group `ι` is completely randomized with `k` treated, stratified interference holds within the
group, and exactly `m` units receive `t`, with `0 < m < n`. Then
`Var(Ŷ(t; ψ)) = (1/m - 1/n) S²`, where `S²` is the finite population variance of the values
`ȳ_j(t; ψ)`; under stratified interference these are the outcomes of the units when receiving
`t` with `k` treated in the group. -/
theorem variance_groupEstimator_completeRandomization {Y : (ι → Bool) → ι → ℝ}
    (hY : StratifiedInterference (fun _ : ι ↦ ()) Y) {k : ℕ} (hk : k ≤ Fintype.card ι)
    {t : Bool} {m : ℕ} (hm : FixedCount (completeRandomization ι k hk) t m)
    (hmn : m < Fintype.card ι) :
    variance (completeRandomization ι k hk) (groupEstimator Y t) =
      (1 / m - 1 / Fintype.card ι) *
        finitePopVar (fun j ↦ indivAvg Y (completeRandomization ι k hk) j t) := by
  rw [← variance_sampleMean_of_perm_invariant _ t (completeRandomization_perm hk) hm.supp
    hm.pos hmn]
  refine variance_congr_supp _ fun a ha ↦ ?_
  rw [groupEstimator, hm.supp a ha]
  congr 1
  exact sum_congr rfl fun j hj ↦
    hY.eq_indivAvg_completeRandomization hk ha (mem_filter.1 hj).2

/-- Variance of the mean outcome of the treated under complete randomization of `k` among `n`
units, `0 < k < n`, and stratified interference: `(1/k - 1/n) S²`, with `S²` the finite
population variance of the `ȳ_j(1; ψ)`. -/
theorem variance_groupEstimator_completeRandomization_true {Y : (ι → Bool) → ι → ℝ}
    (hY : StratifiedInterference (fun _ : ι ↦ ()) Y) {k : ℕ} (hk0 : 0 < k)
    (hk : k < Fintype.card ι) :
    variance (completeRandomization ι k hk.le) (groupEstimator Y true) =
      (1 / k - 1 / Fintype.card ι) *
        finitePopVar (fun j ↦ indivAvg Y (completeRandomization ι k hk.le) j true) :=
  variance_groupEstimator_completeRandomization hY hk.le
    (.completeRandomization_true hk0 hk.le) hk

/-- Variance of the mean outcome of the controls under complete randomization of `k` among `n`
units, `0 < k < n`, and stratified interference: `(1/(n - k) - 1/n) S²`, with `S²` the finite
population variance of the `ȳ_j(0; ψ)`. -/
theorem variance_groupEstimator_completeRandomization_false {Y : (ι → Bool) → ι → ℝ}
    (hY : StratifiedInterference (fun _ : ι ↦ ()) Y) {k : ℕ} (hk0 : 0 < k)
    (hk : k < Fintype.card ι) :
    variance (completeRandomization ι k hk.le) (groupEstimator Y false) =
      (1 / ((Fintype.card ι - k : ℕ) : ℝ) - 1 / Fintype.card ι) *
        finitePopVar (fun j ↦ indivAvg Y (completeRandomization ι k hk.le) j false) :=
  variance_groupEstimator_completeRandomization hY hk.le
    (.completeRandomization_false hk) (by omega)

/-! ### Two-stage randomization -/

section Population

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- Marginalization under independence: for independent coordinates with weights `q g`
summing to one, the expectation of a function of the coordinate `h` alone is its expectation
under `q h`. -/
theorem sum_prod_mul_apply {α : G → Type*} [∀ g, Fintype (α g)] (q : ∀ g, α g → ℝ)
    (hq : ∀ g, ∑ x, q g x = 1) (h : G) (X : α h → ℝ) :
    ∑ A : (∀ g, α g), (∏ g, q g (A g)) * X (A h) = ∑ x, q h x * X x := by
  have hne : ∀ g ∈ ({h}ᶜ : Finset G), g ≠ h := fun g hg ↦ by simpa using hg
  have hcompl : ∀ A : (∀ g, α g), ∏ g ∈ ({h}ᶜ : Finset G),
      Function.update q h (fun x ↦ q h x * X x) g (A g) = ∏ g ∈ ({h}ᶜ : Finset G), q g (A g) :=
    fun A ↦ prod_congr rfl fun g hg ↦ by rw [Function.update_of_ne (hne g hg)]
  have hprod : ∀ A : (∀ g, α g), (∏ g, q g (A g)) * X (A h) =
      ∏ g, Function.update q h (fun x ↦ q h x * X x) g (A g) := by
    intro A
    rw [Fintype.prod_eq_mul_prod_compl h, Fintype.prod_eq_mul_prod_compl h
      (fun g ↦ Function.update q h (fun x ↦ q h x * X x) g (A g)), Function.update_self,
      hcompl A]
    ring
  have hsum : ∏ g ∈ ({h}ᶜ : Finset G), ∑ x, Function.update q h (fun x ↦ q h x * X x) g x = 1 :=
    prod_eq_one fun g hg ↦ by rw [Function.update_of_ne (hne g hg)]; exact hq g
  simp only [hprod]
  rw [← Fintype.prod_sum, Fintype.prod_eq_mul_prod_compl h, Function.update_self, hsum, mul_one]

variable {κ : G → Type*} [∀ g, Fintype (κ g)] [∀ g, DecidableEq (κ g)]

/-- A general two-stage design: an arbitrary joint probability law of the arm vector
`S : G → Bool` (the first stage) and the population assignment `A` (the second stage). The
assignments of different groups may be dependent, even given `S`. -/
structure JointDesign (G : Type*) [Fintype G] [DecidableEq G] (κ : G → Type*)
    [∀ g, Fintype (κ g)] [∀ g, DecidableEq (κ g)] where
  /-- The joint probability of the arm vector `S` and the population assignment `A`. -/
  prob : (G → Bool) → ((g : G) → κ g → Bool) → ℝ
  nonneg : ∀ S A, 0 ≤ prob S A
  sum_eq_one : ∑ S, ∑ A, prob S A = 1

namespace JointDesign

/-- The expectation `∑_{S, A} Q(S, A) F(S, A)` under a joint two-stage design. -/
def expect (Q : JointDesign G κ) (F : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) : ℝ :=
  ∑ S, ∑ A, Q.prob S A * F S A

/-- The first stage of a joint design: the marginal law of the arm vector `S`. -/
def firstStage (Q : JointDesign G κ) : AllocationStrategy G where
  prob S := ∑ A, Q.prob S A
  nonneg S := sum_nonneg fun A _ ↦ Q.nonneg S A
  sum_eq_one := Q.sum_eq_one

/-- The second stage condition of Hudgens and Halloran for a joint design: for every group `g`,
arm `b` and group assignment `z`, `P(S g = b, A g = z) = P(S g = b) * (strat b g)(z)`; that is,
the law of the assignment of group `g` given that `g` is in arm `b` is the strategy
`strat b g`. Nothing is assumed about the dependence between groups. -/
def Compatible (Q : JointDesign G κ) (strat : Bool → (g : G) → AllocationStrategy (κ g)) :
    Prop :=
  ∀ g b z, ∑ S ∈ univ.filter (fun S : G → Bool ↦ S g = b),
      ∑ A ∈ univ.filter (fun A : (g : G) → κ g → Bool ↦ A g = z), Q.prob S A =
    Q.firstStage.treatProb g b * (strat b g).prob z

theorem prob_eq_zero_of_firstStage (Q : JointDesign G κ) {S : G → Bool}
    (h : Q.firstStage.prob S = 0) (A : (g : G) → κ g → Bool) : Q.prob S A = 0 :=
  (sum_eq_zero_iff_of_nonneg fun A _ ↦ Q.nonneg S A).1 h A (mem_univ A)

/-- The key computation for a general two-stage design. Suppose the first stage assigns exactly
`c > 0` groups to arm `b` with probability one, each group with probability `c / N`, and the
second stage is compatible with `strat`. Then the average over the groups in arm `b` of group
level statistics `X g (A g)` has expectation `N⁻¹ ∑_g E_{strat b g}[X g]`. -/
theorem expect_armAverage (Q : JointDesign G κ)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (hQ : Q.Compatible strat) {b : Bool}
    {c : ℕ} (h1 : FixedCount Q.firstStage b c) (X : (g : G) → (κ g → Bool) → ℝ) :
    Q.expect (fun S A ↦ (∑ g ∈ univ.filter (fun g ↦ S g = b), X g (A g)) / numWith S b) =
      (Fintype.card G : ℝ)⁻¹ * ∑ g, Interference.expect (strat b g) (X g) := by
  have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h1.pos.ne'
  have hSA : ∀ S A, Q.prob S A * ((∑ g ∈ univ.filter (fun g ↦ S g = b), X g (A g)) /
      numWith S b) = (c : ℝ)⁻¹ * ∑ g, if S g = b then Q.prob S A * X g (A g) else 0 := by
    intro S A
    by_cases hQ0 : Q.prob S A = 0
    · simp [hQ0]
    rw [h1.supp S fun h ↦ hQ0 (Q.prob_eq_zero_of_firstStage h A), ← sum_filter, ← mul_sum]
    ring
  have hg : ∀ g, ∑ S, ∑ A, (if S g = b then Q.prob S A * X g (A g) else 0) =
      c / Fintype.card G * Interference.expect (strat b g) (X g) := by
    intro g
    calc ∑ S, ∑ A, (if S g = b then Q.prob S A * X g (A g) else 0)
        = ∑ S ∈ univ.filter (fun S : G → Bool ↦ S g = b), ∑ A, Q.prob S A * X g (A g) := by
          rw [sum_filter]
          refine sum_congr rfl fun S _ ↦ ?_
          split_ifs <;> simp
      _ = ∑ S ∈ univ.filter (fun S : G → Bool ↦ S g = b), ∑ z, ∑ A ∈ univ.filter
            (fun A : (g : G) → κ g → Bool ↦ A g = z), Q.prob S A * X g (A g) :=
          sum_congr rfl fun S _ ↦ (sum_fiberwise _ _ _).symm
      _ = ∑ z, X g z * ∑ S ∈ univ.filter (fun S : G → Bool ↦ S g = b), ∑ A ∈ univ.filter
            (fun A : (g : G) → κ g → Bool ↦ A g = z), Q.prob S A := by
          rw [sum_comm]
          refine sum_congr rfl fun z _ ↦ ?_
          rw [mul_sum]
          refine sum_congr rfl fun S _ ↦ ?_
          rw [mul_sum]
          refine sum_congr rfl fun A hA ↦ ?_
          rw [(mem_filter.1 hA).2, mul_comm]
      _ = c / Fintype.card G * Interference.expect (strat b g) (X g) := by
          refine (sum_congr rfl fun z _ ↦ by rw [hQ]).trans ?_
          rw [← h1.prob g, Interference.expect, mul_sum]
          exact sum_congr rfl fun z _ ↦ by ring
  have hswap : ∑ S : G → Bool, ∑ A : (g : G) → κ g → Bool, ∑ g,
      (if S g = b then Q.prob S A * X g (A g) else 0) =
      ∑ g, ∑ S : G → Bool, ∑ A : (g : G) → κ g → Bool,
        (if S g = b then Q.prob S A * X g (A g) else 0) := by
    calc _ = ∑ S : G → Bool, ∑ g, ∑ A : (g : G) → κ g → Bool,
          (if S g = b then Q.prob S A * X g (A g) else 0) := sum_congr rfl fun S _ ↦ sum_comm
      _ = _ := sum_comm
  simp only [expect, hSA, ← mul_sum]
  rw [hswap]
  simp only [hg, ← mul_sum, ← mul_assoc]
  congr 1
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]

end JointDesign

/-- The expectation of `F S A` under two-stage randomization. In the first stage the vector
`S : G → Bool` assigning each group to one of two arms is drawn from `P1`; in the second stage,
given `S`, the groups are randomized independently, group `g` drawing its assignment vector
`A g` from the strategy `strat (S g) g` of its arm. In Hudgens and Halloran the arm `true` uses
the strategy `ψ` and the arm `false` the strategy `φ`. -/
def twoStageExpect (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (F : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) : ℝ :=
  ∑ S, P1.prob S * ∑ A : ((g : G) → κ g → Bool), (∏ g, (strat (S g) g).prob (A g)) * F S A

/-- The two-stage expectation of a difference is the difference of the expectations. -/
theorem twoStageExpect_sub (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (F F' : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) :
    twoStageExpect P1 strat (fun S A ↦ F S A - F' S A) =
      twoStageExpect P1 strat F - twoStageExpect P1 strat F' := by
  simp only [twoStageExpect, mul_sub, sum_sub_distrib]

/-- The two-stage expectation is additive in the estimator. -/
theorem twoStageExpect_add (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (F F' : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) :
    twoStageExpect P1 strat (fun S A ↦ F S A + F' S A) =
      twoStageExpect P1 strat F + twoStageExpect P1 strat F' := by
  simp only [twoStageExpect, mul_add, sum_add_distrib]

/-- The two-stage expectation commutes with multiplication by a constant. -/
theorem twoStageExpect_const_mul (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (r : ℝ)
    (F : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) :
    twoStageExpect P1 strat (fun S A ↦ r * F S A) = r * twoStageExpect P1 strat F := by
  simp only [twoStageExpect, mul_sum]
  exact sum_congr rfl fun S _ ↦ sum_congr rfl fun A _ ↦ by ring

/-- For each arm vector the second stage weights sum to one. -/
theorem sum_prod_strat_eq_one (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (S : G → Bool) : ∑ A : ((g : G) → κ g → Bool), ∏ g, (strat (S g) g).prob (A g) = 1 := by
  rw [← Fintype.prod_sum (fun g x ↦ (strat (S g) g).prob x)]
  exact prod_eq_one fun g _ ↦ (strat (S g) g).sum_eq_one

/-- Normalization: the two-stage expectation of a constant is that constant. -/
theorem twoStageExpect_const (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (r : ℝ) :
    twoStageExpect P1 strat (fun _ _ ↦ r) = r := by
  simp only [twoStageExpect, ← sum_mul, sum_prod_strat_eq_one, one_mul, P1.sum_eq_one]

/-- Monotonicity of the two-stage expectation. -/
theorem twoStageExpect_mono (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {F F' : (G → Bool) → ((g : G) → κ g → Bool) → ℝ} (h : ∀ S A, F S A ≤ F' S A) :
    twoStageExpect P1 strat F ≤ twoStageExpect P1 strat F' :=
  sum_le_sum fun S _ ↦ mul_le_mul_of_nonneg_left (sum_le_sum fun A _ ↦
    mul_le_mul_of_nonneg_left (h S A) (prod_nonneg fun g _ ↦ (strat (S g) g).nonneg _))
    (P1.nonneg S)

/-- The two-stage design with independent groups given the arm vector, as a joint design:
`Q(S, A) = P1(S) ∏_g (strat (S g) g)(A g)`. -/
def productDesign (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) : JointDesign G κ where
  prob S A := P1.prob S * ∏ g, (strat (S g) g).prob (A g)
  nonneg S A := mul_nonneg (P1.nonneg S) (prod_nonneg fun g _ ↦ (strat (S g) g).nonneg _)
  sum_eq_one := by simp only [← mul_sum, sum_prod_strat_eq_one, mul_one, P1.sum_eq_one]

/-- `twoStageExpect` is the expectation under the product design. -/
theorem twoStageExpect_eq_expect (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (F : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) :
    twoStageExpect P1 strat F = (productDesign P1 strat).expect F := by
  simp only [twoStageExpect, JointDesign.expect, productDesign, mul_sum, mul_assoc]

/-- The first stage of the product design is `P1`. -/
theorem productDesign_firstStage_prob (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (S : G → Bool) :
    (productDesign P1 strat).firstStage.prob S = P1.prob S := by
  simp only [JointDesign.firstStage, productDesign, ← mul_sum, sum_prod_strat_eq_one, mul_one]

theorem productDesign_firstStage_treatProb (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (g : G) (b : Bool) :
    (productDesign P1 strat).firstStage.treatProb g b = P1.treatProb g b := by
  simp only [treatProb, productDesign_firstStage_prob]

/-- A fixed count first stage `P1` gives a fixed count first stage of the product design. -/
theorem FixedCount.productDesign {P1 : AllocationStrategy G}
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) {b : Bool} {c : ℕ}
    (h1 : FixedCount P1 b c) : FixedCount (productDesign P1 strat).firstStage b c :=
  ⟨h1.pos, fun S hS ↦ h1.supp S (by rwa [productDesign_firstStage_prob] at hS),
    fun g ↦ by rw [productDesign_firstStage_treatProb, h1.prob g]⟩

/-- The product design satisfies the second stage condition `JointDesign.Compatible`. -/
theorem productDesign_compatible (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) :
    (productDesign P1 strat).Compatible strat := by
  intro g b z
  rw [productDesign_firstStage_treatProb, treatProb, sum_mul]
  refine sum_congr rfl fun S hS ↦ ?_
  have hX := sum_prod_mul_apply (fun g' ↦ (strat (S g') g').prob)
    (fun g' ↦ (strat (S g') g').sum_eq_one) g (fun x ↦ if x = z then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at hX
  rw [(mem_filter.1 hS).2] at hX
  simp only [productDesign, ← mul_sum, sum_filter, ← hX]

/-- The key computation for two-stage randomization. Suppose the first stage assigns exactly
`c > 0` groups to arm `b` with probability one and assigns each group to arm `b` with
probability `c / N`. Then the average over the groups in arm `b` of group level statistics
`X g (A g)` has expectation `N⁻¹ ∑_g E_{strat b g}[X g]`. This is the instance of
`JointDesign.expect_armAverage` for the product design. -/
theorem twoStageExpect_armAverage (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) {b : Bool} {c : ℕ}
    (h1 : FixedCount P1 b c) (X : (g : G) → (κ g → Bool) → ℝ) :
    twoStageExpect P1 strat
        (fun S A ↦ (∑ g ∈ univ.filter (fun g ↦ S g = b), X g (A g)) / numWith S b) =
      (Fintype.card G : ℝ)⁻¹ * ∑ g, expect (strat b g) (X g) := by
  rw [twoStageExpect_eq_expect]
  exact JointDesign.expect_armAverage _ strat (productDesign_compatible P1 strat)
    (h1.productDesign strat) X

/-- The population estimator `Ŷ(t; ·)` for arm `b` of Hudgens and Halloran: the average, over
the groups assigned to arm `b` by the first stage, of the group estimators `Ŷ_g(t)`. -/
noncomputable def popEstimator (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (b t : Bool)
    (S : G → Bool) (A : (g : G) → κ g → Bool) : ℝ :=
  (∑ g ∈ univ.filter (fun g ↦ S g = b), groupEstimator (Y g) t (A g)) / numWith S b

/-- The population marginal estimator for arm `b`: the average, over the groups assigned to
arm `b`, of the mean observed outcome of the group. -/
noncomputable def popMarginalEstimator (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (b : Bool)
    (S : G → Bool) (A : (g : G) → κ g → Bool) : ℝ :=
  (∑ g ∈ univ.filter (fun g ↦ S g = b), groupMarginalEstimator (Y g) (A g)) / numWith S b

namespace JointDesign

/-- The expectation under a joint design is additive. -/
theorem expect_sub (Q : JointDesign G κ) (F F' : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) :
    Q.expect (fun S A ↦ F S A - F' S A) = Q.expect F - Q.expect F' := by
  simp only [expect, mul_sub, sum_sub_distrib]

/-- Unbiasedness of the population estimator under a general two-stage design `Q`, the
assignments of different groups being allowed to be dependent. First stage: exactly `c > 0`
groups are in arm `b`, each with probability `c / N`. Second stage: `Q` is compatible with
`strat` (`JointDesign.Compatible`), and in each group `g` the strategy of arm `b` assigns `t` to
exactly `m g > 0` units, each with probability `m g / n_g`. Then `E[Ŷ(t; ψ_b)] = ȳ(t; ψ_b)`. The
fixed count hypotheses make every group and the set of groups nonempty and every conditional
average genuine (`FixedCount.nonempty`, `FixedCount.treatProb_pos`). -/
theorem expect_popEstimator (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (Q : JointDesign G κ)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (hQ : Q.Compatible strat)
    {b t : Bool} {c : ℕ} (h1 : FixedCount Q.firstStage b c) {m : G → ℕ}
    (h2 : ∀ g, FixedCount (strat b g) t (m g)) :
    Q.expect (popEstimator Y b t) = popAvg Y (strat b) t := by
  rw [show popEstimator Y b t = fun S A ↦
      (∑ g ∈ univ.filter (fun g ↦ S g = b), groupEstimator (Y g) t (A g)) / numWith S b from rfl,
    Q.expect_armAverage strat hQ h1, popAvg]
  simp only [fun g ↦ expect_groupEstimator_of_fixed (Y g) (h2 g)]

/-- Unbiasedness of the population marginal estimator under a general two-stage design
compatible with `strat`, for nonempty groups, with the fixed count first stage condition and
no condition on the second stage strategies. -/
theorem expect_popMarginalEstimator [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (Q : JointDesign G κ)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (hQ : Q.Compatible strat)
    {b : Bool} {c : ℕ} (h1 : FixedCount Q.firstStage b c) :
    Q.expect (popMarginalEstimator Y b) = popMarginal Y (strat b) := by
  rw [show popMarginalEstimator Y b = fun S A ↦
      (∑ g ∈ univ.filter (fun g ↦ S g = b), groupMarginalEstimator (Y g) (A g)) /
        numWith S b from rfl,
    Q.expect_armAverage strat hQ h1, popMarginal]
  simp only [expect_groupMarginalEstimator]

/-- Unbiased estimation of the population direct effect of the strategies of arm `b` under a
general compatible two-stage design. -/
theorem expect_directEffect (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (Q : JointDesign G κ)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (hQ : Q.Compatible strat) {b : Bool}
    {c : ℕ} (h1 : FixedCount Q.firstStage b c) {m₀ m₁ : G → ℕ}
    (h₀ : ∀ g, FixedCount (strat b g) false (m₀ g)) (h₁ : ∀ g, FixedCount (strat b g) true (m₁ g)) :
    Q.expect (fun S A ↦ popEstimator Y b false S A - popEstimator Y b true S A) =
      directEffect (fun t s ↦ popAvg Y s t) (strat b) := by
  rw [expect_sub, Q.expect_popEstimator Y strat hQ h1 h₀, Q.expect_popEstimator Y strat hQ h1 h₁,
    directEffect]

/-- Unbiased estimation of the population indirect effect `IE(φ, ψ)`, with `φ` the strategies of
arm `false` and `ψ` those of arm `true`, under a general compatible two-stage design. -/
theorem expect_indirectEffect (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (Q : JointDesign G κ)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (hQ : Q.Compatible strat)
    {c₀ c₁ : ℕ} (h1₀ : FixedCount Q.firstStage false c₀) (h1₁ : FixedCount Q.firstStage true c₁)
    {mφ mψ : G → ℕ} (hφ : ∀ g, FixedCount (strat false g) false (mφ g))
    (hψ : ∀ g, FixedCount (strat true g) false (mψ g)) :
    Q.expect (fun S A ↦ popEstimator Y false false S A - popEstimator Y true false S A) =
      indirectEffect (fun t s ↦ popAvg Y s t) (strat false) (strat true) := by
  rw [expect_sub, Q.expect_popEstimator Y strat hQ h1₀ hφ,
    Q.expect_popEstimator Y strat hQ h1₁ hψ, indirectEffect]

/-- Unbiased estimation of the population total effect `TE(φ, ψ)` under a general compatible
two-stage design. -/
theorem expect_totalEffect (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (Q : JointDesign G κ)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) (hQ : Q.Compatible strat)
    {c₀ c₁ : ℕ} (h1₀ : FixedCount Q.firstStage false c₀) (h1₁ : FixedCount Q.firstStage true c₁)
    {mφ mψ : G → ℕ} (hφ : ∀ g, FixedCount (strat false g) false (mφ g))
    (hψ : ∀ g, FixedCount (strat true g) true (mψ g)) :
    Q.expect (fun S A ↦ popEstimator Y false false S A - popEstimator Y true true S A) =
      totalEffect (fun t s ↦ popAvg Y s t) (strat false) (strat true) := by
  rw [expect_sub, Q.expect_popEstimator Y strat hQ h1₀ hφ,
    Q.expect_popEstimator Y strat hQ h1₁ hψ, totalEffect]

/-- Unbiased estimation of the population overall effect `OE(φ, ψ)` under a general compatible
two-stage design, for nonempty groups. -/
theorem expect_overallEffect [∀ g, Nonempty (κ g)] (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (Q : JointDesign G κ) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (hQ : Q.Compatible strat) {c₀ c₁ : ℕ} (h1₀ : FixedCount Q.firstStage false c₀)
    (h1₁ : FixedCount Q.firstStage true c₁) :
    Q.expect (fun S A ↦ popMarginalEstimator Y false S A - popMarginalEstimator Y true S A) =
      overallEffect (popMarginal Y) (strat false) (strat true) := by
  rw [expect_sub, Q.expect_popMarginalEstimator Y strat hQ h1₀,
    Q.expect_popMarginalEstimator Y strat hQ h1₁, overallEffect]

end JointDesign

/-- Unbiasedness of the population estimator under two-stage randomization with independent
groups given the arm vector (the instance `productDesign` of `JointDesign.expect_popEstimator`).
First stage: exactly `c > 0` groups are assigned to arm `b`, each with probability `c / N`.
Second stage: in each group `g` the strategy of arm `b` assigns `t` to exactly `m g > 0` units,
each with probability `m g / n_g`. Then `E[Ŷ(t; ψ_b)] = ȳ(t; ψ_b)`, the population average
potential outcome under the strategies of arm `b`. -/
theorem twoStageExpect_popEstimator (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {b t : Bool} {c : ℕ} (h1 : FixedCount P1 b c) {m : G → ℕ}
    (h2 : ∀ g, FixedCount (strat b g) t (m g)) :
    twoStageExpect P1 strat (popEstimator Y b t) = popAvg Y (strat b) t := by
  rw [twoStageExpect_eq_expect]
  exact JointDesign.expect_popEstimator Y _ strat (productDesign_compatible P1 strat)
    (h1.productDesign strat) h2

/-- Unbiasedness of the population marginal estimator under two-stage randomization, for
nonempty groups, with the same first stage condition and no condition on the second stage
strategies. -/
theorem twoStageExpect_popMarginalEstimator [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {b : Bool} {c : ℕ} (h1 : FixedCount P1 b c) :
    twoStageExpect P1 strat (popMarginalEstimator Y b) = popMarginal Y (strat b) := by
  rw [twoStageExpect_eq_expect]
  exact JointDesign.expect_popMarginalEstimator Y _ strat (productDesign_compatible P1 strat)
    (h1.productDesign strat)

/-- The fully specified design of Hudgens and Halloran. First stage: complete randomization of
`c` of the `N` groups to arm `true`, the others going to arm `false`. Second stage: in arm `b`
group `g` is completely randomized with `k b g` of its `n_g` members treated, independently
across groups. The population estimator for arm `b` and treatment `t` is unbiased,
`E[Ŷ(t; ψ_b)] = ȳ(t; ψ_b)`, provided arm `b` is not empty (`0 < c` for `b = true`, `c < N` for
`b = false`) and, in every group, treatment `t` is given to at least one unit in arm `b`
(`0 < k b g` for `t = true`, `k b g < n_g` for `t = false`). -/
theorem twoStageExpect_popEstimator_completeRandomization
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) {c : ℕ} (hc : c ≤ Fintype.card G)
    (k : Bool → G → ℕ) (hk : ∀ b g, k b g ≤ Fintype.card (κ g)) (b t : Bool)
    (hcb : if b then 0 < c else c < Fintype.card G)
    (hkb : ∀ g, if t then 0 < k b g else k b g < Fintype.card (κ g)) :
    twoStageExpect (completeRandomization G c hc)
        (fun b g ↦ completeRandomization (κ g) (k b g) (hk b g)) (popEstimator Y b t) =
      popAvg Y (fun g ↦ completeRandomization (κ g) (k b g) (hk b g)) t := by
  have h2 : ∃ m : G → ℕ, ∀ g,
      FixedCount (completeRandomization (κ g) (k b g) (hk b g)) t (m g) := by
    cases t
    · exact ⟨fun g ↦ Fintype.card (κ g) - k b g, fun g ↦
        .completeRandomization_false (by simpa using hkb g)⟩
    · exact ⟨k b, fun g ↦ .completeRandomization_true (by simpa using hkb g) (hk b g)⟩
  obtain ⟨m, hm⟩ := h2
  cases b
  · exact twoStageExpect_popEstimator Y _ _
      (.completeRandomization_false (by simpa using hcb)) hm
  · exact twoStageExpect_popEstimator Y _ _
      (.completeRandomization_true (by simpa using hcb) hc) hm

/-- Unbiased estimation of the population direct effect `DE(ψ_b) = ȳ(0; ψ_b) - ȳ(1; ψ_b)` of
the strategies of arm `b` by `Ŷ(0; ψ_b) - Ŷ(1; ψ_b)`, under the fixed count conditions of
`twoStageExpect_popEstimator` for arm `b` and both treatments. -/
theorem twoStageExpect_directEffect (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g)) {b : Bool}
    {c : ℕ} (h1 : FixedCount P1 b c) {m₀ m₁ : G → ℕ}
    (h₀ : ∀ g, FixedCount (strat b g) false (m₀ g)) (h₁ : ∀ g, FixedCount (strat b g) true (m₁ g)) :
    twoStageExpect P1 strat (fun S A ↦ popEstimator Y b false S A - popEstimator Y b true S A) =
      directEffect (fun t s ↦ popAvg Y s t) (strat b) := by
  rw [twoStageExpect_sub, twoStageExpect_popEstimator Y P1 strat h1 h₀,
    twoStageExpect_popEstimator Y P1 strat h1 h₁, directEffect]

/-- Unbiased estimation of the population indirect effect `IE(φ, ψ) = ȳ(0; φ) - ȳ(0; ψ)`,
with `φ` the strategies of arm `false` and `ψ` those of arm `true`, by `Ŷ(0; φ) - Ŷ(0; ψ)`,
under the fixed count conditions for both arms and treatment `false`. -/
theorem twoStageExpect_indirectEffect (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {c₀ c₁ : ℕ} (h1₀ : FixedCount P1 false c₀) (h1₁ : FixedCount P1 true c₁) {mφ mψ : G → ℕ}
    (hφ : ∀ g, FixedCount (strat false g) false (mφ g))
    (hψ : ∀ g, FixedCount (strat true g) false (mψ g)) :
    twoStageExpect P1 strat
        (fun S A ↦ popEstimator Y false false S A - popEstimator Y true false S A) =
      indirectEffect (fun t s ↦ popAvg Y s t) (strat false) (strat true) := by
  rw [twoStageExpect_sub, twoStageExpect_popEstimator Y P1 strat h1₀ hφ,
    twoStageExpect_popEstimator Y P1 strat h1₁ hψ, indirectEffect]

/-- Unbiased estimation of the population total effect `TE(φ, ψ) = ȳ(0; φ) - ȳ(1; ψ)` by
`Ŷ(0; φ) - Ŷ(1; ψ)`, under the fixed count conditions for control in arm `false` and treatment
in arm `true`. -/
theorem twoStageExpect_totalEffect (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {c₀ c₁ : ℕ} (h1₀ : FixedCount P1 false c₀) (h1₁ : FixedCount P1 true c₁) {mφ mψ : G → ℕ}
    (hφ : ∀ g, FixedCount (strat false g) false (mφ g))
    (hψ : ∀ g, FixedCount (strat true g) true (mψ g)) :
    twoStageExpect P1 strat
        (fun S A ↦ popEstimator Y false false S A - popEstimator Y true true S A) =
      totalEffect (fun t s ↦ popAvg Y s t) (strat false) (strat true) := by
  rw [twoStageExpect_sub, twoStageExpect_popEstimator Y P1 strat h1₀ hφ,
    twoStageExpect_popEstimator Y P1 strat h1₁ hψ, totalEffect]

/-- Unbiased estimation of the population overall effect `OE(φ, ψ) = ȳ(φ) - ȳ(ψ)` by the
difference of the marginal estimators, for nonempty groups, under the first stage conditions
for both arms. -/
theorem twoStageExpect_overallEffect [∀ g, Nonempty (κ g)] (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {c₀ c₁ : ℕ} (h1₀ : FixedCount P1 false c₀) (h1₁ : FixedCount P1 true c₁) :
    twoStageExpect P1 strat
        (fun S A ↦ popMarginalEstimator Y false S A - popMarginalEstimator Y true S A) =
      overallEffect (popMarginal Y) (strat false) (strat true) := by
  rw [twoStageExpect_sub, twoStageExpect_popMarginalEstimator Y P1 strat h1₀,
    twoStageExpect_popMarginalEstimator Y P1 strat h1₁, overallEffect]

end Population

end Interference

end CausalInference
