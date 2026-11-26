/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Interference.PartialInterference

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
* `twoStageExpect`: the expectation under two-stage randomization; a first stage strategy
  assigns each group `g` to arm `S g`, and given `S` the groups are randomized independently,
  group `g` following the strategy `strat (S g) g`.
* `popEstimator`: the average of the group estimators over the groups assigned to a given arm.

## Main results

* `completeRandomization_treatProb_true`: under complete randomization of `k` among `n` units,
  every unit is treated with probability `k / n`. The proof uses only that the design is
  invariant under permutations of the units and that it treats exactly `k` units.
* `expect_groupEstimator_of_fixed`, `expect_groupEstimator_completeRandomization_true`,
  `expect_groupEstimator_completeRandomization_false`: the group estimator is unbiased for the
  group average potential outcome `ȳ(t; ψ)` within the group.
* `twoStageExpect_popEstimator`, `twoStageExpect_popEstimator_completeRandomization`: the
  population estimator is unbiased for the population average potential outcome under
  two-stage randomization; likewise for the marginal estimators, and for the estimators of the
  direct, indirect, total and overall effects.

Source: M. G. Hudgens and M. E. Halloran (2008), Toward causal inference with interference,
Journal of the American Statistical Association 103. Variance results are not formalized.
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

/-- Complete randomization of `k > 0` units treats a fixed number, `k`, of units. -/
theorem FixedCount.completeRandomization_true {k : ℕ} (hk0 : 0 < k) (hk : k ≤ Fintype.card ι) :
    FixedCount (completeRandomization ι k hk) true k :=
  ⟨hk0, completeRandomization_supp hk, completeRandomization_treatProb_true hk⟩

/-- Complete randomization of `k < n` units leaves a fixed number, `n - k`, of controls. -/
theorem FixedCount.completeRandomization_false {k : ℕ} (hk : k < Fintype.card ι) :
    FixedCount (completeRandomization ι k hk.le) false (Fintype.card ι - k) :=
  ⟨Nat.sub_pos_of_lt hk, fun a ha ↦ by rw [numWith_false, completeRandomization_supp hk.le a ha],
    completeRandomization_treatProb_false hk.le⟩

/-! ### Unbiased estimation within a group -/

/-- The estimator `Ŷ(t; ψ)` of Hudgens and Halloran for the group average potential outcome:
the mean observed outcome `Y a j` among the units `j` with `a j = t`, where `a` is the
realized assignment vector. -/
noncomputable def groupEstimator (Y : (ι → Bool) → ι → ℝ) (t : Bool) (a : ι → Bool) : ℝ :=
  (∑ j ∈ univ.filter (fun j ↦ a j = t), Y a j) / numWith a t

/-- Unbiasedness of the group estimator: if the strategy `ψ` assigns `t` to exactly `m > 0`
units with probability one and assigns `t` to every unit with probability `m / n`, then
`E_ψ[Ŷ(t; ψ)] = ȳ(t; ψ)`. -/
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

/-- The mean observed outcome of the group is unbiased for the marginal group average under
every allocation strategy. -/
theorem expect_groupMarginalEstimator (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) :
    expect ψ (groupMarginalEstimator Y) = groupMarginal Y ψ := by
  simp only [expect, groupMarginalEstimator, groupMarginal, indivMarginal, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

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

/-- The expectation of `F S A` under two-stage randomization. In the first stage the vector
`S : G → Bool` assigning each group to one of two arms is drawn from `P1`; in the second stage,
given `S`, the groups are randomized independently, group `g` drawing its assignment vector
`A g` from the strategy `strat (S g) g` of its arm. In Hudgens and Halloran the arm `true` uses
the strategy `ψ` and the arm `false` the strategy `φ`. -/
def twoStageExpect (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (F : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) : ℝ :=
  ∑ S, P1.prob S * ∑ A : ((g : G) → κ g → Bool), (∏ g, (strat (S g) g).prob (A g)) * F S A

/-- The two-stage expectation is additive in the estimator. -/
theorem twoStageExpect_sub (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (F F' : (G → Bool) → ((g : G) → κ g → Bool) → ℝ) :
    twoStageExpect P1 strat (fun S A ↦ F S A - F' S A) =
      twoStageExpect P1 strat F - twoStageExpect P1 strat F' := by
  simp only [twoStageExpect, mul_sub, sum_sub_distrib]

/-- The key computation for two-stage randomization. Suppose the first stage assigns exactly
`c > 0` groups to arm `b` with probability one and assigns each group to arm `b` with
probability `c / N`. Then the average over the groups in arm `b` of group level statistics
`X g (A g)` has expectation `N⁻¹ ∑_g E_{strat b g}[X g]`. -/
theorem twoStageExpect_armAverage (P1 : AllocationStrategy G)
    (strat : Bool → (g : G) → AllocationStrategy (κ g)) {b : Bool} {c : ℕ}
    (h1 : FixedCount P1 b c) (X : (g : G) → (κ g → Bool) → ℝ) :
    twoStageExpect P1 strat
        (fun S A ↦ (∑ g ∈ univ.filter (fun g ↦ S g = b), X g (A g)) / numWith S b) =
      (Fintype.card G : ℝ)⁻¹ * ∑ g, expect (strat b g) (X g) := by
  have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h1.pos.ne'
  have hS1 : ∀ S : G → Bool, P1.prob S * ∑ A : ((g : G) → κ g → Bool),
      (∏ g, (strat (S g) g).prob (A g)) *
        ((∑ g ∈ univ.filter (fun g ↦ S g = b), X g (A g)) / numWith S b) =
      (c : ℝ)⁻¹ * ∑ g, if S g = b then P1.prob S * expect (strat b g) (X g) else 0 := by
    intro S
    by_cases hS : P1.prob S = 0
    · simp [hS]
    rw [h1.supp S hS]
    have hA : ∀ A : ((g : G) → κ g → Bool), (∏ g, (strat (S g) g).prob (A g)) *
        ((∑ g ∈ univ.filter (fun g ↦ S g = b), X g (A g)) / c) =
        (c : ℝ)⁻¹ * ∑ g ∈ univ.filter (fun g ↦ S g = b),
          (∏ g', (strat (S g') g').prob (A g')) * X g (A g) := by
      intro A
      rw [← mul_sum]
      ring
    have hg : ∀ g ∈ univ.filter (fun g ↦ S g = b), ∑ A : ((g : G) → κ g → Bool),
        (∏ g', (strat (S g') g').prob (A g')) * X g (A g) = expect (strat b g) (X g) := by
      intro g hg
      rw [sum_prod_mul_apply (fun g' ↦ (strat (S g') g').prob)
        (fun g' ↦ (strat (S g') g').sum_eq_one) g (X g), expect, (mem_filter.1 hg).2]
    rw [sum_congr rfl fun A _ ↦ hA A, ← mul_sum, sum_comm, sum_congr rfl hg, sum_filter,
      mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun g _ ↦ ?_
    split_ifs <;> ring
  have h2 : ∀ g, ∑ S : G → Bool, (if S g = b then P1.prob S * expect (strat b g) (X g) else 0) =
      c / Fintype.card G * expect (strat b g) (X g) := by
    intro g
    rw [← h1.prob g, treatProb, sum_mul, sum_filter]
  simp only [twoStageExpect, hS1, ← mul_sum]
  rw [sum_comm]
  simp only [h2, ← mul_sum, ← mul_assoc]
  congr 1
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]

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

/-- Unbiasedness of the population estimator under two-stage randomization. First stage:
exactly `c > 0` groups are assigned to arm `b`, each with probability `c / N`. Second stage:
in each group `g` the strategy of arm `b` assigns `t` to exactly `m g > 0` units, each with
probability `m g / n_g`. Then `E[Ŷ(t; ψ_b)] = ȳ(t; ψ_b)`, the population average potential
outcome under the strategies of arm `b`. -/
theorem twoStageExpect_popEstimator (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {b t : Bool} {c : ℕ} (h1 : FixedCount P1 b c) {m : G → ℕ}
    (h2 : ∀ g, FixedCount (strat b g) t (m g)) :
    twoStageExpect P1 strat (popEstimator Y b t) = popAvg Y (strat b) t := by
  rw [show popEstimator Y b t = fun S A ↦
      (∑ g ∈ univ.filter (fun g ↦ S g = b), groupEstimator (Y g) t (A g)) / numWith S b from rfl,
    twoStageExpect_armAverage P1 strat h1, popAvg]
  simp only [fun g ↦ expect_groupEstimator_of_fixed (Y g) (h2 g)]

/-- Unbiasedness of the population marginal estimator under two-stage randomization, with the
same first stage condition and no condition on the second stage strategies. -/
theorem twoStageExpect_popMarginalEstimator (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (P1 : AllocationStrategy G) (strat : Bool → (g : G) → AllocationStrategy (κ g))
    {b : Bool} {c : ℕ} (h1 : FixedCount P1 b c) :
    twoStageExpect P1 strat (popMarginalEstimator Y b) = popMarginal Y (strat b) := by
  rw [show popMarginalEstimator Y b = fun S A ↦
      (∑ g ∈ univ.filter (fun g ↦ S g = b), groupMarginalEstimator (Y g) (A g)) /
        numWith S b from rfl,
    twoStageExpect_armAverage P1 strat h1, popMarginal]
  simp only [expect_groupMarginalEstimator]

/-- The fully specified design of Hudgens and Halloran. First stage: complete randomization of
`c` of the `N` groups to arm `true` (strategies `ψ`), the others going to arm `false`
(strategies `φ`), with `0 < c < N`. Second stage: in arm `b` group `g` is completely randomized
with `k b g` treated, `0 < k b g < n_g`. Then for both arms and both treatments the population
estimator is unbiased: `E[Ŷ(t; strat b)] = ȳ(t; strat b)`. -/
theorem twoStageExpect_popEstimator_completeRandomization
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) {c : ℕ} (hc0 : 0 < c) (hc : c < Fintype.card G)
    (k : Bool → G → ℕ) (hk0 : ∀ b g, 0 < k b g) (hk : ∀ b g, k b g < Fintype.card (κ g))
    (strat : Bool → (g : G) → AllocationStrategy (κ g))
    (hstrat : ∀ b g, strat b g = completeRandomization (κ g) (k b g) (hk b g).le) (b t : Bool) :
    twoStageExpect (completeRandomization G c hc.le) strat (popEstimator Y b t) =
      popAvg Y (strat b) t := by
  have h2 : ∀ t, ∃ m : G → ℕ, ∀ g, FixedCount (strat b g) t (m g) := by
    intro t
    cases t
    · exact ⟨fun g ↦ Fintype.card (κ g) - k b g, fun g ↦ by
        rw [hstrat]; exact .completeRandomization_false (hk b g)⟩
    · exact ⟨k b, fun g ↦ by rw [hstrat]; exact .completeRandomization_true (hk0 b g) (hk b g).le⟩
  obtain ⟨m, hm⟩ := h2 t
  cases b
  · exact twoStageExpect_popEstimator Y _ strat (.completeRandomization_false hc) hm
  · exact twoStageExpect_popEstimator Y _ strat (.completeRandomization_true hc0 hc.le) hm

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
difference of the marginal estimators, under the first stage conditions for both arms. -/
theorem twoStageExpect_overallEffect (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
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
