/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Interference.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring

/-!
# Partial interference: allocation strategies and the Hudgens and Halloran estimands

A group is a finite set of individuals `ι`; its potential outcomes `Y : (ι → Bool) → ι → ℝ`
are indexed by the group's assignment vector. A population is a finite family of groups
`κ : G → Type*` with group outcomes `Y g`; indexing each group's outcomes by that group's own
assignment vector is exactly the partial interference assumption, and
`PartialInterference.eq_groupOutcome` makes the passage from a population wide outcome
function precise.

An allocation strategy `ψ` is a probability weight function on the group's assignment vectors.
For a group under `ψ` we define, following Hudgens and Halloran:

* `indivAvg Y ψ i t`: the individual average potential outcome `ȳ_i(t; ψ)`, the average of
  `Y a i` over the assignment vectors drawn from `ψ` conditionally on `a i = t`;
* `indivMarginal Y ψ i`: the marginal individual average potential outcome `ȳ_i(ψ)`;
* `groupAvg`, `groupMarginal`: their averages over the individuals of the group;
* `popAvg`, `popMarginal`: the averages of the group quantities over the groups.

The causal effects are defined once, for any family of averages `ybar : Bool → S → ℝ`:
`directEffect ybar ψ = ybar false ψ - ybar true ψ`,
`indirectEffect ybar φ ψ = ybar false φ - ybar false ψ`,
`totalEffect ybar φ ψ = ybar false φ - ybar true ψ`, and
`overallEffect ymarg φ ψ = ymarg φ - ymarg ψ`. This is the sign convention of Hudgens and
Halloran (control minus treatment, natural for a vaccine that lowers the risk of disease).

Positivity (`AllocationStrategy.Positive`: every individual receives each treatment with
positive probability) and nonemptiness of groups and of the set of groups are hypotheses of
every causal statement about these averages, so that no result rests on the convention
`x / 0 = 0`. Some of these identities are algebraic and hold without the hypotheses; their
docstrings say so.

## Main results

* `le_indivAvg`, `indivAvg_le`: under positivity `ȳ_i(t; ψ)` lies between the bounds of the
  outcomes it averages.
* `totalEffect_eq_directEffect_add_indirectEffect`: `TE(φ, ψ) = DE(ψ) + IE(φ, ψ)`, with its
  instances at the individual, group and population levels.
* `groupDirectEffect_eq_average` and relatives: group and population effects are averages of
  the lower level effects.
* `indivOverallEffect_eq`, `groupOverallEffect_eq_sum`, `popOverallEffect_eq_sum`: the
  decomposition `OE(φ, ψ) = IE(φ, ψ) - p_φ DE(φ) + p_ψ DE(ψ)`, where `p_φ` is the probability
  of treatment; at the group and population levels with unit specific probabilities, the
  products `p DE` being averaged over individuals. `popOverallEffect_eq_of_groupTreatProb`,
  `groupOverallEffect_eq` and `popOverallEffect_eq` are the special cases with probabilities
  common within each group or across the population.
* `NoInterference.indivAvg_eq`, `NoInterference.indirectEffect_eq_zero`,
  `NoInterference.directEffect_eq`, `NoInterference.groupDirectEffect_eq`,
  `NoInterference.groupIndirectEffect_eq_zero`, `NoInterference.popDirectEffect_eq`,
  `NoInterference.popIndirectEffect_eq_zero`: reduction to the classical case. Under no
  interference and positivity `ȳ_i(t; ψ)` is the classical potential outcome, the direct effect
  is `y0 - y1` (at group level minus the finite population average treatment effect), and the
  indirect effects vanish.

Source: M. G. Hudgens and M. E. Halloran (2008), Toward causal inference with interference,
Journal of the American Statistical Association 103.
-/

@[expose] public section

open Finset

namespace CausalInference

namespace Interference

/-! ### Groups and partial interference -/

section Bridge

variable {ι G : Type*}

/-- The assignment vector on the whole population obtained from an assignment `b` of the
members of group `c`, giving every nonmember the assignment `false`. -/
def extendFromGroup [DecidableEq G] (g : ι → G) (c : G) (b : {j // g j = c} → Bool) :
    ι → Bool :=
  fun j ↦ if h : g j = c then b ⟨j, h⟩ else false

/-- The group level potential outcomes of group `c` induced by population wide potential
outcomes `Y`: the outcome of member `j` when the group is assigned `b` and every other unit is
assigned `false`. -/
def groupOutcome [DecidableEq G] (g : ι → G) (Y : (ι → Bool) → ι → ℝ) (c : G)
    (b : {j // g j = c} → Bool) (j : {j // g j = c}) : ℝ :=
  Y (extendFromGroup g c b) j

/-- Under partial interference the population wide outcome of unit `j` is the group level
outcome of its group, evaluated at the restriction of the assignment vector to that group. -/
theorem PartialInterference.eq_groupOutcome [DecidableEq G] {g : ι → G}
    {Y : (ι → Bool) → ι → ℝ} (h : PartialInterference g Y) (a : ι → Bool) (j : ι) :
    Y a j = groupOutcome g Y (g j) (fun k ↦ a k) ⟨j, rfl⟩ := by
  refine h a _ j fun k hk ↦ ?_
  simp [extendFromGroup, hk]

end Bridge

/-! ### Allocation strategies and individual averages -/

/-- An allocation strategy for a finite group `ι`: a probability weight function on the
group's assignment vectors (nonnegative weights summing to one). -/
structure AllocationStrategy (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The probability of each assignment vector. -/
  prob : (ι → Bool) → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace AllocationStrategy

/-- The probability under `ψ` that individual `i` receives treatment `t`. -/
def treatProb (ψ : AllocationStrategy ι) (i : ι) (t : Bool) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ι → Bool ↦ a i = t), ψ.prob a

theorem treatProb_nonneg (ψ : AllocationStrategy ι) (i : ι) (t : Bool) :
    0 ≤ ψ.treatProb i t :=
  sum_nonneg fun a _ ↦ ψ.nonneg a

/-- The probabilities of control and of treatment of an individual add up to one. -/
theorem treatProb_false_add_true (ψ : AllocationStrategy ι) (i : ι) :
    ψ.treatProb i false + ψ.treatProb i true = 1 := by
  rw [← ψ.sum_eq_one, treatProb, treatProb, ← sum_filter_add_sum_filter_not univ
    (fun a : ι → Bool ↦ a i = false)]
  congr 1
  refine sum_congr ?_ fun _ _ ↦ rfl
  ext a
  simp

/-- Positivity of an allocation strategy: every individual receives each treatment with positive
probability, so that every conditional average `ȳ_i(t; ψ)` is a genuine conditional mean. -/
def Positive (ψ : AllocationStrategy ι) : Prop := ∀ i t, 0 < ψ.treatProb i t

end AllocationStrategy

open AllocationStrategy

/-- The weighted sum `∑_{a : a i = t} ψ(a) Y a i`, the numerator of `ȳ_i(t; ψ)`. -/
def indivSum (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (i : ι) (t : Bool) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ι → Bool ↦ a i = t), ψ.prob a * Y a i

/-- The individual average potential outcome `ȳ_i(t; ψ)` of Hudgens and Halloran: the average
of `Y a i` over assignment vectors drawn from `ψ`, conditionally on `a i = t`. It is a genuine
conditional average only when `ψ.treatProb i t > 0`; when that probability is zero the value is
the meaningless `0 / 0 = 0`. Every causal contrast built on it below assumes positivity
(`AllocationStrategy.Positive` or the relevant cell); the only results stated without it are
identities in which this average is multiplied by its probability, so that its value is
irrelevant (`treatProb_mul_indivAvg`, `indivMarginal_eq`). -/
noncomputable def indivAvg (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (i : ι)
    (t : Bool) : ℝ :=
  indivSum Y ψ i t / ψ.treatProb i t

/-- The marginal individual average potential outcome `ȳ_i(ψ) = ∑_a ψ(a) Y a i`. -/
def indivMarginal (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (i : ι) : ℝ :=
  ∑ a, ψ.prob a * Y a i

/-- `ψ.treatProb i t * ȳ_i(t; ψ)` is the numerator `indivSum`. When the probability is zero
both sides are zero, because every weight in the numerator is zero; the value assigned to
`ȳ_i(t; ψ)` in that case plays no role. -/
theorem treatProb_mul_indivAvg (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (i : ι)
    (t : Bool) : ψ.treatProb i t * indivAvg Y ψ i t = indivSum Y ψ i t := by
  by_cases hp : ψ.treatProb i t = 0
  · have hz : ∀ a ∈ univ.filter (fun a : ι → Bool ↦ a i = t), ψ.prob a = 0 :=
      (sum_eq_zero_iff_of_nonneg fun a _ ↦ ψ.nonneg a).1 hp
    rw [hp, zero_mul, indivSum, sum_eq_zero fun a ha ↦ by rw [hz a ha, zero_mul]]
  · rw [indivAvg, mul_div_cancel₀ _ hp]

/-- The marginal individual average is the mixture
`ȳ_i(ψ) = P(a i = 0) ȳ_i(0; ψ) + P(a i = 1) ȳ_i(1; ψ)`. -/
theorem indivMarginal_eq (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (i : ι) :
    indivMarginal Y ψ i = ψ.treatProb i false * indivAvg Y ψ i false +
      ψ.treatProb i true * indivAvg Y ψ i true := by
  rw [treatProb_mul_indivAvg, treatProb_mul_indivAvg, indivMarginal, indivSum, indivSum,
    ← sum_filter_add_sum_filter_not univ (fun a : ι → Bool ↦ a i = false)]
  congr 1
  refine sum_congr ?_ fun _ _ ↦ rfl
  ext a
  simp

/-- Interpretation of `ȳ_i(t; ψ)` as a conditional mean, lower bound: if `i` receives `t` with
positive probability and `m ≤ Y a i` for every assignment vector with `a i = t`, then
`m ≤ ȳ_i(t; ψ)`. -/
theorem le_indivAvg (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (i : ι) (t : Bool)
    (hp : 0 < ψ.treatProb i t) {m : ℝ} (hm : ∀ a, a i = t → m ≤ Y a i) :
    m ≤ indivAvg Y ψ i t := by
  rw [indivAvg, le_div_iff₀ hp, treatProb, mul_sum, indivSum]
  refine sum_le_sum fun a ha ↦ ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (hm a (mem_filter.1 ha).2) (ψ.nonneg a)

/-- Interpretation of `ȳ_i(t; ψ)` as a conditional mean, upper bound: if `i` receives `t` with
positive probability and `Y a i ≤ M` for every assignment vector with `a i = t`, then
`ȳ_i(t; ψ) ≤ M`. -/
theorem indivAvg_le (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (i : ι) (t : Bool)
    (hp : 0 < ψ.treatProb i t) {M : ℝ} (hM : ∀ a, a i = t → Y a i ≤ M) :
    indivAvg Y ψ i t ≤ M := by
  rw [indivAvg, div_le_iff₀ hp, treatProb, mul_sum, indivSum]
  refine sum_le_sum fun a ha ↦ ?_
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM a (mem_filter.1 ha).2) (ψ.nonneg a)

/-- Under no interference the individual average potential outcome is the classical potential
outcome, provided the treatment `t` has positive probability for `i`. -/
theorem NoInterference.indivAvg_eq {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y)
    (ψ : AllocationStrategy ι) (i : ι) (t : Bool) (hp : 0 < ψ.treatProb i t) :
    indivAvg Y ψ i t = unitOutcome Y i t := by
  have hs : indivSum Y ψ i t = ψ.treatProb i t * unitOutcome Y i t := by
    rw [indivSum, treatProb, sum_mul]
    refine sum_congr rfl fun a ha ↦ ?_
    rw [h.eq_unitOutcome, (mem_filter.1 ha).2]
  rw [indivAvg, hs, mul_div_cancel_left₀ _ hp.ne']

/-! ### Group and population averages -/

/-- The group average potential outcome `ȳ(t; ψ) = n⁻¹ ∑_i ȳ_i(t; ψ)` of a group of `n`
individuals. It is a genuine average only for a nonempty group (`n > 0`); every causal
statement about it below assumes `[Nonempty ι]`. -/
noncomputable def groupAvg (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) (t : Bool) :
    ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, indivAvg Y ψ i t

/-- The marginal group average potential outcome `ȳ(ψ) = n⁻¹ ∑_i ȳ_i(ψ)`, a genuine average
only for a nonempty group. -/
noncomputable def groupMarginal (Y : (ι → Bool) → ι → ℝ) (ψ : AllocationStrategy ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, indivMarginal Y ψ i

section Population

variable {G : Type*} [Fintype G] {κ : G → Type*} [∀ g, Fintype (κ g)] [∀ g, DecidableEq (κ g)]

/-- The population average potential outcome: the average over the `N` groups of the group
averages, `N⁻¹ ∑_g ȳ_g(t; ψ_g)`, where group `g` follows the strategy `ψ g`. It is a genuine
average only when there is at least one group and every group is nonempty; every causal
statement about it below assumes `[Nonempty G]` and `[∀ g, Nonempty (κ g)]`. -/
noncomputable def popAvg (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (ψ : (g : G) → AllocationStrategy (κ g)) (t : Bool) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, groupAvg (Y g) (ψ g) t

/-- The marginal population average potential outcome `N⁻¹ ∑_g ȳ_g(ψ_g)`, a genuine average only
for a nonempty family of nonempty groups. -/
noncomputable def popMarginal (Y : (g : G) → (κ g → Bool) → κ g → ℝ)
    (ψ : (g : G) → AllocationStrategy (κ g)) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g, groupMarginal (Y g) (ψ g)

end Population

/-! ### Causal effects -/

section Effects

variable {S : Type*}

/-- The direct effect `DE(ψ) = ȳ(0; ψ) - ȳ(1; ψ)` for a family of average potential outcomes
`ybar t ψ` (sign convention of Hudgens and Halloran). -/
def directEffect (ybar : Bool → S → ℝ) (ψ : S) : ℝ := ybar false ψ - ybar true ψ

/-- The indirect effect `IE(φ, ψ) = ȳ(0; φ) - ȳ(0; ψ)`. -/
def indirectEffect (ybar : Bool → S → ℝ) (φ ψ : S) : ℝ := ybar false φ - ybar false ψ

/-- The total effect `TE(φ, ψ) = ȳ(0; φ) - ȳ(1; ψ)`. -/
def totalEffect (ybar : Bool → S → ℝ) (φ ψ : S) : ℝ := ybar false φ - ybar true ψ

/-- The overall effect `OE(φ, ψ) = ȳ(φ) - ȳ(ψ)` for a family of marginal averages. -/
def overallEffect (ymarg : S → ℝ) (φ ψ : S) : ℝ := ymarg φ - ymarg ψ

/-- The total effect is the sum of the direct effect under `ψ` and the indirect effect:
`TE(φ, ψ) = DE(ψ) + IE(φ, ψ)`. -/
theorem totalEffect_eq_directEffect_add_indirectEffect (ybar : Bool → S → ℝ) (φ ψ : S) :
    totalEffect ybar φ ψ = directEffect ybar ψ + indirectEffect ybar φ ψ := by
  simp only [totalEffect, directEffect, indirectEffect]
  ring

/-- If the marginal average is the mixture `ȳ(ψ) = (1 - p_ψ) ȳ(0; ψ) + p_ψ ȳ(1; ψ)` for every
strategy, then `OE(φ, ψ) = IE(φ, ψ) - p_φ DE(φ) + p_ψ DE(ψ)`. -/
theorem overallEffect_eq_of_mixture (ybar : Bool → S → ℝ) (ymarg : S → ℝ) (p : S → ℝ)
    (hmix : ∀ ψ, ymarg ψ = (1 - p ψ) * ybar false ψ + p ψ * ybar true ψ) (φ ψ : S) :
    overallEffect ymarg φ ψ =
      indirectEffect ybar φ ψ - p φ * directEffect ybar φ + p ψ * directEffect ybar ψ := by
  simp only [overallEffect, indirectEffect, directEffect, hmix]
  ring

end Effects

/-- Under no interference the individual indirect effect vanishes, provided `i` is a control
with positive probability under both strategies. -/
theorem NoInterference.indirectEffect_eq_zero {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y)
    (i : ι) (φ ψ : AllocationStrategy ι) (hφ : 0 < φ.treatProb i false)
    (hψ : 0 < ψ.treatProb i false) :
    indirectEffect (fun t s ↦ indivAvg Y s i t) φ ψ = 0 := by
  rw [indirectEffect, h.indivAvg_eq φ i false hφ, h.indivAvg_eq ψ i false hψ, sub_self]

/-! ### The effects at the individual, group and population levels -/

/-- Individual level: `TE_i(φ, ψ) = DE_i(ψ) + IE_i(φ, ψ)`. The identity is algebraic;
positivity of both strategies is assumed so that every average in it is a genuine conditional
mean, and is not used in the proof. -/
theorem indivTotalEffect_eq (Y : (ι → Bool) → ι → ℝ) (i : ι) (φ ψ : AllocationStrategy ι)
    (_hφ : φ.Positive) (_hψ : ψ.Positive) :
    totalEffect (fun t s ↦ indivAvg Y s i t) φ ψ =
      directEffect (fun t s ↦ indivAvg Y s i t) ψ +
        indirectEffect (fun t s ↦ indivAvg Y s i t) φ ψ :=
  totalEffect_eq_directEffect_add_indirectEffect _ φ ψ

/-- Group level: `TE(φ, ψ) = DE(ψ) + IE(φ, ψ)` for the group averages of a nonempty group. The
identity is algebraic; positivity is assumed so that every average in it is meaningful, and is
not used in the proof. -/
theorem groupTotalEffect_eq [Nonempty ι] (Y : (ι → Bool) → ι → ℝ) (φ ψ : AllocationStrategy ι)
    (_hφ : φ.Positive) (_hψ : ψ.Positive) :
    totalEffect (fun t s ↦ groupAvg Y s t) φ ψ =
      directEffect (fun t s ↦ groupAvg Y s t) ψ +
        indirectEffect (fun t s ↦ groupAvg Y s t) φ ψ :=
  totalEffect_eq_directEffect_add_indirectEffect _ φ ψ

/-- The group direct effect is the average of the individual direct effects (nonempty group,
positive strategy; positivity is not used in the proof). -/
theorem groupDirectEffect_eq_average [Nonempty ι] (Y : (ι → Bool) → ι → ℝ)
    (ψ : AllocationStrategy ι) (_hψ : ψ.Positive) :
    directEffect (fun t s ↦ groupAvg Y s t) ψ =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, directEffect (fun t s ↦ indivAvg Y s i t) ψ := by
  simp only [directEffect, groupAvg, sum_sub_distrib, mul_sub]

/-- The group indirect effect is the average of the individual indirect effects (nonempty
group, positive strategies; positivity is not used in the proof). -/
theorem groupIndirectEffect_eq_average [Nonempty ι] (Y : (ι → Bool) → ι → ℝ)
    (φ ψ : AllocationStrategy ι) (_hφ : φ.Positive) (_hψ : ψ.Positive) :
    indirectEffect (fun t s ↦ groupAvg Y s t) φ ψ =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, indirectEffect (fun t s ↦ indivAvg Y s i t) φ ψ := by
  simp only [indirectEffect, groupAvg, sum_sub_distrib, mul_sub]

/-- The group total effect is the average of the individual total effects (nonempty group,
positive strategies; positivity is not used in the proof). -/
theorem groupTotalEffect_eq_average [Nonempty ι] (Y : (ι → Bool) → ι → ℝ)
    (φ ψ : AllocationStrategy ι) (_hφ : φ.Positive) (_hψ : ψ.Positive) :
    totalEffect (fun t s ↦ groupAvg Y s t) φ ψ =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, totalEffect (fun t s ↦ indivAvg Y s i t) φ ψ := by
  simp only [totalEffect, groupAvg, sum_sub_distrib, mul_sub]

/-- The group overall effect is the average of the individual overall effects (nonempty group;
no conditional average is involved, so no positivity is needed). -/
theorem groupOverallEffect_eq_average [Nonempty ι] (Y : (ι → Bool) → ι → ℝ)
    (φ ψ : AllocationStrategy ι) :
    overallEffect (groupMarginal Y) φ ψ =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, overallEffect (fun s ↦ indivMarginal Y s i) φ ψ := by
  simp only [overallEffect, groupMarginal, sum_sub_distrib, mul_sub]

/-- Individual level decomposition of the overall effect:
`OE_i(φ, ψ) = IE_i(φ, ψ) - p_i(φ) DE_i(φ) + p_i(ψ) DE_i(ψ)`, where `p_i(ψ)` is the probability
that `i` is treated under `ψ`. The underlying mixture identity `indivMarginal_eq` holds for any
strategies; positivity is assumed so that the direct and indirect effects are genuine contrasts
of conditional means, and is not used in the proof. -/
theorem indivOverallEffect_eq (Y : (ι → Bool) → ι → ℝ) (i : ι) (φ ψ : AllocationStrategy ι)
    (_hφ : φ.Positive) (_hψ : ψ.Positive) :
    overallEffect (fun s ↦ indivMarginal Y s i) φ ψ =
      indirectEffect (fun t s ↦ indivAvg Y s i t) φ ψ -
        φ.treatProb i true * directEffect (fun t s ↦ indivAvg Y s i t) φ +
        ψ.treatProb i true * directEffect (fun t s ↦ indivAvg Y s i t) ψ := by
  refine overallEffect_eq_of_mixture _ _ (fun s ↦ s.treatProb i true) (fun s ↦ ?_) φ ψ
  rw [indivMarginal_eq, ← s.treatProb_false_add_true i]
  ring

/-- If every individual of the group is treated with the same probability `p s` under each
strategy `s` (as under complete randomization of a fixed number), the marginal group average is
the mixture `ȳ(s) = (1 - p s) ȳ(0; s) + p s ȳ(1; s)`. This is a probability weighted identity:
it holds for any value of an undefined conditional average and for an empty group. -/
theorem groupMarginal_eq_of_treatProb (Y : (ι → Bool) → ι → ℝ) (s : AllocationStrategy ι)
    (p : ℝ) (hp : ∀ i, s.treatProb i true = p) :
    groupMarginal Y s = (1 - p) * groupAvg Y s false + p * groupAvg Y s true := by
  have h0 : ∀ i, s.treatProb i false = 1 - p := fun i ↦ by
    rw [← hp i, ← s.treatProb_false_add_true i]
    ring
  simp only [groupMarginal, groupAvg, indivMarginal_eq, h0, hp, sum_add_distrib, ← mul_sum]
  ring

/-- Group level decomposition of the overall effect in full generality, with unit specific
treatment probabilities `p_i(φ)`, `p_i(ψ)`:
`OE(φ, ψ) = IE(φ, ψ) - n⁻¹ ∑_i p_i(φ) DE_i(φ) + n⁻¹ ∑_i p_i(ψ) DE_i(ψ)`, for a nonempty group
and positive strategies. -/
theorem groupOverallEffect_eq_sum [Nonempty ι] (Y : (ι → Bool) → ι → ℝ)
    (φ ψ : AllocationStrategy ι) (hφ : φ.Positive) (hψ : ψ.Positive) :
    overallEffect (groupMarginal Y) φ ψ =
      indirectEffect (fun t s ↦ groupAvg Y s t) φ ψ -
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ i, φ.treatProb i true * directEffect (fun t s ↦ indivAvg Y s i t) φ +
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ i, ψ.treatProb i true * directEffect (fun t s ↦ indivAvg Y s i t) ψ := by
  rw [groupOverallEffect_eq_average, groupIndirectEffect_eq_average Y φ ψ hφ hψ]
  simp only [fun i ↦ indivOverallEffect_eq Y i φ ψ hφ hψ, sum_add_distrib, sum_sub_distrib]
  ring

/-- Group level decomposition of the overall effect,
`OE(φ, ψ) = IE(φ, ψ) - p_φ DE(φ) + p_ψ DE(ψ)`, under the assumption that each strategy treats
every individual with the same probability: the special case of `groupOverallEffect_eq_sum`
in which all `p_i` agree, proved from the mixture identity. Nonemptiness and positivity are
assumed so that the averages and effects are meaningful; they are not used in the proof. -/
theorem groupOverallEffect_eq [Nonempty ι] (Y : (ι → Bool) → ι → ℝ)
    (φ ψ : AllocationStrategy ι) (_hφpos : φ.Positive) (_hψpos : ψ.Positive)
    (pφ pψ : ℝ) (hφ : ∀ i, φ.treatProb i true = pφ) (hψ : ∀ i, ψ.treatProb i true = pψ) :
    overallEffect (groupMarginal Y) φ ψ =
      indirectEffect (fun t s ↦ groupAvg Y s t) φ ψ -
        pφ * directEffect (fun t s ↦ groupAvg Y s t) φ +
        pψ * directEffect (fun t s ↦ groupAvg Y s t) ψ := by
  simp only [overallEffect, indirectEffect, directEffect,
    groupMarginal_eq_of_treatProb Y φ pφ hφ, groupMarginal_eq_of_treatProb Y ψ pψ hψ]
  ring

/-! ### Reduction to the classical case -/

/-- Reduction to the classical case: under no interference, if `i` receives both treatments with
positive probability, the individual direct effect is `y0 i - y1 i` (control minus treatment). -/
theorem NoInterference.directEffect_eq {Y : (ι → Bool) → ι → ℝ} (h : NoInterference Y)
    (ψ : AllocationStrategy ι) (i : ι) (h0 : 0 < ψ.treatProb i false)
    (h1 : 0 < ψ.treatProb i true) :
    directEffect (fun t s ↦ indivAvg Y s i t) ψ = y0 Y i - y1 Y i := by
  rw [directEffect, h.indivAvg_eq ψ i false h0, h.indivAvg_eq ψ i true h1, y0, y1]

/-- Reduction to the classical case: under no interference and positivity, the group direct
effect is `n⁻¹ ∑_i (y0 i - y1 i)`, minus the finite population average treatment effect. -/
theorem NoInterference.groupDirectEffect_eq [Nonempty ι] {Y : (ι → Bool) → ι → ℝ}
    (h : NoInterference Y) (ψ : AllocationStrategy ι) (hψ : ψ.Positive) :
    directEffect (fun t s ↦ groupAvg Y s t) ψ =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, (y0 Y i - y1 Y i) := by
  rw [groupDirectEffect_eq_average Y ψ hψ]
  simp only [fun i ↦ h.directEffect_eq ψ i (hψ i false) (hψ i true)]

/-- Reduction to the classical case: under no interference and positivity of both strategies,
the group indirect effect vanishes. -/
theorem NoInterference.groupIndirectEffect_eq_zero [Nonempty ι] {Y : (ι → Bool) → ι → ℝ}
    (h : NoInterference Y) (φ ψ : AllocationStrategy ι) (hφ : φ.Positive) (hψ : ψ.Positive) :
    indirectEffect (fun t s ↦ groupAvg Y s t) φ ψ = 0 := by
  rw [groupIndirectEffect_eq_average Y φ ψ hφ hψ]
  simp [fun i ↦ h.indirectEffect_eq_zero i φ ψ (hφ i false) (hψ i false)]

section Population

variable {G : Type*} [Fintype G] {κ : G → Type*} [∀ g, Fintype (κ g)] [∀ g, DecidableEq (κ g)]

/-- Population level: `TE(φ, ψ) = DE(ψ) + IE(φ, ψ)` for the population averages. The identity
is algebraic; nonemptiness and positivity are assumed so that every average is meaningful, and
are not used in the proof. -/
theorem popTotalEffect_eq [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (φ ψ : (g : G) → AllocationStrategy (κ g))
    (_hφ : ∀ g, (φ g).Positive) (_hψ : ∀ g, (ψ g).Positive) :
    totalEffect (fun t s ↦ popAvg Y s t) φ ψ =
      directEffect (fun t s ↦ popAvg Y s t) ψ +
        indirectEffect (fun t s ↦ popAvg Y s t) φ ψ :=
  totalEffect_eq_directEffect_add_indirectEffect _ φ ψ

/-- The population direct effect is the average of the group direct effects (nonempty groups,
positive strategies; these hypotheses are not used in the proof). -/
theorem popDirectEffect_eq_average [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (ψ : (g : G) → AllocationStrategy (κ g))
    (_hψ : ∀ g, (ψ g).Positive) :
    directEffect (fun t s ↦ popAvg Y s t) ψ =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ g, directEffect (fun t s ↦ groupAvg (Y g) s t) (ψ g) := by
  simp only [directEffect, popAvg, sum_sub_distrib, mul_sub]

/-- The population indirect effect is the average of the group indirect effects (nonempty groups,
positive strategies; these hypotheses are not used in the proof). -/
theorem popIndirectEffect_eq_average [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (φ ψ : (g : G) → AllocationStrategy (κ g))
    (_hφ : ∀ g, (φ g).Positive) (_hψ : ∀ g, (ψ g).Positive) :
    indirectEffect (fun t s ↦ popAvg Y s t) φ ψ =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ g, indirectEffect (fun t s ↦ groupAvg (Y g) s t) (φ g) (ψ g) := by
  simp only [indirectEffect, popAvg, sum_sub_distrib, mul_sub]

/-- The population total effect is the average of the group total effects (nonempty groups,
positive strategies; these hypotheses are not used in the proof). -/
theorem popTotalEffect_eq_average [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (φ ψ : (g : G) → AllocationStrategy (κ g))
    (_hφ : ∀ g, (φ g).Positive) (_hψ : ∀ g, (ψ g).Positive) :
    totalEffect (fun t s ↦ popAvg Y s t) φ ψ =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ g, totalEffect (fun t s ↦ groupAvg (Y g) s t) (φ g) (ψ g) := by
  simp only [totalEffect, popAvg, sum_sub_distrib, mul_sub]

/-- The population overall effect is the average of the group overall effects (nonempty
groups). -/
theorem popOverallEffect_eq_average [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (φ ψ : (g : G) → AllocationStrategy (κ g)) :
    overallEffect (popMarginal Y) φ ψ =
      (Fintype.card G : ℝ)⁻¹ * ∑ g, overallEffect (groupMarginal (Y g)) (φ g) (ψ g) := by
  simp only [overallEffect, popMarginal, sum_sub_distrib, mul_sub]

/-- Population level decomposition of the overall effect in full generality, with unit specific
treatment probabilities: `OE(φ, ψ)` equals
`IE(φ, ψ) - N⁻¹ ∑_g n_g⁻¹ ∑_i p_gi(φ_g) DE_gi(φ_g) + N⁻¹ ∑_g n_g⁻¹ ∑_i p_gi(ψ_g) DE_gi(ψ_g)`,
the equal weight average over groups of `groupOverallEffect_eq_sum`. -/
theorem popOverallEffect_eq_sum [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (φ ψ : (g : G) → AllocationStrategy (κ g))
    (hφ : ∀ g, (φ g).Positive) (hψ : ∀ g, (ψ g).Positive) :
    overallEffect (popMarginal Y) φ ψ =
      indirectEffect (fun t s ↦ popAvg Y s t) φ ψ -
        (Fintype.card G : ℝ)⁻¹ * ∑ g, (Fintype.card (κ g) : ℝ)⁻¹ *
          ∑ i, (φ g).treatProb i true * directEffect (fun t s ↦ indivAvg (Y g) s i t) (φ g) +
        (Fintype.card G : ℝ)⁻¹ * ∑ g, (Fintype.card (κ g) : ℝ)⁻¹ *
          ∑ i, (ψ g).treatProb i true * directEffect (fun t s ↦ indivAvg (Y g) s i t) (ψ g) := by
  rw [popOverallEffect_eq_average, popIndirectEffect_eq_average Y φ ψ hφ hψ]
  simp only [fun g ↦ groupOverallEffect_eq_sum (Y g) (φ g) (ψ g) (hφ g) (hψ g),
    sum_add_distrib, sum_sub_distrib]
  ring

/-- Population level decomposition of the overall effect with group specific treatment
probabilities: if strategy `φ g` treats every member of group `g` with probability `pφ g` and
likewise `ψ g` with `pψ g`, then `OE(φ, ψ)` is the average over groups of
`IE_g(φ_g, ψ_g) - pφ g DE_g(φ_g) + pψ g DE_g(ψ_g)`. -/
theorem popOverallEffect_eq_of_groupTreatProb [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (φ ψ : (g : G) → AllocationStrategy (κ g))
    (hφpos : ∀ g, (φ g).Positive) (hψpos : ∀ g, (ψ g).Positive) (pφ pψ : G → ℝ)
    (hφ : ∀ g i, (φ g).treatProb i true = pφ g) (hψ : ∀ g i, (ψ g).treatProb i true = pψ g) :
    overallEffect (popMarginal Y) φ ψ =
      (Fintype.card G : ℝ)⁻¹ * ∑ g,
        (indirectEffect (fun t s ↦ groupAvg (Y g) s t) (φ g) (ψ g) -
          pφ g * directEffect (fun t s ↦ groupAvg (Y g) s t) (φ g) +
          pψ g * directEffect (fun t s ↦ groupAvg (Y g) s t) (ψ g)) := by
  rw [popOverallEffect_eq_average]
  congr 1
  exact sum_congr rfl fun g _ ↦
    groupOverallEffect_eq (Y g) (φ g) (ψ g) (hφpos g) (hψpos g) _ _ (hφ g) (hψ g)

/-- Population level decomposition of the overall effect,
`OE(φ, ψ) = IE(φ, ψ) - p_φ DE(φ) + p_ψ DE(ψ)`, under the assumption that each of the two
strategy families treats every individual of every group with the same probability: the
special case of `popOverallEffect_eq_of_groupTreatProb` with probabilities common to all
groups. Nonemptiness and positivity are assumed so that every average is meaningful; they are
not used in the proof. -/
theorem popOverallEffect_eq [Nonempty G] [∀ g, Nonempty (κ g)]
    (Y : (g : G) → (κ g → Bool) → κ g → ℝ) (φ ψ : (g : G) → AllocationStrategy (κ g))
    (_hφpos : ∀ g, (φ g).Positive) (_hψpos : ∀ g, (ψ g).Positive) (pφ pψ : ℝ)
    (hφ : ∀ g i, (φ g).treatProb i true = pφ) (hψ : ∀ g i, (ψ g).treatProb i true = pψ) :
    overallEffect (popMarginal Y) φ ψ =
      indirectEffect (fun t s ↦ popAvg Y s t) φ ψ -
        pφ * directEffect (fun t s ↦ popAvg Y s t) φ +
        pψ * directEffect (fun t s ↦ popAvg Y s t) ψ := by
  have hmix : ∀ (s : (g : G) → AllocationStrategy (κ g)) (p : ℝ),
      (∀ g i, (s g).treatProb i true = p) →
        popMarginal Y s = (1 - p) * popAvg Y s false + p * popAvg Y s true := by
    intro s p hp
    simp only [popMarginal, popAvg, fun g ↦ groupMarginal_eq_of_treatProb (Y g) (s g) p (hp g),
      sum_add_distrib, ← mul_sum]
    ring
  simp only [overallEffect, indirectEffect, directEffect, hmix φ pφ hφ, hmix ψ pψ hψ]
  ring

/-- Reduction to the classical case at the population level: if every group satisfies no
interference and every strategy is positive, the population indirect effect vanishes. -/
theorem NoInterference.popIndirectEffect_eq_zero [Nonempty G] [∀ g, Nonempty (κ g)]
    {Y : (g : G) → (κ g → Bool) → κ g → ℝ} (h : ∀ g, NoInterference (Y g))
    (φ ψ : (g : G) → AllocationStrategy (κ g)) (hφ : ∀ g, (φ g).Positive)
    (hψ : ∀ g, (ψ g).Positive) :
    indirectEffect (fun t s ↦ popAvg Y s t) φ ψ = 0 := by
  rw [popIndirectEffect_eq_average Y φ ψ hφ hψ]
  simp [fun g ↦ (h g).groupIndirectEffect_eq_zero (φ g) (ψ g) (hφ g) (hψ g)]

/-- Reduction to the classical case at the population level: if every group satisfies no
interference and every strategy is positive, the population direct effect is the average over
groups of minus the finite population average treatment effect of each group,
`N⁻¹ ∑_g n_g⁻¹ ∑_i (y0 i - y1 i)`. -/
theorem NoInterference.popDirectEffect_eq [Nonempty G] [∀ g, Nonempty (κ g)]
    {Y : (g : G) → (κ g → Bool) → κ g → ℝ} (h : ∀ g, NoInterference (Y g))
    (ψ : (g : G) → AllocationStrategy (κ g)) (hψ : ∀ g, (ψ g).Positive) :
    directEffect (fun t s ↦ popAvg Y s t) ψ =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ g, (Fintype.card (κ g) : ℝ)⁻¹ * ∑ i, (y0 (Y g) i - y1 (Y g) i) := by
  rw [popDirectEffect_eq_average Y ψ hψ]
  simp only [fun g ↦ (h g).groupDirectEffect_eq (ψ g) (hψ g)]

end Population

end Interference

end CausalInference
