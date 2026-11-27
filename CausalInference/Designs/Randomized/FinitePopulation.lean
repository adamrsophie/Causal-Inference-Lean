/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Finite populations, assignments, and randomized designs

The design-based (randomization) framework of Neyman (1923) and Fisher (1935), as presented in
Imbens and Rubin (2015), *Causal Inference for Statistics, Social, and Biomedical Sciences*.
A finite population `ι` carries fixed potential outcomes `y1 y0 : ι → ℝ`; the only randomness
is in the treatment assignment `a : ι → Bool`.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `PotentialOutcomes`: the pair of fixed potential outcome vectors.
* `popMean`, `popVar`: finite-population mean and variance
  (the latter with Neyman's `N - 1` denominator); the mean is interpreted only for `0 < N` and
  the variance only for `1 < N`.
* `PotentialOutcomes.ate`: the finite-population average treatment effect.
* `PotentialOutcomes.observed`: the observed outcome vector under an assignment.
* `Design`: a design, that is, a finite summation set of assignments (`support`) carrying
  nonnegative weights summing to one. Bernoulli, complete, stratified, paired, and cluster
  designs are all instances.
* `Design.mass`: the probability of an arbitrary assignment (its weight on the support and `0`
  off it).
* `Design.expect`, `Design.prob`,
  `Design.variance`: expectation, probability, and variance over a design.
* `Design.uniform`: the uniform design on a finite nonempty set of assignments.
* `Design.inclusionProb`, `Design.pairInclusionProb`.
* `PotentialOutcomes.htEstimatorGen`: the Horvitz-Thompson estimator of the average treatment
  effect with unit-specific inclusion probabilities `π i`.
* `PotentialOutcomes.htEstimator`: its special case with a constant treatment probability.

## Main results

* `Design.prob_eq_mass`, `Design.sum_mass`, `Design.expect_eq_sum_mass`: the mass is the
  probability of each assignment, the masses sum to one, and an expectation is the sum over all
  assignments against the mass.
* Basic design lemmas: `Design.expect_nonneg`, `Design.prob_le_one`, `Design.prob_compl`,
  `Design.variance_nonneg`, `Design.variance_eq`, `Design.variance_congr`, and the population
  lemmas `popMean_add`, `popMean_sub`, `popMean_const`, `popMean_smul`.
* `Design.variance_of_linear`: for any design, the variance of a statistic that is affine in
  the treatment indicators, `c + Σ_i A_i w_i`, equals `Σ_i Σ_j (π_ij - π_i π_j) w_i w_j`.
* `PotentialOutcomes.htEstimatorGen_unbiased`: in a nonempty population, if unit `i` is treated
  with probability `π i`, `0 < π i < 1`, then the Horvitz-Thompson estimator is unbiased for
  the average treatment effect.
* `PotentialOutcomes.htEstimator_unbiased`: the constant case `π i = p`.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι : Type*}

/-! ### Finite-population quantities -/

section Population

variable [Fintype ι]

/-- The finite-population mean `(1/N) Σ_i f i` of a vector `f` over the units. It is a mean
only for a nonempty population, `0 < N`; for `N = 0` Lean's convention `0⁻¹ = 0` returns `0`,
and every result interpreting `popMean` as a mean assumes `0 < N` (or `Nonempty ι`). -/
noncomputable def popMean (f : ι → ℝ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i

/-- The finite-population variance `(1/(N - 1)) Σ_i (f i - f̄)^2`, with Neyman's `N - 1`
denominator. It is meaningful only for `1 < N`; for `N = 1` Lean's convention `0⁻¹ = 0`
returns `0`, and every result interpreting `popVar` as a variance assumes `1 < N`. -/
noncomputable def popVar (f : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) - 1)⁻¹ * ∑ i, (f i - popMean f) ^ 2

/-- The finite-population variance is nonnegative when the population has at least two units.
-/
theorem popVar_nonneg (f : ι → ℝ) (hN : 1 < Fintype.card ι) : 0 ≤ popVar f := by
  unfold popVar
  have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have h1 : 0 ≤ ((Fintype.card ι : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  exact mul_nonneg h1 (sum_nonneg fun i _ => sq_nonneg _)

/-- A constant vector has zero finite-population variance (in a population of at least two
units, where the variance is defined). -/
theorem popVar_const (c : ℝ) (f : ι → ℝ) (hf : ∀ i, f i = c) (hN : 1 < Fintype.card ι) :
    popVar f = 0 := by
  have hm : popMean f = c := by
    have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (show 0 < Fintype.card ι by omega).ne'
    simp only [popMean, hf, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  simp [popVar, hm, hf]

/-- The population mean is additive. -/
theorem popMean_add (f g : ι → ℝ) : popMean (fun i => f i + g i) = popMean f + popMean g := by
  simp [popMean, sum_add_distrib, mul_add]

/-- The population mean commutes with subtraction. -/
theorem popMean_sub (f g : ι → ℝ) : popMean (fun i => f i - g i) = popMean f - popMean g := by
  simp [popMean, sum_sub_distrib, mul_sub]

/-- The population mean of a constant vector is that constant (in a nonempty population). -/
theorem popMean_const [Nonempty ι] (c : ℝ) : popMean (fun _ : ι => c) = c := by
  have : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [popMean, sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- The population mean is homogeneous: `mean (c f) = c mean f`. -/
theorem popMean_smul (c : ℝ) (f : ι → ℝ) : popMean (fun i => c * f i) = c * popMean f := by
  simp only [popMean, ← mul_sum]
  ring

end Population

/-- Fixed potential outcomes of a finite population: `y1 i` under treatment and `y0 i` under
control. -/
structure PotentialOutcomes (ι : Type*) where
  /-- The potential outcome of each unit under treatment. -/
  y1 : ι → ℝ
  /-- The potential outcome of each unit under control. -/
  y0 : ι → ℝ

namespace PotentialOutcomes

/-- The unit-level treatment effect `y1 i - y0 i`. -/
def unitEffect (po : PotentialOutcomes ι) (i : ι) : ℝ := po.y1 i - po.y0 i

/-- The observed outcome of each unit under the assignment `a`: `y1 i` if unit `i` is treated
and `y0 i` otherwise. -/
def observed (po : PotentialOutcomes ι) (a : ι → Bool) (i : ι) : ℝ :=
  if a i then po.y1 i else po.y0 i

variable [Fintype ι]

/-- The finite-population average treatment effect `τ = (1/N) Σ_i (y1 i - y0 i)`. -/
noncomputable def ate (po : PotentialOutcomes ι) : ℝ := popMean po.unitEffect

/-- Neyman's `S1²`: the finite-population variance of the treated potential outcomes. -/
noncomputable def varTreated (po : PotentialOutcomes ι) : ℝ := popVar po.y1

/-- Neyman's `S0²`: the finite-population variance of the control potential outcomes. -/
noncomputable def varControl (po : PotentialOutcomes ι) : ℝ := popVar po.y0

/-- Neyman's `S_τ²`: the finite-population variance of the unit-level treatment effects. -/
noncomputable def varEffect (po : PotentialOutcomes ι) : ℝ := popVar po.unitEffect

end PotentialOutcomes

/-! ### Designs -/

/-- The `0`/`1` treatment indicator of unit `i` under the assignment `a`. -/
def treatInd (a : ι → Bool) (i : ι) : ℝ := if a i then 1 else 0

/-- A randomized design: a finite set of assignments with nonnegative weights summing to one.
The set `support` is the summation set of every expectation; an assignment outside it is never
drawn. The weight of an assignment in `support` is its probability of being drawn; the value of
`weight` outside `support` carries no meaning (use `Design.mass` for the probability of an
arbitrary assignment). Assignments in `support` may have weight zero. -/
structure Design (ι : Type*) where
  /-- The summation set: every assignment that can be drawn lies in it. -/
  support : Finset (ι → Bool)
  /-- The probability of each assignment in `support`; meaningless outside `support`. -/
  weight : (ι → Bool) → ℝ
  weight_nonneg : ∀ a ∈ support, 0 ≤ weight a
  sum_weight : ∑ a ∈ support, weight a = 1

namespace Design

/-- The expectation `Σ_a w(a) f(a)` of a function of the assignment over a design. -/
def expect (d : Design ι) (f : (ι → Bool) → ℝ) : ℝ := ∑ a ∈ d.support, d.weight a * f a

/-- The probability that the drawn assignment satisfies `P`. -/
def prob (d : Design ι) (P : (ι → Bool) → Prop) [DecidablePred P] : ℝ :=
  d.expect fun a => if P a then 1 else 0

/-- The variance `E[(f - E f)^2]` of a function of the assignment over a design. -/
def variance (d : Design ι) (f : (ι → Bool) → ℝ) : ℝ :=
  d.expect fun a => (f a - d.expect f) ^ 2

/-- The probability `π_i` that unit `i` is treated. -/
def inclusionProb (d : Design ι) (i : ι) : ℝ := d.expect fun a => treatInd a i

/-- The probability `π_ij` that units `i` and `j` are both treated. -/
def pairInclusionProb (d : Design ι) (i j : ι) : ℝ :=
  d.expect fun a => treatInd a i * treatInd a j

theorem expect_const (d : Design ι) (c : ℝ) : d.expect (fun _ => c) = c := by
  simp [expect, ← sum_mul, d.sum_weight]

theorem expect_add (d : Design ι) (f g : (ι → Bool) → ℝ) :
    d.expect (fun a => f a + g a) = d.expect f + d.expect g := by
  simp [expect, mul_add, sum_add_distrib]

theorem expect_sub (d : Design ι) (f g : (ι → Bool) → ℝ) :
    d.expect (fun a => f a - g a) = d.expect f - d.expect g := by
  simp [expect, mul_sub, sum_sub_distrib]

theorem expect_mul_left (d : Design ι) (c : ℝ) (f : (ι → Bool) → ℝ) :
    d.expect (fun a => c * f a) = c * d.expect f := by
  simp [expect, mul_sum, mul_left_comm]

theorem expect_sum {κ : Type*} (d : Design ι) (s : Finset κ) (f : κ → (ι → Bool) → ℝ) :
    d.expect (fun a => ∑ k ∈ s, f k a) = ∑ k ∈ s, d.expect (f k) := by
  simp only [expect, mul_sum]
  exact sum_comm

theorem expect_congr (d : Design ι) {f g : (ι → Bool) → ℝ} (h : ∀ a ∈ d.support, f a = g a) :
    d.expect f = d.expect g :=
  sum_congr rfl fun a ha => by rw [h a ha]

theorem expect_mono (d : Design ι) {f g : (ι → Bool) → ℝ} (h : ∀ a ∈ d.support, f a ≤ g a) :
    d.expect f ≤ d.expect g :=
  sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (h a ha) (d.weight_nonneg a ha)

theorem prob_nonneg (d : Design ι) (P : (ι → Bool) → Prop) [DecidablePred P] :
    0 ≤ d.prob P := by
  have := d.expect_mono (f := fun _ => (0 : ℝ)) (g := fun a => if P a then 1 else 0)
    (fun a _ => by split_ifs <;> norm_num)
  rwa [expect_const] at this

/-- If `P` implies `Q` on the support, then `P` is at most as probable as `Q`. -/
theorem prob_mono (d : Design ι) {P Q : (ι → Bool) → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ a ∈ d.support, P a → Q a) : d.prob P ≤ d.prob Q := by
  refine d.expect_mono fun a ha => ?_
  by_cases hP : P a
  · simp [hP, h a ha hP]
  · by_cases hQ : Q a <;> simp [hP, hQ]

/-- Expectations of nonnegative functions are nonnegative. -/
theorem expect_nonneg (d : Design ι) {f : (ι → Bool) → ℝ} (h : ∀ a ∈ d.support, 0 ≤ f a) :
    0 ≤ d.expect f :=
  sum_nonneg fun a ha => mul_nonneg (d.weight_nonneg a ha) (h a ha)

/-- Probabilities are at most one. -/
theorem prob_le_one (d : Design ι) (P : (ι → Bool) → Prop) [DecidablePred P] :
    d.prob P ≤ 1 := by
  have := d.expect_mono (f := fun a => if P a then 1 else 0) (g := fun _ => (1 : ℝ))
    (fun a _ => by split_ifs <;> norm_num)
  rwa [expect_const] at this

/-- The probability of the complement of an event is one minus its probability. -/
theorem prob_compl (d : Design ι) (P : (ι → Bool) → Prop) [DecidablePred P] :
    d.prob (fun a => ¬ P a) = 1 - d.prob P := by
  have := d.expect_sub (fun _ => (1 : ℝ)) (fun a => if P a then 1 else 0)
  rw [expect_const] at this
  rw [prob, prob, ← this]
  exact d.expect_congr fun a _ => by by_cases h : P a <;> simp [h]

/-- The variance of a function of the assignment is nonnegative. -/
theorem variance_nonneg (d : Design ι) (f : (ι → Bool) → ℝ) : 0 ≤ d.variance f :=
  d.expect_nonneg fun _ _ => sq_nonneg _

/-- Functions that agree on the support have the same variance. -/
theorem variance_congr (d : Design ι) {f g : (ι → Bool) → ℝ}
    (h : ∀ a ∈ d.support, f a = g a) : d.variance f = d.variance g := by
  unfold variance
  rw [d.expect_congr h]
  exact d.expect_congr fun a ha => by rw [h a ha]

/-- The variance is the mean of the square minus the square of the mean. -/
theorem variance_eq (d : Design ι) (f : (ι → Bool) → ℝ) :
    d.variance f = d.expect (fun a => f a ^ 2) - d.expect f ^ 2 := by
  unfold variance
  rw [d.expect_congr (g := fun a => (f a ^ 2 - (2 * d.expect f) * f a) + d.expect f ^ 2)
    (fun _ _ => by ring), d.expect_add, d.expect_sub, d.expect_mul_left, d.expect_const]
  ring

/-- The variance is the expected squared deviation from any constant equal to the mean. -/
theorem variance_eq_of_expect (d : Design ι) (f : (ι → Bool) → ℝ) (c : ℝ) (hc : d.expect f = c) :
    d.variance f = d.expect fun a => (f a - c) ^ 2 := by
  rw [variance, hc]

/-- The uniform design on a finite nonempty set `S` of assignments: each assignment in `S` has
probability `1 / |S|`. -/
noncomputable def uniform (S : Finset (ι → Bool)) (hS : S.Nonempty) : Design ι where
  support := S
  weight := fun _ => (S.card : ℝ)⁻¹
  weight_nonneg := fun _ _ => by positivity
  sum_weight := by
    have : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    simp [this]

theorem uniform_expect (S : Finset (ι → Bool)) (hS : S.Nonempty) (f : (ι → Bool) → ℝ) :
    (uniform S hS).expect f = (S.card : ℝ)⁻¹ * ∑ a ∈ S, f a := by
  simp [expect, uniform, mul_sum]

/-- For any design, `π_ii = π_i`, since the treatment indicator is idempotent. -/
theorem pairInclusionProb_self (d : Design ι) (i : ι) :
    d.pairInclusionProb i i = d.inclusionProb i :=
  d.expect_congr fun a _ => by unfold treatInd; split_ifs <;> norm_num

/-! ### Assignment mass -/

section Mass

variable [Fintype ι]

/-- The probability mass of an arbitrary assignment: its weight if it lies in the support and
`0` otherwise. -/
def mass (d : Design ι) (a : ι → Bool) : ℝ := if a ∈ d.support then d.weight a else 0

theorem mass_nonneg (d : Design ι) (a : ι → Bool) : 0 ≤ d.mass a := by
  unfold mass
  split_ifs with h
  · exact d.weight_nonneg a h
  · exact le_rfl

theorem mass_of_mem (d : Design ι) {a : ι → Bool} (h : a ∈ d.support) :
    d.mass a = d.weight a := by simp [mass, h]

theorem mass_of_not_mem (d : Design ι) {a : ι → Bool} (h : a ∉ d.support) : d.mass a = 0 := by
  simp [mass, h]

/-- The probability that the drawn assignment equals `a` is the mass of `a`. -/
theorem prob_eq_mass (d : Design ι) (a : ι → Bool) : d.prob (· = a) = d.mass a := by
  simp [prob, expect, mass]

variable [DecidableEq ι]

/-- The expectation as a sum over all assignments against the mass. -/
theorem expect_eq_sum_mass (d : Design ι) (f : (ι → Bool) → ℝ) :
    d.expect f = ∑ a, d.mass a * f a := by
  simp only [expect, mass, ite_mul, zero_mul]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]

/-- The masses of all assignments sum to one. -/
theorem sum_mass (d : Design ι) : ∑ a, d.mass a = 1 := by
  have := d.expect_eq_sum_mass fun _ => 1
  simpa [d.expect_const] using this.symm

end Mass

/-- For any design, if a statistic equals `c + Σ_i A_i w_i` on the support, where `A_i` is the
treatment indicator, then its variance is `Σ_i Σ_j (π_ij - π_i π_j) w_i w_j`. -/
theorem variance_of_linear [Fintype ι] (d : Design ι) (f : (ι → Bool) → ℝ) (c : ℝ)
    (w : ι → ℝ) (hf : ∀ a ∈ d.support, f a = c + ∑ i, treatInd a i * w i) :
    d.variance f = ∑ i, ∑ j,
      (d.pairInclusionProb i j - d.inclusionProb i * d.inclusionProb j) * w i * w j := by
  have hE : d.expect f = c + ∑ i, d.inclusionProb i * w i := by
    rw [d.expect_congr hf, d.expect_add, d.expect_const, d.expect_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [d.expect_congr (g := fun a => w i * treatInd a i) (fun _ _ => mul_comm _ _),
      d.expect_mul_left, Design.inclusionProb, mul_comm]
  rw [d.variance_eq_of_expect f _ hE]
  have hdev : ∀ a ∈ d.support, (f a - (c + ∑ i, d.inclusionProb i * w i)) ^ 2 =
      ∑ i, ∑ j, ((treatInd a i - d.inclusionProb i) * w i) *
        ((treatInd a j - d.inclusionProb j) * w j) := by
    intro a ha
    rw [hf a ha, ← sum_mul_sum, sq]
    congr 1 <;> simp [sub_mul, sum_sub_distrib]
  rw [d.expect_congr hdev, d.expect_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [d.expect_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [d.expect_congr (g := fun a => w i * w j * (treatInd a i * treatInd a j) -
      (w i * w j * d.inclusionProb j) * treatInd a i -
      (w i * w j * d.inclusionProb i) * treatInd a j +
      w i * w j * d.inclusionProb i * d.inclusionProb j) (fun _ _ => by ring),
    d.expect_add, d.expect_sub, d.expect_sub, d.expect_mul_left, d.expect_mul_left,
    d.expect_mul_left, d.expect_const]
  simp only [Design.pairInclusionProb, Design.inclusionProb]
  ring

end Design

/-! ### The Horvitz-Thompson estimator -/

namespace PotentialOutcomes

variable [Fintype ι]

/-- The Horvitz-Thompson estimator of the average treatment effect with unit-specific
inclusion probabilities `π i`: `(1/N) Σ_i (A_i Y_i / π_i - (1 - A_i) Y_i / (1 - π_i))`, where
`A_i` is the treatment indicator and `Y_i` the observed outcome. -/
noncomputable def htEstimatorGen (po : PotentialOutcomes ι) (π : ι → ℝ) (a : ι → Bool) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i,
    (treatInd a i * po.observed a i / π i - (1 - treatInd a i) * po.observed a i / (1 - π i))

/-- The Horvitz-Thompson estimator of the average treatment effect for a design that treats
every unit with probability `p`: `(1/N) Σ_i (A_i Y_i / p - (1 - A_i) Y_i / (1 - p))`, where
`A_i` is the treatment indicator and `Y_i` the observed outcome. -/
noncomputable def htEstimator (po : PotentialOutcomes ι) (p : ℝ) (a : ι → Bool) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ i, (treatInd a i * po.observed a i / p - (1 - treatInd a i) * po.observed a i / (1 - p))

/-- The constant-probability estimator is the general one with `π i = p` for every unit. -/
theorem htEstimator_eq_htEstimatorGen (po : PotentialOutcomes ι) (p : ℝ) :
    po.htEstimator p = po.htEstimatorGen (fun _ => p) := rfl

/-- The general Horvitz-Thompson estimator rewritten with potential outcomes. -/
theorem htEstimatorGen_eq (po : PotentialOutcomes ι) (π : ι → ℝ) (a : ι → Bool) :
    po.htEstimatorGen π a = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (treatInd a i * po.y1 i / π i - (1 - treatInd a i) * po.y0 i / (1 - π i)) := by
  unfold htEstimatorGen
  congr 1
  refine sum_congr rfl fun i _ => ?_
  unfold treatInd observed
  by_cases h : a i <;> simp [h]

/-- The Horvitz-Thompson estimator rewritten with potential outcomes: the treatment indicator
selects `y1` and its complement selects `y0`. -/
theorem htEstimator_eq (po : PotentialOutcomes ι) (p : ℝ) (a : ι → Bool) :
    po.htEstimator p a = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (treatInd a i * po.y1 i / p - (1 - treatInd a i) * po.y0 i / (1 - p)) :=
  po.htEstimatorGen_eq (fun _ => p) a

/-- **Unbiasedness of the Horvitz-Thompson estimator, unit-specific probabilities.** In a
nonempty population, if a design treats unit `i` with probability `π i`, `0 < π i < 1`, then
the expectation of the Horvitz-Thompson estimator with weights `π` equals the
finite-population average treatment effect. -/
theorem htEstimatorGen_unbiased [Nonempty ι] (po : PotentialOutcomes ι) (d : Design ι)
    (π : ι → ℝ) (hπ0 : ∀ i, 0 < π i) (hπ1 : ∀ i, π i < 1)
    (hπ : ∀ i, d.inclusionProb i = π i) :
    d.expect (po.htEstimatorGen π) = po.ate := by
  rw [show po.htEstimatorGen π = _ from funext (htEstimatorGen_eq po π), d.expect_mul_left,
    d.expect_sum, ate, popMean]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have hp0 := (hπ0 i).ne'
  have hp1' : 1 - π i ≠ 0 := by linarith [hπ1 i]
  have hi := hπ i
  unfold Design.inclusionProb at hi
  have e1 : d.expect (fun a => treatInd a i * po.y1 i / π i) = po.y1 i := by
    rw [d.expect_congr (g := fun a => po.y1 i / π i * treatInd a i) (fun _ _ => by ring),
      d.expect_mul_left, hi]
    field_simp
  have e0 : d.expect (fun a => (1 - treatInd a i) * po.y0 i / (1 - π i)) = po.y0 i := by
    have := d.expect_mul_left (po.y0 i / (1 - π i)) (fun a => 1 - treatInd a i)
    rw [d.expect_sub, d.expect_const, hi] at this
    rw [d.expect_congr (g := fun a => po.y0 i / (1 - π i) * (1 - treatInd a i))
      (fun _ _ => by ring), this]
    field_simp
  rw [d.expect_sub, e1, e0, unitEffect]

/-- **Unbiasedness of the Horvitz-Thompson estimator.** In a nonempty population, if a design
treats every unit with the same probability `p`, `0 < p < 1`, then the expectation of the
Horvitz-Thompson estimator over the design equals the finite-population average treatment
effect. This is the constant case of `htEstimatorGen_unbiased`. -/
theorem htEstimator_unbiased [Nonempty ι] (po : PotentialOutcomes ι) (d : Design ι) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hπ : ∀ i, d.inclusionProb i = p) :
    d.expect (po.htEstimator p) = po.ate :=
  po.htEstimatorGen_unbiased d _ (fun _ => hp0) (fun _ => hp1) hπ

end PotentialOutcomes

end CausalInference.Randomized
