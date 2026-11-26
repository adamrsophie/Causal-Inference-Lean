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
  (the latter with Neyman's `N - 1` denominator).
* `PotentialOutcomes.ate`: the finite-population average treatment effect.
* `PotentialOutcomes.observed`: the observed outcome vector under an assignment.
* `Design`: a design, that is, a finite set of assignments carrying nonnegative
  weights summing to one. Bernoulli, complete, stratified, paired, and cluster designs are all
  instances.
* `Design.expect`, `Design.prob`,
  `Design.variance`: expectation, probability, and variance over a design.
* `Design.uniform`: the uniform design on a finite nonempty set of assignments.
* `Design.inclusionProb`, `Design.pairInclusionProb`.
* `PotentialOutcomes.htEstimator`: the Horvitz-Thompson estimator of the
  average treatment effect with a constant treatment probability.

## Main results

* `PotentialOutcomes.htEstimator_unbiased`: if every unit is treated with
  probability `p` under a design, `0 < p < 1`, then the Horvitz-Thompson estimator is unbiased
  for the average treatment effect.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι : Type*}

/-! ### Finite-population quantities -/

section Population

variable [Fintype ι]

/-- The finite-population mean `(1/N) Σ_i f i` of a vector `f` over the units. -/
noncomputable def popMean (f : ι → ℝ) : ℝ := (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i

/-- The finite-population variance `(1/(N - 1)) Σ_i (f i - f̄)^2`, with Neyman's `N - 1`
denominator. -/
noncomputable def popVar (f : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) - 1)⁻¹ * ∑ i, (f i - popMean f) ^ 2

/-- The finite-population variance is nonnegative when the population has at least two units.
-/
theorem popVar_nonneg (f : ι → ℝ) (hN : 1 < Fintype.card ι) : 0 ≤ popVar f := by
  unfold popVar
  have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have h1 : 0 ≤ ((Fintype.card ι : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  exact mul_nonneg h1 (sum_nonneg fun i _ => sq_nonneg _)

/-- A constant vector has zero finite-population variance. -/
theorem popVar_const (c : ℝ) (f : ι → ℝ) (hf : ∀ i, f i = c) (hN : 0 < Fintype.card ι) :
    popVar f = 0 := by
  have hm : popMean f = c := by
    have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [popMean, hf, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  simp [popVar, hm, hf]

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
The weight of an assignment is its probability of being drawn. -/
structure Design (ι : Type*) where
  /-- The assignments that can be drawn. -/
  support : Finset (ι → Bool)
  /-- The probability of each assignment. -/
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

end Design

/-! ### The Horvitz-Thompson estimator -/

namespace PotentialOutcomes

variable [Fintype ι]

/-- The Horvitz-Thompson estimator of the average treatment effect for a design that treats
every unit with probability `p`: `(1/N) Σ_i (A_i Y_i / p - (1 - A_i) Y_i / (1 - p))`, where
`A_i` is the treatment indicator and `Y_i` the observed outcome. -/
noncomputable def htEstimator (po : PotentialOutcomes ι) (p : ℝ) (a : ι → Bool) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ i, (treatInd a i * po.observed a i / p - (1 - treatInd a i) * po.observed a i / (1 - p))

/-- The Horvitz-Thompson estimator rewritten with potential outcomes: the treatment indicator
selects `y1` and its complement selects `y0`. -/
theorem htEstimator_eq (po : PotentialOutcomes ι) (p : ℝ) (a : ι → Bool) :
    po.htEstimator p a = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (treatInd a i * po.y1 i / p - (1 - treatInd a i) * po.y0 i / (1 - p)) := by
  unfold htEstimator
  congr 1
  refine sum_congr rfl fun i _ => ?_
  unfold treatInd observed
  by_cases h : a i <;> simp [h]

/-- **Unbiasedness of the Horvitz-Thompson estimator.** If a design treats every unit with the
same probability `p`, `0 < p < 1`, then the expectation of the Horvitz-Thompson estimator over
the design equals the finite-population average treatment effect. -/
theorem htEstimator_unbiased (po : PotentialOutcomes ι) (d : Design ι) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (hπ : ∀ i, d.inclusionProb i = p) :
    d.expect (po.htEstimator p) = po.ate := by
  have hp1' : 1 - p ≠ 0 := by linarith
  rw [show po.htEstimator p = _ from funext (htEstimator_eq po p), d.expect_mul_left,
    d.expect_sum, ate, popMean]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have hi := hπ i
  unfold Design.inclusionProb at hi
  have e1 : d.expect (fun a => treatInd a i * po.y1 i / p) = po.y1 i := by
    rw [d.expect_congr (g := fun a => po.y1 i / p * treatInd a i) (fun _ _ => by ring),
      d.expect_mul_left, hi]
    field_simp
  have e0 : d.expect (fun a => (1 - treatInd a i) * po.y0 i / (1 - p)) = po.y0 i := by
    have := d.expect_mul_left (po.y0 i / (1 - p)) (fun a => 1 - treatInd a i)
    rw [d.expect_sub, d.expect_const, hi] at this
    rw [d.expect_congr (g := fun a => po.y0 i / (1 - p) * (1 - treatInd a i))
      (fun _ _ => by ring), this]
    field_simp
  rw [d.expect_sub, e1, e0, unitEffect]

end PotentialOutcomes

end CausalInference.Randomized
