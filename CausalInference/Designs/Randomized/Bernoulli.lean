/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.FinitePopulation

/-!
# The Bernoulli design

Each unit is treated by an independent coin flip with probability `p`. The probability of an
assignment `a` is `∏_i (p if a i else 1 - p)`. We show that each unit is treated with
probability `p` and that the Horvitz-Thompson estimator is unbiased for the finite-population
average treatment effect when `0 < p < 1`. Source: Imbens and Rubin (2015), *Causal Inference for
Statistics, Social, and Biomedical Sciences*.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `bernoulliWeight`: the probability of an assignment under independent coin
  flips.
* `bernoulliDesign`: the Bernoulli design as a `Design`.

## Main results

* `bernoulliDesign_inclusionProb`: each unit is treated with probability `p`.
* `bernoulli_htEstimator_unbiased`: the Horvitz-Thompson estimator is unbiased.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability of the assignment `a` when each unit is independently treated with
probability `p`: `∏_i (p if a i else 1 - p)`. -/
def bernoulliWeight (p : ℝ) (a : ι → Bool) : ℝ := ∏ i, if a i then p else 1 - p

/-- The Bernoulli design with treatment probability `p`, `0 ≤ p ≤ 1`: every assignment is in the
support and has probability `bernoulliWeight p`. -/
def bernoulliDesign (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Design ι where
  support := univ
  weight := bernoulliWeight p
  weight_nonneg := fun a _ =>
    prod_nonneg fun i _ => by split_ifs <;> linarith
  sum_weight := by
    unfold bernoulliWeight
    rw [← Fintype.prod_sum (fun (_ : ι) (b : Bool) => if b then p else 1 - p)]
    simp

/-- Under the Bernoulli design every unit is treated with probability `p`. -/
theorem bernoulliDesign_inclusionProb (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ι) :
    (bernoulliDesign p hp0 hp1).inclusionProb i = p := by
  let g : ι → Bool → ℝ := fun j b =>
    (if b then p else 1 - p) * (if j = i then (if b then 1 else 0) else 1)
  have hprod : ∀ a : ι → Bool,
      bernoulliWeight p a * treatInd a i = ∏ j, g j (a j) := by
    intro a
    simp only [g, prod_mul_distrib, bernoulliWeight, prod_ite_eq', mem_univ, ite_true, treatInd]
  have hsum : ∏ j, ∑ b, g j b = p := by
    have : ∀ j, ∑ b, g j b = if j = i then p else 1 := by
      intro j
      by_cases hj : j = i <;> simp [g, hj]
    rw [prod_congr rfl fun j _ => this j]
    simp
  simp only [Design.inclusionProb, Design.expect, bernoulliDesign, hprod]
  rw [← hsum, Fintype.prod_sum]

/-- **Unbiasedness under the Bernoulli design.** If each unit is treated independently with
probability `p`, `0 < p < 1`, then the Horvitz-Thompson estimator
`(1/N) Σ_i (A_i Y_i / p - (1 - A_i) Y_i / (1 - p))` is unbiased for the average treatment
effect. -/
theorem bernoulli_htEstimator_unbiased (po : PotentialOutcomes ι) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    (bernoulliDesign p hp0.le hp1.le).expect (po.htEstimator p) = po.ate :=
  po.htEstimator_unbiased _ p hp0 hp1 (bernoulliDesign_inclusionProb p hp0.le hp1.le)

end CausalInference.Randomized
