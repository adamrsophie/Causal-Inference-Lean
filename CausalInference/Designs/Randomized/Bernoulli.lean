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
assignment `a` is `∏_i (p if a i else 1 - p)`. We prove the finite-pattern product
law (independence of the flips), so that each unit is treated with probability `p` and two
distinct units with probability `p * p`; the Horvitz-Thompson estimator is unbiased for the
finite-population average treatment effect when `0 < p < 1`, and we compute its variance.
Source: Imbens and Rubin (2015), *Causal Inference for Statistics, Social, and Biomedical
Sciences*.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `bernoulliWeight`: the probability of an assignment under independent coin
  flips.
* `bernoulliDesign`: the Bernoulli design as a `Design`.

## Main results

* `bernoulliDesign_prob_pattern`: the probability that the units of a finite set receive given
  treatments is the product of the per-unit probabilities.
* `bernoulliDesign_inclusionProb`: each unit is treated with probability `p`.
* `bernoulliDesign_pairInclusionProb`: two distinct units are both treated with probability
  `p * p`.
* `bernoulli_htEstimator_unbiased`: the Horvitz-Thompson estimator is unbiased (nonempty
  population).
* `bernoulli_htEstimator_variance`: its variance is
  `N⁻² Σ_i p (1 - p) (y1 i / p + y0 i / (1 - p))^2`.
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

/-- **The finite-pattern product law.** Under the Bernoulli design, for any finite set `s` of
units and any target pattern `b`, the probability that every unit of `s` receives its target
treatment is `∏_{i ∈ s} (p if b i else 1 - p)`: the coin flips are independent. -/
theorem bernoulliDesign_prob_pattern (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset ι)
    (b : ι → Bool) :
    (bernoulliDesign p hp0 hp1).prob (fun a => ∀ i ∈ s, a i = b i) =
      ∏ i ∈ s, if b i then p else 1 - p := by
  let g : ι → Bool → ℝ := fun j c =>
    (if c then p else 1 - p) * (if j ∈ s then (if c = b j then 1 else 0) else 1)
  have hprod : ∀ a : ι → Bool, bernoulliWeight p a *
      (if ∀ i ∈ s, a i = b i then 1 else 0) = ∏ j, g j (a j) := by
    intro a
    simp only [g, prod_mul_distrib, bernoulliWeight]
    rw [prod_ite_mem, univ_inter, prod_boole]
    congr
  have hsum : ∏ j, ∑ c, g j c = ∏ i ∈ s, if b i then p else 1 - p := by
    have : ∀ j, ∑ c, g j c = if j ∈ s then (if b j then p else 1 - p) else 1 := by
      intro j
      by_cases hj : j ∈ s <;> cases hb : b j <;> simp [g, hj, hb]
    rw [prod_congr rfl fun j _ => this j, prod_ite_mem, univ_inter]
  simp only [Design.prob, Design.expect, bernoulliDesign, hprod]
  rw [← hsum, Fintype.prod_sum]

/-- Under the Bernoulli design two distinct units are both treated with probability `p * p`.
-/
theorem bernoulliDesign_pairInclusionProb (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {i j : ι}
    (hij : i ≠ j) : (bernoulliDesign p hp0 hp1).pairInclusionProb i j = p * p := by
  have h := bernoulliDesign_prob_pattern p hp0 hp1 {i, j} (fun _ => true)
  rw [prod_pair hij] at h
  simp only [ite_true] at h
  rw [← h]
  refine Design.expect_congr _ fun a _ => ?_
  by_cases hi : a i <;> by_cases hj : a j <;> simp [treatInd, hi, hj]

/-- **Unbiasedness under the Bernoulli design.** In a nonempty population, if each unit is
treated independently with probability `p`, `0 < p < 1`, then the Horvitz-Thompson estimator
`(1/N) Σ_i (A_i Y_i / p - (1 - A_i) Y_i / (1 - p))` is unbiased for the average treatment
effect. -/
theorem bernoulli_htEstimator_unbiased [Nonempty ι] (po : PotentialOutcomes ι) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    (bernoulliDesign p hp0.le hp1.le).expect (po.htEstimator p) = po.ate :=
  po.htEstimator_unbiased _ p hp0 hp1 (bernoulliDesign_inclusionProb p hp0.le hp1.le)

/-- **Variance of the Horvitz-Thompson estimator under the Bernoulli design.** In a nonempty
population, if each unit is treated independently with probability `p`, `0 < p < 1`, the
variance of the estimator over the
design is `N⁻² Σ_i p (1 - p) (y1 i / p + y0 i / (1 - p))^2`. -/
theorem bernoulli_htEstimator_variance [Nonempty ι] (po : PotentialOutcomes ι) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    (bernoulliDesign p hp0.le hp1.le).variance (po.htEstimator p) =
      ((Fintype.card ι : ℝ)⁻¹) ^ 2 *
        ∑ i, p * (1 - p) * (po.y1 i / p + po.y0 i / (1 - p)) ^ 2 := by
  set d := bernoulliDesign (ι := ι) p hp0.le hp1.le
  set w : ι → ℝ := fun i => (Fintype.card ι : ℝ)⁻¹ * (po.y1 i / p + po.y0 i / (1 - p))
  have hf : ∀ a ∈ d.support, po.htEstimator p a =
      -((Fintype.card ι : ℝ)⁻¹ * ∑ i, po.y0 i / (1 - p)) + ∑ i, treatInd a i * w i := by
    intro a _
    rw [po.htEstimator_eq, mul_sum, mul_sum, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [w]
    ring
  rw [d.variance_of_linear _ _ w hf, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_eq_single i (fun j _ hji => by
      rw [bernoulliDesign_pairInclusionProb p _ _ (Ne.symm hji),
        bernoulliDesign_inclusionProb, bernoulliDesign_inclusionProb]
      ring) (by simp),
    d.pairInclusionProb_self, bernoulliDesign_inclusionProb]
  simp only [w]
  ring

end CausalInference.Randomized
