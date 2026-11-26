/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.Complete
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

/-!
# Neyman's variance formula for complete randomization

For the difference in means `τ̂` under complete randomization with `n1` treated and `n0`
control units out of `N = n1 + n0`, Neyman (1923) showed
`Var(τ̂) = S1²/n1 + S0²/n0 - S_τ²/N`, where `S1²`, `S0²`, `S_τ²` are the finite-population
variances (with denominator `N - 1`) of the treated potential outcomes, the control potential
outcomes, and the unit-level effects. Consequently the conservative variance `S1²/n1 + S0²/n0`
is an upper bound, attained when the unit-level effects are constant. Sources: Neyman (1923,
translated 1990); Imbens and Rubin (2015), *Causal Inference for Statistics, Social, and
Biomedical Sciences*.

## Main results

All declarations live in the namespace `CausalInference.Randomized`.

* `Design.variance_of_linear`: for any design, the variance of a statistic that
  is affine in the treatment indicators, `c + Σ_i A_i w_i`, equals
  `Σ_i Σ_j (π_ij - π_i π_j) w_i w_j`.
* `neyman_variance`: Neyman's variance formula.
* `neyman_variance_le`: the conservative variance is an upper bound.
* `neyman_variance_eq_iff`: the bound is attained exactly when `S_τ² = 0`.
* `neyman_variance_eq_of_constant_effect`: equality under constant effects.
* `fourUnit_variance` and companions: a concrete population with `N = 4` and
  `n1 = 2`, where the variance of the difference in means is `7/2`.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι : Type*} [Fintype ι]

/-- The sum of squared deviations from the mean: `Σ_i (f i - f̄)^2 = Σ_i f i ^2 - (Σ_i f i)^2/N`.
-/
theorem sum_sq_sub_popMean (f : ι → ℝ) (hN : 0 < Fintype.card ι) :
    ∑ i, (f i - popMean f) ^ 2 =
      ∑ i, f i ^ 2 - (Fintype.card ι : ℝ)⁻¹ * (∑ i, f i) ^ 2 := by
  have hN' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    popMean]
  rw [← sum_mul, ← mul_sum]
  field_simp
  ring

/-- For any design, if a statistic equals `c + Σ_i A_i w_i` on the support, where `A_i` is the
treatment indicator, then its variance is `Σ_i Σ_j (π_ij - π_i π_j) w_i w_j`. -/
theorem Design.variance_of_linear (d : Design ι) (f : (ι → Bool) → ℝ) (c : ℝ) (w : ι → ℝ)
    (hf : ∀ a ∈ d.support, f a = c + ∑ i, treatInd a i * w i) :
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

/-- A double sum whose coefficient depends only on whether the indices agree:
`Σ_i Σ_j (A if i = j else B) w_i w_j = (A - B) Σ_i w_i^2 + B (Σ_i w_i)^2`. -/
theorem sum_sum_ite_eq [DecidableEq ι] (A B : ℝ) (w : ι → ℝ) :
    ∑ i, ∑ j, (if i = j then A else B) * w i * w j =
      (A - B) * ∑ i, w i ^ 2 + B * (∑ i, w i) ^ 2 := by
  have : ∀ i j, (if i = j then A else B) * w i * w j =
      B * (w i * w j) + if i = j then (A - B) * w i ^ 2 else 0 := by
    intro i j
    split_ifs with h
    · subst h; ring
    · ring
  simp only [this, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, sq,
    sum_mul_sum]
  ring

omit [Fintype ι] in
/-- For any design, `π_ii = π_i`, since the treatment indicator is idempotent. -/
theorem Design.pairInclusionProb_self (d : Design ι) (i : ι) :
    d.pairInclusionProb i i = d.inclusionProb i :=
  d.expect_congr fun a _ => by unfold treatInd; split_ifs <;> norm_num

/-- The difference in means is affine in the treatment indicators:
`τ̂ = -(1/n0) Σ_i y0 i + Σ_i A_i (y1 i / n1 + y0 i / n0)`. -/
theorem PotentialOutcomes.diffInMeans_eq_linear (po : PotentialOutcomes ι) (n1 n0 : ℕ)
    (a : ι → Bool) :
    po.diffInMeans n1 n0 a = -((n0 : ℝ)⁻¹ * ∑ i, po.y0 i) +
      ∑ i, treatInd a i * (po.y1 i / n1 + po.y0 i / n0) := by
  have h1 : ∀ i, treatInd a i * po.observed a i = treatInd a i * po.y1 i := by
    intro i; unfold treatInd observed; split_ifs <;> simp
  have h0 : ∀ i, (1 - treatInd a i) * po.observed a i = (1 - treatInd a i) * po.y0 i := by
    intro i; unfold treatInd observed; split_ifs <;> simp
  simp only [diffInMeans, h1, h0, mul_sum, ← sum_neg_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **Neyman's variance formula.** Under complete randomization with `n1` treated and `n0`
control units, `N = n1 + n0`, `n1, n0 > 0`, the variance of the difference in means over the
randomization distribution is `S1²/n1 + S0²/n0 - S_τ²/N`. -/
theorem neyman_variance [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) =
      po.varTreated / n1 + po.varControl / n0 - po.varEffect / Fintype.card ι := by
  set d := completeDesign (ι := ι) n1 (by omega)
  set w : ι → ℝ := fun i => po.y1 i / n1 + po.y0 i / n0 with hw
  have hN1 : 1 < Fintype.card ι := by omega
  have hNr : (Fintype.card ι : ℝ) = n1 + n0 := by rw [← hn]; push_cast; ring
  have hn1r : (n1 : ℝ) ≠ 0 := by exact_mod_cast hn1.ne'
  have hn0r : (n0 : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hpos1 : (0 : ℝ) < n1 := by exact_mod_cast hn1
  have hpos0 : (0 : ℝ) < n0 := by exact_mod_cast hn0
  have hNm1 : (n1 : ℝ) + n0 - 1 ≠ 0 := by
    have : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
    linarith
  -- Step 1: the general variance formula for an affine statistic.
  rw [d.variance_of_linear _ _ w fun a _ => po.diffInMeans_eq_linear n1 n0 a]
  -- Step 2: the covariances of the treatment indicators under complete randomization.
  set π : ℝ := n1 / Fintype.card ι
  set q : ℝ := n1 * (n1 - 1) / (Fintype.card ι * (Fintype.card ι - 1))
  have hcov : ∀ i j, (d.pairInclusionProb i j - d.inclusionProb i * d.inclusionProb j) * w i *
      w j = (if i = j then π - π * π else q - π * π) * w i * w j := by
    intro i j
    have hπ : ∀ k, d.inclusionProb k = π := fun k =>
      completeDesign_inclusionProb n1 (by omega) (by omega) k
    split_ifs with h
    · subst h
      rw [d.pairInclusionProb_self, hπ]
    · rw [completeDesign_pairInclusionProb n1 (by omega) hN1 h, hπ, hπ]
  simp only [hcov]
  rw [sum_sum_ite_eq]
  -- Step 3: rewrite in terms of the sum of squared deviations of `w`.
  have hsq := sum_sq_sub_popMean w (by omega)
  have hstep : (π - π * π - (q - π * π)) * ∑ i, w i ^ 2 + (q - π * π) * (∑ i, w i) ^ 2 =
      n1 * n0 / ((n1 + n0) * (n1 + n0 - 1)) * ∑ i, (w i - popMean w) ^ 2 := by
    rw [hsq]
    simp only [π, q, hNr]
    field_simp
    ring
  rw [hstep]
  -- Step 4: a unitwise identity between deviations.
  have hmw : popMean w = popMean po.y1 / n1 + popMean po.y0 / n0 := by
    simp only [popMean, hw, sum_add_distrib, ← sum_div]
    ring
  have hmt : popMean po.unitEffect = popMean po.y1 - popMean po.y0 := by
    simp only [popMean, PotentialOutcomes.unitEffect, sum_sub_distrib]
    ring
  simp only [PotentialOutcomes.varTreated, PotentialOutcomes.varControl,
    PotentialOutcomes.varEffect, popVar, hmw, hmt, hNr, mul_sum, sum_div, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [hw, PotentialOutcomes.unitEffect]
  field_simp
  ring

/-- **The conservative variance bound.** Under complete randomization the variance of the
difference in means is at most `S1²/n1 + S0²/n0`. -/
theorem neyman_variance_le [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) ≤
      po.varTreated / n1 + po.varControl / n0 := by
  rw [neyman_variance po hn hn1 hn0]
  have h1 : 0 ≤ po.varEffect := popVar_nonneg _ (by omega)
  have h2 : 0 ≤ po.varEffect / Fintype.card ι := div_nonneg h1 (Nat.cast_nonneg _)
  linarith

/-- The conservative variance `S1²/n1 + S0²/n0` equals the true variance of the difference in
means exactly when the unit-level effects have zero finite-population variance. -/
theorem neyman_variance_eq_iff [DecidableEq ι] (po : PotentialOutcomes ι) {n1 n0 : ℕ}
    (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) =
      po.varTreated / n1 + po.varControl / n0 ↔ po.varEffect = 0 := by
  rw [neyman_variance po hn hn1 hn0]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    have : 0 < Fintype.card ι := by omega
    exact_mod_cast this.ne'
  constructor
  · intro h
    have : po.varEffect / Fintype.card ι = 0 := by linarith
    simpa [hN] using this
  · intro h
    simp [h]

/-- **Equality under constant effects.** If every unit has the same treatment effect, the
variance of the difference in means under complete randomization equals the conservative
variance `S1²/n1 + S0²/n0`. -/
theorem neyman_variance_eq_of_constant_effect [DecidableEq ι] (po : PotentialOutcomes ι)
    {n1 n0 : ℕ} (hn : n1 + n0 = Fintype.card ι) (hn1 : 0 < n1) (hn0 : 0 < n0) (c : ℝ)
    (hc : ∀ i, po.unitEffect i = c) :
    (completeDesign n1 (by omega)).variance (po.diffInMeans n1 n0) =
      po.varTreated / n1 + po.varControl / n0 :=
  (neyman_variance_eq_iff po hn hn1 hn0).mpr (popVar_const c _ hc (by omega))

/-! ### A concrete example: `N = 4`, `n1 = 2` -/

section Example

/-- Potential outcomes of four units: `y1 = (3, 5, 4, 8)` and `y0 = (1, 2, 4, 5)`, so the unit
effects are `(2, 3, 0, 3)`. -/
def fourUnitPO : PotentialOutcomes (Fin 4) where
  y1 := ![3, 5, 4, 8]
  y0 := ![1, 2, 4, 5]

/-- There are `6 = 4 choose 2` assignments treating two of four units. -/
theorem fourUnit_card : #(completeSupport (ι := Fin 4) 2) = 6 := by decide

/-- Each of four units is treated with probability `1/2` when two are treated. -/
theorem fourUnit_inclusionProb (i : Fin 4) :
    (completeDesign (ι := Fin 4) 2 (by decide)).inclusionProb i = 1 / 2 := by
  rw [completeDesign_inclusionProb 2 _ (by decide)]
  norm_num

/-- Two distinct units out of four are both treated with probability `1/6`. -/
theorem fourUnit_pairInclusionProb :
    (completeDesign (ι := Fin 4) 2 (by decide)).pairInclusionProb 0 1 = 1 / 6 := by
  rw [completeDesign_pairInclusionProb 2 _ (by decide) (by decide)]
  norm_num

/-- The average treatment effect of the example is `2`. -/
theorem fourUnit_ate : fourUnitPO.ate = 2 := by
  simp [PotentialOutcomes.ate, popMean, PotentialOutcomes.unitEffect, fourUnitPO,
    Fin.sum_univ_four]
  norm_num

/-- In the example `S1² = 14/3`, `S0² = 10/3`, `S_τ² = 2`, so Neyman's formula gives the variance
`(14/3)/2 + (10/3)/2 - 2/4 = 7/2` for the difference in means. -/
theorem fourUnit_variance :
    (completeDesign (ι := Fin 4) 2 (by decide)).variance (fourUnitPO.diffInMeans 2 2) = 7 / 2 := by
  rw [neyman_variance fourUnitPO (by decide) (by decide) (by decide)]
  simp [PotentialOutcomes.varTreated, PotentialOutcomes.varControl,
    PotentialOutcomes.varEffect, popVar, popMean, PotentialOutcomes.unitEffect, fourUnitPO,
    Fin.sum_univ_four]
  norm_num

end Example

end CausalInference.Randomized
