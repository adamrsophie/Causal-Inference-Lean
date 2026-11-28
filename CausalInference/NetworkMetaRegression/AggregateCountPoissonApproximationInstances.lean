/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountPoissonApproximation

/-!
# Poisson approximation of the aggregate binary count: instances

* **Two risks** (`poissonApprox_twoRisks_le`, `poissonApprox_twoRisks_zero`): for the risks
  `1/10, 1/5` the sum of squares is `1/20`, so the Poisson binomial law and `Po(3/10)` differ by
  at most `1/20` on every set. At `{0}` the two probabilities are `(9/10)(4/5) = 18/25` and
  `e^{-3/10}`.
* **Equal risks** (`poissonApprox_binomial_ten`): `Bin(10, 1/10)` and `Po(1)` differ by at most
  `1/10` on every set.
* **The `ℓ¹` formula** (`tvDist_dirac_zero_one`, `tvDist_bernoulli_quarter_half`): the point
  masses at `0` and `1` are at distance `2 = |1 - 0| + |0 - 1|`, and `Ber(1/4)`, `Ber(1/2)` on
  `{0, 1}` are at distance `|3/4 - 1/2| + |1/4 - 1/2| = 1/2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal NNReal

namespace CausalInference

namespace NetworkMetaRegression

namespace AggregateCountPoissonApproximationInstance

/-- The risks `1/10, 1/5`. -/
noncomputable def risksTenthFifth : Fin 2 → I :=
  ![⟨1 / 10, by norm_num, by norm_num⟩, ⟨1 / 5, by norm_num, by norm_num⟩]

theorem sum_risksTenthFifth : ∑ i, (risksTenthFifth i : ℝ) = 3 / 10 := by
  simp [Fin.sum_univ_two, risksTenthFifth]; norm_num

theorem sum_sq_risksTenthFifth : ∑ i, (risksTenthFifth i : ℝ) ^ 2 = 1 / 20 := by
  simp [Fin.sum_univ_two, risksTenthFifth]; norm_num

/-- **Le Cam's inequality for the risks `1/10, 1/5`**: on every set `A`, the Poisson binomial
law and `Po(3/10)` differ by at most `1/20`, and the total variation norm is at most `1/10`. -/
theorem poissonApprox_twoRisks_le (A : Set ℕ) :
    |(poissonBinomial risksTenthFifth).real A - (poissonMeasure (3 / 10 : ℝ).toNNReal).real A| ≤
        1 / 20 ∧
      tvDist (poissonBinomial risksTenthFifth) (poissonMeasure (3 / 10 : ℝ).toNNReal) ≤ 1 / 10 := by
  have h1 := abs_measureReal_poissonBinomial_sub_poissonMeasure_le risksTenthFifth A
  have h2 := tvDist_poissonBinomial_poissonMeasure_le risksTenthFifth
  rw [sum_risksTenthFifth, sum_sq_risksTenthFifth] at h1 h2
  exact ⟨h1, by linarith⟩

/-- **Both sides at `A = {0}`**: the Poisson binomial law puts `18/25` on `0`, `Po(3/10)` puts
`e^{-3/10}` on `0`, and `|18/25 - e^{-3/10}| ≤ 1/20`. -/
theorem poissonApprox_twoRisks_zero :
    (poissonBinomial risksTenthFifth).real {0} = 18 / 25 ∧
      (poissonMeasure (3 / 10 : ℝ).toNNReal).real {0} = Real.exp (-(3 / 10)) ∧
      |18 / 25 - Real.exp (-(3 / 10))| ≤ 1 / 20 := by
  have hb : (poissonBinomial risksTenthFifth).real {0} = 18 / 25 := by
    rw [(measureReal_poissonBinomial_singleton _ 0).1,
      (measureReal_poissonBinomial_singleton _ 0).2]
    simp [Fin.prod_univ_two, risksTenthFifth]; norm_num
  have hp : (poissonMeasure (3 / 10 : ℝ).toNNReal).real {0} = Real.exp (-(3 / 10)) := by
    rw [poissonMeasure_real_singleton, Real.coe_toNNReal _ (by norm_num)]; simp
  have h := (poissonApprox_twoRisks_le {0}).1
  rw [hb, hp] at h
  exact ⟨hb, hp, h⟩

/-- **Equal risks**: `Bin(10, 1/10)` and `Po(1)` differ by at most `1/10` on every set. -/
theorem poissonApprox_binomial_ten (A : Set ℕ) :
    |(Bin(10, ⟨1 / 10, by norm_num, by norm_num⟩)).real A -
      (poissonMeasure (1 : ℝ).toNNReal).real A| ≤ 1 / 10 := by
  have h := abs_measureReal_binomial_div_sub_poissonMeasure_le (n := 10) (t := 1) (by norm_num)
    (by norm_num) (by norm_num) A
  norm_num at h ⊢
  exact h

/-- **The constant of the `ℓ¹` formula**: the point masses at `0` and `1` are at total
variation distance `2`, which is the sum `|1 - 0| + |0 - 1|` of the point differences. -/
theorem tvDist_dirac_zero_one :
    tvDist (Measure.dirac (0 : ℕ)) (Measure.dirac 1) = 2 ∧
      ∑' k : ℕ, |(Measure.dirac (0 : ℕ)).real {k} - (Measure.dirac (1 : ℕ)).real {k}| = 2 := by
  have h := (tvDist_eq_tsum_abs_measureReal_singleton (Measure.dirac (0 : ℕ))
    (Measure.dirac 1)).2
  have hs : ∑' k : ℕ, |(Measure.dirac (0 : ℕ)).real {k} - (Measure.dirac (1 : ℕ)).real {k}| =
      2 := by
    rw [tsum_eq_sum (s := Finset.range 2) fun k hk => ?_]
    · simp [Finset.sum_range_succ, measureReal_def]; norm_num
    · have h0 : k ≠ 0 := by simp at hk; omega
      have h1 : k ≠ 1 := by simp at hk; omega
      simp [measureReal_def, Set.indicator, h0.symm, h1.symm]
  exact ⟨h.trans hs, hs⟩

/-- **The `ℓ¹` formula on two Bernoulli laws**: `tvDist (Ber(1/4)) (Ber(1/2)) = 1/2`, the sum
`|3/4 - 1/2| + |1/4 - 1/2|` of the point differences on `{0, 1}`. -/
theorem tvDist_bernoulli_quarter_half :
    tvDist (Ber(1, 0, ⟨1 / 4, by norm_num, by norm_num⟩) : Measure ℕ)
      (Ber(1, 0, ⟨1 / 2, by norm_num, by norm_num⟩)) = 1 / 2 := by
  rw [(tvDist_eq_tsum_abs_measureReal_singleton _ _).2,
    tsum_eq_sum (s := Finset.range 2) fun k hk => ?_]
  · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      bernoulli_real_singleton, coeff_bernoulliGenPoly]
    norm_num
  · have h0 : k ≠ 0 := by simp at hk; omega
    have h1 : k ≠ 1 := by simp at hk; omega
    simp [bernoulli_real_singleton, coeff_bernoulliGenPoly, h0, h1]

end AggregateCountPoissonApproximationInstance

end NetworkMetaRegression

end CausalInference
