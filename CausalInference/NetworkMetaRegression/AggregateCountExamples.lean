/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountPoisson
public import CausalInference.NetworkMetaRegression.AggregateCountMultinomial
public import CausalInference.NetworkMetaAnalysis.AggregationLimits

/-!
# Aggregate counts: worked instances

A binary covariate `x ∈ {false, true}` with `P(x = true) = 1/2` (`bernoulliLaw (1/2)`), and
arms of two patients.

* **Binary outcome** with risks `m(true) = 3/4`, `m(false) = 1/4`: the averaged risk is `1/2`,
  the count of the arm is `Bin(2, 1/2)` with `P(count = 1) = 1/2` and generating function
  `(1/2 + z/2)²` (`countExample_measureReal_one`, `countExample_generatingFunction`); given the
  covariates `(true, false)` the count is the Poisson binomial law with risks `3/4, 1/4`, with
  generating function `(1/4 + 3z/4)(3/4 + z/4)`, which is not `Bin(2, 1/2)`
  (`poissonBinomial_example_ne`).
* **Count outcome** with rates `r(true) = 3`, `r(false) = 1`: the count of the arm has mean `4`
  and variance `6`, an overdispersion of `2` (`countExample_poisson_moments`), and it has no
  Poisson law (`countExample_not_poisson`).
* **Categorical outcome** with category probabilities `m(x)` and `1 - m(x)`: the count vector
  `(1, 1)` has probability `1/2` (`countExample_multinomial`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory CausalInference.EffectMeasure
  CausalInference.NetworkMetaAnalysis
open scoped unitInterval ENNReal

namespace CausalInference

namespace NetworkMetaRegression

namespace AggregateCountExample

instance isProbabilityMeasure_bernoulliLaw_half :
    IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
  isProbabilityMeasure_bernoulliLaw (by norm_num) (by norm_num)

/-- The risk of the example: `3/4` for `x = true`, `1/4` for `x = false`. -/
noncomputable def risk (b : Bool) : ℝ := if b then 3 / 4 else 1 / 4

theorem risk_mem (b : Bool) : risk b ∈ I := by
  cases b <;> simp only [risk, Bool.false_eq_true, ite_false, ite_true] <;>
    exact ⟨by norm_num, by norm_num⟩

theorem integral_risk : ∫ b, risk b ∂bernoulliLaw (1 / 2) = 1 / 2 := by
  rw [integral_bernoulliLaw (by norm_num) (by norm_num)]
  norm_num [risk]

/-- The joint law of two patients with binary outcomes. -/
noncomputable def binaryArm : Measure (Fin 2 → Bool × ℕ) :=
  Measure.pi fun _ : Fin 2 => bernoulliLaw (1 / 2) ⊗ₘ
    bernoulliKernel risk Measurable.of_discrete risk_mem

theorem binaryArm_count :
    binaryArm.map (fun z => ∑ i, (z i).2) =
      Bin(2, ⟨∫ b, risk b ∂bernoulliLaw (1 / 2), integral_mem_unitInterval
        Measurable.of_discrete risk_mem⟩) :=
  (map_sum_pi_compProd_bernoulli _ Measurable.of_discrete risk_mem 2).2

/-- **The count of the arm is `Bin(2, 1/2)`**: `P(count = 1) = 1/2`. -/
theorem countExample_measureReal_one : binaryArm.real {z | ∑ i, (z i).2 = 1} = 1 / 2 := by
  rw [show {z : Fin 2 → Bool × ℕ | ∑ i, (z i).2 = 1} = (fun z => ∑ i, (z i).2) ⁻¹' {1} from rfl,
    ← map_measureReal_apply (by fun_prop) (measurableSet_singleton 1), binaryArm_count,
    binomial_real_singleton]
  simp only [integral_risk]
  norm_num

/-- **The generating function of the count is `(1/2 + z/2)²`**. -/
theorem countExample_generatingFunction (z : ℝ) :
    generatingFunction (binaryArm.map fun z => ∑ i, (z i).2) z = (1 / 2 + z / 2) ^ 2 := by
  rw [binaryArm_count, ← poissonBinomial_const, generatingFunction_poissonBinomial]
  simp only [integral_risk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **Given the covariates `(true, false)` the count is Poisson binomial with risks `3/4, 1/4`**,
with generating function `(1/4 + 3z/4)(3/4 + z/4)`; this law is not `Bin(2, 1/2)`. -/
theorem poissonBinomial_example_ne :
    (∀ z : ℝ, generatingFunction (poissonBinomial fun i : Fin 2 =>
        (⟨risk (i = 0), risk_mem _⟩ : I)) z = (1 / 4 + 3 * z / 4) * (3 / 4 + z / 4)) ∧
      poissonBinomial (fun i : Fin 2 => (⟨risk (i = 0), risk_mem _⟩ : I)) ≠
        Bin(2, ⟨1 / 2, by norm_num, by norm_num⟩) := by
  refine ⟨fun z => ?_, fun h => ?_⟩
  · rw [generatingFunction_poissonBinomial, Fin.prod_univ_two]
    norm_num [risk]
    ring
  · have := (poissonBinomial_eq_binomial_iff _ _).mp h 0
    have h' := congrArg Subtype.val this
    norm_num [risk] at h'

/-- The rate of the example: `3` for `x = true`, `1` for `x = false`. -/
noncomputable def rate (b : Bool) : ℝ := if b then 3 else 1

theorem rate_nonneg (b : Bool) : 0 ≤ rate b := by cases b <;> norm_num [rate]

theorem memLp_rate : MemLp rate 2 (bernoulliLaw (1 / 2)) := MemLp.of_discrete

/-- The joint law of two patients with count outcomes. -/
noncomputable def countArm : Measure (Fin 2 → Bool × ℕ) :=
  Measure.pi fun _ : Fin 2 => bernoulliLaw (1 / 2) ⊗ₘ poissonKernel rate Measurable.of_discrete

/-- **Overdispersion of the example**: the count of the arm has mean `4` and variance `6`. -/
theorem countExample_poisson_moments :
    ∫ z, ((∑ i, (z i).2 : ℕ) : ℝ) ∂countArm = 4 ∧
      variance (fun z => ((∑ i, (z i).2 : ℕ) : ℝ)) countArm = 6 := by
  have hE : ∫ b, rate b ∂bernoulliLaw (1 / 2) = 2 := by
    rw [integral_bernoulliLaw (by norm_num) (by norm_num)]; norm_num [rate]
  have hV : variance rate (bernoulliLaw (1 / 2)) = 1 := by
    rw [variance_eq_sub memLp_rate, hE]
    simp only [Pi.pow_apply]
    rw [integral_bernoulliLaw (by norm_num) (by norm_num)]; norm_num [rate]
  refine ⟨?_, ?_⟩
  · rw [countArm, integral_count_poisson rate_nonneg (memLp_rate.integrable one_le_two), hE]
    norm_num
  · rw [countArm, variance_count_poisson rate_nonneg memLp_rate, hE, hV]; norm_num

/-- **The count of the example is not Poisson**: the rate is not almost surely constant. -/
theorem countExample_not_poisson :
    ¬ ∃ lam : NNReal, countArm.map (fun z => ∑ i, (z i).2) = poissonMeasure lam := by
  rw [countArm, exists_poisson_count_iff rate_nonneg memLp_rate (by norm_num)]
  rintro ⟨c, hc⟩
  rw [bernoulliLaw, Filter.EventuallyEq, ae_stratumLaw_iff] at hc
  have h1 := hc true (by norm_num)
  have h2 := hc false (by norm_num)
  simp only [rate, ite_true, Bool.false_eq_true, ite_false] at h1 h2
  linarith

/-- The category probabilities of the example: `m(x)` for `true` and `1 - m(x)` for `false`. -/
noncomputable def categoryProb (k : Bool) (b : Bool) : ℝ := if k then risk b else 1 - risk b

theorem isWeights_categoryProb (b : Bool) : IsWeights fun k => categoryProb k b := by
  refine ⟨fun k => ?_, ?_⟩
  · cases k <;> simp only [categoryProb, Bool.false_eq_true, ite_false, ite_true] <;>
      linarith [(risk_mem b).1, (risk_mem b).2]
  · simp [categoryProb]

/-- **The categorical example**: with covariates integrated out, the count vector of two
patients equals `(1, 1)` with probability `2 · (1/2) · (1/2) = 1/2`. -/
theorem countExample_multinomial :
    (Measure.pi fun _ : Fin 2 => bernoulliLaw (1 / 2) ⊗ₘ
        categoricalKernel categoryProb (fun _ => Measurable.of_discrete)
          isWeights_categoryProb).real
        {z | (categoryCount fun i => (z i).2) = fun _ => 1} = 1 / 2 := by
  rw [measureReal_categoryCount_pi_compProd _ (by simp)]
  have h1 : ∫ b, categoryProb true b ∂bernoulliLaw (1 / 2) = 1 / 2 := by
    simpa [categoryProb] using integral_risk
  have h0 : ∫ b, categoryProb false b ∂bernoulliLaw (1 / 2) = 1 / 2 := by
    rw [integral_bernoulliLaw (by norm_num) (by norm_num)]; norm_num [categoryProb, risk]
  rw [Fintype.prod_bool, Fintype.prod_bool, h1, h0]
  norm_num [Nat.factorial]

end AggregateCountExample

end NetworkMetaRegression

end CausalInference
