/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregateCountApproximation

/-!
# Approximating the aggregate binary count: instances

* **The coupling inequality**: the law on pairs putting mass `1 - t` on `(0, 0)` and `t` on
  `(1, 0)` couples `Ber(t)` with the point mass at `0`; it gives `tvDist ≤ 2 t`
  (`tvDist_bernoulli_dirac_le`).
* **An integer adjusted size**: the risks `0, 2/3, 2/3` have `p̄ = 4/9`, `s² = 8/81`, so
  `π* = 2/3 > p̄` and `N* = 2 < 3`; `Bin(2, 2/3)` has the mean and the variance of the Poisson
  binomial law (`adjusted_integer_instance`).
* **A noninteger adjusted size**: the risks `1/4, 3/4` have `p̄ = 1/2`, `s² = 1/16`, so
  `π* = 5/8` and `N* = 8/5`; no binomial law has both moments of the Poisson binomial law
  (`adjusted_noninteger_instance`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal NNReal

namespace CausalInference

namespace NetworkMetaRegression

namespace AggregateCountApproximationInstance

/-- The law on pairs with mass `1 - t` at `(0, 0)` and `t` at `(1, 0)`. -/
noncomputable def pairLaw (t : ℝ) : Measure (ℕ × ℕ) :=
  ENNReal.ofReal (1 - t) • Measure.dirac (0, 0) + ENNReal.ofReal t • Measure.dirac (1, 0)

theorem isProbabilityMeasure_pairLaw {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsProbabilityMeasure (pairLaw t) := by
  constructor
  simp only [pairLaw, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

/-- **The coupling instance**: `tvDist (Ber(t)) δ₀ ≤ 2 t`, with `Ber(t)` the law on `ℕ` with
mass `1 - t` at `0` and `t` at `1`. -/
theorem tvDist_bernoulli_dirac_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    tvDist (ENNReal.ofReal (1 - t) • Measure.dirac 0 + ENNReal.ofReal t • Measure.dirac 1)
      (Measure.dirac 0) ≤ 2 * t := by
  have := isProbabilityMeasure_pairLaw h0 h1
  have hf : (pairLaw t).map Prod.fst =
      ENNReal.ofReal (1 - t) • Measure.dirac 0 + ENNReal.ofReal t • Measure.dirac 1 := by
    rw [pairLaw, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst]
    all_goals fun_prop
  have hs : (pairLaw t).map Prod.snd = Measure.dirac 0 := by
    rw [pairLaw, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd, ← add_smul,
      ← ENNReal.ofReal_add (by linarith) h0]
    · simp
    all_goals fun_prop
  have hD : (pairLaw t).real {p : ℕ × ℕ | p.1 ≠ p.2} = t := by
    rw [pairLaw, measureReal_def, add_apply, smul_apply, smul_apply,
      Measure.dirac_apply' _ (MeasurableSet.of_discrete),
      Measure.dirac_apply' _ (MeasurableSet.of_discrete)]
    simp [ENNReal.toReal_ofReal h0]
  have := tvDist_le_coupling hf hs
  rwa [hD] at this

/-! ### Adjusted binomial instances -/

/-- The risks `0, 2/3, 2/3`. -/
noncomputable def risksInt : Fin 3 → I :=
  ![⟨0, by norm_num, by norm_num⟩, ⟨2 / 3, by norm_num, by norm_num⟩,
    ⟨2 / 3, by norm_num, by norm_num⟩]

theorem meanRisk_risksInt : meanRisk (fun i => (risksInt i : ℝ)) = 4 / 9 := by
  simp [meanRisk, Fin.sum_univ_three, risksInt]; norm_num

theorem riskSpread_risksInt : riskSpread (fun i => (risksInt i : ℝ)) = 8 / 81 := by
  rw [riskSpread, meanRisk_risksInt]
  simp [Fin.sum_univ_three, risksInt]; norm_num

/-- **The integer instance**: `π* = 2/3 > 4/9 = p̄`, `N* = 2 < 3`, and `Bin(2, 2/3)` has the
mean and the variance of the Poisson binomial law with risks `0, 2/3, 2/3`. -/
theorem adjusted_integer_instance :
    adjustedProb (fun i => (risksInt i : ℝ)) = 2 / 3 ∧
      adjustedSize (fun i => (risksInt i : ℝ)) = 2 ∧
      meanRisk (fun i => (risksInt i : ℝ)) < adjustedProb (fun i => (risksInt i : ℝ)) ∧
      adjustedSize (fun i => (risksInt i : ℝ)) < 3 ∧
      ∫ k, (k : ℝ) ∂Bin(2, ⟨2 / 3, by norm_num, by norm_num⟩) =
        ∫ k, (k : ℝ) ∂poissonBinomial risksInt ∧
      variance (fun k : ℕ => (k : ℝ)) (Bin(2, ⟨2 / 3, by norm_num, by norm_num⟩)) =
        variance (fun k : ℕ => (k : ℝ)) (poissonBinomial risksInt) := by
  have hp : 0 < meanRisk (fun i => (risksInt i : ℝ)) := by rw [meanRisk_risksInt]; norm_num
  have hπ : adjustedProb (fun i => (risksInt i : ℝ)) = 2 / 3 := by
    rw [adjustedProb, meanRisk_risksInt, riskSpread_risksInt]; norm_num
  have hN : adjustedSize (fun i => (risksInt i : ℝ)) = 2 := by
    rw [adjustedSize, meanRisk_risksInt, riskSpread_risksInt]; norm_num
  have hne : ¬ ∀ i j, (risksInt i : ℝ) = risksInt j := fun h => by
    have := h 0 1; simp [risksInt] at this; norm_num at this
  have hlt1 := (le_adjustedProb _ (by norm_num) hp).1.lt_of_ne
    fun h => hne ((le_adjustedProb _ (by norm_num) hp).2.mp h.symm)
  have hlt2 := (adjustedSize_le _ (by norm_num) hp).1.lt_of_ne
    fun h => hne ((adjustedSize_le _ (by norm_num) hp).2.mp h)
  obtain ⟨m1, m2⟩ := binomial_adjusted_moments risksInt (by norm_num) hp (m := 2)
    (by rw [hN]; norm_num) ⟨2 / 3, by norm_num, by norm_num⟩ hπ.symm
  exact ⟨hπ, hN, hlt1, by exact_mod_cast hlt2, m1, m2⟩

/-- The risks `1/4, 3/4`. -/
noncomputable def risksFrac : Fin 2 → I :=
  ![⟨1 / 4, by norm_num, by norm_num⟩, ⟨3 / 4, by norm_num, by norm_num⟩]

theorem meanRisk_risksFrac : meanRisk (fun i => (risksFrac i : ℝ)) = 1 / 2 := by
  simp [meanRisk, Fin.sum_univ_two, risksFrac]; norm_num

theorem riskSpread_risksFrac : riskSpread (fun i => (risksFrac i : ℝ)) = 1 / 16 := by
  rw [riskSpread, meanRisk_risksFrac]
  simp [Fin.sum_univ_two, risksFrac]; norm_num

/-- **The noninteger instance**: `π* = 5/8`, `N* = 8/5`, `π* < 1`, and no binomial law has both
moments of the Poisson binomial law with risks `1/4, 3/4`. -/
theorem adjusted_noninteger_instance :
    adjustedProb (fun i => (risksFrac i : ℝ)) = 5 / 8 ∧
      adjustedSize (fun i => (risksFrac i : ℝ)) = 8 / 5 ∧
      adjustedProb (fun i => (risksFrac i : ℝ)) < 1 ∧
      ¬ ∃ (m : ℕ) (θ : I), ∫ k, (k : ℝ) ∂Bin(m, θ) = ∫ k, (k : ℝ) ∂poissonBinomial risksFrac ∧
        variance (fun k : ℕ => (k : ℝ)) (Bin(m, θ)) =
          variance (fun k : ℕ => (k : ℝ)) (poissonBinomial risksFrac) := by
  have hp : 0 < meanRisk (fun i => (risksFrac i : ℝ)) := by rw [meanRisk_risksFrac]; norm_num
  have hN : adjustedSize (fun i => (risksFrac i : ℝ)) = 8 / 5 := by
    rw [adjustedSize, meanRisk_risksFrac, riskSpread_risksFrac]; norm_num
  refine ⟨by rw [adjustedProb, meanRisk_risksFrac, riskSpread_risksFrac]; norm_num, hN,
    adjustedProb_lt_one _ hp (by rw [meanRisk_risksFrac, riskSpread_risksFrac]; norm_num),
    not_exists_binomial_of_adjustedSize risksFrac (by norm_num) hp fun m h => ?_⟩
  rw [hN] at h
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : (m : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hm
    linarith
  · have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith

end AggregateCountApproximationInstance

end NetworkMetaRegression

end CausalInference
