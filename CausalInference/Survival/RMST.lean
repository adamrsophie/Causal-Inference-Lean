/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Censoring
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Restricted mean survival time in discrete time

For an event time `T : Ω → ℕ` on a probability space and a horizon `τ : ℕ`, the restricted mean
survival time is `RMST(τ) = ∑_{k < τ} S k`, the area under the survival curve up to `τ` in the
discrete-time setting of `CausalInference.Survival.Basic` (`S k = P(T > k)`).

## Main definitions

* `Survival.rmst μ T τ = ∑_{k < τ} survival μ T k`.

## Main results

* `Survival.rmst_eq_integral_min`: `RMST(τ) = E[min(T, τ)]`, the mean of the event time
  restricted at `τ`. No integrability hypothesis is needed: `min(T, τ)` is bounded.
* `Survival.rmst_nonneg`, `Survival.rmst_le`, `Survival.rmst_mono`, `Survival.rmst_succ`:
  `0 ≤ RMST(τ) ≤ τ`, and `RMST` is nondecreasing in the horizon.
* `Survival.rmst_eq_of_map_eq`: `RMST` depends only on the law of `T`. So it can be computed
  from any data set with the same law, for instance counterfactual survival times produced by a
  switching adjustment method, and from a weighted law (the measure `μ` is arbitrary).
* `Survival.rmst_eq_sum_productLimit`: under independent censoring, with a positive at-risk
  probability at every `k < τ`, `RMST(τ)` is the sum of the product-limit functional of the
  observed-data law over `k < τ`. This is identification from the observed-data law.
* `Survival.RMSTExample.sum_productLimit_ne_rmst`: under dependent censoring the same sum
  misses `RMST(3)` in the model `CensoringExample.depModel` (`2.71` against `2.305`).

## Source

H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24: Adjusting
survival time estimates in the presence of treatment switching: an update to TSD 16* (2024),
Section 3.1, last bullet: restricted mean survival time summarizes the survival benefit
observed during the trial, and RMST adjusted for switching can be estimated from the adjusted or
weighted survival times produced by the adjustment methods.
The discrete-time setting is that of M. A. Hernán and J. M. Robins, *Causal Inference: What If*
(2020), Chapter 17.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace Survival

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The restricted mean survival time up to the horizon `τ`:
`RMST(τ) = ∑_{k < τ} P(T > k)`, the area under the discrete survival curve on `[0, τ)`. For a
probability measure and a measurable `T` it equals `E[min(T, τ)]`
(`rmst_eq_integral_min`). -/
noncomputable def rmst (μ : Measure Ω) (T : Ω → ℕ) (τ : ℕ) : ℝ :=
  ∑ k ∈ Finset.range τ, survival μ T k

variable {μ : Measure Ω} {T : Ω → ℕ}

@[simp] theorem rmst_zero : rmst μ T 0 = 0 := by simp [rmst]

theorem rmst_succ (τ : ℕ) : rmst μ T (τ + 1) = rmst μ T τ + survival μ T τ :=
  Finset.sum_range_succ _ _

theorem rmst_nonneg (τ : ℕ) : 0 ≤ rmst μ T τ :=
  Finset.sum_nonneg fun k _ => survival_nonneg k

/-- `RMST` is nondecreasing in the horizon. -/
theorem rmst_mono : Monotone (rmst μ T) := fun _ _ h =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun k _ _ => survival_nonneg k

/-- `RMST(τ) ≤ τ` for a probability measure. -/
theorem rmst_le [IsProbabilityMeasure μ] (τ : ℕ) : rmst μ T τ ≤ τ := by
  have := Finset.sum_le_sum fun k (_ : k ∈ Finset.range τ) => survival_le_one (μ := μ) (T := T) k
  simpa [rmst] using this

/-- The restricted mean: `RMST(τ) = E[min(T, τ)]`. -/
theorem rmst_eq_integral_min [IsFiniteMeasure μ] (hT : Measurable T) (τ : ℕ) :
    rmst μ T τ = ∫ ω, ((min (T ω) τ : ℕ) : ℝ) ∂μ := by
  have hpt : ∀ ω, ((min (T ω) τ : ℕ) : ℝ) =
      ∑ k ∈ Finset.range τ, {ω' | k < T ω'}.indicator (1 : Ω → ℝ) ω := by
    intro ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one]
    congr 1
    rw [show (Finset.range τ).filter (fun k => k < T ω) = Finset.range (min (T ω) τ) by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]; tauto]
    exact (Finset.card_range _).symm
  simp_rw [hpt]
  have hint : ∀ k ∈ Finset.range τ, Integrable ({ω' | k < T ω'}.indicator (1 : Ω → ℝ)) μ :=
    fun k _ => (integrable_const (1 : ℝ)).indicator (measurableSet_setOf_of_discrete hT (k < ·))
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_indicator_one (measurableSet_setOf_of_discrete hT (k < ·))]
  rfl

/-- `RMST` depends only on the law of the event time: two event times with the same
distribution have the same restricted mean survival time at every horizon. -/
theorem rmst_eq_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} {T' : Ω' → ℕ}
    (hT : Measurable T) (hT' : Measurable T') (h : μ.map T = ν.map T') (τ : ℕ) :
    rmst μ T τ = rmst ν T' τ := by
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := map_measureReal_apply (μ := μ) hT (MeasurableSet.of_discrete (s := {x | k < x}))
  have h2 := map_measureReal_apply (μ := ν) hT' (MeasurableSet.of_discrete (s := {x | k < x}))
  rw [h] at h1
  exact h1.symm.trans h2

/-- Identification of `RMST` under independent censoring: if the event time `T` and the
censoring time `C` are independent and the at-risk probability `P(T ≥ k, C ≥ k)` is positive
at every `k < τ`, then `RMST(τ)` is the sum over `k < τ` of the product-limit functional of the
law of the observed data `(min T C, 1{T ≤ C})`. Without independent censoring this fails
(`RMSTExample.sum_productLimit_ne_rmst`). -/
theorem rmst_eq_sum_productLimit [IsProbabilityMeasure μ] {C : Ω → ℕ} (hT : Measurable T)
    (hC : Measurable C) (hind : IndepFun T C μ) (τ : ℕ)
    (hk : ∀ k < τ, 0 < μ.real {ω | k ≤ T ω ∧ k ≤ C ω}) :
    rmst μ T τ = ∑ k ∈ Finset.range τ, productLimit (μ.map (observed T C)) k :=
  Finset.sum_congr rfl fun k hk' =>
    (productLimit_map_observed_eq_survival hT hC hind k (hk k (Finset.mem_range.1 hk'))).symm

namespace RMSTExample

open CensoringExample

/-- In `CensoringExample.indepModel` (independent censoring) `RMST(3) = 1 + 0.9 + 0.81`. -/
theorem rmst_indepModel : rmst indepModel Prod.fst 3 = 271 / 100 := by
  have h0 : survival indepModel Prod.fst 0 = 1 := by
    rw [indepModel_eq]
    simp [survival, measureReal_def, add_apply, smul_apply,
      ENNReal.toReal_add, ENNReal.mul_eq_top, ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num
  have h1 : survival indepModel Prod.fst 1 = 9 / 10 := by
    rw [indepModel_eq]
    simp [survival, measureReal_def, add_apply, smul_apply, Measure.dirac_apply, Set.indicator,
      ENNReal.toReal_add, ENNReal.mul_eq_top, ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num
  simp only [rmst, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h0, h1,
    indepModel_survival_two]
  norm_num

/-- In `CensoringExample.depModel` (dependent censoring) `RMST(3) = 1 + 0.9 + 0.405`. -/
theorem rmst_depModel : rmst depModel Prod.fst 3 = 461 / 200 := by
  have h0 : survival depModel Prod.fst 0 = 1 := by
    simp [depModel, survival, measureReal_def, add_apply, smul_apply,
      ENNReal.toReal_add, ENNReal.mul_eq_top, ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num
  have h1 : survival depModel Prod.fst 1 = 9 / 10 := by
    simp [depModel, survival, measureReal_def, add_apply, smul_apply, Measure.dirac_apply,
      Set.indicator, ENNReal.toReal_add, ENNReal.mul_eq_top, ENNReal.toReal_mul,
      ENNReal.toReal_inv]
    norm_num
  simp only [rmst, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h0, h1,
    depModel_survival_two]
  norm_num

/-- Dependent censoring: in `CensoringExample.depModel`, which has the same observed-data law
as `indepModel`, the sum of the product-limit functional over `k < 3` is `2.71` while
`RMST(3) = 2.305`, although the at-risk probability at time `2` is positive. -/
theorem sum_productLimit_ne_rmst :
    ∑ k ∈ Finset.range 3, productLimit (depModel.map (observed Prod.fst Prod.snd)) k = 271 / 100 ∧
      rmst depModel Prod.fst 3 = 461 / 200 := by
  refine ⟨?_, rmst_depModel⟩
  rw [map_observed_depModel, ← rmst_eq_sum_productLimit measurable_fst measurable_snd
    indepFun_indepModel 3 fun k hk => lt_of_lt_of_le indepModel_atRisk_two_pos
      (measureReal_mono fun p (h : 2 ≤ p.1 ∧ 2 ≤ p.2) => by simp only [Set.mem_ofPred_eq]; omega),
    rmst_indepModel]

end RMSTExample

end Survival

end CausalInference
