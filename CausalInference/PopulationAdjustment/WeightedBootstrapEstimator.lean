/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapCoverage
public import CausalInference.PopulationAdjustment.WeightedNormalityLimit

/-!
# The bootstrapped entropy balancing estimator

A record is `z = (x, a, y)`: covariates `x`, arm `a` and outcome `y`. For a sample
`y = (z_1, …, z_n)` of records, the entropy balancing weights match the feature `φ` to the target
`t`, and the weighted mean of the outcome in arm `a` is the statistic `T_n(y)`. The data estimate
`m̂ₙ = sampleBalancedArmMean` is `T_n` at the first `n` observations; the bootstrap estimate
`m*ₙ` is `T_n` at a resample drawn from their empirical law.

## Main definitions

* `bootstrapTilt φ t n y`: the minimizer of the entropy dual of the sample `y`.
* `bootstrapArmMean φ t a n y`: the weighted mean of the outcome in arm `a` of the sample `y`.

## Main results

* `measurable_bootstrapArmMean`: the statistic is a measurable function of the sample, so the
  bootstrap law `bootstrapLaw (bootstrapArmMean φ t a) O n ω` is the law of a random variable.
* `sampleBalancedArmMean_eq_bootstrapArmMean`: the data estimate is the statistic at the data.
* `bootstrapArmMean_eq_div`: the statistic is the ratio of the resample means of
  `1{A = a} w Y` and `1{A = a} w` at the tilt `w = w_β` of the sample.

## References

* B. Efron (1979), *Bootstrap methods: another look at the jackknife*, Annals of Statistics 7.
* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment Bootstrap

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]

/-- The minimizer `β̂(y)` of the entropy dual `β ↦ log ∑ᵢ exp(βᵀ(φ(xᵢ) - t))` of a sample `y`. -/
noncomputable def bootstrapTilt (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (n : ℕ)
    (y : Fin n → 𝒳 × Bool × ℝ) : Fin p → ℝ :=
  dualMinimizer fun i : Fin n => φ (y i).1 - t

/-- The **weighted arm mean of a sample** `y`: the entropy balancing weights of `y` for the
feature `φ` and the target `t`, and the weighted mean of the outcome in arm `a`. -/
noncomputable def bootstrapArmMean (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool) (n : ℕ)
    (y : Fin n → 𝒳 × Bool × ℝ) : ℝ :=
  weightedArmMean (balancingWeights fun i : Fin n => φ (y i).1 - t) (fun i => (y i).2.1)
    (fun i => (y i).2.2) a

/-- **The weighted arm mean is a measurable function of the sample.** -/
theorem measurable_bootstrapArmMean {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t : Fin p → ℝ)
    (a : Bool) (n : ℕ) : Measurable (bootstrapArmMean φ t a n) := by
  have hw : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      balancingWeights fun i : Fin n => φ (x i).1 - t :=
    measurable_balancingWeights_sample (φ := fun r : 𝒳 × Bool × ℝ => φ r.1)
      (hφ.comp measurable_fst) t
  have hA : ∀ i, Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      armWeights (balancingWeights fun i : Fin n => φ (x i).1 - t) (fun i => (x i).2.1) a i :=
    fun i => Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i).snd.fst
      measurable_const) ((measurable_pi_apply i).comp hw) measurable_const
  exact (Finset.measurable_sum _ fun i _ => (hA i).mul (measurable_pi_apply i).snd.snd).div
    (Finset.measurable_sum _ fun i _ => hA i)

omit [MeasurableSpace 𝒳] [MeasurableSpace Ω] in
/-- **The data estimate is the statistic at the data**: `m̂ₙ = T_n(O_0, …, O_{n-1})`. -/
theorem sampleBalancedArmMean_eq_bootstrapArmMean (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) (n : ℕ) (ω : Ω) :
    sampleBalancedArmMean φ t O a n ω = bootstrapArmMean φ t a n (dataPrefix O n ω) :=
  rfl

omit [MeasurableSpace 𝒳] in
/-- **The statistic as a ratio of resample means**: at the tilt `w = w_{β̂(y)}` of the sample,
`T_n(y) = (n⁻¹ ∑ᵢ 1{aᵢ = a} w(xᵢ) yᵢ) / (n⁻¹ ∑ᵢ 1{aᵢ = a} w(xᵢ))`. -/
theorem bootstrapArmMean_eq_div (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool) (n : ℕ)
    (y : Fin n → 𝒳 × Bool × ℝ) :
    bootstrapArmMean φ t a n y =
      resampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (bootstrapTilt φ t n y) z.1 * z.2.2)
        n y /
      resampleMean (fun z => armIndObs a z * tiltWeight φ t 0 (bootstrapTilt φ t n y) z.1) n y := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bootstrapArmMean, weightedArmMean, weightedMean, resampleMean]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set Δ := fun i : Fin n => φ (y i).1 - t
  set w : 𝒳 → ℝ := tiltWeight φ t 0 (bootstrapTilt φ t n y)
  have hw : balancingWeights Δ = fun i : Fin n => (partitionFunction Δ (bootstrapTilt φ t n y))⁻¹ *
      w (y i).1 := by
    funext i
    simp [balancingWeights, entropyWeights, tiltWeight, bootstrapTilt, Δ, w, div_eq_inv_mul]
  rw [bootstrapArmMean, hw, weightedArmMean_smul (inv_ne_zero (partitionFunction_pos _).ne'),
    weightedArmMean, weightedMean, resampleMean, resampleMean]
  have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
  rw [mul_div_mul_left _ _ hn']
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
    simp only [armWeights, armIndObs] <;> split_ifs <;> simp

end PopulationAdjustment

end CausalInference
