/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.WeightingConsistency

/-!
# Point treatment: the Hájek estimator in a randomized trial

With the sample proportion of treated units `p̂ = n⁻¹ ∑ 1{A_i = 1}` as a constant fitted score,
the mean weight of the arm `a` is `p̂_a / p̂_a`, where `p̂_a` is the sample proportion of the arm.
So on the event where the arm is not empty the Hájek estimator of `E[Y(a)]` is the observed arm
mean `∑ 1{A_i = a} Y_i / ∑ 1{A_i = a}`, and the Hájek estimator of the average effect is the
difference in arm means. The equality in fact holds for every sample: when the arm is empty both
sides are `0` (as divisions by zero), and so they are for an empty sample.

## Main results

* `sampleIpwWeightMean_propTreated`: the mean weight is `p̂_a / p̂_a`.
* `sampleHajekArmMean_propTreated_of_ne_zero`: the closed form on the event of a nonempty arm.
* `sampleHajekArmMean_propTreated`, `sampleHajekAte_propTreated`: the equality for every sample.
* `isConsistent_sampleHajekAte_propTreated`: in a randomized trial the Hájek estimator of the
  average effect with the sample proportion treated as score is consistent.

## References

* J. Hájek, comment on a paper by D. Basu, in *Foundations of Statistical Inference*, Holt,
  Rinehart and Winston (1971).
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Filter Finset

variable {Ω Ξ 𝒲 : Type*} {mΩ : MeasurableSpace Ω} {mΞ : MeasurableSpace Ξ}

/-- The sample proportion of treated units, as a constant fitted score. -/
noncomputable abbrev propTreatedScore (O : ℕ → Ξ → 𝒲 × Bool × ℝ) : ℕ → Ξ → 𝒲 → ℝ :=
  fun n ξ _ => sampleMean (armIndObs true) O n ξ

/-- With the sample proportion treated as score, the mean weight of the arm `a` is
`p̂_a / p̂_a` for a nonempty sample, `p̂_a` being the sample proportion of the arm. -/
theorem sampleIpwWeightMean_propTreated (a : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) {n : ℕ}
    (hn : n ≠ 0) (ξ : Ξ) :
    sampleIpwWeightMean (propTreatedScore O) a O n ξ =
      sampleMean (armIndObs a) O n ξ / sampleMean (armIndObs a) O n ξ := by
  have key : ∀ z, ipwWeightObs (fun _ => sampleMean (armIndObs true) O n ξ) a z =
      armIndObs a z / sampleMean (armIndObs a) O n ξ := fun z => by
    rw [ipwWeightObs, armProb_sampleMean_armIndObs hn a ξ]
  change (n : ℝ)⁻¹ * ∑ i ∈ range n, ipwWeightObs (fun _ => sampleMean (armIndObs true) O n ξ) a
      (O i ξ) = sampleMean (armIndObs a) O n ξ / sampleMean (armIndObs a) O n ξ
  simp only [key]
  rw [← Finset.sum_div, ← mul_div_assoc]
  rfl

/-- **The Hájek estimator in a trial, on a nonempty arm.** If some sampled unit is in the arm
`a`, the Hájek estimator with the sample proportion treated as score is the observed arm mean
`∑ 1{A_i = a} Y_i / ∑ 1{A_i = a}`. -/
theorem sampleHajekArmMean_propTreated_of_ne_zero (a : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ)
    {n : ℕ} {ξ : Ξ} (ha : ∃ i < n, (O i ξ).2.1 = a) :
    sampleHajekArmMean (propTreatedScore O) a O n ξ = sampleArmMean a O n ξ := by
  obtain ⟨i, hi, hia⟩ := ha
  have hn : n ≠ 0 := by omega
  have hpos : sampleMean (armIndObs a) O n ξ ≠ 0 := by
    refine (mul_pos (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))) ?_).ne'
    refine Finset.sum_pos' (fun j _ => armIndObs_nonneg a _) ⟨i, Finset.mem_range.2 hi, ?_⟩
    simp [armIndObs, hia]
  rw [sampleHajekArmMean, sampleIpwWeightMean_propTreated a O hn ξ, div_self hpos, div_one]
  exact sampleIpwArmMean_propTreated a O n ξ

/-- **The Hájek estimator in a trial is the observed arm mean, for every sample.** On a
nonempty arm this is `sampleHajekArmMean_propTreated_of_ne_zero`; on an empty arm, or an empty
sample, both sides are `0`. -/
theorem sampleHajekArmMean_propTreated (a : Bool) (O : ℕ → Ξ → 𝒲 × Bool × ℝ) (n : ℕ) (ξ : Ξ) :
    sampleHajekArmMean (propTreatedScore O) a O n ξ = sampleArmMean a O n ξ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sampleHajekArmMean, sampleIpwArmMean, sampleArmMean, sampleMean]
  rw [sampleHajekArmMean, sampleIpwWeightMean_propTreated a O hn.ne' ξ,
    sampleIpwArmMean_propTreated a O n ξ]
  by_cases h0 : sampleMean (armIndObs a) O n ξ = 0
  · simp [sampleArmMean, h0]
  · rw [div_self h0, div_one]

/-- **The difference in arm means is the Hájek estimator of the average effect** with the sample
proportion treated as score. -/
theorem sampleHajekAte_propTreated (O : ℕ → Ξ → 𝒲 × Bool × ℝ) :
    sampleHajekAte (propTreatedScore O) O = sampleNaiveContrast O := by
  funext n ξ
  simp only [sampleHajekAte, sampleNaiveContrast, sampleHajekArmMean_propTreated]

/-- **Consistency of the Hájek estimator in a randomized trial.** If `A ⫫ (W, (Y(0), Y(1)))`,
`0 < P(A = 1) < 1` and the potential outcomes are integrable, the Hájek estimator of the
average effect with the sample proportion of treated units as score is consistent for
`E[Y(1) - Y(0)]`. -/
theorem isConsistent_sampleHajekAte_propTreated [MeasurableSpace 𝒲] {μ : Measure Ω}
    {P : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure μ] {A : Ω → Bool}
    {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {O : ℕ → Ξ → 𝒲 × Bool × ℝ} (hW : Measurable W)
    (hA : Measurable A) (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hind : IndepFun A (fun ω => (W ω, potentialPair Y ω)) μ)
    (h0 : 0 < μ.real (A ⁻¹' {true})) (h1 : μ.real (A ⁻¹' {true}) < 1) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map fun ω => (W ω, A ω, obsOutcome A Y ω)) :
    IsConsistent (sampleHajekAte (propTreatedScore O) O) (ate μ Y) P := by
  rw [sampleHajekAte_propTreated]
  exact isConsistent_sampleNaiveContrast_of_indepFun hW hA hY hYi hind h0 h1 hO hlaw

end PointTreatment

end CausalInference
