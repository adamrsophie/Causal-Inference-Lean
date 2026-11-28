/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Sandwich
public import CausalInference.Estimation.ZEstimatorExamples

/-!
# The sandwich variance for the sample mean

The sample mean is the Z-estimator with `ψ z θ = f z - θ`. Its empirical bread is `1`, its
empirical meat is `n⁻¹ ∑_{i < n} (f (O i) - P_n f)²`, and the sandwich scale is the sample
standard deviation. The results of `CausalInference.Estimation.Sandwich` and
`CausalInference.zEstimator_tendstoInDistribution` apply with every hypothesis checked.

## Main results

* `CausalInference.sandwichSD_sampleMean`: the sandwich scale of the sample mean is the square root
  of the empirical meat.
* `CausalInference.sampleMean_tendsto_waldInterval_coverage_sandwich`: the Wald interval for
  `E f (O 0)` built from the sample mean and the sandwich scale has asymptotic coverage `1 - α`.
  The proof is `zEstimator_tendsto_waldInterval_coverage`, which uses the consistency of the
  empirical bread, the empirical meat and the sandwich scale.

An `example` derives the normal limit of the sample mean from
`zEstimator_tendstoInDistribution`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  {O : ℕ → Ω → 𝒪}

omit [MeasurableSpace 𝒪] in
/-- The sandwich scale of the sample mean, for `ψ z θ = f z - θ` and `ψ' = -1`, is the square
root of the empirical meat `n⁻¹ ∑_{i < n} (f (O i) - P_n f)²` (the empirical bread is `1`, also
at `n = 0` where both sides vanish). -/
lemma sandwichSD_sampleMean (f : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    sandwichSD O (fun z θ ↦ f z - θ) (fun _ _ ↦ -1) (sampleMean f O) n ω =
      √(sampleMean (fun z ↦ (f z - sampleMean f O n ω) ^ 2) O n ω) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sandwichSD, meatHat, sampleMean]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [sandwichSD, meatHat, breadHat, sampleMean, hn']

/-- **Instance: the Wald interval of the sample mean with the sandwich scale.** For an i.i.d.
sample under a probability measure, a measurable `f` with `f (O 0)` square integrable and of
positive variance, and `z ≥ 0` with `Φ(z) = 1 - α / 2`, the interval
`[P_n f - z σhat n / √n, P_n f + z σhat n / √n]` with the sandwich scale `σhat` covers
`E f (O 0)` with probability tending to `1 - α`. Every hypothesis of
`zEstimator_tendsto_waldInterval_coverage` is checked, with the envelopes `H = 1` and
`G z = 2 f z² + 2 (|E f (O 0)| + 1)²` on the ball of radius `1`. -/
theorem sampleMean_tendsto_waldInterval_coverage_sandwich [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    (hvar : 0 < μ[fun ω ↦ (f (O 0 ω) - μ[fun ω ↦ f (O 0 ω)]) ^ 2]) {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ μ.real {ω | μ[fun ω ↦ f (O 0 ω)] ∈ waldInterval (sampleMean f O n ω)
      (sandwichSD O (fun z θ ↦ f z - θ) (fun _ _ ↦ -1) (sampleMean f O) n ω) z n})
      atTop (𝓝 (1 - α)) := by
  set θ₀ := μ[fun ω ↦ f (O 0 ω)] with hθ₀
  have hfm : MemLp f 2 (μ.map (O 0)) :=
    (memLp_map_measure_iff hf.aestronglyMeasurable (hO.aemeasurable 0)).2 hf2
  have hOf : ∀ i, AEMeasurable (fun ω ↦ f (O i ω)) μ := fun i ↦
    hf.comp_aemeasurable (hO.aemeasurable i)
  have h0 : ∀ n ω, sampleMean (fun z ↦ f z - sampleMean f O n ω) O n ω = 0 := fun n ω ↦ by
    rw [sampleMean, sum_sub_sampleMean_eq_zero, mul_zero]
  refine zEstimator_tendsto_waldInterval_coverage (ψ := fun z θ ↦ f z - θ)
    (ψ' := fun _ _ ↦ -1) (H := fun _ ↦ 1) (G := fun z ↦ 2 * f z ^ 2 + 2 * (|θ₀| + 1) ^ 2)
    (θ₀ := θ₀) (θh := sampleMean f O) hO one_pos (fun θ _ ↦ hf.sub_const θ)
    (fun _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ by simpa using (hasDerivAt_id θ).const_sub (f z))
    (ae_of_all _ fun _ ↦ continuousOn_const) (integrable_const _)
    (ae_of_all _ fun _ _ _ ↦ by simp)
    ((hfm.integrable_sq.const_mul 2).add (integrable_const _))
    (ae_of_all _ fun x θ hθ ↦ ?_)
    (by rw [integral_sub (hf2.integrable one_le_two) (integrable_const _)]; simp [hθ₀])
    (hf2.sub (memLp_const _)) hvar (by rw [sandwichBread_const]; norm_num)
    ((isSampleMeasurable_sampleMean hf O).aemeasurable hO)
    (sampleMean_isConsistent hO hf (hf2.integrable one_le_two))
    ((tendstoInMeasure_const (μ := μ) (0 : ℝ)).congr_withProbTendingToOne
      withProbTendingToOne_univ fun n ω _ ↦ by simp [h0])
    (fun n ↦ ?_) hz hzα
  · have hθ1 : |θ| ≤ |θ₀| + 1 := by
      have h1 := abs_le.1 (Metric.mem_closedBall.1 hθ)
      rw [abs_le]
      constructor <;> linarith [neg_abs_le θ₀, le_abs_self θ₀]
    have hθ2 : θ ^ 2 ≤ (|θ₀| + 1) ^ 2 :=
      sq_le_sq.2 (hθ1.trans (le_abs_self _))
    nlinarith [sq_nonneg (f x + θ)]
  · rw [show sandwichSD O (fun z θ ↦ f z - θ) (fun _ _ ↦ -1) (sampleMean f O) n =
        fun ω ↦ √(sampleMean (fun z ↦ (f z - sampleMean f O n ω) ^ 2) O n ω) from
      funext (sandwichSD_sampleMean f O n)]
    simp only [sampleMean]
    exact (aemeasurable_const.mul
      (Finset.aemeasurable_fun_sum _ fun i _ ↦ ((hOf i).sub (aemeasurable_const.mul
        (Finset.aemeasurable_fun_sum _ fun j _ ↦ hOf j))).pow_const 2)).sqrt

/-- The normal limit of the sample mean through `zEstimator_tendstoInDistribution`, with
`ψ z θ = f z - θ`: the sandwich variance is `E (f (O 0) - E f (O 0))² / 1²`. -/
example [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0
      (μ[fun ω ↦ (f (O 0 ω) - μ[fun ω ↦ f (O 0 ω)]) ^ 2]).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (sampleMean f O n ω - μ[fun ω ↦ f (O 0 ω)]))
      atTop Y (fun _ ↦ μ) P' := by
  set θ₀ := μ[fun ω ↦ f (O 0 ω)] with hθ₀
  have h0 : ∀ n ω, sampleMean (fun z ↦ f z - sampleMean f O n ω) O n ω = 0 := fun n ω ↦ by
    rw [sampleMean, sum_sub_sampleMean_eq_zero, mul_zero]
  have hb : sandwichBread (μ.map (O 0)) (fun _ _ ↦ (-1 : ℝ)) θ₀ = 1 := by
    rw [sandwichBread_const]; norm_num
  refine zEstimator_tendstoInDistribution (ψ := fun z θ ↦ f z - θ)
    (ψ' := fun _ _ ↦ -1) (H := fun _ ↦ 1) (θ₀ := θ₀) (θh := sampleMean f O) hO one_pos
    (hf.sub_const θ₀) (fun _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ by simpa using (hasDerivAt_id θ).const_sub (f z))
    (ae_of_all _ fun _ ↦ continuousOn_const) (integrable_const _)
    (ae_of_all _ fun _ _ _ ↦ by simp)
    (by rw [integral_sub (hf2.integrable one_le_two) (integrable_const _)]; simp [hθ₀])
    (hf2.sub (memLp_const _)) (by rw [hb]; norm_num)
    ((isSampleMeasurable_sampleMean hf O).aemeasurable hO)
    (sampleMean_isConsistent hO hf (hf2.integrable one_le_two))
    ((tendstoInMeasure_const (μ := μ) (0 : ℝ)).congr_withProbTendingToOne
      withProbTendingToOne_univ fun n ω _ ↦ by simp [h0]) ?_
  rw [hb]
  simpa using hY

end CausalInference
