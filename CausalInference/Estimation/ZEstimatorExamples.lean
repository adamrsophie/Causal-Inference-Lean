/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ZEstimatorNormality

/-!
# Z-estimators and M-estimators in which every hypothesis is checked

Instances of the asymptotic linearity theorems of `CausalInference.Estimation.ZEstimatorNormality`
for an i.i.d. sample `O` and a measurable `f` with `f (O 0)` square integrable.

## Main results

* `CausalInference.log_sampleMean_isAsymptoticallyLinear`: for `E f (O 0) > 0`, the logarithm of
  the sample mean is the root of the nonlinear estimating equation
  `n⁻¹ ∑_{i < n} (f (O i) - exp θ) = 0` with probability tending to one, and it is asymptotically
  linear at `log E f (O 0)` with influence function `(f - E f (O 0)) / E f (O 0)`.

Two `example`s check the hypotheses for the sample mean, whose asymptotic linearity is already
`CausalInference.sampleMean_isAsymptoticallyLinear`: as the root of
`θ ↦ n⁻¹ ∑_{i < n} (f (O i) - θ)` (`zEstimator_isAsymptoticallyLinear_of_root`), and as the
maximizer of the least squares criterion `θ ↦ -n⁻¹ ∑_{i < n} (f (O i) - θ)²`
(`mEstimator_isAsymptoticallyLinear`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  {O : ℕ → Ω → 𝒪}

/-- The bread of a constant derivative `ψ' = c` under a probability law is `-c`. -/
lemma sandwichBread_const (ν : Measure 𝒪) [IsProbabilityMeasure ν] (c θ : ℝ) :
    sandwichBread ν (fun _ _ ↦ c) θ = -c := by
  simp [sandwichBread]

omit [MeasurableSpace 𝒪] in
/-- The sample mean is an exact root of `θ ↦ ∑_{i < n} (f (O i) - θ)`. -/
lemma sum_sub_sampleMean_eq_zero (f : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    ∑ i ∈ range n, (f (O i ω) - sampleMean f O n ω) = 0 := by
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sampleMean]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring

/-- **Instance: the sample mean as a Z-estimator.** With `ψ z θ = f z - θ` (derivative `-1`,
bread `1`, envelope `1`), every hypothesis of `zEstimator_isAsymptoticallyLinear_of_root` holds,
and it gives asymptotic linearity of the sample mean with influence function `f - E f (O 0)`. -/
example [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) :
    IsAsymptoticallyLinear (sampleMean f O) (μ[fun ω ↦ f (O 0 ω)])
      (fun z ↦ f z - μ[fun ω ↦ f (O 0 ω)]) O μ := by
  set θ₀ := μ[fun ω ↦ f (O 0 ω)] with hθ₀
  have h := zEstimator_isAsymptoticallyLinear_of_root (ψ := fun z θ ↦ f z - θ)
    (ψ' := fun _ _ ↦ -1) (H := fun _ ↦ 1) (θ₀ := θ₀) (θh := sampleMean f O) hO one_pos
    (hf.sub_const θ₀) (fun _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ by simpa using (hasDerivAt_id θ).const_sub (f z))
    (ae_of_all _ fun _ ↦ continuousOn_const) (integrable_const _)
    (ae_of_all _ fun _ _ _ ↦ by simp)
    (by rw [integral_sub (hf2.integrable one_le_two) (integrable_const _)]; simp [hθ₀])
    (hf2.sub (memLp_const _)) (by rw [sandwichBread_const]; norm_num)
    (sampleMean_isConsistent hO hf (hf2.integrable one_le_two))
    (withProbTendingToOne_univ.mono fun n ω _ ↦ sum_sub_sampleMean_eq_zero f O n ω)
  simpa [sandwichBread_const] using h

/-- **Instance: a nonlinear estimating equation.** Let `E f (O 0) > 0` and
`ψ z θ = f z - exp θ` (derivative `-exp θ`, bread `exp θ₀ = E f (O 0)`, envelope
`exp (θ₀ + 1)` on the ball of radius `1`). The logarithm of the sample mean solves the estimating
equation whenever the sample mean is positive, which happens with probability tending to one,
and it is consistent for `θ₀ = log E f (O 0)`. Hence it is asymptotically linear at `θ₀` with
influence function `(f - E f (O 0)) / E f (O 0)`, the delta method value for the logarithm. -/
theorem log_sampleMean_isAsymptoticallyLinear [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {f : 𝒪 → ℝ} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    (hpos : 0 < μ[fun ω ↦ f (O 0 ω)]) :
    IsAsymptoticallyLinear (fun n ω ↦ Real.log (sampleMean f O n ω))
      (Real.log (μ[fun ω ↦ f (O 0 ω)]))
      (fun z ↦ (μ[fun ω ↦ f (O 0 ω)])⁻¹ * (f z - μ[fun ω ↦ f (O 0 ω)])) O μ := by
  set a := μ[fun ω ↦ f (O 0 ω)] with ha
  set θ₀ := Real.log a with hθ₀
  have hexp : Real.exp θ₀ = a := Real.exp_log hpos
  have hcons : IsConsistent (sampleMean f O) a μ :=
    sampleMean_isConsistent hO hf (hf2.integrable one_le_two)
  have hθ : IsConsistent (fun n ω ↦ Real.log (sampleMean f O n ω)) θ₀ μ :=
    IsConsistent.comp (Real.continuousAt_log hpos.ne') hcons
  have hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n,
      (f (O i ω) - Real.exp (Real.log (sampleMean f O n ω))) = 0}) := by
    refine (TendstoInMeasure.withProbTendingToOne_dist_lt hcons hpos).mono fun n ω hω ↦ ?_
    simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
    have hs : 0 < sampleMean f O n ω := by linarith [(abs_lt.1 hω).1]
    rw [Real.exp_log hs]
    exact sum_sub_sampleMean_eq_zero f O n ω
  have hb : sandwichBread (μ.map (O 0)) (fun _ θ ↦ -Real.exp θ) θ₀ = a := by
    simp [sandwichBread, hexp]
  have h := zEstimator_isAsymptoticallyLinear_of_root (ψ := fun z θ ↦ f z - Real.exp θ)
    (ψ' := fun _ θ ↦ -Real.exp θ) (H := fun _ ↦ Real.exp (θ₀ + 1)) (θ₀ := θ₀) hO one_pos
    (hf.sub_const _) (fun _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ by simpa using (Real.hasDerivAt_exp θ).const_sub (f z))
    (ae_of_all _ fun _ ↦ (Real.continuous_exp.neg).continuousOn) (integrable_const _)
    (ae_of_all _ fun _ θ hθ ↦ by
      rw [abs_neg, abs_of_pos (Real.exp_pos θ), Real.exp_le_exp]
      have := (abs_le.1 (Metric.mem_closedBall.1 hθ)).2
      linarith)
    (by
      rw [integral_sub (hf2.integrable one_le_two) (integrable_const _), hexp]
      simp [ha])
    (hf2.sub (memLp_const _)) (by rw [hb]; exact hpos.ne') hθ hroot
  simpa [hb, hexp] using h

/-- **Instance: the sample mean as a least squares M-estimator.** With the criterion
`m z θ = -(f z - θ)²`, its derivative `ψ z θ = 2 (f z - θ)` (derivative `-2`, bread `2`), the
sample mean is a global, hence local, maximizer of the sample criterion for every `n`
(`sampleMean_sq_sub_eq`). Every hypothesis of `mEstimator_isAsymptoticallyLinear` holds, and it
gives asymptotic linearity of the sample mean with influence function `f - E f (O 0)`. -/
example [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) :
    IsAsymptoticallyLinear (sampleMean f O) (μ[fun ω ↦ f (O 0 ω)])
      (fun z ↦ f z - μ[fun ω ↦ f (O 0 ω)]) O μ := by
  set θ₀ := μ[fun ω ↦ f (O 0 ω)] with hθ₀
  have hmax : ∀ n ω, IsLocalMax (fun θ ↦ sampleMean (fun z ↦ -(f z - θ) ^ 2) O n ω)
      (sampleMean f O n ω) := by
    intro n ω
    refine Eventually.of_forall fun θ ↦ ?_
    have hneg : ∀ g : 𝒪 → ℝ, sampleMean (fun z ↦ -g z) O n ω = -sampleMean g O n ω := by
      intro g
      simp [sampleMean, sum_neg_distrib]
    simp only [hneg]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleMean]
    · rw [sampleMean_sq_sub_eq hn.ne' ω θ]
      nlinarith [sq_nonneg (θ - sampleMean f O n ω)]
  have h := mEstimator_isAsymptoticallyLinear (m := fun z θ ↦ -(f z - θ) ^ 2)
    (ψ := fun z θ ↦ 2 * (f z - θ)) (ψ' := fun _ _ ↦ -2) (H := fun _ ↦ 2) (θ₀ := θ₀)
    (θh := sampleMean f O) hO one_pos
    (ae_of_all _ fun z θ _ ↦ (((hasDerivAt_id θ).const_sub (f z)).pow 2).neg.congr_deriv
      (by simp only [id, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring))
    ((hf.sub_const θ₀).const_mul 2) (fun _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ (((hasDerivAt_id θ).const_sub (f z)).const_mul 2).congr_deriv
      (by ring))
    (ae_of_all _ fun _ ↦ continuousOn_const) (integrable_const _)
    (ae_of_all _ fun _ _ _ ↦ by simp)
    (by
      rw [integral_const_mul, integral_sub (hf2.integrable one_le_two) (integrable_const _)]
      simp [hθ₀])
    ((hf2.sub (memLp_const _)).const_mul 2) (by rw [sandwichBread_const]; norm_num)
    (sampleMean_isConsistent hO hf (hf2.integrable one_le_two))
    (withProbTendingToOne_univ.mono fun n ω _ ↦ hmax n ω)
  have hb : sandwichBread (μ.map (O 0)) (fun _ _ ↦ (-2 : ℝ)) θ₀ = 2 := by
    rw [sandwichBread_const]; norm_num
  rw [hb] at h
  convert h using 2 with z
  field_simp

end CausalInference
