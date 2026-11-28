/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.SandwichMatrix
public import CausalInference.Estimation.VectorDeltaMethod

/-!
# Vector limit theory in which every hypothesis is checked

Instances of the results of `CausalInference.Estimation.VectorZEstimator`,
`CausalInference.Estimation.SandwichMatrix`, `CausalInference.Estimation.VectorDeltaMethod` and
`CausalInference.Estimation.GaussianLinearImage` for an i.i.d. sample `O` and a measurable
`f : 𝒪 → ℝ^ι` with `f (O 0)` square integrable, mean `m` and covariance matrix `Σ`.

## Main results

* `CausalInference.vectorSampleMean_zEstimator_tendstoInDistribution`: the vector sample mean is
  the Z-estimator of `ψ z θ = f z - θ` (Jacobian `-1`, bread the identity), every hypothesis of
  `vectorZEstimator_tendstoInDistribution_of_root` holds, and the conclusion is the multivariate
  central limit theorem.
* `CausalInference.vectorSampleMean_sandwich_tendstoInMeasure`: for this estimating function,
  `n` times the sandwich estimate is the empirical covariance matrix, and it is consistent for
  `Σ`.
* `CausalInference.linearZEstimator_tendstoInDistribution`: a non identity bread: for a
  nonsingular matrix `C`, the root `C⁻¹ (P_n f)` of `n⁻¹ ∑_{i < n} (f (O i) - C θ) = 0` satisfies
  `√n (θh n - C⁻¹ m) → N(0, C⁻¹ Σ C⁻ᵀ)`, through the general theorem with bread `C`.
* `CausalInference.linearZEstimator_isAsymptoticallyLinear`: in the same setting, every
  coordinate of `θh n` is asymptotically linear, through `vectorZEstimator_isAsymptoticallyLinear`.
* `CausalInference.sampleMean_apply_tendstoInDistribution`: joint normality of the coordinate
  sample means, as asymptotically linear estimators.
* `CausalInference.matrixCLM_sampleMean_tendstoInDistribution` and
  `CausalInference.matrixCLM_sampleMean_apply_tendstoInDistribution`: the vector delta method for
  a linear map, for the vector sample mean and for the coordinate sample means.
* Slutsky instances: `CausalInference.inner_sampleMean_tendstoInDistribution` and
  `CausalInference.matrixCLM_sampleMean_mul_tendstoInDistribution`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

/-! ### The vector sample mean -/

omit [MeasurableSpace 𝒪] [IsProbabilityMeasure μ] in
/-- The vector sample mean `P_n f = n⁻¹ ∑_{i < n} f (O i)` is an exact root of
`θ ↦ ∑_{i < n} (f (O i) - C θ)` after the change of variable `θ = C⁻¹ P_n f`, for `C`
nonsingular; `C = 1` is the sample mean itself. -/
lemma sum_sub_mulVec_inv_eq_zero (f : 𝒪 → EuclideanSpace ℝ ι) {C : Matrix ι ι ℝ}
    (hC : C.det ≠ 0) (n : ℕ) (ω : Ω) :
    ∑ i ∈ range n, (f (O i ω) - Matrix.toEuclideanCLM (𝕜 := ℝ) C
      (Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹ ((n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)))) = 0 := by
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.2 hC
  have hCC : ∀ v, Matrix.toEuclideanCLM (𝕜 := ℝ) C (Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹ v) =
      v := fun v ↦ by
    have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) C * Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv C hCu, map_one]
    exact congrArg (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι ↦ T v) h1
  rw [sum_sub_distrib, hCC, sum_const, card_range]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn', one_smul, sub_self]

omit [MeasurableSpace 𝒪] [DecidableEq ι] in
/-- The covariance matrix does not change when a constant vector is subtracted. -/
lemma covMatrix_sub_const {f : 𝒪 → EuclideanSpace ℝ ι}
    (hint : Integrable (fun ω ↦ f (O 0 ω)) μ) (c : EuclideanSpace ℝ ι) :
    covMatrix μ (fun i ω ↦ (f (O 0 ω) - c) i) = covMatrix μ (fun i ω ↦ f (O 0 ω) i) := by
  have hc : ∀ i, Integrable (fun ω ↦ f (O 0 ω) i) μ := fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hint
  ext i j
  simp only [covMatrix, Matrix.of_apply, PiLp.sub_apply]
  rw [covariance_sub_const_left (hc i), covariance_sub_const_right (hc j)]

/-- **A Z-estimator with a non identity bread.** Let `C` be nonsingular and
`ψ z θ = f z - C θ`, with Jacobian `-C` and bread `C`. The root of
`n⁻¹ ∑_{i < n} ψ (O i) θ = 0` is `θh n = C⁻¹ (P_n f)`, the true value is `θ₀ = C⁻¹ m`, and every
hypothesis of `vectorZEstimator_tendstoInDistribution_of_root` holds; hence
`√n (θh n - θ₀) → N(0, C⁻¹ Σ C⁻ᵀ)` in distribution. -/
theorem linearZEstimator_tendstoInDistribution (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {C : Matrix ι ι ℝ} (hC : C.det ≠ 0) {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0
      (C⁻¹ * covMatrix μ (fun i ω ↦ f (O 0 ω) i) * C⁻¹ᵀ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹ ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) -
        Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹ (μ[fun ω ↦ f (O 0 ω)]))) atTop Y (fun _ ↦ μ) P' := by
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.2 hC
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) C
  set Tinv := Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹
  have hCC : ∀ v, T (Tinv v) = v := fun v ↦ by
    have h1 : T * Tinv = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv C hCu, map_one]
    exact congrArg (fun S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι ↦ S v) h1
  have hint : Integrable (fun ω ↦ f (O 0 ω)) μ := hf2.integrable one_le_two
  set m := μ[fun ω ↦ f (O 0 ω)]
  have hbread : breadMatrix (μ.map (O 0)) (fun _ _ ↦ -C) (Tinv m) = C := by
    ext i j
    simp [breadMatrix]
  have hB : MemLp (fun ω ↦ f (O 0 ω) - T (Tinv m)) 2 μ := by
    simp only [hCC]
    exact hf2.sub (memLp_const m)
  have hzero : μ[fun ω ↦ f (O 0 ω) - T (Tinv m)] = 0 := by
    simp only [hCC]
    rw [integral_sub hint (integrable_const _), integral_const]
    simp [m]
  have hmeat : meatMatrix (μ.map (O 0)) (fun z θ ↦ f z - T θ) (Tinv m) =
      covMatrix μ (fun i ω ↦ f (O 0 ω) i) := by
    rw [← covMatrix_eq_meatMatrix (ψ := fun z θ ↦ f z - T θ) (θ := Tinv m) hO
      (hf.sub_const _) hB hzero, ← covMatrix_sub_const hint m]
    simp only [hCC]
  have hsum : ∀ n : ℕ, AEMeasurable (fun ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) μ := by
    intro n
    have h : AEMeasurable (fun ω ↦ ∑ i ∈ range n, f (O i ω)) μ :=
      Finset.aemeasurable_fun_sum _ fun i _ ↦ hf.comp_aemeasurable (hO.aemeasurable i)
    exact h.fun_const_smul _
  refine vectorZEstimator_tendstoInDistribution_of_root (ψ := fun z θ ↦ f z - T θ)
    (J := fun _ _ ↦ -C) (θ₀ := Tinv m) (r := 1) (H := fun _ ↦ ‖(fun k l ↦ C k l : ι → ι → ℝ)‖)
    (θh := fun n ω ↦ Tinv ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)))
    hO one_pos (hf.sub_const _) (fun _ _ _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ ?_) (ae_of_all _ fun z i j ↦ continuousOn_const)
    (integrable_const _) (ae_of_all _ fun z θ _ i j ↦ ?_) hzero hB (by rwa [hbread])
    (fun n ↦ Tinv.continuous.measurable.comp_aemeasurable (hsum n))
    ((hO.tendstoInMeasure_smul_sum hf hint).comp_continuousAt Tinv.continuous.continuousAt)
    (withProbTendingToOne_univ.mono fun n ω _ ↦ sum_sub_mulVec_inv_eq_zero f hC n ω)
    (by rwa [hbread, hmeat])
  · rw [map_neg]
    exact (T.hasFDerivAt).const_sub (f z)
  · rw [Matrix.neg_apply, abs_neg, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm (fun l ↦ C i l) j).trans (norm_le_pi_norm (fun k l ↦ C k l) i)

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ] in
/-- Integrability for the law of the observation is integrability of the composition. -/
lemma integrable_map_iff_comp {G : 𝒪 → ℝ} (hO : IsIIDSample O μ)
    (hG : Measurable G) : Integrable G (μ.map (O 0)) ↔ Integrable (fun ω ↦ G (O 0 ω)) μ :=
  integrable_map_measure hG.aestronglyMeasurable (hO.aemeasurable 0)

/-- **The vector sample mean as a Z-estimator.** The sample mean `P_n f` is the root of
`θ ↦ ∑_{i < n} (f (O i) - θ)`: estimating function `ψ z θ = f z - θ`, Jacobian `-1` and bread the
identity matrix. The case `C = 1` of `linearZEstimator_tendstoInDistribution` gives back the
multivariate central limit theorem `IsIIDSample.tendstoInDistribution_multivariateGaussian`. -/
theorem vectorSampleMean_zEstimator_tendstoInDistribution (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 (covMatrix μ (fun i ω ↦ f (O 0 ω) i))) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω) - μ[fun ω ↦ f (O 0 ω)])) atTop Y
      (fun _ ↦ μ) P' := by
  have hY' : HasLaw Y (multivariateGaussian 0
      ((1 : Matrix ι ι ℝ)⁻¹ * covMatrix μ (fun i ω ↦ f (O 0 ω) i) * (1 : Matrix ι ι ℝ)⁻¹ᵀ)) P' := by
    simpa using hY
  have h := linearZEstimator_tendstoInDistribution hO hf hf2 (C := 1) (by simp) hY'
  simpa using h

/-- **Consistency of the sandwich estimator for the vector sample mean.** For
`ψ z θ = f z - θ` (Jacobian `-1`) and `θh n = P_n f`, every hypothesis of
`sandwichMatrixHat_tendstoInMeasure` holds; the bread is the identity and the meat is the
covariance matrix `Σ` of `f (O 0)`, so every entry of `n` times the sandwich estimate converges in
probability to the corresponding entry of `Σ`. -/
theorem vectorSampleMean_sandwich_tendstoInMeasure (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    (i j : ι) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ ((n : ℝ) • sandwichMatrixHat O (fun z θ ↦ f z - θ)
      (fun _ _ ↦ -1) (fun n ω ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)) n ω) i j) atTop
      (fun _ ↦ covMatrix μ (fun i ω ↦ f (O 0 ω) i) i j) := by
  have hint : Integrable (fun ω ↦ f (O 0 ω)) μ := hf2.integrable one_le_two
  set m := μ[fun ω ↦ f (O 0 ω)]
  have hbread : breadMatrix (μ.map (O 0)) (fun _ _ ↦ -1) m = (1 : Matrix ι ι ℝ) := by
    ext k l
    simp [breadMatrix]
  have hB : MemLp (fun ω ↦ f (O 0 ω) - m) 2 μ := hf2.sub (memLp_const m)
  have hzero : μ[fun ω ↦ f (O 0 ω) - m] = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const]
    simp [m]
  have hmeat : meatMatrix (μ.map (O 0)) (fun z θ ↦ f z - θ) m =
      covMatrix μ (fun i ω ↦ f (O 0 ω) i) := by
    rw [← covMatrix_eq_meatMatrix (ψ := fun z θ ↦ f z - θ) (θ := m) hO (hf.sub_const _) hB
      hzero, covMatrix_sub_const hint m]
  have hGm : Measurable fun z ↦ 2 * ‖f z‖ ^ 2 + 2 * (‖m‖ + 1) ^ 2 := by fun_prop
  have hG : Integrable (fun z ↦ 2 * ‖f z‖ ^ 2 + 2 * (‖m‖ + 1) ^ 2) (μ.map (O 0)) := by
    rw [integrable_map_iff_comp hO hGm]
    exact (((memLp_two_iff_integrable_sq_norm hf2.aestronglyMeasurable).1 hf2).const_mul 2).add
      (integrable_const _)
  have h := sandwichMatrixHat_tendstoInMeasure (ψ := fun z θ ↦ f z - θ) (J := fun _ _ ↦ -1)
    (θ₀ := m) (r := 1) (H := fun _ ↦ 1)
    (θh := fun n ω ↦ (n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)) hO one_pos
    (fun θ _ ↦ hf.sub_const θ) (fun _ _ _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ ?_) (ae_of_all _ fun z i j ↦ continuousOn_const)
    (integrable_const _) (ae_of_all _ fun z θ _ k l ↦ ?_) hG (ae_of_all _ fun z θ hθ ↦ ?_)
    (by rw [hbread]; simp) (hO.tendstoInMeasure_smul_sum hf hint) i j
  · rwa [hbread, hmeat, inv_one, one_mul, transpose_one, mul_one] at h
  · rw [map_neg, map_one]
    exact (hasFDerivAt_id θ).const_sub (f z)
  · rw [Matrix.neg_apply, abs_neg, Matrix.one_apply]
    split_ifs <;> simp
  · have hθ' : ‖θ‖ ≤ ‖m‖ + 1 := norm_le_of_mem_closedBall hθ
    have h1 : ‖f z - θ‖ ≤ ‖f z‖ + ‖θ‖ := norm_sub_le _ _
    have h2 : (‖f z‖ + ‖θ‖) ^ 2 ≤ 2 * ‖f z‖ ^ 2 + 2 * ‖θ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f z‖ - ‖θ‖)]
    have h3 : ‖θ‖ ^ 2 ≤ (‖m‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hθ' 2
    calc ‖f z - θ‖ ^ 2 ≤ (‖f z‖ + ‖θ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ 2 * ‖f z‖ ^ 2 + 2 * ‖θ‖ ^ 2 := h2
      _ ≤ 2 * ‖f z‖ ^ 2 + 2 * (‖m‖ + 1) ^ 2 := by linarith

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ] in
/-- The vector sample mean is almost everywhere measurable. -/
lemma aemeasurable_smul_sum [Finite ι] (hO : IsIIDSample O μ) {f : 𝒪 → EuclideanSpace ℝ ι}
    (hf : Measurable f) (n : ℕ) :
    AEMeasurable (fun ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) μ := by
  have := Fintype.ofFinite ι
  have h : AEMeasurable (fun ω ↦ ∑ i ∈ range n, f (O i ω)) μ :=
    Finset.aemeasurable_fun_sum _ fun i _ ↦ hf.comp_aemeasurable (hO.aemeasurable i)
  exact h.fun_const_smul _

/-- **Asymptotic linearity of the coordinates of a Z-estimator with a non identity bread.** In
the setting of `linearZEstimator_tendstoInDistribution`, every hypothesis of
`vectorZEstimator_isAsymptoticallyLinear` holds: each coordinate of `θh n = C⁻¹ (P_n f)` is
asymptotically linear with influence function `z ↦ (C⁻¹ (f z - m))ᵢ`. -/
theorem linearZEstimator_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {C : Matrix ι ι ℝ} (hC : C.det ≠ 0) (i : ι) :
    IsAsymptoticallyLinear (fun n ω ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹
        ((n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)) i)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹ (μ[fun ω ↦ f (O 0 ω)]) i)
      (fun z ↦ (C⁻¹ *ᵥ WithLp.ofLp (f z - μ[fun ω ↦ f (O 0 ω)])) i) O μ := by
  have hroot : TendstoInMeasure μ (fun (n : ℕ) ω ↦ √(n : ℝ) • ((n : ℝ)⁻¹ •
      ∑ k ∈ range n, (f (O k ω) - Matrix.toEuclideanCLM (𝕜 := ℝ) C
        (Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹ ((n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω))))))
      atTop (fun _ ↦ 0) := by
    simp only [sum_sub_mulVec_inv_eq_zero f hC, smul_zero]
    exact tendstoInMeasure_const 0
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.2 hC
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) C
  set Tinv := Matrix.toEuclideanCLM (𝕜 := ℝ) C⁻¹
  have hCC : ∀ v, T (Tinv v) = v := fun v ↦ by
    have h1 : T * Tinv = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv C hCu, map_one]
    exact congrArg (fun S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι ↦ S v) h1
  have hint : Integrable (fun ω ↦ f (O 0 ω)) μ := hf2.integrable one_le_two
  set m := μ[fun ω ↦ f (O 0 ω)]
  have hbread : breadMatrix (μ.map (O 0)) (fun _ _ ↦ -C) (Tinv m) = C := by
    ext i j
    simp [breadMatrix]
  have hB : MemLp (fun ω ↦ f (O 0 ω) - T (Tinv m)) 2 μ := by
    simp only [hCC]
    exact hf2.sub (memLp_const m)
  have hzero : μ[fun ω ↦ f (O 0 ω) - T (Tinv m)] = 0 := by
    simp only [hCC]
    rw [integral_sub hint (integrable_const _), integral_const]
    simp [m]
  have h := vectorZEstimator_isAsymptoticallyLinear (ψ := fun z θ ↦ f z - T θ)
    (J := fun _ _ ↦ -C) (θ₀ := Tinv m) (r := 1) (H := fun _ ↦ ‖(fun k l ↦ C k l : ι → ι → ℝ)‖)
    (θh := fun n ω ↦ Tinv ((n : ℝ)⁻¹ • ∑ k ∈ range n, f (O k ω)))
    hO one_pos (hf.sub_const _) (fun _ _ _ _ ↦ measurable_const)
    (ae_of_all _ fun z θ _ ↦ ?_) (ae_of_all _ fun z i j ↦ continuousOn_const)
    (integrable_const _) (ae_of_all _ fun z θ _ i j ↦ ?_) hzero hB (by rwa [hbread])
    ((hO.tendstoInMeasure_smul_sum hf hint).comp_continuousAt Tinv.continuous.continuousAt)
    hroot i
  · rw [hbread] at h
    simpa only [hCC] using h
  · rw [map_neg]
    exact (T.hasFDerivAt).const_sub (f z)
  · rw [Matrix.neg_apply, abs_neg, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm (fun l ↦ C i l) j).trans (norm_le_pi_norm (fun k l ↦ C k l) i)

/-! ### Joint normality, the delta method and Slutsky's theorem -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The vector delta method for a linear map of the sample mean.** For `g x = D x`, every
hypothesis of `IsIIDSample.delta_method_multivariateGaussian` holds, and
`√n (D (P_n f) - D m) → N(0, D Σ Dᵀ)`. -/
theorem matrixCLM_sampleMean_tendstoInDistribution (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    (D : Matrix κ ι ℝ) {Y : Ω' → EuclideanSpace ℝ κ}
    (hY : HasLaw Y (multivariateGaussian 0
      (D * covMatrix μ (fun i ω ↦ f (O 0 ω) i) * Dᵀ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (matrixCLM D ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) - matrixCLM D (μ[fun ω ↦ f (O 0 ω)])))
      atTop Y (fun _ ↦ μ) P' :=
  hO.delta_method_multivariateGaussian hf hf2 (matrixCLM D).hasFDerivAt
    (fun n ↦ (((matrixCLM D).continuous.measurable.comp_aemeasurable
      (aemeasurable_smul_sum hO hf n)).sub_const _).fun_const_smul _) hY

omit [DecidableEq ι] [IsProbabilityMeasure μ] in
/-- The coordinates of `f` are measurable and square integrable. -/
lemma measurable_memLp_apply {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f)
    (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ) (i : ι) :
    Measurable (fun z ↦ f z i) ∧ MemLp (fun ω ↦ f (O 0 ω) i) 2 μ :=
  ⟨(EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp hf,
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hf2⟩

/-- **Joint normality of the coordinate sample means.** The coordinate sample means
`sampleMean (f · i) O` are asymptotically linear (`sampleMean_isAsymptoticallyLinear`), so every
hypothesis of `IsAsymptoticallyLinear.tendstoInDistribution_multivariateGaussian` holds; the
influence functions are the centered coordinates `f z i - mᵢ`. -/
theorem sampleMean_apply_tendstoInDistribution (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 (covMatrix μ fun i ω ↦
      f (O 0 ω) i - μ[fun ω ↦ f (O 0 ω) i])) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (fun i ↦ sampleMean (fun z ↦ f z i) O n ω) -
        WithLp.toLp 2 (fun i ↦ μ[fun ω ↦ f (O 0 ω) i]) : EuclideanSpace ℝ ι)) atTop Y
      (fun _ ↦ μ) P' :=
  IsAsymptoticallyLinear.tendstoInDistribution_multivariateGaussian hO
    (fun i ↦ sampleMean_isAsymptoticallyLinear (measurable_memLp_apply hf hf2 i).1
      (measurable_memLp_apply hf hf2 i).2)
    (fun i _ ↦ (Finset.aemeasurable_fun_sum _ fun k _ ↦
      (measurable_memLp_apply hf hf2 i).1.comp_aemeasurable (hO.aemeasurable k)).const_mul _)
    hY

/-- **The delta method for the coordinate sample means.** For `g x = D x`, every hypothesis of
`IsAsymptoticallyLinear.delta_method_multivariateGaussian` holds for the coordinate sample
means. -/
theorem matrixCLM_sampleMean_apply_tendstoInDistribution (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    (D : Matrix κ ι ℝ) {Y : Ω' → EuclideanSpace ℝ κ}
    (hY : HasLaw Y (multivariateGaussian 0 (D * covMatrix μ (fun i ω ↦
      f (O 0 ω) i - μ[fun ω ↦ f (O 0 ω) i]) * Dᵀ)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (matrixCLM D (WithLp.toLp 2 (fun i ↦ sampleMean (fun z ↦ f z i) O n ω)) -
        matrixCLM D (WithLp.toLp 2 (fun i ↦ μ[fun ω ↦ f (O 0 ω) i])))) atTop Y
      (fun _ ↦ μ) P' := by
  have hm : ∀ i n, AEMeasurable (sampleMean (fun z ↦ f z i) O n) μ := fun i n ↦
    (Finset.aemeasurable_fun_sum _ fun k _ ↦
      (measurable_memLp_apply hf hf2 i).1.comp_aemeasurable (hO.aemeasurable k)).const_mul _
  have hvec : ∀ n, AEMeasurable (fun ω ↦ (WithLp.toLp 2 (fun i ↦
      sampleMean (fun z ↦ f z i) O n ω) : EuclideanSpace ℝ ι)) μ := fun n ↦
    (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable (AEMeasurable.of_eval fun i ↦ hm i n)
  exact IsAsymptoticallyLinear.delta_method_multivariateGaussian hO
    (fun i ↦ sampleMean_isAsymptoticallyLinear (measurable_memLp_apply hf hf2 i).1
      (measurable_memLp_apply hf hf2 i).2) hm (matrixCLM D).hasFDerivAt
    (fun n ↦ (((matrixCLM D).continuous.measurable.comp_aemeasurable (hvec n)).sub_const
      _).fun_const_smul _) hY

/-- **Slutsky's theorem for an inner product, an instance.** With a second measurable `g` with
`g (O 0)` integrable, `⟪P_n g, √n (P_n f - m)⟫ → ⟪E g (O 0), Y⟫` in distribution, for `Y` with
law `N(0, Σ)`: every hypothesis of `TendstoInDistribution.inner_tendstoInMeasure` holds. -/
theorem inner_sampleMean_tendstoInDistribution (hO : IsIIDSample O μ)
    {f g : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    (hg : Measurable g) (hg1 : Integrable (fun ω ↦ g (O 0 ω)) μ) {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 (covMatrix μ fun i ω ↦ f (O 0 ω) i)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ ⟪(n : ℝ)⁻¹ • ∑ i ∈ range n, g (O i ω),
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω) - μ[fun ω ↦ f (O 0 ω)])⟫) atTop
      (fun ω ↦ ⟪μ[fun ω ↦ g (O 0 ω)], Y ω⟫) (fun _ ↦ μ) P' :=
  (hO.tendstoInDistribution_multivariateGaussian hf hf2 hY).inner_tendstoInMeasure
    (hO.tendstoInMeasure_smul_sum hg hg1) (aemeasurable_smul_sum hO hg)

omit [DecidableEq κ] in
/-- **Slutsky's theorem for a random matrix, an instance.** For a measurable matrix valued `h`
with integrable entries, the entrywise sample mean `C n` of `h (O i)` converges entrywise in
probability to `E h (O 0)`, and `C n √n (P_n f - m) → (E h (O 0)) Y` in distribution: every
hypothesis of `TendstoInDistribution.matrixCLM_tendstoInMeasure` holds. -/
theorem matrixCLM_sampleMean_mul_tendstoInDistribution (hO : IsIIDSample O μ)
    {f : 𝒪 → EuclideanSpace ℝ ι} (hf : Measurable f) (hf2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ)
    {h : 𝒪 → Matrix κ ι ℝ} (hh : ∀ k i, Measurable fun z ↦ h z k i)
    (hh1 : ∀ k i, Integrable (fun ω ↦ h (O 0 ω) k i) μ) {Y : Ω' → EuclideanSpace ℝ ι}
    (hY : HasLaw Y (multivariateGaussian 0 (covMatrix μ fun i ω ↦ f (O 0 ω) i)) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      matrixCLM (Matrix.of fun k i ↦ sampleMean (fun z ↦ h z k i) O n ω)
        (√(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω) - μ[fun ω ↦ f (O 0 ω)]))) atTop
      (fun ω ↦ matrixCLM (Matrix.of fun k i ↦ μ[fun ω ↦ h (O 0 ω) k i]) (Y ω)) (fun _ ↦ μ) P' := by
  have hX : TendstoInDistribution (fun (n : ℕ) ω ↦
      √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω) - μ[fun ω ↦ f (O 0 ω)])) atTop Y
      (fun _ ↦ μ) P' := hO.tendstoInDistribution_multivariateGaussian hf hf2 hY
  have hC : ∀ k i, TendstoInMeasure μ (fun (n : ℕ) ω ↦ sampleMean (fun z ↦ h z k i) O n ω)
      atTop (fun _ ↦ μ[fun ω ↦ h (O 0 ω) k i]) := fun k i ↦ by
    have h1 := hO.tendstoInMeasure_smul_sum (hh k i) (hh1 k i)
    simp only [smul_eq_mul] at h1
    exact h1
  have hCm : ∀ (n : ℕ) k i, AEMeasurable (fun ω ↦ sampleMean (fun z ↦ h z k i) O n ω) μ :=
    fun n k i ↦ (Finset.aemeasurable_fun_sum _ fun l _ ↦
      (hh k i).comp_aemeasurable (hO.aemeasurable l)).const_mul _
  exact TendstoInDistribution.matrixCLM_tendstoInMeasure
    (C := fun n ω ↦ Matrix.of fun k i ↦ sampleMean (fun z ↦ h z k i) O n ω)
    (C₀ := Matrix.of fun k i ↦ μ[fun ω ↦ h (O 0 ω) k i]) hX hC hCm

end CausalInference
