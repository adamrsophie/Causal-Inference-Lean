/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.VectorDeltaMethod
public import CausalInference.Estimation.BernoulliFamily

/-!
# A nonlinear vector delta method: the sample variance

For an i.i.d. sample `Z_i = X(O_i)` with finite fourth moment, the first two sample moments
`(m̂₁, m̂₂) = (n⁻¹ ∑ Z_i, n⁻¹ ∑ Z_i²)` are jointly asymptotically normal by the multivariate
central limit theorem, and the plug-in sample variance `S²_n = m̂₂ - m̂₁²` is their image under
`g(m₁, m₂) = m₂ - m₁²`, a nonlinear map with Jacobian `D = (-2 m₁, 1)` at the population moments.
The vector delta method gives `√n (S²_n - σ²) → N(0, D Σ Dᵀ)` with `σ² = Var(Z)`, `Σ` the
covariance matrix of `(Z, Z²)`, and

`D Σ Dᵀ = 4 m₁² Var(Z) - 4 m₁ cov(Z, Z²) + Var(Z²)`.

For a Bernoulli sample with success probability `p`, `Z² = Z` and the limit variance is
`p (1 - p) (1 - 2 p)²`; for `p = 1 / 4` it is `3 / 64`, with `σ² = 3 / 16`.

## Main definitions

* `CausalInference.momentPair X z = (X z, X z²)` and `CausalInference.varianceMap m = m₂ - m₁²`.
* `CausalInference.sampleVariance X O n ω`: the plug-in sample variance `m̂₂ - m̂₁²`.
* `CausalInference.sampleVarianceAsymptoticVariance μ Z`: the limit variance.

## Main results

* `CausalInference.hasFDerivAt_varianceMap`: the derivative of `g` on `ℝ²`.
* `CausalInference.varianceJacobian_mul_covMatrix_mul_transpose`: the limit variance `D Σ Dᵀ`.
* `CausalInference.sampleVariance_tendstoInDistribution`: **asymptotic normality of the sample
  variance**.
* `CausalInference.bernoulli_sampleVariance_tendstoInDistribution` and
  `bernoulli_sampleVariance_tendstoInDistribution_quarter`: the Bernoulli check.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix

namespace CausalInference

open BiasAnalysis.MeasurementError (covMatrix)

/-- The pair `(X z, X z²)` of the first two powers of an observation. -/
noncomputable def momentPair {𝒪 : Type*} (X : 𝒪 → ℝ) (z : 𝒪) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![X z, X z ^ 2]

/-- The map `g(m₁, m₂) = m₂ - m₁²` from the first two moments to the variance. -/
noncomputable def varianceMap (m : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 fun _ ↦ m 1 - m 0 ^ 2

/-- The Jacobian matrix `(-2 m₁, 1)` of `varianceMap` at `m`. -/
noncomputable def varianceJacobian (m : EuclideanSpace ℝ (Fin 2)) : Matrix (Fin 1) (Fin 2) ℝ :=
  Matrix.of fun _ j ↦ ![-2 * m 0, 1] j

/-- **The derivative of `g(m₁, m₂) = m₂ - m₁²`** on `ℝ²` is `v ↦ -2 m₁ v₁ + v₂`. -/
theorem hasFDerivAt_varianceMap (m : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt varianceMap (matrixCLM (varianceJacobian m)) m := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt (x := m)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt (x := m)
  have hq := h1.sub (h0.pow 2)
  have hpi := (hasFDerivAt_pi (φ := fun (_ : Fin 1) (x : EuclideanSpace ℝ (Fin 2)) ↦
    EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) x -
      EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) x ^ 2)).2 fun _ ↦ hq
  have h := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.hasFDerivAt.comp m hpi
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v ↦ ?_
  ext i
  simp [matrixCLM_apply, varianceJacobian, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- `varianceMap` is continuous. -/
theorem continuous_varianceMap : Continuous varianceMap :=
  continuous_iff_continuousAt.2 fun m ↦ (hasFDerivAt_varianceMap m).continuousAt

/-- The limit variance `4 m₁² Var(Z) - 4 m₁ cov(Z, Z²) + Var(Z²)` of the sample variance,
`m₁ = E Z`. -/
noncomputable def sampleVarianceAsymptoticVariance {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  4 * μ[Z] ^ 2 * Var[Z; μ] - 4 * μ[Z] * cov[Z, Z ^ 2; μ] + Var[Z ^ 2; μ]

/-- The plug-in sample variance `n⁻¹ ∑ X(O_i)² - (n⁻¹ ∑ X(O_i))²`. -/
noncomputable def sampleVariance {Ω 𝒪 : Type*} (X : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    ℝ :=
  sampleMean (fun z ↦ X z ^ 2) O n ω - sampleMean X O n ω ^ 2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
  {𝒪 : Type*} [MeasurableSpace 𝒪] {O : ℕ → Ω → 𝒪}

omit [IsProbabilityMeasure μ] in
/-- **The limit variance** `D Σ Dᵀ` at the population moments `m = (E Z, E Z²)`, with `Σ` the
covariance matrix of `(Z, Z²)`. -/
theorem varianceJacobian_mul_covMatrix_mul_transpose (Z : Ω → ℝ) (hZ : AEMeasurable Z μ)
    (m : EuclideanSpace ℝ (Fin 2)) (hm : m 0 = μ[Z]) :
    varianceJacobian m * covMatrix μ (fun i ω ↦ (WithLp.toLp 2 ![Z ω, Z ω ^ 2] :
      EuclideanSpace ℝ (Fin 2)) i) * (varianceJacobian m)ᵀ =
      Matrix.of fun _ _ ↦ sampleVarianceAsymptoticVariance μ Z := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, transpose_apply, varianceJacobian, of_apply,
    covMatrix, cons_val_zero, cons_val_one, sampleVarianceAsymptoticVariance, hm]
  have c1 : cov[fun ω ↦ Z ω ^ 2, fun x ↦ Z x; μ] = cov[Z, Z ^ 2; μ] := covariance_comm _ _
  have c2 : cov[fun x ↦ Z x, fun x ↦ Z x; μ] = Var[Z; μ] := covariance_self hZ
  have c3 : cov[fun x ↦ Z x, fun ω ↦ Z ω ^ 2; μ] = cov[Z, Z ^ 2; μ] := rfl
  have c4 : cov[fun ω ↦ Z ω ^ 2, fun ω ↦ Z ω ^ 2; μ] = Var[Z ^ 2; μ] :=
    covariance_self (hZ.pow_const 2)
  rw [c1, c2, c3, c4]
  ring

/-- **Asymptotic normality of the sample variance.** For an i.i.d. sample, a measurable `X` with
`X(O 0)` having a finite fourth moment, and `Z = X(O 0)`, the plug-in sample variance satisfies
`√n (S²_n - Var Z) → N(0, 4 (E Z)² Var(Z) - 4 E Z cov(Z, Z²) + Var(Z²))` in distribution, as
vectors in `ℝ¹`. -/
theorem sampleVariance_tendstoInDistribution (hO : IsIIDSample O μ) {X : 𝒪 → ℝ}
    (hX : Measurable X) (hX4 : MemLp (fun ω ↦ X (O 0 ω)) 4 μ)
    {Y' : Ω'' → EuclideanSpace ℝ (Fin 1)}
    (hY' : HasLaw Y' (multivariateGaussian 0
      (Matrix.of fun _ _ ↦ sampleVarianceAsymptoticVariance μ (fun ω ↦ X (O 0 ω)))) P'') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (fun _ ↦ sampleVariance X O n ω) -
        WithLp.toLp 2 (fun _ ↦ Var[fun ω ↦ X (O 0 ω); μ]) : EuclideanSpace ℝ (Fin 1))) atTop Y'
      (fun _ ↦ μ) P'' := by
  set Z : Ω → ℝ := fun ω ↦ X (O 0 ω) with hZdef
  have hZm : AEMeasurable Z μ := hX.comp_aemeasurable (hO.aemeasurable 0)
  have hZ2 : MemLp Z 2 μ := hX4.mono_exponent (by norm_num)
  have hZsq : MemLp (fun ω ↦ Z ω ^ 2) 2 μ := by
    have h4 : MemLp Z ((4 : ℕ) : ENNReal) μ := by exact_mod_cast hX4
    refine (memLp_two_iff_integrable_sq (hX4.aestronglyMeasurable.pow 2)).2 ?_
    convert h4.integrable_norm_pow (by norm_num) using 2 with ω
    rw [Real.norm_eq_abs, Pi.pow_apply, ← pow_mul, Even.pow_abs ⟨2, rfl⟩]
  have hf : Measurable (momentPair X) :=
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_iff.2 (Fin.forall_fin_two.2 ⟨hX, hX.pow_const 2⟩))
  have hf2 : MemLp (fun ω ↦ momentPair X (O 0 ω)) 2 μ :=
    memLp_piLp_iff.2 (Fin.forall_fin_two.2 ⟨hZ2, hZsq⟩)
  set c := μ[fun ω ↦ momentPair X (O 0 ω)] with hc
  have hc0 : c 0 = μ[Z] :=
    eval_integral_piLp (fun j ↦ (hf2.eval_piLp j).integrable one_le_two) 0
  have hc1 : c 1 = μ[fun ω ↦ Z ω ^ 2] :=
    eval_integral_piLp (fun j ↦ (hf2.eval_piLp j).integrable one_le_two) 1
  have hmat := varianceJacobian_mul_covMatrix_mul_transpose Z hZm c hc0
  have hgm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) •
      (varianceMap ((n : ℝ)⁻¹ • ∑ i ∈ range n, momentPair X (O i ω)) - varianceMap c)) μ :=
    fun n ↦ by
      have hs : AEMeasurable (fun ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, momentPair X (O i ω)) μ :=
        (Finset.aemeasurable_fun_sum (range n) fun i _ ↦
          hf.comp_aemeasurable (hO.aemeasurable i)).const_smul ((n : ℝ)⁻¹)
      exact ((continuous_varianceMap.measurable.comp_aemeasurable hs).sub_const _).const_smul
        (√(n : ℝ))
  have h := hO.delta_method_multivariateGaussian hf hf2 (hasFDerivAt_varianceMap c) hgm
    (Y' := Y') (by
      rw [show (fun i ω ↦ momentPair X (O 0 ω) i) =
        fun i ω ↦ (WithLp.toLp 2 ![Z ω, Z ω ^ 2] : EuclideanSpace ℝ (Fin 2)) i from rfl, hmat]
      exact hY')
  convert h using 3 with n ω
  have hvar : Var[Z; μ] = μ[fun ω ↦ Z ω ^ 2] - μ[Z] ^ 2 := variance_eq_sub hZ2
  have hsv : sampleVariance X O n ω =
      ((n : ℝ)⁻¹ • ∑ i ∈ range n, momentPair X (O i ω)) 1 -
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, momentPair X (O i ω)) 0 ^ 2 := by
    simp [sampleVariance, sampleMean, momentPair]
  rw [varianceMap, varianceMap, hc0, hc1, hsv, hvar]

/-! ### The Bernoulli check -/

open ParametricFamily

omit [MeasurableSpace 𝒪] in
/-- The square of a success indicator is the indicator. -/
lemma successIndicator_sq (b : Bool) : successIndicator b ^ 2 = successIndicator b := by
  cases b <;> simp [successIndicator]

/-- **The Bernoulli check.** For an i.i.d. Bernoulli sample with success probability
`p ∈ (0, 1)`, the plug-in sample variance of the success indicators satisfies
`√n (S²_n - p (1 - p)) → N(0, p (1 - p) (1 - 2 p)²)`. -/
theorem bernoulli_sampleVariance_tendstoInDistribution {B : ℕ → Ω → Bool}
    (hB : IsIIDSample B μ) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hlaw : μ.map (B 0) = ParametricFamily.bernoulli.law p)
    {Y' : Ω'' → EuclideanSpace ℝ (Fin 1)}
    (hY' : HasLaw Y' (multivariateGaussian 0
      (Matrix.of fun _ _ ↦ p * (1 - p) * (1 - 2 * p) ^ 2)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (fun _ ↦ sampleVariance successIndicator B n ω) -
        WithLp.toLp 2 (fun _ ↦ p * (1 - p)) : EuclideanSpace ℝ (Fin 1))) atTop Y'
      (fun _ ↦ μ) P'' := by
  have := ParametricFamily.isProbabilityMeasure_law (F := ParametricFamily.bernoulli) hp
  set Z : Ω → ℝ := fun ω ↦ successIndicator (B 0 ω) with hZdef
  have hBm := hB.aemeasurable 0
  have hsm : Measurable successIndicator := .of_discrete
  have hsq : Z ^ 2 = Z := funext fun ω ↦ successIndicator_sq _
  have hE : μ[Z] = p := by
    rw [hZdef, ← integral_map hBm hsm.aestronglyMeasurable, hlaw,
      ParametricFamily.bernoulli_integral_law hp]
    simp [successIndicator]
  have hV : Var[Z; μ] = p * (1 - p) := by
    have h := variance_map (μ := μ) (X := successIndicator) hsm.aemeasurable hBm
    rw [hlaw, variance_eq_sub .of_discrete, ParametricFamily.bernoulli_integral_law hp,
      ParametricFamily.bernoulli_integral_law hp] at h
    rw [← show successIndicator ∘ B 0 = Z from rfl, ← h]
    simp [successIndicator]
    ring
  have hv : sampleVarianceAsymptoticVariance μ Z = p * (1 - p) * (1 - 2 * p) ^ 2 := by
    have hcs : cov[Z, Z; μ] = Var[Z; μ] := covariance_self (hsm.comp_aemeasurable hBm)
    rw [sampleVarianceAsymptoticVariance, hsq, hcs, hE, hV]
    ring
  have h := sampleVariance_tendstoInDistribution hB hsm (X := successIndicator)
    (MemLp.of_bound (hsm.comp_aemeasurable hBm).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by cases B 0 ω <;> simp [successIndicator])) (Y' := Y')
    (by rw [show (fun ω ↦ successIndicator (B 0 ω)) = Z from rfl, hv]; exact hY')
  rwa [show (fun ω ↦ successIndicator (B 0 ω)) = Z from rfl, hV] at h

/-- **The Bernoulli check with computed numbers.** For `p = 1 / 4`, the sample variance
estimates `σ² = 3 / 16` and `√n (S²_n - 3 / 16) → N(0, 3 / 64)`. -/
theorem bernoulli_sampleVariance_tendstoInDistribution_quarter {B : ℕ → Ω → Bool}
    (hB : IsIIDSample B μ) (hlaw : μ.map (B 0) = ParametricFamily.bernoulli.law (1 / 4))
    {Y' : Ω'' → EuclideanSpace ℝ (Fin 1)}
    (hY' : HasLaw Y' (multivariateGaussian 0 (Matrix.of fun _ _ ↦ 3 / 64)) P'') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) •
      (WithLp.toLp 2 (fun _ ↦ sampleVariance successIndicator B n ω) -
        WithLp.toLp 2 (fun _ ↦ 3 / 16) : EuclideanSpace ℝ (Fin 1))) atTop Y'
      (fun _ ↦ μ) P'' := by
  have h := bernoulli_sampleVariance_tendstoInDistribution hB ⟨by norm_num, by norm_num⟩ hlaw
    (Y' := Y') (by norm_num; exact hY')
  norm_num at h
  exact h

end CausalInference
