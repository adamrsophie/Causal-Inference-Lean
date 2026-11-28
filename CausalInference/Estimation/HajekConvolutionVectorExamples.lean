/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekRegularLinearVector
public import CausalInference.Estimation.BernoulliPairLikelihoodTests
public import CausalInference.Estimation.DeltaMethodMultivariate
public import CausalInference.Estimation.HajekConvolutionExamples

/-!
# The Hájek convolution bound for a pair of Bernoulli parameters

The family `bernoulliPair` of two independent Bernoulli observations with success probabilities
`θ = (θ₀, θ₁) ∈ (0, 1)²` satisfies every hypothesis of the vector theory at every interior
point: it is regular (`bernoulliPair_isRegularAtVec`), its score is regular
(`bernoulliPair_isScoreRegularVec`), its information matrix is the positive definite diagonal
matrix `diag(1 / (θ₀ (1 - θ₀)), 1 / (θ₁ (1 - θ₁)))` (`bernoulliPair_fisherInfoMatrix`), and the
sample space is finite, so every line is measurable.

## Main results

* `CausalInference.ParametricFamily.bernoulliPair_pairMeanVec_isHajekRegularVec`: the vector of the
  two sample means is regular with limit `N(0, I(θ)⁻¹)` and asymptotically efficient.
* `CausalInference.ParametricFamily.bernoulliPair_covAdjusted_isHajekRegularVec`: the estimator
  `(X̄ + (\overline{XY} - X̄ Ȳ), Ȳ)`, which adds the sample covariance of the two coordinates to
  the first mean, is regular with limit `N(0, V)`,
  `V = diag(θ₀ (1 - θ₀) (1 + θ₁ (1 - θ₁)), θ₁ (1 - θ₁))`, so that
  `V - I(θ)⁻¹ = diag(θ₀ (1 - θ₀) θ₁ (1 - θ₁), 0)` is positive semidefinite and not zero: the
  estimator is regular and not efficient; `bernoulliPair_covAdjusted_convolution` gives its
  convolution decomposition and `covAdjusted_hajek_bound`, `covAdjusted_sum_hajek_bound` the
  vector and functional bounds with no remaining hypothesis.
* `CausalInference.ParametricFamily.bernoulliPair_clipStat_isHajekRegularVec`: the maximum
  likelihood estimator (the clipped sample means) is regular and efficient.
* `CausalInference.ParametricFamily.bernoulliPair_line_hypotheses` and
  `bernoulliPair_line_fisherInfo`: the line submodels of the pair family.
* `CausalInference.ParametricFamily.bernoulliSampleMean_isAsymptoticallyEfficient`: the scalar
  equality case for the sample proportion.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric Matrix
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → Bool × Bool} {θ₀ : Fin 2 → ℝ}

/-! ### The hypotheses of the vector theory -/

/-- Every line through a point of the pair family is measurable, the sample space being
finite. -/
theorem bernoulliPair_lineMeasurable (θ₀ u : Fin 2 → ℝ) : bernoulliPair.LineMeasurable θ₀ u :=
  lineMeasurable_of_discrete _ _ _

/-- The inverse information matrix of the pair applied to the score is the centered pair of
success indicators: `I(θ)⁻¹ s(θ; x) = (1{x₁} - θ₀, 1{x₂} - θ₁)`. -/
theorem bernoulliPair_inv_mulVec_scoreVec {θ : Fin 2 → ℝ} (hθ : θ ∈ bernoulliPair.Θ)
    (x : Bool × Bool) :
    (bernoulliPair.fisherInfoMatrix θ)⁻¹ *ᵥ bernoulliPair.scoreVec θ x =
      ![successIndicator x.1 - θ 0, successIndicator x.2 - θ 1] := by
  have a1 : 1 - θ 0 ≠ 0 := by linarith [hθ.1.2]
  have b1 : 1 - θ 1 ≠ 0 := by linarith [hθ.2.2]
  have a0 := hθ.1.1.ne'
  have b0 := hθ.2.1.ne'
  rw [bernoulliPair_inv_fisherInfoMatrix hθ, bernoulliPair_scoreVec hθ]
  funext j
  rw [mulVec_diagonal]
  fin_cases j <;> obtain ⟨b, c⟩ := x <;> cases b <;> cases c <;>
    simp [score, bernoulli_densityDeriv, bernoulli_density, successIndicator] <;>
    field_simp

/-! ### Sample means -/

/-- The sample mean `n⁻¹ ∑ᵢ f(xᵢ)` of a sample `x` of size `n`. -/
noncomputable def finMean {n : ℕ} (f : Bool × Bool → ℝ) (x : Fin n → Bool × Bool) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (x i)

/-- On the first `n` observations the sample mean is `sampleMean`. -/
theorem finMean_sample (f : Bool × Bool → ℝ) (n : ℕ) (ω : Ω) :
    finMean f (fun i : Fin n ↦ O i ω) = sampleMean f O n ω := by
  rw [finMean, sampleMean, Fin.sum_univ_eq_sum_range (fun i ↦ f (O i ω)) n]

/-- **The sample mean of a function of the pair is asymptotically linear** at its mean under
`P_θ₀`, with influence function `f - E_θ₀[f]`. -/
theorem isAsymptoticallyLinear_finMean (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulliPair.law θ₀) (hθ₀ : θ₀ ∈ bernoulliPair.Θ)
    (f : Bool × Bool → ℝ) :
    IsAsymptoticallyLinear (fun n ω ↦ finMean f (fun i : Fin n ↦ O i ω))
      (∫ x, f x ∂bernoulliPair.law θ₀) (fun x ↦ f x - ∫ x, f x ∂bernoulliPair.law θ₀) O μ := by
  have := isProbabilityMeasure_law hθ₀
  have hmean : μ[fun ω ↦ f (O 0 ω)] = ∫ x, f x ∂bernoulliPair.law θ₀ := by
    rw [← hlaw, integral_map (hO.aemeasurable 0) Measurable.of_discrete.aestronglyMeasurable]
  have hmem : MemLp (fun ω ↦ f (O 0 ω)) 2 μ :=
    (memLp_map_measure_iff Measurable.of_discrete.aestronglyMeasurable (hO.aemeasurable 0)).1
      (by rw [hlaw]; exact MemLp.of_discrete)
  have h := sampleMean_isAsymptoticallyLinear (O := O) Measurable.of_discrete hmem
  rw [hmean] at h
  simpa only [finMean_sample] using h

/-- The vector `(X̄, Ȳ)` of the two sample means of a sample of size `n`. -/
noncomputable def pairMeanVec (n : ℕ) (x : Fin n → Bool × Bool) : Fin 2 → ℝ :=
  ![finMean (fun z ↦ successIndicator z.1) x, finMean (fun z ↦ successIndicator z.2) x]

/-- **The vector of the two sample means is regular and efficient.** At every `θ₀ ∈ (0, 1)²`, on
every i.i.d. sample with law `P_θ₀`, the vector of the two sample means is regular at `θ₀` with
limit `N(0, I(θ₀)⁻¹) = N(0, diag(θ₀ (1 - θ₀), θ₁ (1 - θ₁)))` and asymptotically efficient. Its
coordinates are asymptotically linear with influence functions `1{x₁} - θ₀` and `1{x₂} - θ₁`,
which are the coordinates of `I(θ₀)⁻¹ s(θ₀; ·)`. -/
theorem bernoulliPair_pairMeanVec_isHajekRegularVec (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulliPair.law θ₀) (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    bernoulliPair.IsHajekRegularVec pairMeanVec θ₀
        (multivariateGaussian 0 (diagonal ![θ₀ 0 * (1 - θ₀ 0), θ₀ 1 * (1 - θ₀ 1)])) ∧
      bernoulliPair.IsAsymptoticallyEfficientVec (fun n ω ↦ pairMeanVec n fun i ↦ O i ω) θ₀ μ := by
  have hlin : ∀ j, IsAsymptoticallyLinear (fun n ω ↦ pairMeanVec n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ ((bernoulliPair.fisherInfoMatrix θ₀)⁻¹ *ᵥ bernoulliPair.scoreVec θ₀ x) j)
      O μ := by
    intro j
    simp_rw [bernoulliPair_inv_mulVec_scoreVec hθ₀]
    fin_cases j
    · have h := isAsymptoticallyLinear_finMean hO hlaw hθ₀ fun z ↦ successIndicator z.1
      have e : ∫ x, successIndicator x.1 ∂bernoulliPair.law θ₀ = θ₀ 0 := by
        rw [bernoulliPair_integral_law hθ₀]; simp [successIndicator]; ring
      rw [e] at h
      exact h
    · have h := isAsymptoticallyLinear_finMean hO hlaw hθ₀ fun z ↦ successIndicator z.2
      have e : ∫ x, successIndicator x.2 ∂bernoulliPair.law θ₀ = θ₀ 1 := by
        rw [bernoulliPair_integral_law hθ₀]; simp [successIndicator]; ring
      rw [e] at h
      exact h
  have h := isHajekRegularVec_of_isAsymptoticallyLinear_inv hO hlaw
    (bernoulliPair_isRegularAtVec hθ₀) (bernoulliPair_isScoreRegularVec hθ₀)
    (bernoulliPair_fisherInfoMatrix_posDef hθ₀) (bernoulliPair_lineMeasurable θ₀)
    (fun _ ↦ .of_discrete) hlin
  rwa [bernoulliPair_inv_fisherInfoMatrix hθ₀] at h

/-! ### The bounds in the pair family -/

/-- **The Hájek bound in the pair family.** At every `θ₀ ∈ (0, 1)²`, every estimator of `θ`
regular at `θ₀` with limit `N(0, V)` has `V - diag(θ₀ (1 - θ₀), θ₁ (1 - θ₁))` positive
semidefinite, every hypothesis of `hajek_convolution_bound_vec` being verified. -/
theorem bernoulliPair_hajek_convolution_bound_vec (hθ₀ : θ₀ ∈ bernoulliPair.Θ)
    {T : ∀ n, (Fin n → Bool × Bool) → Fin 2 → ℝ} {V : Matrix (Fin 2) (Fin 2) ℝ}
    (hV : V.PosSemidef) (hT : bernoulliPair.IsHajekRegularVec T θ₀ (multivariateGaussian 0 V)) :
    (V - diagonal ![θ₀ 0 * (1 - θ₀ 0), θ₀ 1 * (1 - θ₀ 1)]).PosSemidef := by
  have h := (hajek_convolution_bound_vec (bernoulliPair_isRegularAtVec hθ₀)
    (bernoulliPair_isScoreRegularVec hθ₀) (bernoulliPair_fisherInfoMatrix_posDef hθ₀)
    (fun a ↦ bernoulliPair_lineMeasurable θ₀ _) hV hT).2
  rwa [bernoulliPair_inv_fisherInfoMatrix hθ₀] at h

/-- **The Hájek bound for a functional in the pair family.** At every `θ₀ ∈ (0, 1)²`, for a
functional `ψ` with gradient `g` at `θ₀`, every estimator of `ψ` regular at `θ₀` with limit
`N(0, W)` has `θ₀ (1 - θ₀) g₀² + θ₁ (1 - θ₁) g₁² ≤ W`. -/
theorem bernoulliPair_hajek_convolution_bound_functional (hθ₀ : θ₀ ∈ bernoulliPair.Θ)
    {ψ : (Fin 2 → ℝ) → ℝ} {g : Fin 2 → ℝ} (hψ : HasFDerivAt ψ (gradCLM g) θ₀)
    {T : ∀ n, (Fin n → Bool × Bool) → ℝ} {W : ℝ≥0}
    (hT : bernoulliPair.IsHajekRegularFunctional T ψ θ₀ (gaussianReal 0 W)) :
    θ₀ 0 * (1 - θ₀ 0) * g 0 ^ 2 + θ₀ 1 * (1 - θ₀ 1) * g 1 ^ 2 ≤ W := by
  have h := hajek_convolution_bound_functional (bernoulliPair_isRegularAtVec hθ₀)
    (bernoulliPair_isScoreRegularVec hθ₀) (bernoulliPair_fisherInfoMatrix_posDef hθ₀) hψ
    (bernoulliPair_lineMeasurable θ₀ _) hT
  rw [bernoulliPair_inv_fisherInfoMatrix hθ₀] at h
  convert h using 1
  simp [dotProduct, Fin.sum_univ_two, mulVec_diagonal]
  ring

/-! ### A regular estimator that is not efficient -/

/-- The estimator `(X̄ + (\overline{XY} - X̄ Ȳ), Ȳ)`: the first sample mean plus the sample
covariance of the two coordinates, and the second sample mean. -/
noncomputable def covAdjusted (n : ℕ) (x : Fin n → Bool × Bool) : Fin 2 → ℝ :=
  ![finMean (fun z ↦ successIndicator z.1) x +
      (finMean (fun z ↦ successIndicator z.1 * successIndicator z.2) x -
        finMean (fun z ↦ successIndicator z.1) x * finMean (fun z ↦ successIndicator z.2) x),
    finMean (fun z ↦ successIndicator z.2) x]

/-- The influence function of `covAdjusted`:
`((1{x₁} - θ₀) + (1{x₁} - θ₀)(1{x₂} - θ₁), 1{x₂} - θ₁)`. -/
noncomputable def covAdjustedInfluence (θ₀ : Fin 2 → ℝ) (x : Bool × Bool) : Fin 2 → ℝ :=
  ![(successIndicator x.1 - θ₀ 0) +
      (successIndicator x.1 - θ₀ 0) * (successIndicator x.2 - θ₀ 1),
    successIndicator x.2 - θ₀ 1]

/-- **`covAdjusted` is asymptotically linear.** Its first coordinate is the smooth function
`g(a, b, c) = a + (c - a b)` of the three sample means of `1{x₁}`, `1{x₂}` and `1{x₁} 1{x₂}`
(the multivariate delta method, `IsAsymptoticallyLinear.comp_hasFDerivAt`), and the sample
covariance has the mean `0` of the covariance of the two independent coordinates. -/
theorem isAsymptoticallyLinear_covAdjusted (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulliPair.law θ₀) (hθ₀ : θ₀ ∈ bernoulliPair.Θ) (j : Fin 2) :
    IsAsymptoticallyLinear (fun n ω ↦ covAdjusted n (fun i ↦ O i ω) j) (θ₀ j)
      (fun x ↦ covAdjustedInfluence θ₀ x j) O μ := by
  have hm1 : ∫ x, successIndicator x.2 ∂bernoulliPair.law θ₀ = θ₀ 1 := by
    rw [bernoulliPair_integral_law hθ₀]; simp [successIndicator]; ring
  fin_cases j
  swap
  · have h := isAsymptoticallyLinear_finMean hO hlaw hθ₀ fun z ↦ successIndicator z.2
    rw [hm1] at h
    exact h
  let fs : Fin 3 → Bool × Bool → ℝ := ![fun z ↦ successIndicator z.1,
    fun z ↦ successIndicator z.2, fun z ↦ successIndicator z.1 * successIndicator z.2]
  let θv : Fin 3 → ℝ := ![θ₀ 0, θ₀ 1, θ₀ 0 * θ₀ 1]
  have hfs : ∀ i, IsAsymptoticallyLinear (fun n ω ↦ finMean (fs i) fun k : Fin n ↦ O k ω)
      (θv i) (fun x ↦ fs i x - θv i) O μ := by
    intro i
    have h := isAsymptoticallyLinear_finMean hO hlaw hθ₀ (fs i)
    have e : ∫ x, fs i x ∂bernoulliPair.law θ₀ = θv i := by
      rw [bernoulliPair_integral_law hθ₀]
      fin_cases i <;> simp [fs, θv, successIndicator] <;> ring
    rw [e] at h
    exact h
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) θv
  have hg := h0.add ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) θv).sub
    (h0.mul (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) θv)))
  have h := IsAsymptoticallyLinear.comp_hasFDerivAt hO hfs hg
  change IsAsymptoticallyLinear (fun n ω ↦ covAdjusted n (fun i ↦ O i ω) 0) (θ₀ 0)
    (fun x ↦ covAdjustedInfluence θ₀ x 0) O μ
  convert h using 1
  all_goals first
    | rfl
    | (simp [θv]; done)
    | (funext x
       obtain ⟨b, c⟩ := x
       simp only [covAdjustedInfluence, Fin.sum_univ_three, fs, θv]
       cases b <;> cases c <;> simp [successIndicator] <;> ring)

/-- The limit covariance `diag(θ₀ (1 - θ₀) (1 + θ₁ (1 - θ₁)), θ₁ (1 - θ₁))` of `covAdjusted` is
positive semidefinite. -/
theorem covAdjusted_cov_posSemidef (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    (diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)]).PosSemidef := by
  have a0 := hθ₀.1.1
  have a1 : 0 < 1 - θ₀ 0 := by linarith [hθ₀.1.2]
  have b0 := hθ₀.2.1
  have b1 : 0 < 1 - θ₀ 1 := by linarith [hθ₀.2.2]
  rw [posSemidef_diagonal_iff]
  intro i
  fin_cases i
  · exact (by positivity : 0 ≤ θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)))
  · exact (by positivity : 0 ≤ θ₀ 1 * (1 - θ₀ 1))

/-- **`covAdjusted` is regular and not efficient.** At every `θ₀ ∈ (0, 1)²`, on every i.i.d.
sample with law `P_θ₀`, the estimator `covAdjusted` is regular at `θ₀` with limit `N(0, V)`,
`V = diag(θ₀ (1 - θ₀) (1 + θ₁ (1 - θ₁)), θ₁ (1 - θ₁))`; the gap
`V - I(θ₀)⁻¹ = diag(θ₀ (1 - θ₀) θ₁ (1 - θ₁), 0)` is positive semidefinite and not zero, and the
estimator is not asymptotically efficient. -/
theorem bernoulliPair_covAdjusted_isHajekRegularVec (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulliPair.law θ₀) (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    bernoulliPair.IsHajekRegularVec covAdjusted θ₀ (multivariateGaussian 0
        (diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)])) ∧
      diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)] -
          (bernoulliPair.fisherInfoMatrix θ₀)⁻¹ =
        diagonal ![θ₀ 0 * (1 - θ₀ 0) * (θ₀ 1 * (1 - θ₀ 1)), 0] ∧
      (diagonal ![θ₀ 0 * (1 - θ₀ 0) * (θ₀ 1 * (1 - θ₀ 1)), 0]).PosSemidef ∧
      diagonal ![θ₀ 0 * (1 - θ₀ 0) * (θ₀ 1 * (1 - θ₀ 1)), (0 : ℝ)] ≠ 0 ∧
      ¬ bernoulliPair.IsAsymptoticallyEfficientVec (fun n ω ↦ covAdjusted n fun i ↦ O i ω)
        θ₀ μ := by
  have a0 := hθ₀.1.1
  have a1 : 0 < 1 - θ₀ 0 := by linarith [hθ₀.1.2]
  have b0 := hθ₀.2.1
  have b1 : 0 < 1 - θ₀ 1 := by linarith [hθ₀.2.2]
  have hc : crossMoment (bernoulliPair.law θ₀) (covAdjustedInfluence θ₀)
      (bernoulliPair.scoreVec θ₀) = 1 := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [crossMoment, bernoulliPair_integral_law hθ₀, bernoulliPair_scoreVec hθ₀,
        covAdjustedInfluence, score, bernoulli_densityDeriv, bernoulli_density,
        successIndicator] <;> field_simp <;> ring
  have hG : crossMoment (bernoulliPair.law θ₀) (covAdjustedInfluence θ₀)
      (covAdjustedInfluence θ₀) =
        diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)] := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [crossMoment, bernoulliPair_integral_law hθ₀, covAdjustedInfluence,
        successIndicator] <;> ring
  have hT := isHajekRegularVec_of_crossMoment_eq_one hO hlaw (bernoulliPair_isRegularAtVec hθ₀)
    (bernoulliPair_isScoreRegularVec hθ₀) (bernoulliPair_fisherInfoMatrix_posDef hθ₀)
    (bernoulliPair_lineMeasurable θ₀) (fun _ ↦ .of_discrete)
    (isAsymptoticallyLinear_covAdjusted hO hlaw hθ₀) hc
  rw [hG] at hT
  have hgap : diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)] -
      (bernoulliPair.fisherInfoMatrix θ₀)⁻¹ =
        diagonal ![θ₀ 0 * (1 - θ₀ 0) * (θ₀ 1 * (1 - θ₀ 1)), 0] := by
    rw [bernoulliPair_inv_fisherInfoMatrix hθ₀, diagonal_sub]
    congr 1
    funext i
    fin_cases i <;> simp
    ring
  have hpos : 0 < θ₀ 0 * (1 - θ₀ 0) * (θ₀ 1 * (1 - θ₀ 1)) := by positivity
  have hne : diagonal ![θ₀ 0 * (1 - θ₀ 0) * (θ₀ 1 * (1 - θ₀ 1)), (0 : ℝ)] ≠ 0 := by
    intro h0
    have h00 : (diagonal ![θ₀ 0 * (1 - θ₀ 0) * (θ₀ 1 * (1 - θ₀ 1)), (0 : ℝ)]) 0 0 = 0 := by
      rw [h0]; rfl
    rw [diagonal_apply_eq] at h00
    exact hpos.ne' h00
  refine ⟨hT, hgap, ?_, hne, fun heff ↦ hne ?_⟩
  · rw [posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · exact hpos.le
    · simp
  · have hVpsd := covAdjusted_cov_posSemidef hθ₀
    have he := (hajek_eq_iff_isAsymptoticallyEfficientVec hO hlaw
      (bernoulliPair_isRegularAtVec hθ₀) (bernoulliPair_fisherInfoMatrix_posDef hθ₀)
      hVpsd hT).2 heff
    rw [← hgap, he, sub_self]

/-- **The convolution structure of `covAdjusted`** (`hajek_isAsymptoticallyLinear_vec` in the
pair family): its influence function has cross moment `1` with the score, its limit covariance
is `I(θ₀)⁻¹ + E[(φ - I⁻¹ s)(φ - I⁻¹ s)ᵀ]`, and its influence function is not `I(θ₀)⁻¹ s`
almost everywhere. -/
theorem bernoulliPair_covAdjusted_convolution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulliPair.law θ₀) (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    crossMoment (bernoulliPair.law θ₀) (covAdjustedInfluence θ₀)
        (bernoulliPair.scoreVec θ₀) = 1 ∧
      diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)] =
        (bernoulliPair.fisherInfoMatrix θ₀)⁻¹ + crossMoment (bernoulliPair.law θ₀)
          (fun x ↦ covAdjustedInfluence θ₀ x -
            (bernoulliPair.fisherInfoMatrix θ₀)⁻¹ *ᵥ bernoulliPair.scoreVec θ₀ x)
          (fun x ↦ covAdjustedInfluence θ₀ x -
            (bernoulliPair.fisherInfoMatrix θ₀)⁻¹ *ᵥ bernoulliPair.scoreVec θ₀ x) ∧
      ¬ (covAdjustedInfluence θ₀ =ᵐ[bernoulliPair.law θ₀]
        fun x ↦ (bernoulliPair.fisherInfoMatrix θ₀)⁻¹ *ᵥ bernoulliPair.scoreVec θ₀ x) := by
  obtain ⟨hT, hgap, -, hne, -⟩ := bernoulliPair_covAdjusted_isHajekRegularVec hO hlaw hθ₀
  have h := hajek_isAsymptoticallyLinear_vec hO hlaw (bernoulliPair_isRegularAtVec hθ₀)
    (bernoulliPair_isScoreRegularVec hθ₀) (bernoulliPair_fisherInfoMatrix_posDef hθ₀)
    (bernoulliPair_lineMeasurable θ₀) (fun _ ↦ .of_discrete)
    (isAsymptoticallyLinear_covAdjusted hO hlaw hθ₀) (covAdjusted_cov_posSemidef hθ₀) hT
  refine ⟨h.1, h.2.2.1, fun hae ↦ hne ?_⟩
  rw [← hgap, h.2.2.2.2.2 hae, sub_self]

/-- `covAdjusted` is regular at every `θ₀ ∈ (0, 1)²`, as a statement about the sample family
alone: an i.i.d. sample with law `P_θ₀` exists. -/
theorem covAdjusted_isHajekRegularVec (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    bernoulliPair.IsHajekRegularVec covAdjusted θ₀ (multivariateGaussian 0
      (diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)])) := by
  have := isProbabilityMeasure_law hθ₀
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (bernoulliPair.law θ₀)
  exact (bernoulliPair_covAdjusted_isHajekRegularVec hO' (hlaw' 0).map_eq hθ₀).1

/-- **The vector bound for `covAdjusted`**, from `bernoulliPair_hajek_convolution_bound_vec`
with no remaining hypothesis. -/
theorem covAdjusted_hajek_bound (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    (diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)] -
      diagonal ![θ₀ 0 * (1 - θ₀ 0), θ₀ 1 * (1 - θ₀ 1)]).PosSemidef :=
  bernoulliPair_hajek_convolution_bound_vec hθ₀ (covAdjusted_cov_posSemidef hθ₀)
    (covAdjusted_isHajekRegularVec hθ₀)

/-- **The functional bound for `covAdjusted`**: the sum of its coordinates is a regular estimator
of `θ₀ + θ₁` (`IsHajekRegularVec.dotProduct`), and
`bernoulliPair_hajek_convolution_bound_functional` with gradient `(1, 1)` bounds its asymptotic
variance below by `θ₀ (1 - θ₀) + θ₁ (1 - θ₁)`. -/
theorem covAdjusted_sum_hajek_bound (hθ₀ : θ₀ ∈ bernoulliPair.Θ) :
    θ₀ 0 * (1 - θ₀ 0) * (1 : ℝ) ^ 2 + θ₀ 1 * (1 - θ₀ 1) * (1 : ℝ) ^ 2 ≤
      (![1, 1] ⬝ᵥ (diagonal ![θ₀ 0 * (1 - θ₀ 0) * (1 + θ₀ 1 * (1 - θ₀ 1)), θ₀ 1 * (1 - θ₀ 1)] *ᵥ
        ![1, 1]) : ℝ).toNNReal := by
  have h := (covAdjusted_isHajekRegularVec hθ₀).dotProduct ![1, 1]
  rw [multivariateGaussian_map_inner (covAdjusted_cov_posSemidef hθ₀), WithLp.ofLp_toLp] at h
  have hψ : HasFDerivAt (fun θ : Fin 2 → ℝ ↦ ![1, 1] ⬝ᵥ θ) (gradCLM ![1, 1]) θ₀ :=
    (gradCLM ![(1 : ℝ), 1]).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun θ ↦ (gradCLM_apply _ θ).symm)
  have hb := bernoulliPair_hajek_convolution_bound_functional hθ₀ hψ h
  simpa using hb

/-! ### The maximum likelihood estimator -/

/-- The clipped sample means `max ε (min (1 - ε) X̄)` and `max ε (min (1 - ε) Ȳ)`, as a statistic
of a sample of size `n`. -/
noncomputable def clipStat (ε : ℝ) (n : ℕ) (x : Fin n → Bool × Bool) : Fin 2 → ℝ :=
  ![max ε (min (1 - ε) (finMean (fun z ↦ successIndicator z.1) x)),
    max ε (min (1 - ε) (finMean (fun z ↦ successIndicator z.2) x))]

/-- On the first `n` observations `clipStat` is `bernoulliPairClip`. -/
theorem clipStat_sample (ε : ℝ) (n : ℕ) (ω : Ω) :
    clipStat ε n (fun i ↦ O i ω) = bernoulliPairClip ε O n ω := by
  funext j
  fin_cases j <;> simp [clipStat, bernoulliPairClip, finMean_sample] <;> rfl

/-- **The maximum likelihood estimator of the pair is regular and efficient**
(`mle_isHajekRegularVec` with every hypothesis discharged). For `0 < ε ≤ 1/2` and
`θ₀ ∈ (ε, 1 - ε)²`, the clipped sample means are consistent and solve the likelihood equations
with probability tending to one, so they are regular at `θ₀` with limit
`N(0, diag(θ₀ (1 - θ₀), θ₁ (1 - θ₁)))` and asymptotically efficient. -/
theorem bernoulliPair_clipStat_isHajekRegularVec {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hO : IsIIDSample O μ) (hθ₀ : ∀ j, θ₀ j ∈ Set.Ioo ε (1 - ε))
    (hlaw : μ.map (O 0) = bernoulliPair.law θ₀) :
    bernoulliPair.IsHajekRegularVec (clipStat ε) θ₀
        (multivariateGaussian 0 (diagonal ![θ₀ 0 * (1 - θ₀ 0), θ₀ 1 * (1 - θ₀ 1)])) ∧
      bernoulliPair.IsAsymptoticallyEfficientVec (fun n ω ↦ clipStat ε n fun i ↦ O i ω) θ₀ μ := by
  have hθ := mem_bernoulliPair_Θ_of_eps hε hθ₀
  have he : (fun n ω ↦ clipStat ε n fun i ↦ O i ω) = bernoulliPairClip ε O :=
    funext fun n ↦ funext fun ω ↦ clipStat_sample ε n ω
  have h := mle_isHajekRegularVec hO hlaw (bernoulliPair_isRegularAtVec hθ)
    (bernoulliPair_isScoreRegularVec hθ) (bernoulliPair_fisherInfoMatrix_posDef hθ)
    (bernoulliPair_lineMeasurable θ₀) (fun _ ↦ .of_discrete)
    (by rw [he]; exact bernoulliPairClip_tendstoInMeasure hε hε2 hO hθ₀ hlaw)
    (by simp_rw [clipStat_sample]; exact bernoulliPairClip_root hε hε2 hO hθ₀ hlaw)
  rwa [bernoulliPair_inv_fisherInfoMatrix hθ] at h

/-! ### The line submodels and the scalar equality case -/

/-- The scalar hypotheses hold along every line through a point of the pair family
(`line_hypotheses` with every hypothesis discharged). -/
theorem bernoulliPair_line_hypotheses (hθ₀ : θ₀ ∈ bernoulliPair.Θ) {u : Fin 2 → ℝ}
    (hu : u ≠ 0) :
    (bernoulliPair.line θ₀ u).IsRegularAt 0 ∧ 0 < (bernoulliPair.line θ₀ u).fisherInfo 0 ∧
      ∃ r' > 0, (bernoulliPair.line θ₀ u).IsScoreRegular 0 r' ∧
        ∀ᵐ z ∂(bernoulliPair.line θ₀ u).law 0, ∀ t ∈ closedBall (0 : ℝ) r',
          HasDerivAt (fun s ↦ (bernoulliPair.line θ₀ u).logLik s z)
            ((bernoulliPair.line θ₀ u).score t z) t :=
  line_hypotheses (bernoulliPair_isRegularAtVec hθ₀) (bernoulliPair_isScoreRegularVec hθ₀)
    (bernoulliPair_fisherInfoMatrix_posDef hθ₀) hu (bernoulliPair_lineMeasurable θ₀ u)

/-- The information of the line through `θ₀` in the direction `u` is
`u₀² / (θ₀ (1 - θ₀)) + u₁² / (θ₁ (1 - θ₁))` (`line_fisherInfo`). -/
theorem bernoulliPair_line_fisherInfo (hθ₀ : θ₀ ∈ bernoulliPair.Θ) (u : Fin 2 → ℝ) :
    (bernoulliPair.line θ₀ u).fisherInfo 0 =
      u 0 ^ 2 / (θ₀ 0 * (1 - θ₀ 0)) + u 1 ^ 2 / (θ₀ 1 * (1 - θ₀ 1)) := by
  have a0 := hθ₀.1.1.ne'
  have a1 : 1 - θ₀ 0 ≠ 0 := by linarith [hθ₀.1.2]
  have b0 := hθ₀.2.1.ne'
  have b1 : 1 - θ₀ 1 ≠ 0 := by linarith [hθ₀.2.2]
  rw [line_fisherInfo (bernoulliPair_isRegularAtVec hθ₀), bernoulliPair_fisherInfoMatrix hθ₀]
  simp only [dotProduct, Fin.sum_univ_two, mulVec_diagonal]
  simp
  field_simp

/-- **The sample proportion is asymptotically efficient**, from its regularity
(`bernoulliSampleMean_isHajekRegular`) and `hajek_eq_iff_isAsymptoticallyEfficient`: its limit
variance `p₀ (1 - p₀)` is `I(p₀)⁻¹`. -/
theorem bernoulliSampleMean_isAsymptoticallyEfficient {Q : ℕ → Ω → Bool}
    (hO : IsIIDSample Q μ) {p₀ : ℝ} (hlaw : μ.map (Q 0) = bernoulli.law p₀)
    (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulli.IsAsymptoticallyEfficient (fun n ω ↦ bernoulliSampleMean n fun i ↦ Q i ω) p₀ μ :=
  (hajek_eq_iff_isAsymptoticallyEfficient hO hlaw (bernoulli_isRegularAt hp)
    (bernoulli_fisherInfo_pos hp) (bernoulliSampleMean_isHajekRegular hp)).1 (by
      rw [Real.coe_toNNReal _ (mul_nonneg hp.1.le (by linarith [hp.2])),
        bernoulli_inv_fisherInfo hp])

end ParametricFamily

end CausalInference
