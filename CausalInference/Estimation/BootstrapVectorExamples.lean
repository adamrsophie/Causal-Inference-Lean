/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.BootstrapExamples
public import CausalInference.Estimation.BootstrapMeanLimitVector
public import CausalInference.Estimation.BootstrapQuantile

/-!
# Examples for the vector bootstrap and for the bootstrap of the mean

* **Two independent fair coins.** The observation is a pair of fair coin flips, independent of
  each other, with law `Bootstrap.coinPairLaw` (mass `1/4` on each of the four outcomes), scored
  as the vector `Bootstrap.coinPairScore = (1{first is heads}, 1{second is heads}) ∈ ℝ²`. Its
  mean is `(1/2, 1/2)` and its covariance matrix is `Σ = diag(1/4, 1/4)`, which is nonsingular.
  Every hypothesis of `Bootstrap.ae_tendsto_inner_sq`,
  `Bootstrap.ae_tendstoInDistribution_resampleMean_euclidean` and
  `Bootstrap.isBernsteinVonMisesWeak_resampleMeanVec` is discharged, with the limits written out:
  `(t₀² + t₀ t₁ + t₁²) / 2` and `N(0, Σ)`.
* **The bootstrap delta method for the difference of two coordinates.** For
  `Ψ(x) = x₀ - x₁ = ⟪(1, -1), x⟫`, the variance of the linearized limit `Ψ(Z)`, `Z ∼ N(0, Σ)`, is
  `1/2 > 0`, and the percentile interval of the bootstrap law of `Ψ(X̄*_n)` covers
  `Ψ(1/2, 1/2) = 0` with probability tending to `1 - α`
  (`Bootstrap.coinPair_bootstrap_delta_coverage`).
* **The ratio of the two coordinates.** For `Ψ(x) = x₀ / x₁`, strictly differentiable at the mean
  `(1/2, 1/2)` with derivative `v ↦ 2 v₀ - 2 v₁`, the linearized limit has variance `2 > 0`, and
  the bootstrap percentile interval covers `Ψ(1/2, 1/2) = 1` with probability tending to `1 - α`
  (`Bootstrap.coinPair_bootstrap_ratio_coverage`).
* **The fair coin again.** For the fair coin of `CausalInference.Estimation.BootstrapExamples`,
  the conditional expectation of `φ(√n (X̄*_n - X̄_n))` given the data converges almost surely to
  `∫ φ dN(0, 1/4)` (`Bootstrap.coin_condExp_resampleMean_tendsto`), and the bootstrap quantiles
  satisfy `√n (q*_n(p) - X̄_n) → z / 2` almost surely when `Φ(z) = p`
  (`Bootstrap.coin_ae_tendsto_bootstrapQuantile`).

## Main definitions

* `Bootstrap.coinPairLaw`, `Bootstrap.coinPairScore`, `Bootstrap.coinPairDiff`,
  `Bootstrap.coinPairRatio`.

## Main results

* `Bootstrap.covMatrix_coinPairScore`, `Bootstrap.det_coinPairCov`: the covariance matrix is
  `diag(1/4, 1/4)`, with determinant `1/16`.
* `Bootstrap.coinPair_ae_tendstoInDistribution_resampleMean`,
  `Bootstrap.coinPair_isBernsteinVonMisesWeak`, `Bootstrap.coinPair_ae_tendsto_inner_sq`,
  `Bootstrap.coinPair_bootstrap_delta_coverage`,
  `Bootstrap.exists_coinPair_bootstrap_delta_coverage`,
  `Bootstrap.coinPair_bootstrap_ratio_coverage`.
* `Bootstrap.coin_condExp_resampleMean_tendsto`, `Bootstrap.coin_ae_tendsto_bootstrapQuantile`,
  with the existence statements `Bootstrap.exists_coin_condExp_resampleMean_tendsto` and
  `Bootstrap.exists_coin_ae_tendsto_bootstrapQuantile`.

## References

* P. J. Bickel and D. A. Freedman (1981), *Some asymptotic theory for the bootstrap*, Annals of
  Statistics 9.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 23.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace CausalInference

namespace Bootstrap

open PosteriorLimit BiasAnalysis.Distributions NetworkMetaAnalysis EffectMeasure
open BiasAnalysis.MeasurementError (covMatrix)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Two independent fair coins -/

/-- The law of two independent fair coin flips: mass `1/4` on each pair of outcomes. -/
noncomputable def coinPairLaw : Measure (Bool × Bool) :=
  stratumLaw fun _ ↦ (1 / 4 : ℝ)

instance isProbabilityMeasure_coinPairLaw : IsProbabilityMeasure coinPairLaw :=
  isProbabilityMeasure_stratumLaw ⟨fun _ ↦ by norm_num, by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    norm_num⟩

/-- The score of a pair of coin flips: the vector `(1{first is heads}, 1{second is heads})`. -/
noncomputable def coinPairScore (b : Bool × Bool) : EuclideanSpace ℝ (Fin 2) :=
  !₂[coinScore b.1, coinScore b.2]

theorem measurable_coinPairScore : Measurable coinPairScore := measurable_of_countable _

@[simp] theorem coinPairScore_zero (b : Bool × Bool) : coinPairScore b 0 = coinScore b.1 := rfl

@[simp] theorem coinPairScore_one (b : Bool × Bool) : coinPairScore b 1 = coinScore b.2 := rfl

section Sample

variable {P : Measure Ω} {O : ℕ → Ω → Bool × Bool}

/-- Expectations of a function of a pair of fair coins: the average of its four values. -/
theorem integral_comp_coinPair (hlaw : HasLaw (O 0) coinPairLaw P) (g : Bool × Bool → ℝ) :
    P[fun ω ↦ g (O 0 ω)] =
      (g (false, false) + g (false, true) + g (true, false) + g (true, true)) / 4 := by
  have h := hlaw.integral_comp (f := g) (measurable_of_countable g).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, coinPairLaw, integral_stratumLaw (fun _ ↦ by norm_num), standardizedRisk,
    Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  ring

/-- The covariance matrix of the score of two independent fair coins is `diag(1/4, 1/4)`. -/
theorem covMatrix_coinPairScore (hlaw : HasLaw (O 0) coinPairLaw P) :
    covMatrix P (fun i ω ↦ coinPairScore (O 0 ω) i) = Matrix.diagonal fun _ ↦ 1 / 4 := by
  have hm : ∀ i : Fin 2, P[fun ω ↦ coinPairScore (O 0 ω) i] = 1 / 2 := by
    intro i
    rw [integral_comp_coinPair hlaw (fun b ↦ coinPairScore b i)]
    fin_cases i <;> simp [coinScore] <;> norm_num
  ext i j
  simp only [covMatrix, Matrix.of_apply, covariance]
  rw [hm i, hm j, integral_comp_coinPair hlaw
    (fun b ↦ (coinPairScore b i - 1 / 2) * (coinPairScore b j - 1 / 2))]
  fin_cases i <;> fin_cases j <;> simp [coinScore] <;> norm_num

variable [IsProbabilityMeasure P]

theorem memLp_coinPairScore (hlaw : HasLaw (O 0) coinPairLaw P) :
    MemLp (fun ω ↦ coinPairScore (O 0 ω)) 2 P :=
  MemLp.of_bound (measurable_coinPairScore.comp_aemeasurable hlaw.aemeasurable).aestronglyMeasurable
    (∑ b, ‖coinPairScore b‖) (ae_of_all _ fun ω ↦
      Finset.single_le_sum (f := fun b ↦ ‖coinPairScore b‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_univ (O 0 ω)))

theorem posSemidef_coinPairCov :
    (Matrix.diagonal fun _ : Fin 2 ↦ (1 / 4 : ℝ)).PosSemidef := by
  obtain ⟨Ω, mΩ, P, O, hP, -, -, hlaw⟩ := exists_isIIDSample coinPairLaw
  rw [← covMatrix_coinPairScore (hlaw 0)]
  exact posSemidef_covMatrix fun i ↦
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (memLp_coinPairScore (hlaw 0))

/-- The covariance matrix `diag(1/4, 1/4)` is nonsingular: its determinant is `1/16`. -/
theorem det_coinPairCov : (Matrix.diagonal fun _ : Fin 2 ↦ (1 / 4 : ℝ)).det = 1 / 16 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  norm_num

/-- The mean of the score of two independent fair coins is `(1/2, 1/2)`. -/
theorem integral_coinPairScore (hlaw : HasLaw (O 0) coinPairLaw P) :
    P[fun ω ↦ coinPairScore (O 0 ω)] = !₂[1 / 2, 1 / 2] := by
  have hi := (memLp_coinPairScore hlaw).integrable one_le_two
  ext i
  have h : (P[fun ω ↦ coinPairScore (O 0 ω)]) i = P[fun ω ↦ coinPairScore (O 0 ω) i] :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).integral_comp_comm hi).symm
  rw [h, integral_comp_coinPair hlaw (fun b ↦ coinPairScore b i)]
  fin_cases i <;> simp [coinScore] <;> norm_num

variable (hO : IsIIDSample O P) (hlaw : HasLaw (O 0) coinPairLaw P)
include hO hlaw

/-- **Directional second moments for two fair coins.** Almost surely, for every `t ∈ ℝ²`,
`n⁻¹ ∑_{k < n} ⟪f(O_k), t⟫² → (t₀² + t₀ t₁ + t₁²) / 2`. -/
theorem coinPair_ae_tendsto_inner_sq :
    ∀ᵐ ω ∂P, ∀ t : EuclideanSpace ℝ (Fin 2), Tendsto (fun n : ℕ ↦
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ⟪coinPairScore (O k ω), t⟫ ^ 2) atTop
      (𝓝 ((t 0 ^ 2 + t 0 * t 1 + t 1 ^ 2) / 2)) := by
  filter_upwards [ae_tendsto_inner_sq hO measurable_coinPairScore (memLp_coinPairScore hlaw)]
    with ω hω t
  convert hω t using 2
  rw [integral_comp_coinPair hlaw (fun b ↦ ⟪coinPairScore b, t⟫ ^ 2)]
  simp [PiLp.inner_apply, Fin.sum_univ_two, coinScore]
  ring

/-- **The vector bootstrap of two fair coins.** For almost every data path, under resampling,
`√n (X̄*_n - X̄_n)` converges in distribution to `N(0, diag(1/4, 1/4))`. -/
theorem coinPair_ae_tendstoInDistribution_resampleMean :
    ∀ᵐ ω ∂P, TendstoInDistribution
      (fun (n : ℕ) (y : Fin n → Bool × Bool) ↦ √(n : ℝ) • ((n : ℝ)⁻¹ • ∑ i, coinPairScore (y i) -
        (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, coinPairScore (O k ω)))
      atTop (fun x ↦ x) (fun n ↦ resampleLaw O n ω)
      (multivariateGaussian 0 (Matrix.diagonal fun _ ↦ 1 / 4)) := by
  have h := ae_tendstoInDistribution_resampleMean_euclidean hO measurable_coinPairScore
    (memLp_coinPairScore hlaw)
  rwa [covMatrix_coinPairScore hlaw] at h

/-- **Conditional weak convergence in probability for two fair coins**, with limit
`N(0, diag(1/4, 1/4))`. -/
theorem coinPair_isBernsteinVonMisesWeak :
    IsBernsteinVonMisesWeak P (bootstrapLaw (resampleMeanVec coinPairScore) O)
      (fun n ω ↦ (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, coinPairScore (O k ω))
      (multivariateGaussian 0 (Matrix.diagonal fun _ ↦ 1 / 4)) := by
  have h := isBernsteinVonMisesWeak_resampleMeanVec hO measurable_coinPairScore
    (memLp_coinPairScore hlaw)
  rwa [covMatrix_coinPairScore hlaw] at h

end Sample

/-! ### The difference of the two coordinates -/

/-- The difference of the two coordinates, `Ψ(x) = x₀ - x₁ = ⟪(1, -1), x⟫`, as a continuous linear
functional. -/
noncomputable def coinPairDiff : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  innerSL ℝ !₂[1, -1]

theorem coinPairDiff_apply (x : EuclideanSpace ℝ (Fin 2)) : coinPairDiff x = x 0 - x 1 := by
  simp [coinPairDiff, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **Variances of projections of the limit law.** For `Z ∼ N(0, diag(1/4, 1/4))` and `t ∈ ℝ²`,
`Var⟪t, Z⟫ = (t₀² + t₁²) / 4`. -/
theorem variance_innerSL_coinPairCov (t : EuclideanSpace ℝ (Fin 2)) :
    Var[innerSL ℝ t; multivariateGaussian 0 (Matrix.diagonal fun _ ↦ 1 / 4)] =
      (t 0 ^ 2 + t 1 ^ 2) / 4 := by
  have h1 := covarianceBilin_self (μ := multivariateGaussian 0
    (Matrix.diagonal fun _ : Fin 2 ↦ (1 / 4 : ℝ))) IsGaussian.memLp_two_id t
  rw [covarianceBilin_multivariateGaussian posSemidef_coinPairCov] at h1
  have h2 : (⇑(innerSL ℝ t)) = fun u ↦ ⟪t, u⟫ := by
    funext u
    simp
  rw [h2, ← h1]
  simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring

/-- **The variance of the linearized limit.** For `Z ∼ N(0, diag(1/4, 1/4))`,
`Var(Z₀ - Z₁) = 1/2`. -/
theorem variance_coinPairDiff :
    Var[coinPairDiff; multivariateGaussian 0 (Matrix.diagonal fun _ ↦ 1 / 4)] = 1 / 2 := by
  rw [coinPairDiff, variance_innerSL_coinPairCov]
  simp
  norm_num

/-- **The bootstrap delta method for two fair coins.** For an i.i.d. sample of pairs of
independent fair coins, `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the percentile interval of the bootstrap
law of `Ψ(X̄*_n)`, `Ψ(x) = x₀ - x₁`, covers `Ψ(1/2, 1/2) = 0` with probability tending to
`1 - α`. -/
theorem coinPair_bootstrap_delta_coverage {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → Bool × Bool} (hO : IsIIDSample O P) (hlaw : HasLaw (O 0) coinPairLaw P)
    {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | (0 : ℝ) ∈ percentileInterval
      ((bootstrapLaw (resampleMeanVec coinPairScore) O n ω).map coinPairDiff) α}) atTop
      (𝓝 (1 - α)) := by
  have hσ : 0 < Var[coinPairDiff;
      multivariateGaussian 0 (covMatrix P fun i ω ↦ coinPairScore (O 0 ω) i)] := by
    rw [covMatrix_coinPairScore hlaw, variance_coinPairDiff]
    norm_num
  have h := tendsto_bootstrap_delta_coverage hO measurable_coinPairScore
    (memLp_coinPairScore hlaw) coinPairDiff.continuous.measurable
    coinPairDiff.hasStrictFDerivAt hσ hα hz
  have h0 : coinPairDiff (P[fun ω ↦ coinPairScore (O 0 ω)]) = 0 := by
    rw [integral_coinPairScore hlaw, coinPairDiff_apply]
    simp
  rwa [h0] at h

/-- **The two coin example is not vacuous.** There is a probability space carrying an i.i.d.
sample of pairs of independent fair coins, and on it the bootstrap delta method interval for
`x₀ - x₁` covers `0` with probability tending to `1 - α`. -/
theorem exists_coinPair_bootstrap_delta_coverage {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → Bool × Bool,
      IsProbabilityMeasure P ∧ IsIIDSample O P ∧ HasLaw (O 0) coinPairLaw P ∧
        Tendsto (fun n ↦ P.real {ω | (0 : ℝ) ∈ percentileInterval
          ((bootstrapLaw (resampleMeanVec coinPairScore) O n ω).map coinPairDiff) α}) atTop
          (𝓝 (1 - α)) := by
  obtain ⟨Ω, mΩ, P, O, hP, -, hO, hlaw⟩ := exists_isIIDSample coinPairLaw
  exact ⟨Ω, mΩ, P, O, hP, hO, hlaw 0, coinPair_bootstrap_delta_coverage hO (hlaw 0) hα hz⟩

/-! ### The ratio of the two coordinates -/

/-- The ratio of the two coordinates, `Ψ(x) = x₀ / x₁`. -/
noncomputable def coinPairRatio (x : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 / x 1

theorem measurable_coinPairRatio : Measurable coinPairRatio := by
  unfold coinPairRatio
  fun_prop

/-- **The ratio is strictly differentiable at the mean.** At `(1/2, 1/2)` the derivative of
`x₀ / x₁` is `v ↦ 2 v₀ - 2 v₁ = ⟪(2, -2), v⟫`. -/
theorem hasStrictFDerivAt_coinPairRatio :
    HasStrictFDerivAt coinPairRatio (innerSL ℝ !₂[2, -2]) !₂[1 / 2, 1 / 2] := by
  set m : EuclideanSpace ℝ (Fin 2) := !₂[1 / 2, 1 / 2] with hm
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasStrictFDerivAt (x := m)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasStrictFDerivAt (x := m)
  have hne : EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1 m ≠ 0 := by simp [hm]
  have hinv := (hasStrictFDerivAt_inv (𝕜 := ℝ) hne).comp m h1
  have h := h0.mul hinv
  have hfun : coinPairRatio = (fun x ↦ EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0 x) *
      ((fun x : ℝ ↦ x⁻¹) ∘ EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1) := by
    funext x
    simp [coinPairRatio, div_eq_mul_inv]
  rw [hfun]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  simp [hm, PiLp.inner_apply, Fin.sum_univ_two]
  norm_num
  ring

/-- **The bootstrap delta method for the ratio of two fair coins.** For an i.i.d. sample of pairs
of independent fair coins, `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the percentile interval of the
bootstrap law of `X̄*_{n,0} / X̄*_{n,1}` covers the ratio of the means, `1`, with probability
tending to `1 - α`. The linearized limit `2 Z₀ - 2 Z₁` has variance `2`. -/
theorem coinPair_bootstrap_ratio_coverage {P : Measure Ω} [IsProbabilityMeasure P]
    {O : ℕ → Ω → Bool × Bool} (hO : IsIIDSample O P) (hlaw : HasLaw (O 0) coinPairLaw P)
    {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | (1 : ℝ) ∈ percentileInterval
      ((bootstrapLaw (resampleMeanVec coinPairScore) O n ω).map coinPairRatio) α}) atTop
      (𝓝 (1 - α)) := by
  have hσ : 0 < Var[innerSL ℝ !₂[2, -2];
      multivariateGaussian 0 (covMatrix P fun i ω ↦ coinPairScore (O 0 ω) i)] := by
    rw [covMatrix_coinPairScore hlaw, variance_innerSL_coinPairCov]
    norm_num
  have hd := hasStrictFDerivAt_coinPairRatio
  rw [← integral_coinPairScore hlaw] at hd
  have h := tendsto_bootstrap_delta_coverage hO measurable_coinPairScore
    (memLp_coinPairScore hlaw) measurable_coinPairRatio hd hσ hα hz
  have h1 : coinPairRatio (P[fun ω ↦ coinPairScore (O 0 ω)]) = 1 := by
    rw [integral_coinPairScore hlaw, coinPairRatio]
    simp
  rwa [h1] at h

/-! ### The fair coin: conditional expectations and quantiles -/

section Coin

variable {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Bool}

theorem memLp_coinScore (hlaw : HasLaw (O 0) (bernoulliLaw (1 / 2)) P) :
    MemLp (fun ω ↦ coinScore (O 0 ω)) 2 P :=
  MemLp.of_bound (measurable_coinScore.comp_aemeasurable hlaw.aemeasurable).aestronglyMeasurable
    1 (ae_of_all _ fun ω ↦ by unfold coinScore; split_ifs <;> simp)

/-- The variance of the score of a fair coin is `1/4`. -/
theorem variance_coinScore (hlaw : HasLaw (O 0) (bernoulliLaw (1 / 2)) P) :
    Var[fun ω ↦ coinScore (O 0 ω); P] = 1 / 4 := by
  have hb : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    isProbabilityMeasure_bernoulliLaw (by norm_num) (by norm_num)
  have hint : ∀ g : Bool → ℝ, P[fun ω ↦ g (O 0 ω)] = (1 - 1 / 2) * g false + 1 / 2 * g true :=
    fun g ↦ by
      rw [← integral_bernoulliLaw (by norm_num) (by norm_num) g]
      exact hlaw.integral_comp (measurable_of_countable g).aestronglyMeasurable
  rw [variance_eq_sub (memLp_coinScore hlaw)]
  have h2 := hint (fun b ↦ coinScore b ^ 2)
  have h1 := hint coinScore
  simp only [Pi.pow_apply]
  rw [h2, h1]
  simp [coinScore]
  norm_num

/-- **Conditional expectations of the bootstrap of a fair coin.** For measurable i.i.d. fair coin
flips and a bounded continuous `φ`, the conditional expectation of `φ(√n (X̄*_n - X̄_n))` given the
data, on the product of the data space and the resampling indices, is the integral against the
resample law, and this integral converges to `∫ φ dN(0, 1/4)` for almost every data path. -/
theorem coin_condExp_resampleMean_tendsto (hO : IsIIDSample O P) (hOm : ∀ k, Measurable (O k))
    (hlaw : HasLaw (O 0) (bernoulliLaw (1 / 2)) P) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    (∀ n : ℕ, (P.prod (resampleIndexLaw n))[fun p ↦
        φ (√(n : ℝ) * (resampleMean coinScore n (resample O n p.1 p.2) -
          sampleMean coinScore O n p.1)) |
        MeasurableSpace.comap Prod.fst mΩ] =ᵐ[P.prod (resampleIndexLaw n)]
      fun p ↦ ∫ y, φ (√(n : ℝ) * (resampleMean coinScore n y - sampleMean coinScore O n p.1))
        ∂resampleLaw O n p.1) ∧
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ∫ y, φ (√(n : ℝ) * (resampleMean coinScore n y -
        sampleMean coinScore O n ω)) ∂resampleLaw O n ω) atTop
      (𝓝 (∫ x, φ x ∂gaussianReal 0 (1 / 4 : ℝ≥0))) := by
  have h := condExp_resampleMean_tendsto hO hOm measurable_coinScore (memLp_coinScore hlaw)
    hφc hφb
  have hv : (Var[fun ω ↦ coinScore (O 0 ω); P]).toNNReal = 1 / 4 := by
    rw [variance_coinScore hlaw]
    ext
    simp only [one_div, Real.coe_toNNReal', NNReal.coe_inv, NNReal.coe_ofNat]
    norm_num
  rwa [hv] at h

/-- **Bootstrap quantiles of a fair coin.** For i.i.d. fair coin flips and `Φ(z) = p`, almost
surely `√n (q*_n(p) - X̄_n) → z / 2`, with `q*_n(p)` the `p`-quantile of the bootstrap law of the
mean. -/
theorem coin_ae_tendsto_bootstrapQuantile (hO : IsIIDSample O P)
    (hlaw : HasLaw (O 0) (bernoulliLaw (1 / 2)) P) {p z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = p) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
      √(n : ℝ) * (bootstrapQuantile (resampleMean coinScore) O n ω p -
        sampleMean coinScore O n ω)) atTop (𝓝 (z / 2)) := by
  have hσ : 0 < Var[fun ω ↦ coinScore (O 0 ω); P] := by
    rw [variance_coinScore hlaw]; norm_num
  have h := ae_tendsto_bootstrapQuantile_resampleMean hO measurable_coinScore
    (memLp_coinScore hlaw) hσ hz
  have hs : √(Var[fun ω ↦ coinScore (O 0 ω); P]) * z = z / 2 := by
    rw [variance_coinScore hlaw, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    ring
  rwa [hs] at h

end Coin

/-- **The conditional expectation example is not vacuous.** There is a probability space with
measurable i.i.d. fair coin flips; on it, for every bounded continuous `φ`, the integral of
`φ(√n (X̄*_n - X̄_n))` against the resample law converges almost surely to `∫ φ dN(0, 1/4)`. -/
theorem exists_coin_condExp_resampleMean_tendsto :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → Bool,
      IsProbabilityMeasure P ∧ IsIIDSample O P ∧ HasLaw (O 0) (bernoulliLaw (1 / 2)) P ∧
        ∀ φ : ℝ → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
          ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ ∫ y, φ (√(n : ℝ) * (resampleMean coinScore n y -
            sampleMean coinScore O n ω)) ∂resampleLaw O n ω) atTop
            (𝓝 (∫ x, φ x ∂gaussianReal 0 (1 / 4 : ℝ≥0))) := by
  have hb : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    isProbabilityMeasure_bernoulliLaw (by norm_num) (by norm_num)
  obtain ⟨Ω, mΩ, P, O, hP, hOm, hO, hlaw⟩ := exists_isIIDSample (bernoulliLaw (1 / 2))
  exact ⟨Ω, mΩ, P, O, hP, hO, hlaw 0, fun φ hφc hφb ↦
    (coin_condExp_resampleMean_tendsto hO hOm (hlaw 0) hφc hφb).2⟩

/-- **The quantile example is not vacuous.** There is a probability space with i.i.d. fair coin
flips on which, for every `z` with `Φ(z) = p`, almost surely `√n (q*_n(p) - X̄_n) → z / 2`. -/
theorem exists_coin_ae_tendsto_bootstrapQuantile {p z : ℝ} (hz : cdf (gaussianReal 0 1) z = p) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → Bool,
      IsProbabilityMeasure P ∧ IsIIDSample O P ∧ HasLaw (O 0) (bernoulliLaw (1 / 2)) P ∧
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
          √(n : ℝ) * (bootstrapQuantile (resampleMean coinScore) O n ω p -
            sampleMean coinScore O n ω)) atTop (𝓝 (z / 2)) := by
  have hb : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    isProbabilityMeasure_bernoulliLaw (by norm_num) (by norm_num)
  obtain ⟨Ω, mΩ, P, O, hP, -, hO, hlaw⟩ := exists_isIIDSample (bernoulliLaw (1 / 2))
  exact ⟨Ω, mΩ, P, O, hP, hO, hlaw 0, coin_ae_tendsto_bootstrapQuantile hO (hlaw 0) hz⟩

end Bootstrap

end CausalInference
