/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregationLog
public import CausalInference.NetworkMetaAnalysis.ProbitAggregation

/-!
# The probit link under Gaussian covariates

With `Φ` the standard normal distribution function as inverse link and a Gaussian covariate
law, the aggregate mean of arm `k` has the closed form `Φ(η_k(x̄) / √(1 + v_k))`, with
`v_k = (β₁ + β₂,k)ᵀ Σ (β₁ + β₂,k)` (`MultilevelModel.armMean_probit_gaussian`). The aggregate
probability is the plug in probability with the linear predictor shrunk toward `0` by the factor
`1 / √(1 + v_k)`: the bias pulls the probability toward `1/2`.

## Main results

* `MultilevelModel.armMean_probit_gaussian`: the closed form.
* `MultilevelModel.aggBias_probit_neg`, `MultilevelModel.aggBias_probit_pos`,
  `MultilevelModel.aggBias_probit_eq_zero`: for `v_k > 0` the bias is negative when
  `η_k(x̄) > 0`, positive when `η_k(x̄) < 0`, and zero when `η_k(x̄) = 0`; for `v_k = 0` it is
  zero (`MultilevelModel.aggBias_probit_of_slopeVar_eq_zero`).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory IndirectComparison NetworkMetaAnalysis

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

local notation "Φ" => cdf (gaussianReal 0 1)

/-- **Probit aggregation under Gaussian covariates**: the aggregate mean is
`Φ(η_k(x̄) / √(1 + v_k))`. -/
theorem armMean_probit_gaussian (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) :
    M.armMean Φ α F k = Φ (M.eta α k (covMean F) / √(1 + slopeVar F (M.β₁ + M.β₂ k))) := by
  have hv := slopeVar_nonneg (memLp_coord_of_isGaussian F) (M.β₁ + M.β₂ k)
  have hL := M.hasLaw_eta_gaussian α F k
  have e : M.armMean Φ α F k = ∫ w, Φ w ∂F.map (M.eta α k) :=
    (integral_map hL.aemeasurable
      (monotone_cdf (gaussianReal 0 1)).measurable.aestronglyMeasurable).symm
  rw [e, hL.map_eq, integral_cdf_gaussianReal, Real.coe_toNNReal _ hv]

/-- The plug in value against the aggregate mean: the bias is `Φ(m / √(1 + v)) - Φ(m)`. -/
theorem aggBias_probit_gaussian (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) :
    M.aggBias Φ α F k = Φ (M.eta α k (covMean F) / √(1 + slopeVar F (M.β₁ + M.β₂ k))) -
      Φ (M.eta α k (covMean F)) := by
  rw [aggBias, armMean_probit_gaussian]

/-- **For a positive plug in predictor the probit bias is negative** (when `v_k > 0`). -/
theorem aggBias_probit_neg (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) (hv : 0 < slopeVar F (M.β₁ + M.β₂ k))
    (hm : 0 < M.eta α k (covMean F)) : M.aggBias Φ α F k < 0 := by
  rw [aggBias_probit_gaussian, sub_neg]
  refine strictMono_cdf_gaussianReal ?_
  have h1 : 1 < √(1 + slopeVar F (M.β₁ + M.β₂ k)) := by
    exact (Real.lt_sqrt zero_le_one).2 (by linarith)
  exact div_lt_self hm h1

/-- **For a negative plug in predictor the probit bias is positive** (when `v_k > 0`). -/
theorem aggBias_probit_pos (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) (hv : 0 < slopeVar F (M.β₁ + M.β₂ k))
    (hm : M.eta α k (covMean F) < 0) : 0 < M.aggBias Φ α F k := by
  rw [aggBias_probit_gaussian, sub_pos]
  refine strictMono_cdf_gaussianReal ?_
  have h1 : 1 < √(1 + slopeVar F (M.β₁ + M.β₂ k)) := by
    exact (Real.lt_sqrt zero_le_one).2 (by linarith)
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- At a zero plug in predictor the probit bias vanishes. -/
theorem aggBias_probit_eq_zero (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) (hm : M.eta α k (covMean F) = 0) : M.aggBias Φ α F k = 0 := by
  rw [aggBias_probit_gaussian, hm, zero_div, sub_self]

/-- Without variation of the linear predictor the probit bias vanishes. -/
theorem aggBias_probit_of_slopeVar_eq_zero (M : MultilevelModel J K p) (α : ℝ)
    (F : Measure (Fin p → ℝ)) [IsGaussian F] (k : K) (hv : slopeVar F (M.β₁ + M.β₂ k) = 0) :
    M.aggBias Φ α F k = 0 := by
  rw [aggBias_probit_gaussian, hv, add_zero, Real.sqrt_one, div_one, sub_self]

end MultilevelModel

end NetworkMetaRegression

end CausalInference
