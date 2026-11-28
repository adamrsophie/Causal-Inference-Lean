/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregationIdentity
public import CausalInference.Estimation.GaussianLinearImage

/-!
# Gaussian covariates and the log link

For a Gaussian covariate law `F` with covariance matrix `Σ` and the slope vector
`b_k = β₁ + β₂,k` of arm `k`, the linear predictor `η_k(X)` is normal with mean `η_k(x̄)` and
variance `v_k = b_kᵀ Σ b_k` (`MultilevelModel.hasLaw_eta_gaussian`). On the log link the aggregate
mean is then the normal moment generating function at `1`.

## Main definitions

* `slopeVar F b = bᵀ Σ_F b`, the variance of `xᵀb` under `F`.

## Main results

* `MultilevelModel.hasLaw_eta_gaussian`: `η_k(X) ∼ N(η_k(x̄), v_k)` under a Gaussian law.
* `MultilevelModel.armMean_exp_gaussian`: on the log link the aggregate mean is
  `exp(η_k(x̄) + v_k / 2)`; it is the plug in value times `exp(v_k / 2) ≥ 1`
  (`MultilevelModel.aggBias_exp_gaussian`), so the bias is nonnegative and is zero exactly when
  `Σ b_k = 0` (`MultilevelModel.aggBias_exp_gaussian_eq_zero_iff`).
* `MultilevelModel.overdispersion_exp_gaussian`: the rate `W = exp(η_k(X))` has
  `Var W / (E W)² = exp(v_k) - 1`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory IndirectComparison NetworkMetaAnalysis Matrix
open BiasAnalysis.MeasurementError (covMatrix)
open BiasAnalysis.VarianceCovariance (quadraticVariance_eq_dotProduct variance_linearization_cov)

variable {p : ℕ}

/-- The variance `bᵀ Σ_F b` of the linear form `xᵀb` under `F`. -/
noncomputable def slopeVar (F : Measure (Fin p → ℝ)) (b : Fin p → ℝ) : ℝ :=
  b ⬝ᵥ covMatrix F (fun i x => x i) *ᵥ b

/-- The linear form `x ↦ xᵀb` as a continuous linear functional. -/
noncomputable def dotForm (b : Fin p → ℝ) : StrongDual ℝ (Fin p → ℝ) :=
  ∑ j, b j • ContinuousLinearMap.proj j

theorem dotForm_apply (b x : Fin p → ℝ) : dotForm b x = x ⬝ᵥ b := by
  simp [dotForm, dotProduct, mul_comm]

/-- The coordinates of a Gaussian law have second moments. -/
theorem memLp_coord_of_isGaussian (F : Measure (Fin p → ℝ)) [IsGaussian F] (i : Fin p) :
    MemLp (fun x : Fin p → ℝ => x i) 2 F :=
  IsGaussian.memLp_dual F (ContinuousLinearMap.proj i) 2 (by simp)

/-- `slopeVar F b` is the variance of `xᵀb`. -/
theorem slopeVar_eq_variance {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF : ∀ i, MemLp (fun x : Fin p → ℝ => x i) 2 F) (b : Fin p → ℝ) :
    slopeVar F b = Var[fun x => x ⬝ᵥ b; F] := by
  have e : (fun x : Fin p → ℝ => x ⬝ᵥ b) = fun x => ∑ i, b i * x i :=
    funext fun x => by simp [dotProduct, mul_comm]
  have h := variance_linearization_cov (fun i (x : Fin p → ℝ) => x i) hF b
  rw [e]
  exact (h.trans (quadraticVariance_eq_dotProduct _ _)).symm

theorem slopeVar_nonneg {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF : ∀ i, MemLp (fun x : Fin p → ℝ => x i) 2 F) (b : Fin p → ℝ) : 0 ≤ slopeVar F b := by
  rw [slopeVar_eq_variance hF]
  exact variance_nonneg _ _

/-- `bᵀ Σ b = 0` exactly when `Σ b = 0`. -/
theorem slopeVar_eq_zero_iff {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF : ∀ i, MemLp (fun x : Fin p → ℝ => x i) 2 F) (b : Fin p → ℝ) :
    slopeVar F b = 0 ↔ covMatrix F (fun i x => x i) *ᵥ b = 0 := by
  have := (posSemidef_covMatrix hF).dotProduct_mulVec_zero_iff (x := b)
  simpa [slopeVar] using this

namespace MultilevelModel

variable {J K : Type*}

/-- **The linear predictor of Gaussian covariates is normal**:
`η_k(X) ∼ N(η_k(x̄), (β₁ + β₂,k)ᵀ Σ (β₁ + β₂,k))`. -/
theorem hasLaw_eta_gaussian (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) :
    HasLaw (M.eta α k) (gaussianReal (M.eta α k (covMean F))
      (slopeVar F (M.β₁ + M.β₂ k)).toNNReal) F := by
  set b := M.β₁ + M.β₂ k
  have h2 := memLp_coord_of_isGaussian F
  have hcomp : M.eta α k = (fun s => (α + M.γ k) + s) ∘ dotForm b := by
    funext x; simp [eta_eq_affine, dotForm_apply, b]
  have hL := IsGaussian.map_eq_gaussianReal (μ := F) (dotForm b)
  refine ⟨by rw [hcomp]; exact (by fun_prop : Measurable _).aemeasurable, ?_⟩
  rw [hcomp, ← Measure.map_map (by fun_prop) (dotForm b).continuous.measurable, hL,
    gaussianReal_map_const_add]
  have hmean : F[dotForm b] = covMean F ⬝ᵥ b := by
    simp only [dotForm_apply, dotProduct]
    rw [integral_finsetSum _ fun j _ => ((h2 j).integrable one_le_two).mul_const (b j)]
    simp [integral_mul_const, covMean]
  have hvar : Var[dotForm b; F] = slopeVar F b := by
    rw [slopeVar_eq_variance h2]
    congr 1
    funext x
    exact dotForm_apply b x
  rw [hmean, hvar]
  congr 1
  simp only [Function.comp, dotForm_apply]
  ring

/-- **Log link aggregation under Gaussian covariates**: the aggregate mean is
`exp(η_k(x̄) + v_k / 2)`. -/
theorem armMean_exp_gaussian (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) :
    M.armMean Real.exp α F k =
      Real.exp (M.eta α k (covMean F) + slopeVar F (M.β₁ + M.β₂ k) / 2) := by
  have hv := slopeVar_nonneg (memLp_coord_of_isGaussian F) (M.β₁ + M.β₂ k)
  have hmgf := mgf_gaussianReal (M.hasLaw_eta_gaussian α F k) 1
  simp only [mgf, one_mul, mul_one, one_pow] at hmgf
  rw [armMean, show (fun x => M.surface Real.exp α k x) = fun x => Real.exp (M.eta α k x) from
    rfl, hmgf, Real.coe_toNNReal _ hv]

/-- **The log link bias is multiplicative**: the aggregate mean is the plug in value times
`exp(v_k / 2) ≥ 1`, so the aggregation bias `exp(η_k(x̄))(exp(v_k / 2) - 1)` is nonnegative. -/
theorem aggBias_exp_gaussian (M : MultilevelModel J K p) (α : ℝ) (F : Measure (Fin p → ℝ))
    [IsGaussian F] (k : K) :
    M.aggBias Real.exp α F k =
        Real.exp (M.eta α k (covMean F)) * (Real.exp (slopeVar F (M.β₁ + M.β₂ k) / 2) - 1) ∧
      1 ≤ Real.exp (slopeVar F (M.β₁ + M.β₂ k) / 2) ∧ 0 ≤ M.aggBias Real.exp α F k := by
  have hv := slopeVar_nonneg (memLp_coord_of_isGaussian F) (M.β₁ + M.β₂ k)
  have h1 : 1 ≤ Real.exp (slopeVar F (M.β₁ + M.β₂ k) / 2) := Real.one_le_exp (by linarith)
  have he : M.aggBias Real.exp α F k =
      Real.exp (M.eta α k (covMean F)) * (Real.exp (slopeVar F (M.β₁ + M.β₂ k) / 2) - 1) := by
    rw [aggBias, armMean_exp_gaussian, Real.exp_add]
    ring
  exact ⟨he, h1, by rw [he]; exact mul_nonneg (Real.exp_pos _).le (by linarith)⟩

/-- The log link bias under Gaussian covariates is zero exactly when `Σ (β₁ + β₂,k) = 0`. -/
theorem aggBias_exp_gaussian_eq_zero_iff (M : MultilevelModel J K p) (α : ℝ)
    (F : Measure (Fin p → ℝ)) [IsGaussian F] (k : K) :
    M.aggBias Real.exp α F k = 0 ↔ covMatrix F (fun i x => x i) *ᵥ (M.β₁ + M.β₂ k) = 0 := by
  rw [(aggBias_exp_gaussian M α F k).1, mul_eq_zero, sub_eq_zero, Real.exp_eq_one_iff,
    div_eq_zero_iff, ← slopeVar_eq_zero_iff (memLp_coord_of_isGaussian F)]
  simp [(Real.exp_pos _).ne']

/-- **Overdispersion of a Gaussian log-normal rate**: for `W = exp(η_k(X))`,
`Var W / (E W)² = exp(v_k) - 1`. -/
theorem overdispersion_exp_gaussian (M : MultilevelModel J K p) (α : ℝ)
    (F : Measure (Fin p → ℝ)) [IsGaussian F] (k : K) :
    Var[fun x => Real.exp (M.eta α k x); F] / (M.armMean Real.exp α F k) ^ 2 =
      Real.exp (slopeVar F (M.β₁ + M.β₂ k)) - 1 := by
  have hv : 0 ≤ slopeVar F (M.β₁ + M.β₂ k) := slopeVar_nonneg (memLp_coord_of_isGaussian F) _
  have hL := M.hasLaw_eta_gaussian α F k
  have hmgf2 := mgf_gaussianReal hL 2
  simp only [mgf] at hmgf2
  rw [Real.coe_toNNReal _ hv] at hmgf2
  have hsq : (fun x => Real.exp (M.eta α k x)) ^ 2 = fun x => Real.exp (2 * M.eta α k x) := by
    funext x; simp only [Pi.pow_apply]; rw [← Real.exp_nat_mul]; norm_num
  have hint2 : Integrable (fun x => Real.exp (2 * M.eta α k x)) F := by
    have := integrable_exp_mul_gaussianReal (μ := M.eta α k (covMean F))
      (v := (slopeVar F (M.β₁ + M.β₂ k)).toNNReal) 2
    rw [← hL.map_eq] at this
    exact (integrable_map_measure (by fun_prop) hL.aemeasurable).mp this
  have hmem : MemLp (fun x => Real.exp (M.eta α k x)) 2 F := by
    have hm : AEStronglyMeasurable (fun x => Real.exp (M.eta α k x)) F :=
      (Real.continuous_exp.measurable.comp_aemeasurable hL.aemeasurable).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hm]
    simpa [← Real.exp_nat_mul] using hint2
  have hθ := armMean_exp_gaussian M α F k
  rw [variance_eq_sub hmem, hsq]
  change (∫ x, Real.exp (2 * M.eta α k x) ∂F - (∫ x, Real.exp (M.eta α k x) ∂F) ^ 2) /
    (M.armMean Real.exp α F k) ^ 2 = _
  have e0 : ∫ x, Real.exp (M.eta α k x) ∂F = M.armMean Real.exp α F k := rfl
  have e1 : ∀ m v : ℝ,
      Real.exp (m * 2 + v * 2 ^ 2 / 2) = Real.exp v * Real.exp (m + v / 2) ^ 2 := by
    intro m v
    rw [pow_two (Real.exp (m + v / 2)), ← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  rw [e0, hmgf2, hθ, e1]
  field_simp

end MultilevelModel

end NetworkMetaRegression

end CausalInference
