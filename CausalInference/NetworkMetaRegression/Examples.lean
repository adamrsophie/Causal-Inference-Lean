/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.SharedModifiersNecessary
public import CausalInference.NetworkMetaRegression.AggregationProbit
public import CausalInference.NetworkMetaRegression.AggregationLogit

/-!
# Examples of multilevel network meta-regression

Concrete instances in which the hypotheses of the main results hold.

## Main results

* `affineRank_binaryLaw`: a binary covariate with `P(X = 1) = q ∈ (0, 1)` has full affine rank.
* `twoStudy_hypotheses_example`: the triangle model with shared effect modifiers, the identity
  link and binary covariate laws satisfies every hypothesis of
  `MultilevelModel.twoStudy_identifiable`.
* `stdGaussianLaw`: the standard normal law on `ℝ¹`, with covariate mean `0` and
  `slopeVar = b₀²` (`covMean_stdGaussianLaw`, `slopeVar_stdGaussianLaw`).
* `aggBias_link_example`: for the triangle model with intercept `1`, prognostic effect `1` and
  standard normal covariates, the reference arm has plug in predictor `1` and predictor
  variance `1`, so the bias is `e(√e - 1) > 0` on the log link and negative on the probit and the
  logit links.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory IndirectComparison NetworkMetaAnalysis MultilevelModel

/-- A binary covariate with `P(X = 1) = q ∈ (0, 1)` has full affine rank. -/
theorem affineRank_binaryLaw {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) : AffineRank (binaryLaw q) := by
  intro s b h
  have hI := integral_congr_ae (h.mono fun x hx =>
    show (s + x ⬝ᵥ b) ^ 2 = (fun _ => (0 : ℝ)) x by rw [hx]; ring)
  rw [integral_binaryLaw ⟨hq.1.le, hq.2.le⟩, integral_zero] at hI
  simp only [dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    zero_mul, add_zero, one_mul] at hI
  have h1q : 0 < 1 - q := by linarith [hq.2]
  have t1 := mul_nonneg h1q.le (sq_nonneg s)
  have t2 := mul_nonneg hq.1.le (sq_nonneg (s + b 0))
  have hs : s = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1
    ((mul_eq_zero.1 (by linarith : (1 - q) * s ^ 2 = 0)).resolve_left h1q.ne')
  have hb : s + b 0 = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1
    ((mul_eq_zero.1 (by linarith : q * (s + b 0) ^ 2 = 0)).resolve_left hq.1.ne')
  refine ⟨hs, funext fun i => ?_⟩
  rw [Subsingleton.elim i 0]
  simp only [Pi.zero_apply]
  linarith

/-- **An instance of the two study theorem.** For the triangle model with all parameters zero
(anchored at `2`, shared effect modifiers of `0` and `1`), the identity link and binary laws
with `q = 1/2` in both studies, every hypothesis of `MultilevelModel.twoStudy_identifiable`
other than the data equations holds, and the data equations hold for the model against
itself. -/
theorem twoStudy_hypotheses_example :
    let M := triangleModel 0 0 0 0 0 0 0
    StrictMono (id : ℝ → ℝ) ∧ IsProbabilityMeasure (binaryLaw (1 / 2)) ∧
      AffineRank (binaryLaw (1 / 2)) ∧ M.IsAnchoredAt 2 ∧ M.SharedEffectModifiers {0, 1} ∧
      (∀ s, Integrable (fun x => id (s + x ⬝ᵥ (M.β₁ + M.β₂ 1))) (binaryLaw (1 / 2))) ∧
      (∀ s, Integrable (fun x => id (s + x ⬝ᵥ (M.β₁ + M.β₂ 2))) (binaryLaw (1 / 2))) := by
  have hI : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact ⟨strictMono_id, isProbabilityMeasure_binaryLaw ⟨hI.1.le, hI.2.le⟩,
    affineRank_binaryLaw hI, triangleModel_anchored _ _ _ _ _ _ _,
    (triangleModel_shared_iff _ _ _ _ _ _ _).2 rfl, fun _ => integrable_binaryLaw _ _,
    fun _ => integrable_binaryLaw _ _⟩

/-! ### A Gaussian covariate -/

/-- The embedding `s ↦ (s)` of `ℝ` in `ℝ¹`. -/
noncomputable def embedFin1 : ℝ →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

/-- The standard normal law on `ℝ¹`. -/
noncomputable def stdGaussianLaw : Measure (Fin 1 → ℝ) := (gaussianReal 0 1).map embedFin1

instance : IsGaussian stdGaussianLaw := by unfold stdGaussianLaw; infer_instance

theorem integral_stdGaussianLaw {f : (Fin 1 → ℝ) → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂stdGaussianLaw = ∫ s, f (fun _ => s) ∂gaussianReal 0 1 := by
  rw [stdGaussianLaw, integral_map embedFin1.continuous.measurable.aemeasurable
    hf.aestronglyMeasurable]
  rfl

theorem covMean_stdGaussianLaw : covMean stdGaussianLaw = 0 := by
  funext i
  simp only [covMean, Pi.zero_apply]
  rw [integral_stdGaussianLaw (measurable_pi_apply i)]
  exact integral_id_gaussianReal

theorem slopeVar_stdGaussianLaw (b : Fin 1 → ℝ) : slopeVar stdGaussianLaw b = b 0 ^ 2 := by
  rw [slopeVar_eq_variance (memLp_coord_of_isGaussian _), stdGaussianLaw,
    variance_map ((by unfold dotProduct; fun_prop :
      Continuous fun x : Fin 1 → ℝ => x ⬝ᵥ b).aemeasurable)
      embedFin1.continuous.measurable.aemeasurable]
  have e : ((fun x : Fin 1 → ℝ => x ⬝ᵥ b) ∘ embedFin1) = fun s => b 0 * s := funext fun s => by
    simp [embedFin1, dotProduct, mul_comm]
  rw [e, variance_const_mul, variance_fun_id_gaussianReal]
  simp

/-- **The bias by link in one instance.** For `M = triangleModel 1 1 1 0 0 0 0` (intercepts `1`,
prognostic effect `1`), its reference arm `2` at baseline `1` under the standard normal
covariate has plug in predictor `1` and predictor variance `1`. The log link bias is
`e(√e - 1) > 0`; the probit and the logit biases are negative. -/
theorem aggBias_link_example :
    let M := triangleModel 1 1 1 0 0 0 0
    M.eta 1 2 (covMean stdGaussianLaw) = 1 ∧ slopeVar stdGaussianLaw (M.β₁ + M.β₂ 2) = 1 ∧
      M.aggBias Real.exp 1 stdGaussianLaw 2 = Real.exp 1 * (Real.exp (1 / 2) - 1) ∧
      0 < M.aggBias Real.exp 1 stdGaussianLaw 2 ∧
      M.aggBias (cdf (gaussianReal 0 1)) 1 stdGaussianLaw 2 < 0 ∧
      M.aggBias Real.sigmoid 1 stdGaussianLaw 2 < 0 := by
  intro M
  have hm : M.eta 1 2 (covMean stdGaussianLaw) = 1 := by
    rw [covMean_stdGaussianLaw]
    simp [M, eta_eq_affine, triangleModel]
  have hv : slopeVar stdGaussianLaw (M.β₁ + M.β₂ 2) = 1 := by
    rw [slopeVar_stdGaussianLaw]
    simp [M, triangleModel]
  have hlog := (aggBias_exp_gaussian M 1 stdGaussianLaw 2).1
  rw [hm, hv] at hlog
  refine ⟨hm, hv, hlog, ?_, aggBias_probit_neg M 1 _ 2 (by rw [hv]; norm_num)
    (by rw [hm]; norm_num), aggBias_sigmoid_neg M 1 _ 2 (by rw [hv]; norm_num)
    (by rw [hm]; norm_num)⟩
  rw [hlog]
  refine mul_pos (Real.exp_pos 1) (sub_pos.2 ?_)
  linarith [Real.add_one_lt_exp (by norm_num : (1 / 2 : ℝ) ≠ 0)]

end NetworkMetaRegression

end CausalInference
