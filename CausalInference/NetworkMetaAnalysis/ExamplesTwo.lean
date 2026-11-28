/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.RandomEffectsNetwork
public import CausalInference.NetworkMetaAnalysis.NodeSplitting
public import CausalInference.NetworkMetaAnalysis.Deviance
public import CausalInference.NetworkMetaAnalysis.ProbitAggregation

/-!
# Worked instances: random effects, node splitting, deviance and probit attenuation

Every number is computed in the proof.

* **A three arm study** (`threeArm_randomEffects_covariance`). With heterogeneity variance
  `τ² = 2`, the two contrasts against the baseline arm have covariance matrix
  `(τ² / 2)(I + J) = [[2, 1], [1, 2]]` (correlation `1/2`), with eigenvalue `3` on the constant
  vector and `1` on `(1, -1)`, determinant `3` and inverse `[[2/3, -1/3], [-1/3, 2/3]]`.
* **A triangle with a node split** (`triangle_nodeSplit_example`). Unit variances and the
  estimates `y = (1, 3/2, 1)` of the comparisons `a → b`, `a → c`, `b → c`: the node split model
  estimates the effect of `b` from the indirect route as `1/2` and the effect of `c` as `3/2`,
  with inconsistency `ω̂ = 1/2`; the consistent triangle pools the effect of `b` to `5/6`, and
  `1 = 5/6 + (1/3)(1/2)`, `1/2 = 5/6 - (2/3)(1/2)` split it into the direct and indirect
  estimates.
* **A binomial deviance** (`binomialDeviance_example`). With `3` events out of `10` the deviance
  at `p = 1/2` is `2 (3 log (3/5) + 7 log (7/5)) > 0` and at the saturated fit `p = 3/10` it
  is `0`.
* **Probit attenuation** (`probit_attenuation_example`). With `X ∼ N(1, 4/3)` and slope `3/2`,
  `1 + (3/2)² (4/3) = 4`, so the attenuation factor is `1/2`:
  `E Φ(1/2 + (3/2) X) = Φ(1)`, the aggregate slope is `3/4 < 3/2`, and with a common slope
  `3/2` a conditional probit contrast `1` becomes the marginal contrast `1/2`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open Matrix MeasureTheory ProbabilityTheory EffectMeasure
open scoped NNReal

/-! ### A three arm study -/

/-- **The random effects covariance of a three arm study** with `τ² = 2`. -/
theorem threeArm_randomEffects_covariance :
    ((2 : ℝ) / 2) • (1 + onesMatrix (Fin 2)) = !![2, 1; 1, 2] ∧
      (((2 : ℝ) / 2) • (1 + onesMatrix (Fin 2))) *ᵥ ![1, 1] = (3 : ℝ) • ![1, 1] ∧
      (((2 : ℝ) / 2) • (1 + onesMatrix (Fin 2))) *ᵥ ![1, -1] = (1 : ℝ) • ![1, -1] ∧
      (((2 : ℝ) / 2) • (1 + onesMatrix (Fin 2))).det = 3 ∧
      (((2 : ℝ) / 2) • (1 + onesMatrix (Fin 2)))⁻¹ = !![2 / 3, -1 / 3; -1 / 3, 2 / 3] := by
  have hM : ((2 : ℝ) / 2) • (1 + onesMatrix (Fin 2)) = !![2, 1; 1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [onesMatrix] <;> norm_num
  refine ⟨hM, ?_, ?_, ?_, ?_⟩
  · rw [hM]
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · rw [hM]
    funext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · rw [det_smul_one_add_onesMatrix]
    norm_num
  · rw [inv_smul_one_add_onesMatrix (by norm_num)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [onesMatrix] <;> norm_num

/-! ### A triangle with a node split -/

/-- **A node split in a triangle** with unit variances and `y = (1, 3/2, 1)`. -/
theorem triangle_nodeSplit_example :
    glsEstimate nodeSplitDesign (diagonal fun _ => (1 : ℝ)) ![1, 3 / 2, 1] =
        ![1 / 2, 3 / 2, 1 / 2] ∧
      glsEstimate triangleDesign (diagonal fun _ => (1 : ℝ)) ![1, 3 / 2, 1] 0 = 5 / 6 ∧
      (1 : ℝ) = 5 / 6 + 1 / 3 * (1 / 2) ∧ (3 / 2 - 1 : ℝ) = 5 / 6 - 2 / 3 * (1 / 2) := by
  have hV : (diagonal fun _ : Fin 3 => (1 : ℝ)).PosDef :=
    posDef_diagonal_iff.2 fun _ => one_pos
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · rw [glsEstimate_nodeSplitDesign hV]
    funext i
    fin_cases i <;> simp <;> norm_num
  · rw [(triangle_glsEstimate (v := fun _ => (1 : ℝ)) (fun _ => one_pos) _).1, ivwEstimate_two]
    all_goals norm_num

/-! ### A binomial deviance -/

/-- **A binomial deviance**: `3` events out of `10`. -/
theorem binomialDeviance_example :
    binomialDeviance 10 3 (1 / 2) = 2 * (3 * Real.log (3 / 5) + 7 * Real.log (7 / 5)) ∧
      0 < binomialDeviance 10 3 (1 / 2) ∧ binomialDeviance 10 3 (3 / 10) = 0 := by
  have h0 := binomialDeviance_nonneg (n := 10) (y := 3) (p := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hz := binomialDeviance_eq_zero_iff (n := 10) (y := 3) (p := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, lt_of_le_of_ne h0 fun h => ?_, ?_⟩
  · rw [binomialDeviance]
    norm_num
  · have := hz.1 h.symm
    norm_num at this
  · exact (binomialDeviance_eq_zero_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2 (by norm_num)

/-! ### Probit attenuation -/

/-- **Probit attenuation** with `X ∼ N(1, 4/3)` and slope `3/2`: the attenuation factor is `1/2`. -/
theorem probit_attenuation_example :
    probitAttenuation (4 / 3) (3 / 2) = 1 / 2 ∧
      ∫ x, cdf (gaussianReal 0 1) (1 / 2 + 3 / 2 * x) ∂gaussianReal 1 (4 / 3) =
        cdf (gaussianReal 0 1) 1 ∧
      probitEcoSlope (4 / 3) 0 (3 / 2) = 3 / 4 ∧ probitEcoSlope (4 / 3) 0 (3 / 2) < 3 / 2 ∧
      linkMarginal probit (gaussianReal 1 (4 / 3))
          (fun x => cdf (gaussianReal 0 1) (0 + 3 / 2 * x))
          (fun x => cdf (gaussianReal 0 1) (1 + 3 / 2 * x)) = 1 / 2 := by
  have hs : (((4 / 3 : ℝ≥0)) : ℝ) = 4 / 3 := by norm_num
  have hsq : √(1 + (3 / 2 : ℝ) ^ 2 * (4 / 3)) = 2 := by
    rw [show (1 + (3 / 2 : ℝ) ^ 2 * (4 / 3)) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hA : probitAttenuation (4 / 3) (3 / 2) = 1 / 2 := by
    rw [probitAttenuation, hsq]
  have hX : HasLaw (fun x : ℝ => x) (gaussianReal 1 (4 / 3)) (gaussianReal 1 (4 / 3)) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · rw [hX.integral_cdf_affine, hs, hsq]
    norm_num
  · rw [probitEcoSlope, probitShrink, probitShrink, hsq]
    norm_num
  · rw [probitEcoSlope, probitShrink, probitShrink, hsq]
    norm_num
  · rw [(linkMarginal_probit_gaussian_common_slope 1 (4 / 3) 0 1 (3 / 2)).2, hs, hA]
    norm_num

end NetworkMetaAnalysis

end CausalInference
