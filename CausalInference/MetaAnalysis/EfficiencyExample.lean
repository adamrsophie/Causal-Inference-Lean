/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.Examples

/-!
# Meta-analysis: the Cramér-Rao bound applied to linear unbiased estimators

The Cramér-Rao theorem of the Gaussian common effect family, `variance_ivwEstimate_le`, compares
the pooled estimate with every unbiased estimator `T` whose mean can be differentiated under the
integral sign. This file verifies its hypotheses for every **linear unbiased estimator**
`T(y) = ∑ cᵢ yᵢ` with `∑ cᵢ = 1`:

* `T` is unbiased and square integrable under every `P_θ` (`isUnbiased_sum_mul`,
  `memLp_sum_mul`);
* the interchange holds: `∫ T ∂_θ f dν = E_θ[T s] = ∑ cᵢ wᵢ vᵢ = ∑ cᵢ = 1`, from
  `E_θ[(yᵢ - θ)(yⱼ - θ)] = vᵢ` for `i = j` and `0` otherwise (`integral_sub_mul_sub`,
  `meanDerivInterchange_sum_mul`);

so the Cramér-Rao theorem gives `Var_θ(θ̂) ≤ Var_θ(T)` (`variance_ivwEstimate_le_sum_mul`).

**The example.** For the three study example (variances `(1, 1/2, 1/4)`) and the equal weight
average `∑ yᵢ / 3`, the theorem gives `1/7 ≤ 7/36` (`example_cramerRao_equalWeights`): the left
side is the variance of the pooled estimate and the right side that of the equal weight
average, each computed in `MetaAnalysis.Examples`, and the inequality between them is the
conclusion of the Cramér-Rao theorem.

## Main results

* `integral_sub_mul_sub`, `isUnbiased_sum_mul`, `memLp_sum_mul`,
  `meanDerivInterchange_sum_mul`, `variance_ivwEstimate_le_sum_mul`.
* `example_cramerRao_equalWeights`.
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset

section Linear

variable {ι : Type*} [Fintype ι] {v : ι → ℝ} (hv : ∀ i, 0 < v i)
include hv

/-- **Second moments of the family**: `E_θ[(yᵢ - θ)(yⱼ - θ)] = vᵢ` if `i = j` and `0` otherwise. -/
theorem integral_sub_mul_sub [DecidableEq ι] (θ : ℝ) (i j : ι) :
    ∫ y, (y i - θ) * (y j - θ) ∂(commonEffectFamily hv).law θ = if i = j then v i else 0 := by
  have h := (isGaussianCommonEffectModel_pi hv θ).isCommonEffectModel
  have := h.isProbabilityMeasure
  have hcov : ∫ y, (y i - θ) * (y j - θ)
      ∂(Measure.pi fun i => gaussianReal θ (v i).toNNReal) =
      cov[fun y : ι → ℝ => y i, fun y => y j;
        Measure.pi fun i => gaussianReal θ (v i).toNNReal] := by
    rw [covariance]
    have hi : ∫ y, y i ∂(Measure.pi fun i => gaussianReal θ (v i).toNNReal) = θ := h.integral_eq i
    have hj : ∫ y, y j ∂(Measure.pi fun i => gaussianReal θ (v i).toNNReal) = θ := h.integral_eq j
    rw [hi, hj]
  rw [commonEffectFamily_law hv, hcov]
  split_ifs with hij
  · subst hij
    rw [covariance_self (h.memLp i).aemeasurable]
    exact h.variance_eq i
  · exact h.covariance_eq_zero hij

/-- A linear estimator is square integrable under every `P_θ`. -/
theorem memLp_sum_mul (c : ι → ℝ) (θ : ℝ) :
    MemLp (fun y : ι → ℝ => ∑ i, c i * y i) 2 ((commonEffectFamily hv).law θ) := by
  have h := (isGaussianCommonEffectModel_pi hv θ).isCommonEffectModel
  rw [commonEffectFamily_law hv]
  exact memLp_finsetSum _ fun i _ => (h.memLp i).const_mul _

/-- A linear estimator with weights summing to one is unbiased for `θ`. -/
theorem isUnbiased_sum_mul {c : ι → ℝ} (hc : ∑ i, c i = 1) :
    (commonEffectFamily hv).IsUnbiased (fun y => ∑ i, c i * y i) id := by
  intro θ _
  have h := (isGaussianCommonEffectModel_pi hv θ).isCommonEffectModel
  have := ParametricFamily.isProbabilityMeasure_law (F := commonEffectFamily hv) (Set.mem_univ θ)
  refine ⟨(memLp_sum_mul hv c θ).integrable one_le_two, ?_⟩
  rw [ParametricFamily.mean, commonEffectFamily_law hv,
    integral_sum_mul (fun i => (h.memLp i).integrable one_le_two) h.integral_eq c, hc, mul_one]
  rfl

/-- **The interchange for a linear unbiased estimator**: for `T(y) = ∑ cᵢ yᵢ` with `∑ cᵢ = 1`, the
mean `u ↦ E_u[T] = u` is differentiated under the integral sign at every `θ`:
`∫ T ∂_θ f dν = E_θ[T s] = 1`. -/
theorem meanDerivInterchange_sum_mul [Nonempty ι] {c : ι → ℝ} (hc : ∑ i, c i = 1) (θ : ℝ) :
    (commonEffectFamily hv).MeanDerivInterchange (fun y => ∑ i, c i * y i) θ := by
  classical
  set F := commonEffectFamily hv
  have := ParametricFamily.isProbabilityMeasure_law (F := F) (Set.mem_univ θ)
  have h := (isGaussianCommonEffectModel_pi hv θ).isCommonEffectModel
  have hcov' : ∀ i j, ∫ y, (y i - θ) * (y j - θ) ∂F.law θ = if i = j then v i else 0 :=
    integral_sub_mul_sub hv θ
  have hm : ∀ i, MemLp (fun y : ι → ℝ => y i - θ) 2 (F.law θ) := fun i => by
    rw [commonEffectFamily_law hv]; exact (h.memLp i).sub (memLp_const θ)
  set T : (ι → ℝ) → ℝ := fun y => ∑ i, c i * y i with hT
  have hd : (fun y => T y * F.densityDeriv θ y) = fun y => F.density θ y * (T y * F.score θ y) := by
    funext y
    rw [commonEffectFamily_densityDeriv hv, commonEffectFamily_score hv]
    ring
  have hTs : (fun y => T y * F.score θ y) = fun y =>
      ∑ i, ∑ j, c i * ivWeight v j * ((y i - θ) * (y j - θ)) +
        θ * ∑ j, ivWeight v j * (y j - θ) := by
    funext y
    rw [commonEffectFamily_score hv]
    have hTy : T y = ∑ i, c i * (y i - θ) + θ := by
      simp only [hT, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc, one_mul,
        sub_add_cancel]
    rw [hTy, add_mul, Finset.sum_mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hint1 : ∀ i j, Integrable (fun y : ι → ℝ => c i * ivWeight v j * ((y i - θ) * (y j - θ)))
      (F.law θ) := fun i j => ((hm i).integrable_mul (hm j)).const_mul _
  have hint2 : Integrable (fun y : ι → ℝ => θ * ∑ j, ivWeight v j * (y j - θ)) (F.law θ) :=
    (integrable_finsetSum _ fun j _ => ((hm j).integrable one_le_two).const_mul _).const_mul _
  have hint1' : Integrable (fun y : ι → ℝ =>
      ∑ i, ∑ j, c i * ivWeight v j * ((y i - θ) * (y j - θ))) (F.law θ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j
  have hint : Integrable (fun y => T y * F.score θ y) (F.law θ) := by
    rw [hTs]; exact hint1'.add hint2
  have h0 : ∀ j, ∫ y, (y j - θ) ∂F.law θ = 0 := fun j => by
    have hj : ∫ y, y j ∂(Measure.pi fun i => gaussianReal θ (v i).toNNReal) = θ :=
      h.integral_eq j
    rw [commonEffectFamily_law hv, integral_sub ((h.memLp j).integrable one_le_two)
      (integrable_const θ), hj, integral_const, probReal_univ, one_smul, sub_self]
  have hE0 : ∫ y, θ * ∑ j, ivWeight v j * (y j - θ) ∂F.law θ = 0 := by
    rw [integral_const_mul, integral_finsetSum _ fun j _ =>
      ((hm j).integrable one_le_two).const_mul _]
    simp only [integral_const_mul, h0, mul_zero, Finset.sum_const_zero]
  have hE1 : ∫ y, ∑ i, ∑ j, c i * ivWeight v j * ((y i - θ) * (y j - θ)) ∂F.law θ = 1 := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint1 i j]
    simp only [fun i => integral_finsetSum (μ := F.law θ) _ fun j (_ : j ∈ Finset.univ) =>
      hint1 i j, integral_const_mul, hcov', mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, mul_comm (ivWeight v i), mul_ivWeight hv, mul_one]
  have hval : ∫ y, T y * F.densityDeriv θ y ∂F.ν = 1 := by
    rw [hd, ← ParametricFamily.integral_law (Set.mem_univ θ), hTs, integral_add hint1' hint2,
      hE1, hE0, add_zero]
  have hmean : (fun u => ∫ x, T x * F.density u x ∂F.ν) = id := by
    funext u
    rw [show (fun x => T x * F.density u x) = fun x => F.density u x * T x from
      funext fun x => mul_comm _ _, ← ParametricFamily.integral_law (Set.mem_univ u)]
    exact ((isUnbiased_sum_mul hv hc) u (Set.mem_univ u)).2
  refine ⟨?_, ?_⟩
  · rw [hd]
    exact (ParametricFamily.integrable_law_iff (Set.mem_univ θ)).1 hint
  · rw [hmean, hval]
    exact hasDerivAt_id θ

/-- **The Cramér-Rao bound for linear unbiased estimators**: in the Gaussian common effect
family, `Var_θ(θ̂) ≤ Var_θ(∑ cᵢ yᵢ)` for all weights with `∑ cᵢ = 1`, as an instance of
`variance_ivwEstimate_le` with all its hypotheses verified. -/
theorem variance_ivwEstimate_le_sum_mul [Nonempty ι] {c : ι → ℝ} (hc : ∑ i, c i = 1) (θ : ℝ) :
    Var[ivwEstimate v; (commonEffectFamily hv).law θ] ≤
      Var[fun y => ∑ i, c i * y i; (commonEffectFamily hv).law θ] :=
  variance_ivwEstimate_le hv (isUnbiased_sum_mul hv hc) (meanDerivInterchange_sum_mul hv hc θ)
    (memLp_sum_mul hv c θ)

end Linear

/-- **The Cramér-Rao theorem on the example, for the equal weight average**: the variance `1/7`
of the pooled estimate is at most the variance `7/36` of `∑ yᵢ / 3`. The inequality is the
conclusion of `variance_ivwEstimate_le`; the two numbers are the variances computed in
`example_gaussianModel` and `example_equalWeights`. -/
theorem example_cramerRao_equalWeights : (1 / 7 : ℝ) ≤ 7 / 36 := by
  have h := variance_ivwEstimate_le_sum_mul exampleVar_pos (c := fun _ => 1 / 3)
    (by norm_num) 0
  rw [commonEffectFamily_law exampleVar_pos, (example_gaussianModel 0).2.1,
    (example_equalWeights 0).2.1] at h
  exact h

end MetaAnalysis

end CausalInference
