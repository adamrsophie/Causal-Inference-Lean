/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.FisherInformationVector
public import CausalInference.Estimation.CramerRao
public import CausalInference.BiasAnalysis.MeasurementError
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Cramér-Rao bound for a vector parameter

For a vector parameter `θ ∈ ℝ^p` with positive definite Fisher information matrix `I(θ)`:

* gradient form: for a scalar statistic `T` with mean `g(θ) = E_θ[T]`,
  `∇g(θ)ᵀ I(θ)⁻¹ ∇g(θ) ≤ Var_θ(T)`;
* matrix form: for an unbiased estimator `T` of `θ`, `Cov_θ(T) - I(θ)⁻¹` is positive
  semidefinite (the covariance matrix is `CausalInference.BiasAnalysis.MeasurementError.covMatrix`).

Both reduce to the scalar Cauchy-Schwarz step `CausalInference.cramer_rao_core`: for a statistic
`U` with `d_j = E[U s_j]`, the combination `w = (I⁻¹ d)ᵀ s` has `E[U w] = E[w²] = dᵀ I⁻¹ d`. The
inverse `I(θ)⁻¹` is a genuine inverse because `I(θ)` is assumed positive definite.

## Main results

* `CausalInference.cramer_rao_core_vec`: `dᵀ I⁻¹ d ≤ Var U` on a probability space.
* `CausalInference.ParametricFamily.cramer_rao_gradient`, `cramer_rao_matrix`.
* `CausalInference.ParametricFamily.IsRegularAtVec.cramer_rao_gradient_of_bounded`,
  `IsRegularAtVec.cramer_rao_matrix_of_bounded`: at a regular point, for bounded measurable
  statistics, with no interchange hypothesis left.

References: C. R. Rao (1945), *Information and the accuracy attainable in the estimation of
statistical parameters*, Bulletin of the Calcutta Mathematical Society; E. L. Lehmann and
G. Casella (1998), *Theory of Point Estimation*, 2nd edition, chapter 2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric Matrix
open CausalInference.BiasAnalysis.MeasurementError (covMatrix)
open scoped ENNReal

namespace CausalInference

section CoreVec

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℕ}

/-- **The Cramér-Rao inequality with several score components, on a probability space.** If
`s_1, …, s_p` are square integrable with mean zero and the matrix `I = (E[s_j s_k])` is
invertible, and `U` is square integrable with `d_j = E[U s_j]`, then `dᵀ I⁻¹ d ≤ Var U`. -/
theorem cramer_rao_core_vec {U : Ω → ℝ} {s : Fin p → Ω → ℝ} (hU : MemLp U 2 μ)
    (hs : ∀ j, MemLp (s j) 2 μ) (hs0 : ∀ j, μ[s j] = 0)
    (hI : IsUnit (Matrix.of fun j k ↦ ∫ ω, s j ω * s k ω ∂μ)) :
    (fun j ↦ ∫ ω, U ω * s j ω ∂μ) ⬝ᵥ
        ((Matrix.of fun j k ↦ ∫ ω, s j ω * s k ω ∂μ)⁻¹ *ᵥ fun j ↦ ∫ ω, U ω * s j ω ∂μ) ≤
      Var[U; μ] := by
  set I : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun j k ↦ ∫ ω, s j ω * s k ω ∂μ with hIdef
  set d : Fin p → ℝ := fun j ↦ ∫ ω, U ω * s j ω ∂μ with hd
  set c := I⁻¹ *ᵥ d with hc
  set q := d ⬝ᵥ c with hq
  set w : Ω → ℝ := fun ω ↦ ∑ j, c j * s j ω with hw
  have hwL : MemLp w 2 μ := memLp_finsetSum _ fun j _ ↦ (hs j).const_mul (c j)
  have hw0 : μ[w] = 0 := by
    rw [hw, integral_finsetSum _ fun j _ ↦ ((hs j).integrable one_le_two).const_mul _]
    simp [integral_const_mul, hs0]
  have hIc : I *ᵥ c = d := by
    rw [hc, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det I).1 hI), one_mulVec]
  have hUw : μ[U * w] = q := by
    have : (U * w) = fun ω ↦ ∑ j, c j * (U ω * s j ω) := by
      ext ω; simp only [Pi.mul_apply, hw, Finset.mul_sum]; ring_nf
    rw [this, integral_finsetSum _ (f := fun j ω ↦ c j * (U ω * s j ω))
      fun j _ ↦ (hU.integrable_mul (hs j)).const_mul _]
    simp only [integral_const_mul, hq, dotProduct]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hww : μ[w ^ 2] = q := by
    have : (w ^ 2) = fun ω ↦ ∑ j, ∑ k, c j * c k * (s j ω * s k ω) := by
      ext ω
      simp only [Pi.pow_apply, hw, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
    rw [this, integral_finsetSum _ (f := fun j ω ↦ ∑ k, c j * c k * (s j ω * s k ω))
      fun j _ ↦ integrable_finsetSum _ fun k _ ↦ ((hs j).integrable_mul (hs k)).const_mul _]
    have hin : ∀ j, ∫ ω, ∑ k, c j * c k * (s j ω * s k ω) ∂μ =
        ∑ k, c j * c k * ∫ ω, s j ω * s k ω ∂μ := fun j ↦ by
      rw [integral_finsetSum _ (f := fun k ω ↦ c j * c k * (s j ω * s k ω))
        fun k _ ↦ ((hs j).integrable_mul (hs k)).const_mul _]
      simp_rw [integral_const_mul]
    simp_rw [hin]
    rw [hq, ← hIc, dotProduct_comm]
    simp only [dotProduct, mulVec, hIdef, of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hq0 : 0 ≤ q := by
    rw [← hww]; exact integral_nonneg fun ω ↦ pow_two_nonneg (w ω)
  rcases hq0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact variance_nonneg _ _
  · have := (cramer_rao_core hU hwL hw0 (by rw [hww]; exact hpos)).1
    rw [hUw, hww, sq, mul_self_div_self] at this
    exact this

end CoreVec

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S] {p : ℕ} {F : ParametricFamily (Fin p → ℝ) S}

/-- **The Cramér-Rao bound, gradient form.** At an interior point where the first order
interchange holds, the score is square integrable and the information matrix is positive
definite, for a statistic `T` with finite variance whose mean `g` can be differentiated under the
integral sign, `∇g(θ)ᵀ I(θ)⁻¹ ∇g(θ) ≤ Var_θ(T)`. -/
theorem cramer_rao_gradient {T : S → ℝ} {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (h1 : F.PartialDerivInterchange θ) (hT : F.MeanPartialDerivInterchange T θ)
    (hT2 : MemLp T 2 (F.law θ)) (hs : ∀ j, MemLp (fun x ↦ F.scoreVec θ x j) 2 (F.law θ))
    (hI : (F.fisherInfoMatrix θ).PosDef) :
    F.gradMean T θ ⬝ᵥ ((F.fisherInfoMatrix θ)⁻¹ *ᵥ F.gradMean T θ) ≤ Var[T; F.law θ] := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hΘ)
  have hg : F.gradMean T θ = fun j ↦ ∫ x, T x * F.scoreVec θ x j ∂F.law θ :=
    funext fun j ↦ (gradMean_eq hΘ hT j).2
  rw [hg]
  exact cramer_rao_core_vec hT2 hs (integral_scoreVec_eq_zero hΘ h1) hI.isUnit

/-- `T` is an unbiased estimator of the vector parameter: for every `θ ∈ Θ` and every
coordinate `i`, `T_i` is `P_θ`-integrable and `E_θ[T_i] = θ_i`. -/
def IsUnbiasedVec (F : ParametricFamily (Fin p → ℝ) S) (T : S → Fin p → ℝ) : Prop :=
  ∀ θ ∈ F.Θ, ∀ i, Integrable (fun x ↦ T x i) (F.law θ) ∧ F.mean (fun x ↦ T x i) θ = θ i

/-- The partial derivative of a coordinate along a coordinate line: `∂θ_i/∂θ_j = δ_ij`. -/
theorem deriv_update_apply (θ : Fin p → ℝ) (j i : Fin p) :
    deriv (fun t ↦ Function.update θ j t i) (θ j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The variance of a linear combination `aᵀT` is the quadratic form of the covariance
matrix. -/
theorem variance_dotProduct {T : S → Fin p → ℝ} {μ : Measure S} [IsProbabilityMeasure μ]
    (hT2 : ∀ i, MemLp (fun x ↦ T x i) 2 μ) (a : Fin p → ℝ) :
    Var[fun x ↦ ∑ i, a i * T x i; μ] = a ⬝ᵥ (covMatrix μ (fun i x ↦ T x i) *ᵥ a) := by
  have hfun : (fun x ↦ ∑ i, a i * T x i) = ∑ i, fun x ↦ a i * T x i := by
    ext x; simp
  have hm : ∀ i, MemLp (fun x ↦ a i * T x i) 2 μ := fun i ↦ (hT2 i).const_mul _
  rw [← covariance_self (memLp_finsetSum _ fun i _ ↦ hm i).aemeasurable, hfun,
    covariance_sum_left hm (memLp_finsetSum' _ fun i _ ↦ hm i)]
  simp_rw [covariance_sum_right hm (hm _), covariance_const_mul_left,
    covariance_const_mul_right]
  simp only [dotProduct, mulVec, covMatrix, of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The matrix Cramér-Rao bound.** If `T` is an unbiased estimator of `θ ∈ ℝ^p` with finite
second moments, the mean of each `T_i` can be differentiated under the integral sign at the
interior point `θ`, the first order interchange holds, the score is square integrable and the
information matrix is positive definite, then `aᵀ I(θ)⁻¹ a ≤ aᵀ Cov_θ(T) a` for every `a`, that
is, `Cov_θ(T) - I(θ)⁻¹` is positive semidefinite. -/
theorem cramer_rao_matrix {T : S → Fin p → ℝ} {θ : Fin p → ℝ} (hΘ : F.Θ ∈ 𝓝 θ)
    (hu : F.IsUnbiasedVec T) (h1 : F.PartialDerivInterchange θ)
    (hT : ∀ i, F.MeanPartialDerivInterchange (fun x ↦ T x i) θ)
    (hT2 : ∀ i, MemLp (fun x ↦ T x i) 2 (F.law θ))
    (hs : ∀ j, MemLp (fun x ↦ F.scoreVec θ x j) 2 (F.law θ))
    (hI : (F.fisherInfoMatrix θ).PosDef) :
    (∀ a : Fin p → ℝ, a ⬝ᵥ ((F.fisherInfoMatrix θ)⁻¹ *ᵥ a) ≤
        a ⬝ᵥ (covMatrix (F.law θ) (fun i x ↦ T x i) *ᵥ a)) ∧
      (covMatrix (F.law θ) (fun i x ↦ T x i) - (F.fisherInfoMatrix θ)⁻¹).PosSemidef := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds hΘ)
  have hquad : ∀ a : Fin p → ℝ, a ⬝ᵥ ((F.fisherInfoMatrix θ)⁻¹ *ᵥ a) ≤
      a ⬝ᵥ (covMatrix (F.law θ) (fun i x ↦ T x i) *ᵥ a) := by
    intro a
    set U : S → ℝ := fun x ↦ ∑ i, a i * T x i with hUdef
    have hU : MemLp U 2 (F.law θ) := memLp_finsetSum _ fun i _ ↦ (hT2 i).const_mul _
    have hgrad : ∀ i j, ∫ x, T x i * F.scoreVec θ x j ∂F.law θ = if i = j then 1 else 0 := by
      intro i j
      rw [← (gradMean_eq hΘ (hT i) j).2, gradMean, ← deriv_update_apply θ j i]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [slice_mem_nhds hΘ j] with t ht
      exact (hu _ ht i).2
    have hd : (fun j ↦ ∫ x, U x * F.scoreVec θ x j ∂F.law θ) = a := by
      ext j
      have : (fun x ↦ U x * F.scoreVec θ x j) =
          fun x ↦ ∑ i, a i * (T x i * F.scoreVec θ x j) := by
        ext x
        simp only [hUdef, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
      rw [this, integral_finsetSum _ (f := fun i x ↦ a i * (T x i * F.scoreVec θ x j))
        fun i _ ↦ ((hT2 i).integrable_mul (hs j)).const_mul _]
      simp_rw [integral_const_mul, hgrad]
      simp
    have hc := cramer_rao_core_vec hU hs (integral_scoreVec_eq_zero hΘ h1) hI.isUnit
    rw [hd] at hc
    rw [← variance_dotProduct hT2 a]
    exact hc
  refine ⟨hquad, posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun a ↦ ?_⟩⟩
  · refine IsHermitian.sub ?_ hI.isHermitian.inv
    ext i k
    simp [covMatrix, covariance_comm]
  · rw [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg]
    exact hquad a

/-! ### Regular points and bounded statistics -/

namespace IsRegularAtVec

variable {θ : Fin p → ℝ}

/-- At a regular point, the mean of a bounded measurable statistic can be differentiated under
the integral sign along every coordinate line. -/
theorem meanPartialDerivInterchange_of_bounded (h : F.IsRegularAtVec θ) {T : S → ℝ}
    (hTm : Measurable T) {C : ℝ} (hTC : ∀ x, |T x| ≤ C) :
    F.MeanPartialDerivInterchange T θ := by
  obtain ⟨ε, hε, hball, hC, b₁, b₂, hb₁, hb₂, hbd⟩ := h.smooth_dominated
  have hθ : θ ∈ ball θ (ε / 2) := mem_ball_self (half_pos hε)
  intro k
  exact (F.slice θ k).meanDerivInterchange_of_bounded hTm hTC (half_pos hε)
    (fun t ht ↦ hball (update_mem_ball hε hθ k ht)) hb₁
    (hC.mono fun x hx t ht ↦ (hasDerivAt_slice_of_contDiffOn hx k
      (update_mem_ball hε hθ k ht)).differentiableAt)
    (hbd.mono fun x hx t ht ↦ by
      have := (hx _ (update_mem_ball hε hθ k ht) k k).1
      rwa [partialDeriv_update] at this)

/-- **The gradient Cramér-Rao bound for a bounded statistic at a regular point** with positive
definite information: `∇g(θ)ᵀ I(θ)⁻¹ ∇g(θ) ≤ Var_θ(T)`, with no interchange hypothesis. -/
theorem cramer_rao_gradient_of_bounded (h : F.IsRegularAtVec θ)
    (hI : (F.fisherInfoMatrix θ).PosDef) {T : S → ℝ} (hTm : Measurable T) {C : ℝ}
    (hTC : ∀ x, |T x| ≤ C) :
    F.gradMean T θ ⬝ᵥ ((F.fisherInfoMatrix θ)⁻¹ *ᵥ F.gradMean T θ) ≤ Var[T; F.law θ] := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds h.mem_nhds)
  exact cramer_rao_gradient h.mem_nhds h.interchange.1.self_of_nhds
    (h.meanPartialDerivInterchange_of_bounded hTm hTC)
    (MemLp.of_bound hTm.aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hTC x))
    h.memLp_scoreVec hI

/-- **The matrix Cramér-Rao bound for a bounded unbiased estimator at a regular point** with
positive definite information: `Cov_θ(T) - I(θ)⁻¹` is positive semidefinite, with no
interchange hypothesis. -/
theorem cramer_rao_matrix_of_bounded (h : F.IsRegularAtVec θ)
    (hI : (F.fisherInfoMatrix θ).PosDef) {T : S → Fin p → ℝ} (hu : F.IsUnbiasedVec T)
    (hTm : ∀ i, Measurable fun x ↦ T x i) {C : ℝ} (hTC : ∀ x i, |T x i| ≤ C) :
    (∀ a : Fin p → ℝ, a ⬝ᵥ ((F.fisherInfoMatrix θ)⁻¹ *ᵥ a) ≤
        a ⬝ᵥ (covMatrix (F.law θ) (fun i x ↦ T x i) *ᵥ a)) ∧
      (covMatrix (F.law θ) (fun i x ↦ T x i) - (F.fisherInfoMatrix θ)⁻¹).PosSemidef := by
  have := isProbabilityMeasure_law (mem_of_mem_nhds h.mem_nhds)
  exact cramer_rao_matrix h.mem_nhds hu h.interchange.1.self_of_nhds
    (fun i ↦ h.meanPartialDerivInterchange_of_bounded (hTm i) (fun x ↦ hTC x i))
    (fun i ↦ MemLp.of_bound (hTm i).aestronglyMeasurable C
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hTC x i))
    h.memLp_scoreVec hI

end IsRegularAtVec

end ParametricFamily

end CausalInference
