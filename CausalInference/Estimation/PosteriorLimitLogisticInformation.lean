/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLogisticLikelihood
public import CausalInference.Estimation.LawOfLargeNumbers
public import CausalInference.Estimation.ConvergenceInProbability
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The information matrix of the logistic model

For the law `R` of the design argument `c` and a coefficient `ξ₀`, the **information matrix** of
the logistic model is

  `I(ξ₀) = ∫ w(z(c) ⬝ ξ₀) z(c) z(c)ᵀ dR(c)`,  `w = σ (1 - σ)`

(`logisticInfo`). Its quadratic form is `vᵀ I v = ∫ w(z(c) ⬝ ξ₀) (z(c) ⬝ v)² dR`
(`dotProduct_mulVec_logisticInfo`). When the design is bounded almost surely and has full rank
(`z(c) ⬝ v = 0` almost surely only for `v = 0`), `I(ξ₀)` is positive definite
(`posDef_logisticInfo`): the weight is positive, so `vᵀ I v = 0` forces `z(c) ⬝ v = 0` almost
surely.

For an i.i.d. sample of records whose design arguments have law `R`, the weak law of large
numbers gives, for every `e > 0`, with probability tending to one, that the empirical information
`∑_{i < n} w(z(cᵢ) ⬝ ξ₀) z(cᵢ) z(cᵢ)ᵀ` is within `n e` of `n I(ξ₀)` in every entry
(`withProbTendingToOne_abs_logisticEmpInfo_sub_le`).

## Main definitions

* `PosteriorLimit.logisticInfo`.

## Main results

* `integrable_logisticInfo_entry`, `dotProduct_mulVec_logisticInfo`, `posDef_logisticInfo`.
* `withProbTendingToOne_abs_logisticEmpInfo_sub_le`.

## References

* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd edition, Chapman and Hall
  (1989), chapter 4.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Matrix Finset
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open PopulationAdjustment

variable {C κ : Type*} [MeasurableSpace C] [Fintype κ]

/-- The **information matrix** of the logistic model at `ξ₀` for the design law `R`:
`∫ w(z(c) ⬝ ξ₀) z(c) z(c)ᵀ dR(c)` with `w = σ (1 - σ)`. -/
noncomputable def logisticInfo (R : Measure C) (z : C → κ → ℝ) (ξ₀ : κ → ℝ) : Matrix κ κ ℝ :=
  Matrix.of fun j k ↦ ∫ c, sigmoidWeight (z c ⬝ᵥ ξ₀) * z c j * z c k ∂R

variable {R : Measure C} {z : C → κ → ℝ}

lemma measurable_sigmoidWeight_dotProduct (hz : Measurable z) (ξ₀ : κ → ℝ) :
    Measurable fun c ↦ sigmoidWeight (z c ⬝ᵥ ξ₀) :=
  continuous_sigmoidWeight.measurable.comp
    (Finset.measurable_sum _ fun j _ ↦ ((measurable_pi_apply j).comp hz).mul_const _)

/-- The square of a linear form, weighted, as a double sum. -/
lemma sq_dotProduct_mul_eq (a v : κ → ℝ) (s : ℝ) :
    s * (a ⬝ᵥ v) ^ 2 = ∑ j, ∑ k, v j * v k * (s * a j * a k) := by
  rw [sq, dotProduct, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The entries of the information matrix are integrable for a bounded design. -/
lemma integrable_logisticInfo_entry [IsFiniteMeasure R] (hz : Measurable z) {B : ℝ}
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (ξ₀ : κ → ℝ) (j k : κ) :
    Integrable (fun c ↦ sigmoidWeight (z c ⬝ᵥ ξ₀) * z c j * z c k) R := by
  refine Integrable.of_bound (((measurable_sigmoidWeight_dotProduct hz ξ₀).mul
    ((measurable_pi_apply j).comp hz)).mul ((measurable_pi_apply k).comp hz)).aestronglyMeasurable
    (B * B) ?_
  filter_upwards [hB] with c hc
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (sigmoidWeight_pos _)]
  have h1 := sigmoidWeight_le_one (z c ⬝ᵥ ξ₀)
  have h0 := (sigmoidWeight_pos (z c ⬝ᵥ ξ₀)).le
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hc j)
  calc sigmoidWeight (z c ⬝ᵥ ξ₀) * |z c j| * |z c k| ≤ 1 * B * B :=
        mul_le_mul (mul_le_mul h1 (hc j) (abs_nonneg _) zero_le_one) (hc k) (abs_nonneg _)
          (by positivity)
    _ = B * B := by ring

/-- **The quadratic form of the information matrix**:
`vᵀ I v = ∫ w(z(c) ⬝ ξ₀) (z(c) ⬝ v)² dR`. -/
lemma dotProduct_mulVec_logisticInfo [IsFiniteMeasure R] (hz : Measurable z) {B : ℝ}
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (ξ₀ v : κ → ℝ) :
    v ⬝ᵥ logisticInfo R z ξ₀ *ᵥ v = ∫ c, sigmoidWeight (z c ⬝ᵥ ξ₀) * (z c ⬝ᵥ v) ^ 2 ∂R := by
  have hi := integrable_logisticInfo_entry hz hB ξ₀
  have e : ∀ c, sigmoidWeight (z c ⬝ᵥ ξ₀) * (z c ⬝ᵥ v) ^ 2 =
      ∑ j, ∑ k, v j * v k * (sigmoidWeight (z c ⬝ᵥ ξ₀) * z c j * z c k) := fun c ↦
    sq_dotProduct_mul_eq _ _ _
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ (hi j k).const_mul _]
  have h : ∀ j, ∫ c, ∑ k, v j * v k * (sigmoidWeight (z c ⬝ᵥ ξ₀) * z c j * z c k) ∂R =
      ∑ k, v j * v k * logisticInfo R z ξ₀ j k := fun j ↦ by
    rw [integral_finsetSum _ fun k _ ↦ (hi j k).const_mul _]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [integral_const_mul, logisticInfo, Matrix.of_apply]
  rw [Finset.sum_congr rfl fun j _ ↦ h j]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The information matrix is positive definite** for an almost surely bounded design of full
rank. -/
theorem posDef_logisticInfo [IsFiniteMeasure R] (hz : Measurable z) {B : ℝ}
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (hfull : ∀ v : κ → ℝ, (∀ᵐ c ∂R, z c ⬝ᵥ v = 0) → v = 0)
    (ξ₀ : κ → ℝ) : (logisticInfo R z ξ₀).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv ↦ ?_⟩
  · ext j k
    simp only [conjTranspose_apply, logisticInfo, Matrix.of_apply, star_trivial]
    exact integral_congr_ae (ae_of_all _ fun c ↦ by ring)
  · rw [star_trivial, dotProduct_mulVec_logisticInfo hz hB]
    have hint : Integrable (fun c ↦ sigmoidWeight (z c ⬝ᵥ ξ₀) * (z c ⬝ᵥ v) ^ 2) R := by
      have e : (fun c ↦ sigmoidWeight (z c ⬝ᵥ ξ₀) * (z c ⬝ᵥ v) ^ 2) = fun c ↦
          ∑ j, ∑ k, v j * v k * (sigmoidWeight (z c ⬝ᵥ ξ₀) * z c j * z c k) :=
        funext fun c ↦ sq_dotProduct_mul_eq _ _ _
      rw [e]
      exact integrable_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦
        (integrable_logisticInfo_entry hz hB ξ₀ j k).const_mul _
    have h0 : 0 ≤ᵐ[R] fun c ↦ sigmoidWeight (z c ⬝ᵥ ξ₀) * (z c ⬝ᵥ v) ^ 2 :=
      ae_of_all _ fun c ↦ mul_nonneg (sigmoidWeight_pos _).le (sq_nonneg _)
    refine lt_of_le_of_ne (integral_nonneg_of_ae h0) fun hzero ↦ hv (hfull v ?_)
    have := (integral_eq_zero_iff_of_nonneg_ae h0 hint).1 hzero.symm
    filter_upwards [this] with c hc
    have := (mul_eq_zero.1 hc).resolve_left (sigmoidWeight_pos _).ne'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- **The empirical information converges.** For an i.i.d. sample of records whose design
arguments have law `R` and an almost surely bounded design, for every `e > 0`, with probability
tending to one, every entry of the empirical information `∑_{i < n} w(z(cᵢ) ⬝ ξ₀) z(cᵢ) z(cᵢ)ᵀ`
is within `n e` of the matching entry of `n I(ξ₀)`. -/
theorem withProbTendingToOne_abs_logisticEmpInfo_sub_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → C × ℝ} (hO : IsIIDSample O P)
    (hR : P.map (fun ω ↦ (O 0 ω).1) = R) (hz : Measurable z) {B : ℝ}
    (hB : ∀ᵐ c ∂R, ∀ j, |z c j| ≤ B) (ξ₀ : κ → ℝ) {e : ℝ} (he : 0 < e) :
    WithProbTendingToOne P fun n ↦ {ω | ∀ j k,
      |logisticEmpInfo z (fun i : Fin n ↦ O i ω) ξ₀ j k - n * logisticInfo R z ξ₀ j k| ≤
        n * e} := by
  have : IsProbabilityMeasure R := by
    rw [← hR]
    exact (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0).fst).2 inferInstance
  set f : C × ℝ → κ → κ → ℝ :=
    fun x j k ↦ sigmoidWeight (z x.1 ⬝ᵥ ξ₀) * z x.1 j * z x.1 k with hf
  have hfm : Measurable f := by
    refine measurable_pi_iff.2 fun j ↦ measurable_pi_iff.2 fun k ↦ ?_
    exact (((measurable_sigmoidWeight_dotProduct hz ξ₀).mul
      ((measurable_pi_apply j).comp hz)).mul ((measurable_pi_apply k).comp hz)).comp measurable_fst
  have hO1 : AEMeasurable (fun ω ↦ (O 0 ω).1) P := (hO.aemeasurable 0).fst
  have hentry : ∀ j k, Integrable (fun ω ↦ f (O 0 ω) j k) P := fun j k ↦ by
    have h := integrable_logisticInfo_entry hz hB ξ₀ j k
    rw [← hR] at h
    exact h.comp_aemeasurable hO1
  have hint : Integrable (fun ω ↦ f (O 0 ω)) P :=
    Integrable.of_eval fun j ↦ Integrable.of_eval fun k ↦ hentry j k
  have hlim : ∀ j k, (∫ ω, f (O 0 ω) ∂P) j k = logisticInfo R z ξ₀ j k := fun j k ↦ by
    rw [eval_integral (fun j ↦ Integrable.of_eval fun k ↦ hentry j k),
      eval_integral (fun k ↦ hentry j k), logisticInfo, Matrix.of_apply, ← hR,
      integral_map hO1]
    exact ((measurable_sigmoidWeight_dotProduct hz ξ₀).mul ((measurable_pi_apply j).comp
      hz) |>.mul ((measurable_pi_apply k).comp hz)).aestronglyMeasurable
  have hlln := (hO.tendstoInMeasure_smul_sum hfm hint).withProbTendingToOne_dist_lt he
  refine hlln.mono fun n ω hω j k ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω
  have hjk' : dist (((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) j k)
      ((∫ ω, f (O 0 ω) ∂P) j k) < e :=
    ((dist_le_pi_dist _ _ k).trans (dist_le_pi_dist _ _ j)).trans_lt hω
  rw [hlim, Real.dist_eq] at hjk'
  have hsum : logisticEmpInfo z (fun i : Fin n ↦ O i ω) ξ₀ j k = ∑ i ∈ range n, f (O i ω) j k := by
    simp only [logisticEmpInfo, Matrix.of_apply, hf]
    exact Fin.sum_univ_eq_sum_range (fun i ↦ sigmoidWeight (z (O i ω).1 ⬝ᵥ ξ₀) *
      z (O i ω).1 j * z (O i ω).1 k) n
  have happ : ((n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) j k =
      (n : ℝ)⁻¹ * ∑ i ∈ range n, f (O i ω) j k := by
    simp [Finset.sum_apply]
  rw [happ] at hjk'
  rw [hsum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e1 : ∑ i ∈ range n, f (O i ω) j k - n * logisticInfo R z ξ₀ j k =
        n * ((n : ℝ)⁻¹ * ∑ i ∈ range n, f (O i ω) j k - logisticInfo R z ξ₀ j k) := by
      field_simp
    rw [e1, abs_mul, abs_of_pos hn']
    exact mul_le_mul_of_nonneg_left hjk'.le hn'.le

end PosteriorLimit

end CausalInference
