/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.SandwichMatrix
public import CausalInference.PopulationAdjustment.WeightedConsistencyArm
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The stacked estimating equations of the weighted arm mean

The weighted (matching adjusted) estimate of the mean of arm `a` is a function of a dual
parameter `β ∈ ℝ^p` (the tilt of the weights) and of the arm mean `m`. Both solve one stacked
system of estimating equations in the parameter `θ = (β, m) ∈ ℝ^(Fin p ⊕ Unit)`:

`ψ(x, s, y; θ) = (w_β(x) (φ(x) - t), 1{s = a} w_β(x) (y - m))`, with
`w_β(x) = exp(βᵀ(φ(x) - t)) = tiltWeight φ t 0 β x`.

The first block is the gradient of the dual of the entropy balancing problem (the balance
equations), the second the equation of a weighted mean. This file gives the estimating function,
its Jacobian matrix, their measurability and regularity, envelopes under bounded features, and
the bread `A = -E ∇ψ`. The bread is block lower triangular: its balance block is minus the
second moment matrix of the centered features under the tilt, `M(β) = E[w_β Δ Δᵀ]`
(`tiltedSecondMoment`), and its arm block is `E[1{A = a} w_β]`. Under the margin condition of
`WeightedConsistencyFeasible` and bounded features `M(β)` is positive definite, so the bread is
nonsingular as soon as `P(A = a) > 0` (`det_breadMatrix_weightedEstJac_ne_zero`).

## Main definitions

* `stackedBalance`, `stackedParam`: the coordinates of a stacked parameter.
* `weightedEstFun`, `weightedEstJac`: the estimating function and its Jacobian matrix.
* `tiltedSecondMoment`: the second moment matrix of the centered features under the tilt.

## Main results

* `weightedEstFun_hasFDerivAt`: `ψ(z; ·)` has Jacobian matrix `weightedEstJac`.
* `measurable_weightedEstFun`, `measurable_weightedEstJac`, `continuous_weightedEstJac`.
* `abs_weightedEstJac_le`, `norm_weightedEstFun_sq_le`: envelopes on a ball.
* `breadMatrix_weightedEstJac`, `det_breadMatrix_weightedEstJac`.
* `posDef_tiltedSecondMoment`, `det_breadMatrix_weightedEstJac_ne_zero`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* L. A. Stefanski and D. D. Boos (2002), *The calculus of M-estimation*, The American
  Statistician.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

variable {𝒳 : Type*} {p : ℕ}

/-! ### The stacked parameter, the estimating function and its Jacobian -/

/-- The balance coordinates `β` of a stacked parameter `θ = (β, m)`. -/
def stackedBalance (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) : Fin p → ℝ := fun j => θ (Sum.inl j)

/-- The stacked parameter `θ = (β, m)`. -/
def stackedParam (β : Fin p → ℝ) (m : ℝ) : EuclideanSpace ℝ (Fin p ⊕ Unit) :=
  WithLp.toLp 2 (Sum.elim β fun _ => m)

@[simp]
theorem stackedBalance_stackedParam (β : Fin p → ℝ) (m : ℝ) :
    stackedBalance (stackedParam β m) = β := rfl

@[simp]
theorem stackedParam_inr (β : Fin p → ℝ) (m : ℝ) (u : Unit) :
    stackedParam β m (Sum.inr u) = m := rfl

/-- **The stacked estimating function** of the weighted arm mean of arm `a`:
`ψ(z; θ) = (w_β(x) (φ(x) - t), 1{s = a} w_β(x) (y - m))` for the record `z = (x, s, y)`, with
the tilt `w_β = tiltWeight φ t 0 β`. -/
noncomputable def weightedEstFun (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool)
    (z : 𝒳 × Bool × ℝ) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    EuclideanSpace ℝ (Fin p ⊕ Unit) :=
  WithLp.toLp 2 (Sum.elim (fun j => tiltWeight φ t 0 (stackedBalance θ) z.1 * (φ z.1 j - t j))
    fun _ => armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 * (z.2.2 - θ (Sum.inr ())))

/-- **The Jacobian matrix of the stacked estimating function**: block lower triangular, with the
balance block `w_β Δ Δᵀ` (`Δ = φ(x) - t`), a zero upper right block, the coupling row
`1{s = a} w_β (y - m) Δᵀ` and the arm entry `-1{s = a} w_β`. -/
noncomputable def weightedEstJac (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool)
    (z : 𝒳 × Bool × ℝ) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ :=
  Matrix.fromBlocks
    (Matrix.of fun j k => tiltWeight φ t 0 (stackedBalance θ) z.1 * (φ z.1 j - t j) *
      (φ z.1 k - t k)) 0
    (Matrix.of fun _ k => armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 *
      (z.2.2 - θ (Sum.inr ())) * (φ z.1 k - t k))
    (Matrix.of fun _ _ => -(armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1))

/-- The tilt as the exponential of a finite sum of coordinates. -/
theorem tiltWeight_stackedBalance (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (x : 𝒳)
    (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    tiltWeight φ t 0 (stackedBalance θ) x = Real.exp (∑ j, θ (Sum.inl j) * (φ x j - t j)) := by
  simp [tiltWeight, stackedBalance, dotProduct]

/-- **The Jacobian of the stacked estimating function**: for every record and every parameter,
`ψ(z; ·)` has derivative `v ↦ J(z; θ) v` with `J = weightedEstJac`. -/
theorem weightedEstFun_hasFDerivAt (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool)
    (z : 𝒳 × Bool × ℝ) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    HasFDerivAt (weightedEstFun φ t a z)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (weightedEstJac φ t a z θ)) θ := by
  refine HasStrictFDerivAt.hasFDerivAt ?_
  rw [hasStrictFDerivAt_euclidean]
  have hs : HasStrictFDerivAt
      (fun θ : EuclideanSpace ℝ (Fin p ⊕ Unit) => ∑ j, θ (Sum.inl j) * (φ z.1 j - t j))
      (∑ j, (φ z.1 j - t j) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin p ⊕ Unit => ℝ) (Sum.inl j)) θ :=
    HasStrictFDerivAt.fun_sum fun j _ =>
      (PiLp.hasStrictFDerivAt_apply 2 θ (Sum.inl j)).mul_const (φ z.1 j - t j)
  have he := hs.exp
  intro k
  rcases k with j | u
  · have h1 := he.mul_const (φ z.1 j - t j)
    have hfun : (fun x : EuclideanSpace ℝ (Fin p ⊕ Unit) => weightedEstFun φ t a z x (Sum.inl j)) =
        fun x => Real.exp (∑ j, x (Sum.inl j) * (φ z.1 j - t j)) * (φ z.1 j - t j) := by
      funext x; simp only [weightedEstFun, tiltWeight_stackedBalance]; rfl
    rw [hfun]
    refine h1.congr_fderiv ?_
    ext v
    simp only [smul_apply, sum_apply, PiLp.proj_apply,
      smul_eq_mul, ContinuousLinearMap.comp_apply, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec,
      dotProduct, weightedEstJac, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, Finset.mul_sum, tiltWeight_stackedBalance]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have h1 := (he.const_mul (armIndObs a z)).mul
      ((hasStrictFDerivAt_const z.2.2 θ).sub (PiLp.hasStrictFDerivAt_apply 2 θ (Sum.inr u)))
    have hfun : (fun x : EuclideanSpace ℝ (Fin p ⊕ Unit) => weightedEstFun φ t a z x (Sum.inr u)) =
        fun x => armIndObs a z * Real.exp (∑ j, x (Sum.inl j) * (φ z.1 j - t j)) *
          (z.2.2 - x (Sum.inr u)) := by
      funext x; simp only [weightedEstFun, tiltWeight_stackedBalance]; rfl
    rw [hfun]
    refine h1.congr_fderiv ?_
    ext v
    simp only [zero_sub, smul_neg, Pi.sub_apply, add_apply,
      neg_apply, smul_apply, PiLp.proj_apply, smul_eq_mul,
      sum_apply, ContinuousLinearMap.comp_apply, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec, dotProduct, weightedEstJac, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Finset.mul_sum, tiltWeight_stackedBalance,
      Finset.univ_unique, Finset.sum_singleton, neg_mul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-! ### Measurability and continuity -/

section Measurability

variable [MeasurableSpace 𝒳]

theorem measurable_tiltWeight_fst {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t β : Fin p → ℝ) :
    Measurable fun z : 𝒳 × Bool × ℝ => tiltWeight φ t 0 β z.1 :=
  (measurable_tiltWeight φ t 0 β hφ).comp measurable_fst

theorem measurable_feature_fst {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (j : Fin p) :
    Measurable fun z : 𝒳 × Bool × ℝ => φ z.1 j :=
  (measurable_pi_apply j).comp (hφ.comp measurable_fst)

/-- The stacked estimating function is measurable in the record. -/
theorem measurable_weightedEstFun {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t : Fin p → ℝ)
    (a : Bool) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    Measurable fun z : 𝒳 × Bool × ℝ => weightedEstFun φ t a z θ := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun k => ?_)
  rcases k with j | u
  · exact (measurable_tiltWeight_fst hφ t _).mul ((measurable_feature_fst hφ j).sub_const _)
  · exact ((measurable_armIndObs a).mul (measurable_tiltWeight_fst hφ t _)).mul
      (measurable_snd.snd.sub_const _)

/-- Every entry of the Jacobian matrix is measurable in the record. -/
theorem measurable_weightedEstJac {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) (t : Fin p → ℝ)
    (a : Bool) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) (k l : Fin p ⊕ Unit) :
    Measurable fun z : 𝒳 × Bool × ℝ => weightedEstJac φ t a z θ k l := by
  have ht := measurable_tiltWeight_fst hφ t (stackedBalance θ)
  rcases k with j | u <;> rcases l with k | v
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
    exact (ht.mul ((measurable_feature_fst hφ j).sub_const _)).mul
      ((measurable_feature_fst hφ k).sub_const _)
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    exact measurable_const
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
    exact (((measurable_armIndObs a).mul ht).mul (measurable_snd.snd.sub_const _)).mul
      ((measurable_feature_fst hφ k).sub_const _)
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    exact ((measurable_armIndObs a).mul ht).neg

end Measurability

/-- The tilt is continuous in the stacked parameter. -/
theorem continuous_tiltWeight_stackedBalance (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (x : 𝒳) :
    Continuous fun θ : EuclideanSpace ℝ (Fin p ⊕ Unit) =>
      tiltWeight φ t 0 (stackedBalance θ) x := by
  simp only [tiltWeight_stackedBalance]
  have : ∀ i, Continuous fun θ : EuclideanSpace ℝ (Fin p ⊕ Unit) => θ i := fun i =>
    PiLp.continuous_apply 2 _ i
  fun_prop

/-- Every entry of the Jacobian matrix is continuous in the parameter. -/
theorem continuous_weightedEstJac (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ) (a : Bool)
    (z : 𝒳 × Bool × ℝ) (k l : Fin p ⊕ Unit) :
    Continuous fun θ => weightedEstJac φ t a z θ k l := by
  have ht := continuous_tiltWeight_stackedBalance φ t z.1
  have hm : Continuous fun θ : EuclideanSpace ℝ (Fin p ⊕ Unit) => θ (Sum.inr ()) :=
    PiLp.continuous_apply 2 _ _
  rcases k with j | u <;> rcases l with k | v
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
    fun_prop
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    exact continuous_const
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]
    fun_prop
  · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    fun_prop

/-! ### Envelopes under bounded features -/

/-- A coordinate of a vector is at most its sup norm in absolute value. -/
theorem abs_apply_le_of_norm_le {v : Fin p → ℝ} {B : ℝ} (hv : ‖v‖ ≤ B) (j : Fin p) :
    |v j| ≤ B := by
  rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm v j).trans hv

/-- **The tilt is bounded on bounded parameters**: if `‖φ(x) - t‖ ≤ B` and `‖β‖ ≤ R`, then
`exp(-p R B) ≤ w_β(x) ≤ exp(p R B)`. -/
theorem tiltWeight_mem_Icc {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {B R : ℝ} {x : 𝒳}
    (hx : ‖φ x - t‖ ≤ B) {β : Fin p → ℝ} (hβ : ‖β‖ ≤ R) :
    Real.exp (-(p * (R * B))) ≤ tiltWeight φ t 0 β x ∧
      tiltWeight φ t 0 β x ≤ Real.exp (p * (R * B)) := by
  have h := (abs_dotProduct_le_mul_norm β (φ x - t)).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hβ hx (norm_nonneg _) ((norm_nonneg _).trans hβ)) (Nat.cast_nonneg p))
  rw [tiltWeight, zero_add]
  exact ⟨Real.exp_le_exp.2 (neg_le_of_abs_le h), Real.exp_le_exp.2 (le_of_abs_le h)⟩

/-- The balance coordinates are bounded by the norm of the stacked parameter. -/
theorem norm_stackedBalance_le (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    ‖stackedBalance θ‖ ≤ ‖θ‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg θ)).2 fun j => by
    simpa [stackedBalance] using PiLp.norm_apply_le θ (Sum.inl j)

/-- The envelope constant on the closed ball of radius `r` around `θ₀`, with features bounded by
`B`: `exp(p R B) (1 + B)² (1 + R)` with `R = ‖θ₀‖ + r`. -/
noncomputable def weightedEnvConst (p : ℕ) (B : ℝ) (θ₀ : EuclideanSpace ℝ (Fin p ⊕ Unit))
    (r : ℝ) : ℝ :=
  Real.exp (p * ((‖θ₀‖ + r) * B)) * (1 + B) ^ 2 * (1 + (‖θ₀‖ + r))

/-- **Envelopes of the stacked equations.** For a record with `‖φ(x) - t‖ ≤ B` and a parameter in
the closed ball of radius `r ≥ 0` around `θ₀`, every entry of the Jacobian matrix and of the
estimating function is at most `weightedEnvConst p B θ₀ r (1 + |y|)` in absolute value. -/
theorem abs_weightedEstJac_le {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {a : Bool} {B r : ℝ}
    {θ₀ θ : EuclideanSpace ℝ (Fin p ⊕ Unit)} (hθ : θ ∈ Metric.closedBall θ₀ r) (hr : 0 ≤ r)
    {z : 𝒳 × Bool × ℝ} (hz : ‖φ z.1 - t‖ ≤ B) :
    (∀ k l, |weightedEstJac φ t a z θ k l| ≤ weightedEnvConst p B θ₀ r * (1 + |z.2.2|)) ∧
      ∀ k, |weightedEstFun φ t a z θ k| ≤ weightedEnvConst p B θ₀ r * (1 + |z.2.2|) := by
  set R := ‖θ₀‖ + r with hR
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hz
  have hR0 : 0 ≤ R := add_nonneg (norm_nonneg _) hr
  have hθR : ‖θ‖ ≤ R := by
    have := norm_le_of_mem_closedBall hθ
    linarith
  set E := Real.exp (p * (R * B)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨-, hw⟩ := tiltWeight_mem_Icc (β := stackedBalance θ) hz
    ((norm_stackedBalance_le θ).trans hθR)
  have hw0 : 0 < tiltWeight φ t 0 (stackedBalance θ) z.1 := tiltWeight_pos _ _ _ _ _
  have hΔ : ∀ j, |φ z.1 j - t j| ≤ B := fun j => abs_apply_le_of_norm_le hz j
  have hm : |θ (Sum.inr ())| ≤ R := by
    have := PiLp.norm_apply_le θ (Sum.inr ())
    rw [Real.norm_eq_abs] at this; linarith
  have hy : |z.2.2 - θ (Sum.inr ())| ≤ (1 + R) * (1 + |z.2.2|) := by
    have := abs_sub z.2.2 (θ (Sum.inr ()))
    nlinarith [abs_nonneg z.2.2]
  have hInd := armIndObs_eq_zero_or_one a z
  have hI0 : 0 ≤ armIndObs a z := by rcases hInd with h | h <;> simp [h]
  have hI1 : armIndObs a z ≤ 1 := by rcases hInd with h | h <;> simp [h]
  have hK : weightedEnvConst p B θ₀ r * (1 + |z.2.2|) = E * (1 + B) ^ 2 * ((1 + R) * (1 + |z.2.2|))
    := by rw [weightedEnvConst]; ring
  have h1y : 1 ≤ (1 + R) * (1 + |z.2.2|) := by nlinarith [abs_nonneg z.2.2]
  have hB1 : 1 ≤ (1 + B) ^ 2 := by nlinarith
  have hBB : B * B ≤ (1 + B) ^ 2 := by nlinarith
  have hB2 : B ≤ (1 + B) ^ 2 := by nlinarith
  have hpos : 0 ≤ E * (1 + B) ^ 2 := by positivity
  refine ⟨fun k l => ?_, fun k => ?_⟩
  · rw [hK]
    rcases k with j | u <;> rcases l with k | v
    · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, abs_mul,
        abs_of_pos hw0]
      calc tiltWeight φ t 0 (stackedBalance θ) z.1 * |φ z.1 j - t j| * |φ z.1 k - t k|
          ≤ E * B * B := by gcongr; exacts [hΔ j, hΔ k]
        _ = E * (B * B) * 1 := by ring
        _ ≤ E * (1 + B) ^ 2 * ((1 + R) * (1 + |z.2.2|)) := by gcongr
    · simp only [weightedEstJac, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, abs_zero]
      positivity
    · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, abs_mul,
        abs_of_pos hw0, abs_of_nonneg hI0]
      calc armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 *
            |z.2.2 - θ (Sum.inr ())| * |φ z.1 k - t k|
          ≤ 1 * E * ((1 + R) * (1 + |z.2.2|)) * B := by gcongr; exact hΔ k
        _ = E * B * ((1 + R) * (1 + |z.2.2|)) := by ring
        _ ≤ E * (1 + B) ^ 2 * ((1 + R) * (1 + |z.2.2|)) := by gcongr
    · simp only [weightedEstJac, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, abs_neg, abs_mul,
        abs_of_pos hw0, abs_of_nonneg hI0]
      calc armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 ≤ 1 * E := by gcongr
        _ = E * 1 * 1 := by ring
        _ ≤ E * (1 + B) ^ 2 * ((1 + R) * (1 + |z.2.2|)) := by gcongr
  · rw [hK]
    rcases k with j | u
    · simp only [weightedEstFun, Sum.elim_inl, PiLp.toLp_apply, abs_mul, abs_of_pos hw0]
      calc tiltWeight φ t 0 (stackedBalance θ) z.1 * |φ z.1 j - t j| ≤ E * B := by
            gcongr; exact hΔ j
        _ = E * B * 1 := by ring
        _ ≤ E * (1 + B) ^ 2 * ((1 + R) * (1 + |z.2.2|)) := by gcongr
    · simp only [weightedEstFun, Sum.elim_inr, PiLp.toLp_apply, abs_mul, abs_of_pos hw0,
        abs_of_nonneg hI0]
      calc armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 * |z.2.2 - θ (Sum.inr ())|
          ≤ 1 * E * ((1 + R) * (1 + |z.2.2|)) := by gcongr
        _ = E * 1 * ((1 + R) * (1 + |z.2.2|)) := by ring
        _ ≤ E * (1 + B) ^ 2 * ((1 + R) * (1 + |z.2.2|)) := by gcongr

/-- The squared norm of the estimating function on the ball is at most
`(p + 1) (K (1 + |y|))²`, `K = weightedEnvConst p B θ₀ r`. -/
theorem norm_weightedEstFun_sq_le {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {a : Bool} {B r : ℝ}
    {θ₀ θ : EuclideanSpace ℝ (Fin p ⊕ Unit)} (hθ : θ ∈ Metric.closedBall θ₀ r) (hr : 0 ≤ r)
    {z : 𝒳 × Bool × ℝ} (hz : ‖φ z.1 - t‖ ≤ B) :
    ‖weightedEstFun φ t a z θ‖ ^ 2 ≤
      (p + 1) * (weightedEnvConst p B θ₀ r * (1 + |z.2.2|)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ k, ‖weightedEstFun φ t a z θ k‖ ^ 2
      ≤ ∑ _k : Fin p ⊕ Unit, (weightedEnvConst p B θ₀ r * (1 + |z.2.2|)) ^ 2 :=
        Finset.sum_le_sum fun k _ => by
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) ((abs_weightedEstJac_le hθ hr hz).2 k) 2
    _ = (p + 1) * (weightedEnvConst p B θ₀ r * (1 + |z.2.2|)) ^ 2 := by simp

/-! ### Integrability -/

section Integrability

variable [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)}

/-- A bounded measurable function is integrable under a finite measure. -/
theorem integrable_of_abs_le [IsFiniteMeasure ν] {f : 𝒳 × Bool × ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (h : ∀ z, |f z| ≤ C) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun z => by
    rw [Real.norm_eq_abs]; exact h z)

/-- The tilt times an integrable function is integrable, for bounded features. -/
theorem integrable_tiltWeight_mul {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ) {f : 𝒳 × Bool × ℝ → ℝ}
    (hf : Integrable f ν) : Integrable (fun z => tiltWeight φ t 0 β z.1 * f z) ν :=
  hf.bdd_mul (c := Real.exp (p * (‖β‖ * B))) (measurable_tiltWeight_fst hφ t β).aestronglyMeasurable
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (tiltWeight_pos _ _ _ _ _)]
      exact (tiltWeight_mem_Icc (hB z.1) le_rfl).2)

/-- The products of the tilt with centered features are integrable under a finite measure. -/
theorem integrable_tiltWeight_mul_feature [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ)
    (j k : Fin p) :
    Integrable (fun z : 𝒳 × Bool × ℝ =>
      tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) ν := by
  have h : Integrable (fun z : 𝒳 × Bool × ℝ => (φ z.1 j - t j) * (φ z.1 k - t k)) ν :=
    integrable_of_abs_le (((measurable_feature_fst hφ j).sub_const _).mul
      ((measurable_feature_fst hφ k).sub_const _)) (C := B * B) fun z => by
        rw [abs_mul]
        exact mul_le_mul (abs_apply_le_of_norm_le (hB z.1) j) (abs_apply_le_of_norm_le (hB z.1) k)
          (abs_nonneg _) ((abs_nonneg _).trans (abs_apply_le_of_norm_le (hB z.1) j))
  simpa only [mul_assoc] using integrable_tiltWeight_mul hφ hB β h

end Integrability

/-! ### The bread -/

section Bread

variable [MeasurableSpace 𝒳] {ν : Measure (𝒳 × Bool × ℝ)}

/-- The **second moment matrix of the centered features under the tilt**:
`M(β) = E[w_β(X) (φ(X) - t)(φ(X) - t)ᵀ]`. -/
noncomputable def tiltedSecondMoment (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t β : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k => ∫ z, tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) * (φ z.1 k - t k) ∂ν

/-- **The bread is block lower triangular**: `A = -E ∇ψ` has the balance block `-M(β)`, a zero
upper right block (the balance equations do not involve `m`), the coupling row
`-E[1{A = a} w_β (Y - m) Δᵀ]` and the arm entry `E[1{A = a} w_β]`. -/
theorem breadMatrix_weightedEstJac (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    breadMatrix ν (weightedEstJac φ t a) θ = Matrix.fromBlocks
      (-tiltedSecondMoment ν φ t (stackedBalance θ)) 0
      (Matrix.of fun _ k => -∫ z, armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 *
        (z.2.2 - θ (Sum.inr ())) * (φ z.1 k - t k) ∂ν)
      (Matrix.of fun _ _ => ∫ z, armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 ∂ν) := by
  ext k l
  rcases k with j | u <;> rcases l with k | v <;>
    simp [breadMatrix, weightedEstJac, tiltedSecondMoment, integral_neg]

/-- **The determinant of the bread**: `det A = (-1)^p det M(β) E[1{A = a} w_β]`. -/
theorem det_breadMatrix_weightedEstJac (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    (breadMatrix ν (weightedEstJac φ t a) θ).det = (-1) ^ p *
      (tiltedSecondMoment ν φ t (stackedBalance θ)).det *
        ∫ z, armIndObs a z * tiltWeight φ t 0 (stackedBalance θ) z.1 ∂ν := by
  rw [breadMatrix_weightedEstJac, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg,
    Matrix.det_unique (n := Unit)]
  simp

/-- The quadratic form of the tilted second moment matrix:
`vᵀ M(β) v = E[w_β(X) (vᵀ(φ(X) - t))²]`. -/
theorem dotProduct_tiltedSecondMoment_mulVec [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β v : Fin p → ℝ) :
    v ⬝ᵥ (tiltedSecondMoment ν φ t β *ᵥ v) =
      ∫ z, tiltWeight φ t 0 β z.1 * (v ⬝ᵥ (φ z.1 - t)) ^ 2 ∂ν := by
  have hint := integrable_tiltWeight_mul_feature (ν := ν) hφ hB β
  have hpt : ∀ z : 𝒳 × Bool × ℝ, tiltWeight φ t 0 β z.1 * (v ⬝ᵥ (φ z.1 - t)) ^ 2 =
      ∑ j, ∑ k, v j * (tiltWeight φ t 0 β z.1 * (φ z.1 j - t j) * (φ z.1 k - t k)) * v k := by
    intro z
    simp only [dotProduct, Pi.sub_apply]
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    ((hint j k).const_mul _).mul_const _]
  simp only [dotProduct, mulVec, tiltedSecondMoment, Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => ((hint j k).const_mul _).mul_const _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, integral_const_mul]
  ring

/-- **The tilted second moment matrix is positive definite** under the margin condition: for
`v ≠ 0`, `vᵀ M(β) v > 0`, because `vᵀ(φ(X) - t) ≥ ‖v‖ δ > 0` with probability at least `δ`. -/
theorem dotProduct_tiltedSecondMoment_mulVec_pos [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (β : Fin p → ℝ) {v : Fin p → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ (tiltedSecondMoment ν φ t β *ᵥ v) := by
  rw [dotProduct_tiltedSecondMoment_mulVec hφ hB]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  set u := ‖v‖⁻¹ • v with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hv0), inv_mul_cancel₀ hv0.ne']
  have hvu : v = ‖v‖ • u := by rw [hu_def, smul_smul, mul_inv_cancel₀ hv0.ne', one_smul]
  have hdot : Measurable fun z : 𝒳 × Bool × ℝ => v ⬝ᵥ (φ z.1 - t) :=
    (continuous_const.dotProduct continuous_id).measurable.comp
      ((hφ.comp measurable_fst).sub_const t)
  have hint : Integrable (fun z : 𝒳 × Bool × ℝ => tiltWeight φ t 0 β z.1 *
      (v ⬝ᵥ (φ z.1 - t)) ^ 2) ν :=
    integrable_tiltWeight_mul hφ hB β (integrable_of_abs_le (hdot.pow_const 2)
      (C := (p * (‖v‖ * B)) ^ 2) fun z => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_dotProduct_le_mul_norm v _).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB z.1) (norm_nonneg _))
            (Nat.cast_nonneg p))) 2)
  rw [integral_pos_iff_support_of_nonneg (fun z => mul_nonneg (tiltWeight_pos _ _ _ _ _).le
    (sq_nonneg _)) hint]
  have hsub : {z : 𝒳 × Bool × ℝ | δ ≤ u ⬝ᵥ (φ z.1 - t)} ⊆
      Function.support fun z : 𝒳 × Bool × ℝ => tiltWeight φ t 0 β z.1 *
        (v ⬝ᵥ (φ z.1 - t)) ^ 2 := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    have hpos : 0 < v ⬝ᵥ (φ z.1 - t) := by
      rw [hvu, smul_dotProduct, smul_eq_mul]
      exact mul_pos hv0 (hδ.trans_le hz)
    exact (mul_pos (tiltWeight_pos _ _ _ _ _) (pow_pos hpos 2)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  have h1 := hδ.trans_le (hmargin u hu)
  exact (ENNReal.toReal_pos_iff.1 h1).1

/-- The tilted second moment matrix is nonsingular under the margin condition. -/
theorem det_tiltedSecondMoment_ne_zero [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (β : Fin p → ℝ) :
    (tiltedSecondMoment ν φ t β).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have := dotProduct_tiltedSecondMoment_mulVec_pos hφ hB hδ hmargin β hv
  rw [hMv, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- The tilted mass of an arm is positive when the arm has positive probability. -/
theorem integral_armIndObs_mul_tiltWeight_pos [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) (β : Fin p → ℝ)
    {a : Bool} (hq : 0 < ν.real {z | z.2.1 = a}) :
    0 < ∫ z, armIndObs a z * tiltWeight φ t 0 β z.1 ∂ν := by
  have hint : Integrable (fun z : 𝒳 × Bool × ℝ => armIndObs a z * tiltWeight φ t 0 β z.1) ν := by
    simpa only [mul_comm] using integrable_tiltWeight_mul hφ hB β (f := armIndObs a)
      (integrable_of_abs_le (measurable_armIndObs a) (C := 1) fun z => by
        unfold armIndObs; split_ifs <;> simp)
  have hnn : 0 ≤ fun z : 𝒳 × Bool × ℝ => armIndObs a z * tiltWeight φ t 0 β z.1 := fun z =>
    mul_nonneg (by unfold armIndObs; split_ifs <;> norm_num) (tiltWeight_pos _ _ _ _ _).le
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hsub : {z : 𝒳 × Bool × ℝ | z.2.1 = a} ⊆
      Function.support fun z : 𝒳 × Bool × ℝ => armIndObs a z * tiltWeight φ t 0 β z.1 := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    simp only [Function.mem_support, armIndObs, hz, ite_true, one_mul]
    exact (tiltWeight_pos _ _ _ _ _).ne'
  exact lt_of_lt_of_le (ENNReal.toReal_pos_iff.1 hq).1 (measure_mono hsub)

/-- **The bread is nonsingular** under bounded features, the margin condition and
`P(A = a) > 0`, at every parameter. -/
theorem det_breadMatrix_weightedEstJac_ne_zero [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ}
    (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool} (hq : 0 < ν.real {z | z.2.1 = a})
    (θ : EuclideanSpace ℝ (Fin p ⊕ Unit)) :
    (breadMatrix ν (weightedEstJac φ t a) θ).det ≠ 0 := by
  rw [det_breadMatrix_weightedEstJac]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (det_tiltedSecondMoment_ne_zero hφ hB hδ hmargin _))
    (integral_armIndObs_mul_tiltWeight_pos hφ hB _ hq).ne'

end Bread

end PopulationAdjustment

end CausalInference
