/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityRoot
public import CausalInference.Estimation.VectorZEstimator

/-!
# Asymptotic normality of the weighted arm mean

The weighted (matching adjusted) arm mean `m̂ₙ = sampleBalancedArmMean` is the last coordinate of
the root `θ̂ₙ = (β̂ₙ, m̂ₙ)` of the stacked equations of `WeightedNormalityEquations`. The vector
Z estimator theory then gives its asymptotically linear representation with the influence function

`IF(x, s, y) = (1{s = a} w₀(x) (y - m₀) - cᵀ M⁻¹ w₀(x) (φ(x) - t)) / q`,

where `w₀ = w_{β₀}` is the population tilt, `M = E[w₀ Δ Δᵀ]` the tilted second moment matrix,
`c = E[1{A = a} w₀ (Y - m₀) Δ]` and `q = E[1{A = a} w₀]` (`weightedArmInfluence`). The second
term is the correction for the estimation of the tilt. The limit law is normal with the sandwich
variance `σ² = E[IF²] ≥ 0` (`weightedArmVariance`).

No outcome model is assumed, affine or otherwise, and neither is randomization: the estimator
always converges to `m₀ = E[1{A = a} w₀ Y] / E[1{A = a} w₀]`, the arm mean in the population
reweighted by the tilt. That this is the arm mean in the target population (the quantity of
interest) needs further conditions, such as an outcome regression affine in the features
(`sampleBalancedArmMean_isConsistent`; the two limits then agree by
`tiltArmMean_eq_of_isConsistent`).

The hypotheses are primitive: an i.i.d. sample, measurable and bounded features, the margin
condition, a positive probability of the arm and a square integrable outcome. The consistency
of `θ̂ₙ`, the root property, the nonsingularity of the bread and all envelopes are derived.

## Main definitions

* `weightedArmInfluence`: the influence function of the weighted arm mean.
* `weightedArmVariance`: its variance `E[IF²]`, the sandwich variance.

## Main results

* `sampleBalancedArmMean_isAsymptoticallyLinear`: the asymptotically linear representation.
* `sampleBalancedArmMean_tendstoInDistribution`: `√n (m̂ₙ - m₀) → N(0, σ²)` in law.
* `weightedArmVariance_nonneg`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* L. A. Stefanski and D. D. Boos (2002), *The calculus of M-estimation*, The American
  Statistician.
* P. J. Huber (1967), *The behavior of maximum likelihood estimates under nonstandard
  conditions*.
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳] {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- The coupling vector `c = E[1{A = a} w₀ (Y - m₀) (φ(X) - t)]` of the bread. -/
noncomputable def weightedCoupling (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) : Fin p → ℝ :=
  fun k => ∫ z, armIndObs a z * tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 *
    (z.2.2 - tiltArmMean ν φ t a (tiltMinimizer ν φ t)) * (φ z.1 k - t k) ∂ν

/-- The tilted mass `q = E[1{A = a} w₀]` of the arm. -/
noncomputable def weightedArmMass (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) : ℝ :=
  ∫ z, armIndObs a z * tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 ∂ν

/-- **The influence function of the weighted arm mean**:
`IF(z) = (1{s = a} w₀(x) (y - m₀) - cᵀ M⁻¹ (w₀(x) (φ(x) - t))) / q`. -/
noncomputable def weightedArmInfluence (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) (z : 𝒳 × Bool × ℝ) : ℝ :=
  (armIndObs a z * tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 *
      (z.2.2 - tiltArmMean ν φ t a (tiltMinimizer ν φ t)) -
    weightedCoupling ν φ t a ⬝ᵥ ((tiltedSecondMoment ν φ t (tiltMinimizer ν φ t))⁻¹ *ᵥ
      fun j => tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 * (φ z.1 j - t j))) /
    weightedArmMass ν φ t a

/-- **The asymptotic variance of the weighted arm mean**, `σ² = E[IF²]`. -/
noncomputable def weightedArmVariance (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) : ℝ :=
  ∫ z, weightedArmInfluence ν φ t a z ^ 2 ∂ν

/-- The asymptotic variance is nonnegative. -/
theorem weightedArmVariance_nonneg (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a : Bool) : 0 ≤ weightedArmVariance ν φ t a :=
  integral_nonneg fun _ => sq_nonneg _

/-- **The influence function is the last row of the inverse bread applied to the estimating
function.** -/
theorem inv_breadMatrix_mulVec_weightedEstFun {ν : Measure (𝒳 × Bool × ℝ)} [IsFiniteMeasure ν]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool} (hq : 0 < ν.real {z | z.2.1 = a})
    (z : 𝒳 × Bool × ℝ) :
    ((breadMatrix ν (weightedEstJac φ t a) (weightedStackedParam ν φ t a))⁻¹ *ᵥ
      WithLp.ofLp (weightedEstFun φ t a z (weightedStackedParam ν φ t a))) (Sum.inr ()) =
      weightedArmInfluence ν φ t a z := by
  set θ₀ := weightedStackedParam ν φ t a
  set A := breadMatrix ν (weightedEstJac φ t a) θ₀ with hAdef
  have hA : IsUnit A.det := isUnit_iff_ne_zero.2
    (det_breadMatrix_weightedEstJac_ne_zero hφ hB hδ hmargin hq θ₀)
  set M := tiltedSecondMoment ν φ t (tiltMinimizer ν φ t) with hM
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2
    (det_tiltedSecondMoment_ne_zero hφ hB hδ hmargin _)
  have hq0 : weightedArmMass ν φ t a ≠ 0 :=
    (integral_armIndObs_mul_tiltWeight_pos hφ hB _ hq).ne'
  set v := WithLp.ofLp (weightedEstFun φ t a z θ₀) with hv
  set v₁ : Fin p → ℝ := fun j => tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 * (φ z.1 j - t j)
  set x : Fin p ⊕ Unit → ℝ := Sum.elim (-(M⁻¹ *ᵥ v₁)) fun _ => weightedArmInfluence ν φ t a z
  have hAx : A *ᵥ x = v := by
    rw [hAdef, breadMatrix_weightedEstJac, fromBlocks_mulVec]
    funext k
    rcases k with j | u
    · simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero, x, Function.comp_def,
        Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
      rw [show tiltedSecondMoment ν φ t (stackedBalance θ₀) = M from rfl,
        Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mulVec]
      rfl
    · have hIF : weightedArmMass ν φ t a * weightedArmInfluence ν φ t a z =
          armIndObs a z * tiltWeight φ t 0 (tiltMinimizer ν φ t) z.1 *
            (z.2.2 - tiltArmMean ν φ t a (tiltMinimizer ν φ t)) -
          weightedCoupling ν φ t a ⬝ᵥ (M⁻¹ *ᵥ v₁) := by
        rw [weightedArmInfluence, mul_div_cancel₀ _ hq0]
      have hD : ∫ z, armIndObs a z * tiltWeight φ t 0 (stackedBalance θ₀) z.1 ∂ν =
          weightedArmMass ν φ t a := rfl
      have hc : ∀ k, ∫ z, armIndObs a z * tiltWeight φ t 0 (stackedBalance θ₀) z.1 *
          (z.2.2 - θ₀ (Sum.inr ())) * (φ z.1 k - t k) ∂ν = weightedCoupling ν φ t a k :=
        fun k => rfl
      simp only [Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Finset.univ_unique, Finset.sum_singleton, Function.comp_def, x, Sum.elim_inl,
        Pi.neg_apply, neg_mul_neg, hD, hc]
      rw [hIF]
      simp only [dotProduct, Matrix.mulVec]
      rw [show ∀ a b : ℝ, a + (b - a) = b from fun a b => by ring]
      rfl
  rw [← hAx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  rfl

/-! ### The limit law -/

/-- The mean of the stacked estimating function vanishes at `θ₀`. -/
theorem integral_weightedEstFun_eq_zero {ν : Measure (𝒳 × Bool × ℝ)} [IsProbabilityMeasure ν]
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool} (hq : 0 < ν.real {z | z.2.1 = a})
    (hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν)
    (hint : Integrable (fun z => weightedEstFun φ t a z (weightedStackedParam ν φ t a)) ν) :
    ∫ z, weightedEstFun φ t a z (weightedStackedParam ν φ t a) ∂ν = 0 := by
  set β₀ := tiltMinimizer ν φ t
  ext k
  have hc := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin p ⊕ Unit) k).integral_comp_comm hint
  change EuclideanSpace.proj (𝕜 := ℝ) k
    (∫ z, weightedEstFun φ t a z (weightedStackedParam ν φ t a) ∂ν) = 0
  rw [← hc]
  change ∫ z, weightedEstFun φ t a z (weightedStackedParam ν φ t a) k ∂ν = 0
  rcases k with j | u
  · exact integral_tiltWeight_tiltMinimizer_mul_sub hφ hB hδ hmargin j
  · simp only [weightedEstFun, Sum.elim_inr, PiLp.toLp_apply]
    change ∫ z, armIndObs a z * tiltWeight φ t 0 β₀ z.1 * (z.2.2 - tiltArmMean ν φ t a β₀) ∂ν = 0
    have hD := integrable_tiltWeight_mul_of_abs_le (ν := ν) hφ hB β₀ (measurable_armIndObs a)
      (C := 1) fun z => by unfold armIndObs; split_ifs <;> simp
    have hN := integrable_tiltWeight_mul (ν := ν) hφ hB β₀
      ((hy.bdd_mul (c := 1) (measurable_armIndObs a).aestronglyMeasurable
        (ae_of_all _ fun z => by unfold armIndObs; split_ifs <;> simp)))
    have hD0 := (integral_armIndObs_mul_tiltWeight_pos hφ hB β₀ hq).ne'
    have hpt : ∀ z : 𝒳 × Bool × ℝ, armIndObs a z * tiltWeight φ t 0 β₀ z.1 *
        (z.2.2 - tiltArmMean ν φ t a β₀) = tiltWeight φ t 0 β₀ z.1 * (armIndObs a z * z.2.2) -
          tiltArmMean ν φ t a β₀ * (tiltWeight φ t 0 β₀ z.1 * armIndObs a z) := fun z => by ring
    simp_rw [hpt]
    rw [integral_sub hN (hD.const_mul _), integral_const_mul]
    have e1 : ∫ z, tiltWeight φ t 0 β₀ z.1 * (armIndObs a z * z.2.2) ∂ν =
        ∫ z, armIndObs a z * tiltWeight φ t 0 β₀ z.1 * z.2.2 ∂ν := by
      congr 1; funext z; ring
    have e2 : ∫ z, tiltWeight φ t 0 β₀ z.1 * armIndObs a z ∂ν =
        ∫ z, armIndObs a z * tiltWeight φ t 0 β₀ z.1 ∂ν := by
      congr 1; funext z; ring
    rw [e1, e2, tiltArmMean, div_mul_cancel₀ _ hD0, sub_self]

omit [MeasurableSpace Ω] in
/-- **The weighted arm mean is a measurable function of the sample.** -/
theorem isSampleMeasurable_sampleBalancedArmMean {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    (t : Fin p → ℝ) (O : ℕ → Ω → 𝒳 × Bool × ℝ) (a : Bool) :
    IsSampleMeasurable (sampleBalancedArmMean φ t O a) O := fun n => by
  refine ⟨fun x => weightedArmMean (balancingWeights fun i : Fin n => φ (x i).1 - t)
    (fun i => (x i).2.1) (fun i => (x i).2.2) a, ?_, rfl⟩
  have hw : Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      balancingWeights fun i : Fin n => φ (x i).1 - t :=
    measurable_balancingWeights_sample (φ := fun r : 𝒳 × Bool × ℝ => φ r.1)
      (hφ.comp measurable_fst) t
  have hA : ∀ i, Measurable fun x : Fin n → 𝒳 × Bool × ℝ =>
      armWeights (balancingWeights fun i : Fin n => φ (x i).1 - t) (fun i => (x i).2.1) a i :=
    fun i => Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i).snd.fst
      measurable_const) ((measurable_pi_apply i).comp hw) measurable_const
  exact (Finset.measurable_sum _ fun i _ => (hA i).mul (measurable_pi_apply i).snd.snd).div
    (Finset.measurable_sum _ fun i _ => hA i)

/-- **The asymptotically linear representation of the weighted arm mean.** Under an i.i.d.
sample, measurable features bounded by `B` around the target `t`, the margin condition,
`P(A = a) > 0` and a square integrable outcome,
`√n (m̂ₙ - m₀) = n^{-1/2} ∑ᵢ IF(Zᵢ) + o_P(1)` with the influence function
`weightedArmInfluence`. The limit `m₀ = tiltArmMean` is the weighted mean of the arm under the
population tilt; no outcome model is assumed. -/
theorem sampleBalancedArmMean_isAsymptoticallyLinear [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    IsAsymptoticallyLinear (sampleBalancedArmMean φ t O a)
      (tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t))
      (weightedArmInfluence (P.map (O 0)) φ t a) O P := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set θ₀ := weightedStackedParam ν φ t a with hθ₀
  have hy1 : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν := hy.integrable one_le_two
  set K := weightedEnvConst p B θ₀ 1 with hK
  have hψm := measurable_weightedEstFun hφ t a θ₀
  have hψ2 : MemLp (fun z => weightedEstFun φ t a z θ₀) 2 ν := by
    refine MemLp.of_le (((memLp_const 1).add hy.norm).const_mul (√(p + 1) * K))
      hψm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    have hB0 : 0 ≤ ‖φ z.1 - t‖ := norm_nonneg _
    have hK0 : 0 ≤ K := by rw [hK, weightedEnvConst]; positivity
    have h := norm_weightedEstFun_sq_le (a := a) (Metric.mem_closedBall_self (x := θ₀) zero_le_one)
      zero_le_one (hB z.1)
    simp only [Pi.add_apply, Real.norm_eq_abs, norm_mul]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hK0,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + |z.2.2|)]
    rw [← hK] at h
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hψ1 := hψ2.integrable one_le_two
  have hfm : AEMeasurable (O 0) P := hO.aemeasurable 0
  have hzero : P[fun ω => weightedEstFun φ t a (O 0 ω) θ₀] = 0 := by
    rw [← integral_map hfm hψm.aestronglyMeasurable]
    exact integral_weightedEstFun_eq_zero hφ hB hδ hmargin hq hy1 hψ1
  have hBP : MemLp (fun ω => weightedEstFun φ t a (O 0 ω) θ₀) 2 P :=
    (memLp_map_measure_iff hψm.aestronglyMeasurable hfm).1 hψ2
  have h := vectorZEstimator_isAsymptoticallyLinear hO zero_lt_one hψm
    (fun θ _ k l => measurable_weightedEstJac hφ t a θ k l)
    (ae_of_all _ fun z θ _ => weightedEstFun_hasFDerivAt φ t a z θ)
    (ae_of_all _ fun z k l => (continuous_weightedEstJac φ t a z k l).continuousOn)
    (H := fun z => K * (1 + |z.2.2|)) (((integrable_const 1).add hy1.abs).const_mul K)
    (ae_of_all _ fun z θ hθ k l => (abs_weightedEstJac_le hθ zero_le_one (hB z.1)).1 k l)
    hzero hBP (det_breadMatrix_weightedEstJac_ne_zero hφ hB hδ hmargin hq θ₀)
    (weightedStackedEstimate_tendstoInMeasure hO hφ hB hδ hmargin a hq hy1)
    (weightedStackedEstimate_root hO hφ hB hδ hmargin a) (Sum.inr ())
  have hIF : (fun z => ((breadMatrix ν (weightedEstJac φ t a) θ₀)⁻¹ *ᵥ
      WithLp.ofLp (weightedEstFun φ t a z θ₀)) (Sum.inr ())) = weightedArmInfluence ν φ t a :=
    funext fun z => inv_breadMatrix_mulVec_weightedEstFun hφ hB hδ hmargin hq z
  rw [hIF] at h
  exact h

/-- **Asymptotic normality of the weighted arm mean**: `√n (m̂ₙ - m₀) → N(0, σ²)` in law, with
the sandwich variance `σ² = weightedArmVariance = E[IF²] ≥ 0`. The limit `m₀ = tiltArmMean` is
the weighted mean of the arm under the population tilt; no outcome model is assumed. -/
theorem sampleBalancedArmMean_tendstoInDistribution [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0)))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (weightedArmVariance (P.map (O 0)) φ t a).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (sampleBalancedArmMean φ t O a n ω -
      tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t))) atTop Y
      (fun _ => P) P' := by
  have h := sampleBalancedArmMean_isAsymptoticallyLinear hO hφ hB hδ hmargin a hq hy
  have hvar : P[fun ω => weightedArmInfluence (P.map (O 0)) φ t a (O 0 ω) ^ 2] =
      weightedArmVariance (P.map (O 0)) φ t a := by
    rw [weightedArmVariance, integral_map (hO.aemeasurable 0)
      (h.measurable.pow_const 2).aestronglyMeasurable]
  rw [← hvar] at hY
  exact h.tendstoInDistribution_of_isSampleMeasurable hO
    (isSampleMeasurable_sampleBalancedArmMean hφ t O a) hY

/-! ### Identification of the limit -/

/-- **Limits in probability are unique**: a sequence converging in probability to two constants
under a probability measure has equal limits. -/
theorem tendstoInMeasure_const_unique [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {c d : ℝ}
    (h1 : TendstoInMeasure P X atTop (fun _ => c)) (h2 : TendstoInMeasure P X atTop (fun _ => d)) :
    c = d := by
  by_contra hcd
  set ε := dist c d / 2 with hε
  have hε0 : 0 < ε := by have := dist_pos.2 hcd; positivity
  rw [tendstoInMeasure_iff_dist] at h1 h2
  have hsum := (h1 ε hε0).add (h2 ε hε0)
  rw [add_zero] at hsum
  have hcov : ∀ n, (1 : ℝ≥0∞) ≤ P {ω | ε ≤ dist (X n ω) c} + P {ω | ε ≤ dist (X n ω) d} :=
    fun n => by
      calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
        _ ≤ P ({ω | ε ≤ dist (X n ω) c} ∪ {ω | ε ≤ dist (X n ω) d}) := by
          refine measure_mono fun ω _ => ?_
          by_contra h
          simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
          have := dist_triangle_left c d (X n ω)
          linarith
        _ ≤ _ := measure_union_le _ _
  exact absurd (ge_of_tendsto' hsum hcov) (by simp)

/-- **Identification of the limit.** If the weighted arm mean is also consistent for `L` (for
instance for `a₀ + bᵀt` under the affine outcome regression and the randomization of
`sampleBalancedArmMean_isConsistent`), then the weighted mean under the population tilt is `L`. -/
theorem tiltArmMean_eq_of_isConsistent [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) (P.map (O 0))) {L : ℝ}
    (hL : IsConsistent (sampleBalancedArmMean φ t O a) L P) :
    tiltArmMean (P.map (O 0)) φ t a (tiltMinimizer (P.map (O 0)) φ t) = L :=
  tendstoInMeasure_const_unique (sampleBalancedArmMean_tendstoInMeasure hO hφ hB hδ hmargin a hq hy)
    hL

end PopulationAdjustment

end CausalInference
