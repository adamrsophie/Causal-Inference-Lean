/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedNormalityWald

/-!
# Wald intervals for the anchored weighted comparison

The anchored comparison `(g(m̂_false) - g(m̂_true)) - d̂ₙ` has the influence function
`g'(m_F) IF_F - g'(m_T) IF_T`, whose variance
`g'(m_F)² σ_F² - 2 g'(m_F) g'(m_T) c_FT + g'(m_T)² σ_T²` involves the covariance
`c_FT = E[IF_F IF_T]` of the influence functions of the two arms (`weightedInfluenceCov`). Its
plug-in estimate is the cross covariance estimate `weightedInfluenceCovHat false true`, built from
the empirical breads of the two stacked systems and the cross meat; it is consistent
(`weightedInfluenceCovHat_tendstoInMeasure`) under the hypotheses of the normal limit. With an
estimate of the aggregate variance this gives a Wald interval of asymptotic level `1 - α` for the
anchored comparison (`tendsto_anchored_waldInterval_coverage`), and, under the consistency
conditions of `anchoredBalancedEstimate_isConsistent`, for the marginal effect of the target
population (`tendsto_anchored_waldInterval_coverage_marginalEffect`).

## Main definitions

* `weightedInfluenceCov`: `E[IF_a IF_b]`.
* `anchoredSdHat`: the delta method standard error of the anchored comparison.

## Main results

* `integrable_weightedArmInfluence_mul`, `integral_weightedAnchoredInfluence_sq`.
* `crossMeat_weighted_tendstoInMeasure`, `weightedInfluenceCovHat_tendstoInMeasure`.
* `memLp_outcome_of_affine`: with both arm regressions affine in bounded features, a square
  integrable residual makes the outcome square integrable.
* `tendsto_anchored_waldInterval_coverage`,
  `tendsto_anchored_waldInterval_coverage_marginalEffect`.

## References

* Signorovitch, Wu, Yu, Gerrits, Kantor, Cai, Gupta, Mulani, *Comparative effectiveness without
  head-to-head trials* (2010).
* Stefanski, Boos, *The calculus of M-estimation* (2002).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Matrix
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

variable {𝒳 : Type*} {p : ℕ} [MeasurableSpace 𝒳]

/-! ### The covariance of the influence functions of two arms -/

section Population

variable {ν : Measure (𝒳 × Bool × ℝ)}

/-- The **covariance of the influence functions** of arms `a` and `b`, `E[IF_a IF_b]`. -/
noncomputable def weightedInfluenceCov (ν : Measure (𝒳 × Bool × ℝ)) (φ : 𝒳 → Fin p → ℝ)
    (t : Fin p → ℝ) (a b : Bool) : ℝ :=
  ∫ z, weightedArmInfluence ν φ t a z * weightedArmInfluence ν φ t b z ∂ν

/-- The influence function is a fixed linear combination of the coordinates of the estimating
function at `θ₀`. -/
theorem weightedArmInfluence_eq_sum [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a : Bool}
    (hq : 0 < ν.real {z | z.2.1 = a}) (z : 𝒳 × Bool × ℝ) :
    weightedArmInfluence ν φ t a z =
      ∑ k, (breadMatrix ν (weightedEstJac φ t a) (weightedStackedParam ν φ t a))⁻¹
        (Sum.inr ()) k * weightedEstFun φ t a z (weightedStackedParam ν φ t a) k := by
  rw [← inv_breadMatrix_mulVec_weightedEstFun hφ hB hδ hmargin hq z]
  rfl

/-- **Products of influence functions are integrable** for a square integrable outcome. -/
theorem integrable_weightedArmInfluence_mul [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a b : Bool}
    (hqa : 0 < ν.real {z | z.2.1 = a}) (hqb : 0 < ν.real {z | z.2.1 = b})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) :
    Integrable (fun z => weightedArmInfluence ν φ t a z * weightedArmInfluence ν φ t b z) ν := by
  have he : (fun z => weightedArmInfluence ν φ t a z * weightedArmInfluence ν φ t b z) =
      fun z => ∑ k, ∑ l, ((breadMatrix ν (weightedEstJac φ t a)
        (weightedStackedParam ν φ t a))⁻¹ (Sum.inr ()) k *
        (breadMatrix ν (weightedEstJac φ t b) (weightedStackedParam ν φ t b))⁻¹ (Sum.inr ()) l) *
        (weightedEstFun φ t a z (weightedStackedParam ν φ t a) k *
          weightedEstFun φ t b z (weightedStackedParam ν φ t b) l) := by
    funext z
    rw [weightedArmInfluence_eq_sum hφ hB hδ hmargin hqa,
      weightedArmInfluence_eq_sum hφ hB hδ hmargin hqb, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [he]
  exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrable_weightedEstFun_mul hφ hB hy a b _ _ k l).const_mul _

/-- The squared anchored influence function is integrable. -/
theorem integrable_weightedAnchoredInfluence_sq [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : ∀ a, 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    (gf' gt' : ℝ) :
    Integrable (fun z => weightedAnchoredInfluence ν φ t gf' gt' z ^ 2) ν := by
  have hFF := integrable_weightedArmInfluence_mul hφ hB hδ hmargin (hq false) (hq false) hy
  have hFT := integrable_weightedArmInfluence_mul hφ hB hδ hmargin (hq false) (hq true) hy
  have hTT := integrable_weightedArmInfluence_mul hφ hB hδ hmargin (hq true) (hq true) hy
  have h := ((hFF.const_mul (gf' ^ 2)).sub (hFT.const_mul (2 * gf' * gt'))).add
    (hTT.const_mul (gt' ^ 2))
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, weightedAnchoredInfluence]
  ring

/-- The **variance of the anchored influence function**
`E[(g'_F IF_F - g'_T IF_T)²] = g'_F² σ_F² - 2 g'_F g'_T c_FT + g'_T² σ_T²`. -/
theorem integral_weightedAnchoredInfluence_sq [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : ∀ a, 0 < ν.real {z | z.2.1 = a}) (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν)
    (gf' gt' : ℝ) :
    ∫ z, weightedAnchoredInfluence ν φ t gf' gt' z ^ 2 ∂ν =
      gf' ^ 2 * weightedArmVariance ν φ t false -
        2 * gf' * gt' * weightedInfluenceCov ν φ t false true +
        gt' ^ 2 * weightedArmVariance ν φ t true := by
  have hFF := integrable_weightedArmInfluence_mul hφ hB hδ hmargin (hq false) (hq false) hy
  have hFT := integrable_weightedArmInfluence_mul hφ hB hδ hmargin (hq false) (hq true) hy
  have hTT := integrable_weightedArmInfluence_mul hφ hB hδ hmargin (hq true) (hq true) hy
  have he : (fun z => weightedAnchoredInfluence ν φ t gf' gt' z ^ 2) = fun z =>
      gf' ^ 2 * (weightedArmInfluence ν φ t false z * weightedArmInfluence ν φ t false z) -
        2 * gf' * gt' * (weightedArmInfluence ν φ t false z * weightedArmInfluence ν φ t true z) +
        gt' ^ 2 * (weightedArmInfluence ν φ t true z * weightedArmInfluence ν φ t true z) := by
    funext z
    simp only [weightedAnchoredInfluence]
    ring
  have h1 : Integrable (fun z =>
      gf' ^ 2 * (weightedArmInfluence ν φ t false z * weightedArmInfluence ν φ t false z) -
        2 * gf' * gt' * (weightedArmInfluence ν φ t false z * weightedArmInfluence ν φ t true z))
      ν := (hFF.const_mul _).sub (hFT.const_mul _)
  rw [he, integral_add h1 (hTT.const_mul (gt' ^ 2))]
  rw [integral_sub (hFF.const_mul (gf' ^ 2)) (hFT.const_mul (2 * gf' * gt')),
    integral_const_mul, integral_const_mul, integral_const_mul, weightedArmVariance,
    weightedArmVariance, weightedInfluenceCov]
  simp only [sq]

/-- **The cross entry of the population sandwich is `c_ab`**: `(A_a⁻¹ C A_b⁻ᵀ)_{m m}` with the
breads of the two stacked systems and the cross meat `C = E[ψ_a ψ_bᵀ]` at the two limits. -/
theorem crossSandwich_eq_weightedInfluenceCov [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ}
    (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 → δ ≤ ν.real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a b : Bool}
    (hqa : 0 < ν.real {z | z.2.1 = a}) (hqb : 0 < ν.real {z | z.2.1 = b})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν) :
    ((breadMatrix ν (weightedEstJac φ t a) (weightedStackedParam ν φ t a))⁻¹ *
      Matrix.of (fun k l => ∫ z, weightedEstFun φ t a z (weightedStackedParam ν φ t a) k *
        weightedEstFun φ t b z (weightedStackedParam ν φ t b) l ∂ν) *
      ((breadMatrix ν (weightedEstJac φ t b) (weightedStackedParam ν φ t b))⁻¹)ᵀ)
        (Sum.inr ()) (Sum.inr ()) = weightedInfluenceCov ν φ t a b := by
  refine (mul_of_integral_mul_transpose_apply (ν := ν) _ _
    (f := fun z => WithLp.ofLp (weightedEstFun φ t a z (weightedStackedParam ν φ t a)))
    (g := fun z => WithLp.ofLp (weightedEstFun φ t b z (weightedStackedParam ν φ t b)))
    (fun k l => integrable_weightedEstFun_mul hφ hB hy a b _ _ k l) _ _).trans ?_
  rw [weightedInfluenceCov]
  congr 1
  funext z
  rw [inv_breadMatrix_mulVec_weightedEstFun hφ hB hδ hmargin hqa z,
    inv_breadMatrix_mulVec_weightedEstFun hφ hB hδ hmargin hqb z]

/-- **Square integrability of the outcome from affine arm regressions.** If both arm
regressions are affine in features bounded around `t` and the residual `Y - μ_A(X)` is square
integrable, then the outcome is square integrable. -/
theorem memLp_outcome_of_affine [IsFiniteMeasure ν] {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ)
    {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B) {mu : Bool → 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) ν)
    {a0A a0C : ℝ} {bA bC : Fin p → ℝ} (haffA : ∀ x, mu true x = a0A + bA ⬝ᵥ φ x)
    (haffC : ∀ x, mu false x = a0C + bC ⬝ᵥ φ x) :
    MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 ν := by
  have hmu := measurable_regressions_of_affine hφ haffA haffC
  have hm : Measurable fun z : 𝒳 × Bool × ℝ => mu z.2.1 z.1 :=
    measurable_regression_surface hmu
  have h1 : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2 - mu z.2.1 z.1) 2 ν :=
    (memLp_two_iff_integrable_sq (measurable_snd.snd.sub hm).aestronglyMeasurable).2 hres2
  set R := B + ‖t‖
  have hφR : ∀ x k, |φ x k| ≤ R := fun x k => by
    rw [← Real.norm_eq_abs]
    calc ‖φ x k‖ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) k
      _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
      _ ≤ ‖φ x - t‖ + ‖t‖ := norm_add_le _ _
      _ ≤ R := by linarith [hB x]
  have hdot : ∀ (b : Fin p → ℝ) x, |b ⬝ᵥ φ x| ≤ ∑ k, |b k| * R := fun b x => by
    rw [dotProduct]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hφR x k) (abs_nonneg _)
  have hbd : ∀ z : 𝒳 × Bool × ℝ, |mu z.2.1 z.1| ≤
      max (|a0A| + ∑ k, |bA k| * R) (|a0C| + ∑ k, |bC k| * R) := by
    rintro ⟨x, s, y⟩
    cases s
    · rw [haffC]
      exact ((abs_add_le _ _).trans (add_le_add_right (hdot bC x) _)).trans (le_max_right _ _)
    · rw [haffA]
      exact ((abs_add_le _ _).trans (add_le_add_right (hdot bA x) _)).trans (le_max_left _ _)
  have h2 : MemLp (fun z : 𝒳 × Bool × ℝ => mu z.2.1 z.1) 2 ν :=
    MemLp.of_bound hm.aestronglyMeasurable _ (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hbd z)
  convert h1.add h2 using 1
  funext z
  simp

end Population

/-! ### Consistency of the cross covariance estimate -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **Consistency of the cross meat**, by the uniform law of large numbers on the product of
closed balls around the two limits `θ_a` and `θ_b`, with the envelope `K_a K_b (1 + |y|)²`. -/
theorem crossMeat_weighted_tendstoInMeasure [IsProbabilityMeasure P] (hO : IsIIDSample O P)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a b : Bool}
    (hqa : 0 < (P.map (O 0)).real {z | z.2.1 = a}) (hqb : 0 < (P.map (O 0)).real {z | z.2.1 = b})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) (k l : Fin p ⊕ Unit) :
    TendstoInMeasure P (fun n ω => sampleMean (fun z =>
      weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω) k *
        weightedEstFun φ t b z (weightedStackedEstimate φ t O b n ω) l) O n ω) atTop
      (fun _ => ∫ z, weightedEstFun φ t a z (weightedStackedParam (P.map (O 0)) φ t a) k *
        weightedEstFun φ t b z (weightedStackedParam (P.map (O 0)) φ t b) l ∂(P.map (O 0))) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  set θa := weightedStackedParam ν φ t a
  set θb := weightedStackedParam ν φ t b
  set Ka := weightedEnvConst p B θa 1 with hKa
  set Kb := weightedEnvConst p B θb 1 with hKb
  have hKa0 : 0 ≤ Ka := by rw [hKa, weightedEnvConst]; positivity
  have hKb0 : 0 ≤ Kb := by rw [hKb, weightedEnvConst]; positivity
  have hy1 : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν := hy.integrable one_le_two
  have hbd : Integrable (fun z : 𝒳 × Bool × ℝ => Ka * Kb * (1 + 2 * |z.2.2| + z.2.2 ^ 2)) ν :=
    (((integrable_const 1).add (hy1.abs.const_mul 2)).add hy.integrable_sq).const_mul _
  have hp : ∀ m, Continuous fun x : EuclideanSpace ℝ (Fin p ⊕ Unit) => x m := fun m =>
    (EuclideanSpace.proj (𝕜 := ℝ) m).continuous
  have hcψ : ∀ c z, Continuous fun θ => weightedEstFun φ t c z θ := fun c z =>
    continuous_iff_continuousAt.2 fun θ => (weightedEstFun_hasFDerivAt φ t c z θ).continuousAt
  have hdom : ∀ z : 𝒳 × Bool × ℝ, ∀ q ∈ Metric.closedBall (θa, θb) (1 : ℝ),
      |weightedEstFun φ t a z q.1 k * weightedEstFun φ t b z q.2 l| ≤
        Ka * Kb * (1 + 2 * |z.2.2| + z.2.2 ^ 2) := by
    intro z q hq
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] at hq
    have h1 := (abs_weightedEstJac_le (a := a) (Metric.mem_closedBall.2 hq.1) zero_le_one
      (hB z.1)).2 k
    have h2 := (abs_weightedEstJac_le (a := b) (Metric.mem_closedBall.2 hq.2) zero_le_one
      (hB z.1)).2 l
    rw [abs_mul]
    calc |weightedEstFun φ t a z q.1 k| * |weightedEstFun φ t b z q.2 l|
        ≤ (Ka * (1 + |z.2.2|)) * (Kb * (1 + |z.2.2|)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = Ka * Kb * (1 + 2 * |z.2.2| + z.2.2 ^ 2) := by rw [← sq_abs z.2.2]; ring
  have hK := Metric.closedBall_mem_nhds (θa, θb) one_pos
  have hmeas : ∀ q : EuclideanSpace ℝ (Fin p ⊕ Unit) × EuclideanSpace ℝ (Fin p ⊕ Unit),
      Measurable fun z => weightedEstFun φ t a z q.1 k * weightedEstFun φ t b z q.2 l := by
    intro q
    have h1 := (hp k).measurable.comp (measurable_weightedEstFun hφ t a q.1)
    have h2 := (hp l).measurable.comp (measurable_weightedEstFun hφ t b q.2)
    exact h1.mul h2
  have hcont : ∀ z : 𝒳 × Bool × ℝ, Continuous fun q :
      EuclideanSpace ℝ (Fin p ⊕ Unit) × EuclideanSpace ℝ (Fin p ⊕ Unit) =>
        weightedEstFun φ t a z q.1 k * weightedEstFun φ t b z q.2 l := by
    intro z
    have h1 := (hp k).comp ((hcψ a z).comp (continuous_fst (X := EuclideanSpace ℝ (Fin p ⊕ Unit))
      (Y := EuclideanSpace ℝ (Fin p ⊕ Unit))))
    have h2 := (hp l).comp ((hcψ b z).comp (continuous_snd (X := EuclideanSpace ℝ (Fin p ⊕ Unit))
      (Y := EuclideanSpace ℝ (Fin p ⊕ Unit))))
    exact h1.mul h2
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall (θa, θb) 1)
    (ψ := fun z (q : EuclideanSpace ℝ (Fin p ⊕ Unit) × EuclideanSpace ℝ (Fin p ⊕ Unit)) =>
      weightedEstFun φ t a z q.1 k * weightedEstFun φ t b z q.2 l)
    (fun q _ => hmeas q) (ae_of_all _ fun z => (hcont z).continuousOn) hbd (ae_of_all _ hdom)
  have hθ := (weightedStackedEstimate_tendstoInMeasure hO hφ hB hδ hmargin a hqa hy1).prodMk
    (weightedStackedEstimate_tendstoInMeasure hO hφ hB hδ hmargin b hqb hy1)
  have h := hunif.comp_tendstoInMeasure hK (hMc.continuousAt hK) hθ
  exact h

/-- **Consistency of the inverse empirical bread**, as an array of entries: matrix inversion is
continuous at the nonsingular bread. -/
theorem inv_breadMatrixHat_weighted_tendstoInMeasure [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) (a : Bool)
    (hq : 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) (P.map (O 0))) :
    TendstoInMeasure P (fun n ω => (Matrix.of.symm
      ((breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω)⁻¹) :
        Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ)) atTop
      (fun _ => Matrix.of.symm ((breadMatrix (P.map (O 0)) (weightedEstJac φ t a)
        (weightedStackedParam (P.map (O 0)) φ t a))⁻¹)) := by
  set ν := P.map (O 0) with hν
  set θ₀ := weightedStackedParam ν φ t a
  set A := breadMatrix ν (weightedEstJac φ t a) θ₀ with hA
  set K := weightedEnvConst p B θ₀ 1
  have h1 := breadMatrixHat_tendstoInMeasure hO zero_lt_one
    (fun θ _ k l => measurable_weightedEstJac hφ t a θ k l)
    (ae_of_all _ fun z k l => (continuous_weightedEstJac φ t a z k l).continuousOn)
    (H := fun z => K * (1 + |z.2.2|)) (((integrable_const 1).add hy.abs).const_mul K)
    (ae_of_all _ fun z θ hθ k l => (abs_weightedEstJac_le hθ zero_le_one (hB z.1)).1 k l)
    (weightedStackedEstimate_tendstoInMeasure hO hφ hB hδ hmargin a hq hy)
  have h1' : TendstoInMeasure P (fun n ω => (fun k l =>
      breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω k l :
        Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ)) atTop (fun _ => Matrix.of.symm A) :=
    tendstoInMeasure_pi (X := fun k n ω l =>
      breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω k l)
      fun k => tendstoInMeasure_pi (X := fun l n ω =>
        breadMatrixHat O (weightedEstJac φ t a) (weightedStackedEstimate φ t O a) n ω k l)
        fun l => h1 k l
  have hA0 : A.det ≠ 0 := by
    have : IsProbabilityMeasure ν :=
      (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
    exact det_breadMatrix_weightedEstJac_ne_zero hφ hB hδ hmargin hq θ₀
  have hdet : ContinuousAt Ring.inverse A.det := by
    have := NormedRing.inverse_continuousAt (Units.mk0 A.det hA0)
    rwa [Units.val_mk0] at this
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ → _) A :=
    continuousAt_matrix_inv A hdet
  have hof : Continuous (fun F : Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ =>
    (Matrix.of F : Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ)) := continuous_id
  have hsymm : Continuous (Matrix.of.symm :
    Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ → Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ) := continuous_id
  have hg : ContinuousAt (fun F : Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ =>
      (Matrix.of.symm ((Matrix.of F)⁻¹) : Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ))
      (Matrix.of.symm A) :=
    hsymm.continuousAt.comp (ContinuousAt.comp_of_eq hinv hof.continuousAt rfl)
  exact h1'.comp_continuousAt hg

/-- **Consistency of the cross covariance estimate**: `Ĉ_ab → c_ab = E[IF_a IF_b]` in
probability, under the hypotheses of the normal limit for both arms. -/
theorem weightedInfluenceCovHat_tendstoInMeasure [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)}) {a b : Bool}
    (hqa : 0 < (P.map (O 0)).real {z | z.2.1 = a}) (hqb : 0 < (P.map (O 0)).real {z | z.2.1 = b})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) :
    TendstoInMeasure P (weightedInfluenceCovHat φ t O a b) atTop
      (fun _ => weightedInfluenceCov (P.map (O 0)) φ t a b) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set ν := P.map (O 0) with hν
  have hy1 : Integrable (fun z : 𝒳 × Bool × ℝ => z.2.2) ν := hy.integrable one_le_two
  have hI : ∀ c : Bool, 0 < ν.real {z | z.2.1 = c} → TendstoInMeasure P (fun n ω =>
      (fun k l => (breadMatrixHat O (weightedEstJac φ t c) (weightedStackedEstimate φ t O c) n ω)⁻¹
        k l : Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ)) atTop
      (fun _ => fun k l => (breadMatrix ν (weightedEstJac φ t c) (weightedStackedParam ν φ t c))⁻¹
        k l) := fun c hqc => by
    have h0 := inv_breadMatrixHat_weighted_tendstoInMeasure hO hφ hB hδ hmargin c hqc hy1
    exact tendstoInMeasure_pi (X := fun k n ω l =>
      (breadMatrixHat O (weightedEstJac φ t c) (weightedStackedEstimate φ t O c) n ω)⁻¹ k l)
      fun k => tendstoInMeasure_pi (X := fun l n ω =>
        (breadMatrixHat O (weightedEstJac φ t c) (weightedStackedEstimate φ t O c) n ω)⁻¹ k l)
        fun l => h0.comp_continuousAt (g := fun F => F k l)
          (continuous_apply_apply k l).continuousAt
  have hIa := hI a hqa
  have hIb := hI b hqb
  have hC : TendstoInMeasure P (fun n ω => (fun k l => sampleMean (fun z =>
      weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω) k *
        weightedEstFun φ t b z (weightedStackedEstimate φ t O b n ω) l) O n ω :
          Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ)) atTop
      (fun _ => fun k l => ∫ z, weightedEstFun φ t a z (weightedStackedParam ν φ t a) k *
        weightedEstFun φ t b z (weightedStackedParam ν φ t b) l ∂ν) :=
    tendstoInMeasure_pi (X := fun k n ω l => sampleMean (fun z =>
      weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω) k *
        weightedEstFun φ t b z (weightedStackedEstimate φ t O b n ω) l) O n ω)
      fun k => tendstoInMeasure_pi (X := fun l n ω => sampleMean (fun z =>
        weightedEstFun φ t a z (weightedStackedEstimate φ t O a n ω) k *
          weightedEstFun φ t b z (weightedStackedEstimate φ t O b n ω) l) O n ω)
        fun l => crossMeat_weighted_tendstoInMeasure hO hφ hB hδ hmargin hqa hqb hy k l
  have hm : Continuous (fun q : (Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ ×
      Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ) × Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ =>
      (q.1.1 * q.1.2 * q.2ᵀ) (Sum.inr ()) (Sum.inr ())) :=
    ((continuous_fst.fst.matrix_mul continuous_fst.snd).matrix_mul
      continuous_snd.matrix_transpose).matrix_elem _ _
  have hof : Continuous (fun r : ((Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ) ×
      (Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ)) × (Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ) =>
      (((Matrix.of r.1.1, Matrix.of r.1.2), Matrix.of r.2) :
        (Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ × Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ) ×
          Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ)) := continuous_id
  have hc : Continuous (fun r : ((Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ) ×
      (Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ)) × (Fin p ⊕ Unit → Fin p ⊕ Unit → ℝ) =>
      ((Matrix.of r.1.1 : Matrix (Fin p ⊕ Unit) (Fin p ⊕ Unit) ℝ) * Matrix.of r.1.2 *
        (Matrix.of r.2)ᵀ) (Sum.inr ()) (Sum.inr ())) := by
    have := hm.comp hof
    exact this
  have h01 := hIa.prodMk hC
  have h0 := h01.prodMk hIb
  have h := h0.comp_continuousAt hc.continuousAt
  rw [← crossSandwich_eq_weightedInfluenceCov hφ hB hδ hmargin hqa hqb hy]
  unfold weightedInfluenceCovHat
  exact h

/-! ### The anchored Wald interval -/

/-- The **delta method standard error of the anchored comparison**
`√(g'(m̂_F)² Ĉ_FF - 2 g'(m̂_F) g'(m̂_T) Ĉ_FT + g'(m̂_T)² Ĉ_TT + ŵₙ)`, with the derivative
functions `dgF` and `dgT` of the link at the two arm means (in practice `dgF = dgT = g'`), the
cross covariance estimates of the influence values and an estimate `ŵₙ` of the asymptotic
variance of the aggregate part. -/
noncomputable def anchoredSdHat (dgF dgT : ℝ → ℝ) (φ : 𝒳 → Fin p → ℝ) (t : Fin p → ℝ)
    (O : ℕ → Ω → 𝒳 × Bool × ℝ) (wHat : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  √(dgF (sampleBalancedArmMean φ t O false n ω) ^ 2 *
      weightedInfluenceCovHat φ t O false false n ω -
    2 * dgF (sampleBalancedArmMean φ t O false n ω) *
      dgT (sampleBalancedArmMean φ t O true n ω) * weightedInfluenceCovHat φ t O false true n ω +
    dgT (sampleBalancedArmMean φ t O true n ω) ^ 2 * weightedInfluenceCovHat φ t O true true n ω +
    wHat n ω)

/-- **Asymptotic coverage of the Wald interval for the anchored comparison.** Under the
hypotheses of `anchoredBalancedEstimate_tendstoInDistribution` with derivatives
`g'(m_F) = dgF m_F` and `g'(m_T) = dgT m_T`, measurable `dgF` and `dgT` continuous at the two arm
means, a consistent and almost everywhere measurable estimate `ŵₙ` of the aggregate variance
`w`, and a positive total variance, the interval built from `anchoredSdHat` covers
`g(m_F) - g(m_T) - d` with probability tending to `1 - α`. -/
theorem tendsto_anchored_waldInterval_coverage [IsProbabilityMeasure P]
    (hO : IsIIDSample O P) {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ}
    (hB : ∀ x, ‖φ x - t‖ ≤ B) {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hq : ∀ a, 0 < (P.map (O 0)).real {z | z.2.1 = a})
    (hy : MemLp (fun z : 𝒳 × Bool × ℝ => z.2.2) 2 (P.map (O 0))) {g dgF dgT : ℝ → ℝ}
    (hg : Measurable g) (hdgF : Measurable dgF) (hdgT : Measurable dgT)
    (hgf : HasDerivAt g
      (dgF (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)))
      (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)))
    (hgt : HasDerivAt g
      (dgT (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
      (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
    (hdgFc : ContinuousAt dgF
      (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)))
    (hdgTc : ContinuousAt dgT
      (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)))
    {dBC : ℕ → Ω → ℝ} {d : ℝ}
    (hindep : ∀ n, IndepFun (fun ω (i : Fin n) => O i ω) (dBC n) P)
    {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {Y₂ : Ω₂ → ℝ}
    {w : ℝ≥0}
    (hagg : TendstoInDistribution (fun (n : ℕ) ω => √n * (d - dBC n ω)) atTop Y₂
      (fun _ => P) P₂) (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    {wHat : ℕ → Ω → ℝ} (hwHat : IsConsistent wHat w P) (hwm : ∀ n, AEMeasurable (wHat n) P)
    (hσ : 0 < dgF (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)) ^ 2 *
        weightedArmVariance (P.map (O 0)) φ t false -
      2 * dgF (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)) *
        dgT (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)) *
        weightedInfluenceCov (P.map (O 0)) φ t false true +
      dgT (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)) ^ 2 *
        weightedArmVariance (P.map (O 0)) φ t true + w) {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω |
      g (tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)) -
        g (tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)) - d ∈
      waldInterval (anchoredBalancedEstimate g φ t O dBC n ω)
        (anchoredSdHat dgF dgT φ t O wHat n ω) z n}) atTop (𝓝 (1 - α)) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  set mF := tiltArmMean (P.map (O 0)) φ t false (tiltMinimizer (P.map (O 0)) φ t)
  set mT := tiltArmMean (P.map (O 0)) φ t true (tiltMinimizer (P.map (O 0)) φ t)
  set s := dgF mF ^ 2 * weightedArmVariance (P.map (O 0)) φ t false -
      2 * dgF mF * dgT mT * weightedInfluenceCov (P.map (O 0)) φ t false true +
      dgT mT ^ 2 * weightedArmVariance (P.map (O 0)) φ t true with hs
  have hint := integrable_weightedAnchoredInfluence_sq hφ hB hδ hmargin hq hy (dgF mF) (dgT mT)
  have hseq : P[fun ω => weightedAnchoredInfluence (P.map (O 0)) φ t (dgF mF) (dgT mT)
      (O 0 ω) ^ 2] = s := by
    rw [← integral_map (hO.aemeasurable 0) hint.aestronglyMeasurable]
    exact integral_weightedAnchoredInfluence_sq hφ hB hδ hmargin hq hy _ _
  have hs0 : 0 ≤ s := hseq ▸ integral_nonneg fun _ => sq_nonneg _
  have hAN := anchoredBalancedEstimate_tendstoInDistribution hO hφ hB hδ hmargin hq hy hg hgf hgt
    hindep (HasLaw.id (μ := gaussianReal 0 (P[fun ω => weightedAnchoredInfluence (P.map (O 0)) φ
      t (dgF mF) (dgT mT) (O 0 ω) ^ 2]).toNNReal)) hagg hY₂
    (HasLaw.id (μ := gaussianReal 0 ((P[fun ω => weightedAnchoredInfluence (P.map (O 0)) φ t
      (dgF mF) (dgT mT) (O 0 ω) ^ 2]).toNNReal + w)))
  rw [hseq] at hAN
  have hY : HasLaw id (gaussianReal 0 ((√(s + w)) ^ 2).toNNReal)
      (gaussianReal 0 (s.toNNReal + w)) := by
    rw [gaussianReal_sq_sqrt_add hs0]
    exact HasLaw.id
  have hy1 := hy.integrable one_le_two
  have hmF := (sampleBalancedArmMean_tendstoInMeasure hO hφ hB hδ hmargin false (hq false)
    hy1).comp_continuousAt hdgFc
  have hmT := (sampleBalancedArmMean_tendstoInMeasure hO hφ hB hδ hmargin true (hq true)
    hy1).comp_continuousAt hdgTc
  have hFF := weightedInfluenceCovHat_self_tendstoInMeasure hO hφ hB hδ hmargin false (hq false) hy
  have hFT := weightedInfluenceCovHat_tendstoInMeasure hO hφ hB hδ hmargin (hq false) (hq true) hy
  have hTT := weightedInfluenceCovHat_self_tendstoInMeasure hO hφ hB hδ hmargin true (hq true) hy
  have h6 := ((((hmF.prodMk hmT).prodMk hFF).prodMk hFT).prodMk hTT).prodMk hwHat
  have hc : Continuous fun r : ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) × ℝ =>
      √(r.1.1.1.1.1 ^ 2 * r.1.1.1.2 - 2 * r.1.1.1.1.1 * r.1.1.1.1.2 * r.1.1.2 +
        r.1.1.1.1.2 ^ 2 * r.1.2 + r.2) := by fun_prop
  have hcons : IsConsistent (anchoredSdHat dgF dgT φ t O wHat) (√(s + w)) P := by
    have h := h6.comp_continuousAt hc.continuousAt
    exact h
  have hmeas : ∀ n, AEMeasurable (anchoredSdHat dgF dgT φ t O wHat n) P := fun n => by
    have hF := hdgF.comp_aemeasurable
      ((isSampleMeasurable_sampleBalancedArmMean hφ t O false).aemeasurable hO n)
    have hT := hdgT.comp_aemeasurable
      ((isSampleMeasurable_sampleBalancedArmMean hφ t O true).aemeasurable hO n)
    have hcFF := (isSampleMeasurable_weightedInfluenceCovHat hφ t O false false).aemeasurable hO n
    have hcFT := (isSampleMeasurable_weightedInfluenceCovHat hφ t O false true).aemeasurable hO n
    have hcTT := (isSampleMeasurable_weightedInfluenceCovHat hφ t O true true).aemeasurable hO n
    have h2 : AEMeasurable (fun _ : Ω => (2 : ℝ)) P := aemeasurable_const
    have h := (((((hF.pow_const 2).mul hcFF).sub (((h2.mul hF).mul hT).mul hcFT)).add
      ((hT.pow_const 2).mul hcTT)).add (hwm n)).sqrt
    exact h
  exact tendsto_waldInterval_coverage (Real.sqrt_pos.2 hσ) hz hzα hY hAN hcons hmeas

/-- **Coverage of the anchored marginal effect of the target population.** Under randomization of
the index trial, both arm regressions affine in the features, a square integrable residual,
target moments `t` equal to the feature means of the target population `Q`, the conditional
means of `Q.Y ta` and `Q.Y tc` equal to the arm regressions, and an aggregate comparison
`d̂ₙ` asymptotically normal around the marginal effect `Q.marginalEffect g tb tc` of `tc`
against `tb`, the anchored Wald interval covers the marginal effect `Q.marginalEffect g ta tb`
with probability tending to `1 - α`. The square integrability of the outcome is not assumed: it
follows from the affine regressions (`memLp_outcome_of_affine`). -/
theorem tendsto_anchored_waldInterval_coverage_marginalEffect [IsProbabilityMeasure P]
    {Ω' ι : Type*} [MeasurableSpace Ω'] (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i))
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ} {B : ℝ} (hB : ∀ x, ‖φ x - t‖ ≤ B)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (P.map (O 0)).real {z | δ ≤ v ⬝ᵥ (φ z.1 - t)})
    (hind : IndepFun (fun z : 𝒳 × Bool × ℝ => z.1) (fun z => z.2.1) (P.map (O 0)))
    (hq : ∀ a, 0 < (P.map (O 0)).real {z | z.2.1 = a}) {mu : Bool → 𝒳 → ℝ}
    (hres2 : Integrable (fun z : 𝒳 × Bool × ℝ => (z.2.2 - mu z.2.1 z.1) ^ 2) (P.map (O 0)))
    (hreg : (P.map (O 0))[fun z => z.2.2 | MeasurableSpace.comap
      (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance] =ᵐ[P.map (O 0)]
        fun z => mu z.2.1 z.1) {σ2 : ℝ}
    (hvar : (P.map (O 0))[fun z => (z.2.2 - mu z.2.1 z.1) ^ 2 |
      MeasurableSpace.comap (fun z : 𝒳 × Bool × ℝ => (z.1, z.2.1)) inferInstance]
        ≤ᵐ[P.map (O 0)] fun _ => σ2)
    {a0A a0C : ℝ} {bA bC : Fin p → ℝ} (haffA : ∀ x, mu true x = a0A + bA ⬝ᵥ φ x)
    (haffC : ∀ x, mu false x = a0C + bC ⬝ᵥ φ x)
    {Q : Population Ω' 𝒳 ι} [IsProbabilityMeasure Q.μ] (hQX : Measurable Q.X)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {ta tb tc : ι} (hQYa : Integrable (Q.Y ta) Q.μ)
    (hQYc : Integrable (Q.Y tc) Q.μ) (hQma : Q.IsCondMean ta (mu true))
    (hQmc : Q.IsCondMean tc (mu false)) {g dgF dgT : ℝ → ℝ}
    (hg : Measurable g) (hdgF : Measurable dgF) (hdgT : Measurable dgT)
    (hgf : HasDerivAt g (dgF (Q.armMean tc)) (Q.armMean tc))
    (hgt : HasDerivAt g (dgT (Q.armMean ta)) (Q.armMean ta))
    (hdgFc : ContinuousAt dgF (Q.armMean tc)) (hdgTc : ContinuousAt dgT (Q.armMean ta))
    {dBC : ℕ → Ω → ℝ} (hindep : ∀ n, IndepFun (fun ω (i : Fin n) => O i ω) (dBC n) P)
    {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {Y₂ : Ω₂ → ℝ}
    {w : ℝ≥0}
    (hagg : TendstoInDistribution (fun (n : ℕ) ω => √n * (Q.marginalEffect g tb tc - dBC n ω))
      atTop Y₂ (fun _ => P) P₂) (hY₂ : HasLaw Y₂ (gaussianReal 0 w) P₂)
    {wHat : ℕ → Ω → ℝ} (hwHat : IsConsistent wHat w P) (hwm : ∀ n, AEMeasurable (wHat n) P)
    (hσ : 0 < dgF (Q.armMean tc) ^ 2 * weightedArmVariance (P.map (O 0)) φ t false -
      2 * dgF (Q.armMean tc) * dgT (Q.armMean ta) *
        weightedInfluenceCov (P.map (O 0)) φ t false true +
      dgT (Q.armMean ta) ^ 2 * weightedArmVariance (P.map (O 0)) φ t true + w)
    {z α : ℝ} (hz : 0 ≤ z) (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n => P.real {ω | Q.marginalEffect g ta tb ∈
      waldInterval (anchoredBalancedEstimate g φ t O dBC n ω)
        (anchoredSdHat dgF dgT φ t O wHat n ω) z n}) atTop (𝓝 (1 - α)) := by
  have : IsProbabilityMeasure (P.map (O 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hO.aemeasurable 0)).2 inferInstance
  have hy := memLp_outcome_of_affine hφ hB hres2 haffA haffC
  have hmu := measurable_regressions_of_affine hφ haffA haffC
  have hy1 := hy.integrable one_le_two
  have hLT := tiltArmMean_eq_of_isConsistent hO hφ hB hδ hmargin true (hq true) hy1
    (sampleBalancedArmMean_isConsistent_armMean hO hOm hφ hB hδ hmargin hind true (hq true) hmu
      hres2 hreg hvar haffA hQX ht hQYa hQma)
  have hLF := tiltArmMean_eq_of_isConsistent hO hφ hB hδ hmargin false (hq false) hy1
    (sampleBalancedArmMean_isConsistent_armMean hO hOm hφ hB hδ hmargin hind false (hq false) hmu
      hres2 hreg hvar haffC hQX ht hQYc hQmc)
  have hlim : Q.marginalEffect g ta tb =
      g (Q.armMean tc) - g (Q.armMean ta) - Q.marginalEffect g tb tc := by
    simp only [Population.marginalEffect]; ring
  rw [hlim, ← hLT, ← hLF]
  rw [← hLT] at hgt hdgTc
  rw [← hLF] at hgf hdgFc
  rw [← hLT, ← hLF] at hσ
  exact tendsto_anchored_waldInterval_coverage hO hφ hB hδ hmargin hq hy hg hdgF hdgT hgf hgt
    hdgFc hdgTc hindep hagg hY₂ hwHat hwm hσ hz hzα

end PopulationAdjustment

end CausalInference
