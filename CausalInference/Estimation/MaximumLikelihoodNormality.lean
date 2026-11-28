/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.FisherInformation
public import CausalInference.Estimation.ZEstimatorNormality

/-!
# Asymptotic normality of the maximum likelihood estimator

The maximum likelihood estimator of a real parameter is a Z-estimator: it solves the score
equation `∑_{i < n} s(θ; O_i) = 0`. The estimating function is the score `ψ z θ = s(θ; z)`, whose
derivative in `θ` is `∂²ℓ(θ; z)`, so the bread of the sandwich is
`A = -E_θ₀[∂²ℓ(θ₀; X)] = I(θ₀)` by the information equality, and the meat is
`E_θ₀[s(θ₀; X)²] = I(θ₀)`. Hence the influence function is `I(θ₀)⁻¹ s(θ₀; ·)`, the sandwich
variance `I(θ₀) / I(θ₀)²` collapses to `I(θ₀)⁻¹`, and `√n (θ̂_n - θ₀)` converges in distribution
to `N(0, I(θ₀)⁻¹)`: the limit variance is the Cramér-Rao bound.

## Main definitions

* `CausalInference.ParametricFamily.IsScoreRegular`: smoothness of the score on a closed ball
  around `θ₀`, with a dominated second derivative of the log density.

## Main results

* `CausalInference.ParametricFamily.sandwichBread_eq_fisherInfo`: the bread is the information.
* `CausalInference.ParametricFamily.sandwich_eq_inv_fisherInfo`: the sandwich variance is
  `I(θ₀)⁻¹`.
* `CausalInference.ParametricFamily.mle_isAsymptoticallyLinear_of_root`: a consistent root of
  the score equation is asymptotically linear with influence function `I(θ₀)⁻¹ s(θ₀; ·)`.
* `CausalInference.ParametricFamily.mle_isAsymptoticallyLinear`: the same for a consistent local
  maximizer of the log-likelihood.
* `CausalInference.ParametricFamily.mle_tendstoInDistribution`: `√n (θ̂_n - θ₀)` converges to
  `N(0, I(θ₀)⁻¹)`.

The instance in which every hypothesis is checked (the Bernoulli family with the clipped sample
mean) is in `CausalInference.Estimation.BernoulliLikelihoodTests`.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5; E. L. Lehmann and
G. Casella (1998), *Theory of Point Estimation*, 2nd edition, chapter 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

variable {S : Type*} [MeasurableSpace S]

/-- Smoothness of the score on the closed ball of radius `r > 0` around `θ₀`: the score at `θ₀`
and every `∂²ℓ(θ; ·)` on the ball are measurable; for `P_θ₀`-almost every `z`, `θ ↦ s(θ; z)` has
derivative `∂²ℓ(θ; z)` at every point of the ball and this derivative is continuous on the ball;
and `|∂²ℓ(θ; z)| ≤ H z` on the ball for a `P_θ₀`-integrable envelope `H`. -/
structure IsScoreRegular (F : ParametricFamily ℝ S) (θ₀ r : ℝ) : Prop where
  /-- The radius is positive. -/
  pos : 0 < r
  /-- The score at `θ₀` is measurable. -/
  measurable_score : Measurable (F.score θ₀)
  /-- The second derivatives of the log density on the ball are measurable. -/
  measurable_hessLogLik : ∀ θ ∈ closedBall θ₀ r, Measurable (F.hessLogLik θ)
  /-- The score is differentiable in the parameter on the ball. -/
  hasDerivAt_score : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
    HasDerivAt (fun u ↦ F.score u z) (F.hessLogLik θ z) θ
  /-- The second derivative of the log density is continuous on the ball. -/
  continuousOn_hessLogLik : ∀ᵐ z ∂F.law θ₀,
    ContinuousOn (fun u ↦ F.hessLogLik u z) (closedBall θ₀ r)
  /-- An integrable envelope of the second derivative on the ball. -/
  dominated : ∃ H : S → ℝ, Integrable H (F.law θ₀) ∧
    ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r, |F.hessLogLik θ z| ≤ H z

variable {F : ParametricFamily ℝ S} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {O : ℕ → Ω → S} {θ₀ : ℝ}

/-- **The bread is the information.** If the observations have law `P_θ₀` and the information
equality `I(θ₀) = -E_θ₀[∂²ℓ(θ₀; X)]` holds, the bread of the score equation is `I(θ₀)`. -/
theorem sandwichBread_eq_fisherInfo (hlaw : μ.map (O 0) = F.law θ₀)
    (hinfo : F.fisherInfo θ₀ = -∫ x, F.hessLogLik θ₀ x ∂F.law θ₀) :
    sandwichBread (μ.map (O 0)) (fun z θ ↦ F.hessLogLik θ z) θ₀ = F.fisherInfo θ₀ := by
  rw [sandwichBread, hlaw, hinfo]

/-- The second moment of the score at an observation is the information. -/
theorem integral_score_sq_eq_fisherInfo {O : ℕ → Ω → S} (hO : AEMeasurable (O 0) μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hm : Measurable (F.score θ₀)) :
    μ[fun ω ↦ F.score θ₀ (O 0 ω) ^ 2] = F.fisherInfo θ₀ := by
  rw [fisherInfo, ← hlaw, integral_map hO (hm.pow_const 2).aestronglyMeasurable]

/-- **The sandwich collapses to the inverse information.** With meat `E_θ₀[s(θ₀; X)²] = I(θ₀)`
and bread `I(θ₀)`, the sandwich variance is `I(θ₀) / I(θ₀)² = I(θ₀)⁻¹`. -/
theorem sandwich_eq_inv_fisherInfo (hO : AEMeasurable (O 0) μ) (hlaw : μ.map (O 0) = F.law θ₀)
    (hm : Measurable (F.score θ₀))
    (hinfo : F.fisherInfo θ₀ = -∫ x, F.hessLogLik θ₀ x ∂F.law θ₀) (hI : F.fisherInfo θ₀ ≠ 0) :
    μ[fun ω ↦ F.score θ₀ (O 0 ω) ^ 2] /
        sandwichBread (μ.map (O 0)) (fun z θ ↦ F.hessLogLik θ z) θ₀ ^ 2 =
      (F.fisherInfo θ₀)⁻¹ := by
  rw [integral_score_sq_eq_fisherInfo hO hlaw hm, sandwichBread_eq_fisherInfo hlaw hinfo]
  field_simp

/-- **Asymptotic linearity of a root of the score equation.** Let `O` be an i.i.d. sample with
law `P_θ₀`, `θ₀` a regular point (`IsRegularAt`: it gives the mean zero score, its finite
variance and the information equality) with positive information, the score smooth on a closed
ball around `θ₀` (`IsScoreRegular`), `θh` consistent for `θ₀`, and `θh n` a root of the score
equation with probability tending to one. Then `θh` is asymptotically linear at `θ₀` with
influence function `I(θ₀)⁻¹ s(θ₀; ·)`. -/
theorem mle_isAsymptoticallyLinear_of_root [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hI : 0 < F.fisherInfo θ₀) {θh : ℕ → Ω → ℝ}
    (hθ : IsConsistent θh θ₀ μ)
    (hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, F.score (θh n ω) (O i ω) = 0})) :
    IsAsymptoticallyLinear θh θ₀ (fun z ↦ (F.fisherInfo θ₀)⁻¹ * F.score θ₀ z) O μ := by
  obtain ⟨-, -, hinfo⟩ := hreg.information_equality
  have hθ₀ : θ₀ ∈ F.Θ := mem_of_mem_nhds hreg.mem_nhds
  have := isProbabilityMeasure_law hθ₀
  obtain ⟨H, hH, hdom⟩ := hs.dominated
  have hX := hO.aemeasurable 0
  have hzero : μ[fun ω ↦ F.score θ₀ (O 0 ω)] = 0 := by
    rw [← integral_map hX hs.measurable_score.aestronglyMeasurable, hlaw,
      hreg.integral_score_eq_zero]
  have hB : MemLp (fun ω ↦ F.score θ₀ (O 0 ω)) 2 μ :=
    (memLp_map_measure_iff hs.measurable_score.aestronglyMeasurable hX).1
      (by rw [hlaw]; exact hreg.memLp_score)
  have h := zEstimator_isAsymptoticallyLinear_of_root hO (ψ := fun z θ ↦ F.score θ z)
    (ψ' := fun z θ ↦ F.hessLogLik θ z) hs.pos hs.measurable_score hs.measurable_hessLogLik
    (by rw [hlaw]; exact hs.hasDerivAt_score) (by rw [hlaw]; exact hs.continuousOn_hessLogLik)
    (by rw [hlaw]; exact hH) (by rw [hlaw]; exact hdom) hzero hB
    (by rw [sandwichBread_eq_fisherInfo hlaw hinfo]; exact hI.ne') hθ hroot
  rwa [sandwichBread_eq_fisherInfo hlaw hinfo] at h

/-- **Asymptotic linearity of a local maximizer of the log-likelihood.** Under the hypotheses of
`mle_isAsymptoticallyLinear_of_root`, with the root condition replaced by: `θ ↦ ℓ(θ; z)` has
derivative `s(θ; z)` on the ball for `P_θ₀`-almost every `z`, and `θh n` is a local maximizer of
the sample log-likelihood with probability tending to one. -/
theorem mle_isAsymptoticallyLinear [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hI : 0 < F.fisherInfo θ₀)
    (hdl : ∀ᵐ z ∂F.law θ₀, ∀ θ ∈ closedBall θ₀ r,
      HasDerivAt (fun u ↦ F.logLik u z) (F.score θ z) θ)
    {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ)
    (hmax : WithProbTendingToOne μ
      (fun n ↦ {ω | IsLocalMax (fun θ ↦ sampleMean (fun z ↦ F.logLik θ z) O n ω) (θh n ω)})) :
    IsAsymptoticallyLinear θh θ₀ (fun z ↦ (F.fisherInfo θ₀)⁻¹ * F.score θ₀ z) O μ := by
  refine mle_isAsymptoticallyLinear_of_root hO hlaw hreg hs hI hθ
    (((hmax.inter (TendstoInMeasure.withProbTendingToOne_dist_lt hθ hs.pos)).inter
      (WithProbTendingToOne.of_ae (hO.ae_forall (hlaw ▸ hdl)))).mono fun n ω hω ↦ ?_)
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 ⊢
  have hin : θh n ω ∈ closedBall θ₀ r := mem_closedBall.2 h2.le
  have hd : HasDerivAt (fun θ ↦ sampleMean (fun z ↦ F.logLik θ z) O n ω)
      ((n : ℝ)⁻¹ * ∑ i ∈ range n, F.score (θh n ω) (O i ω)) (θh n ω) :=
    (HasDerivAt.fun_sum fun i _ ↦ h3 i _ hin).const_mul _
  have h0 := h1.hasDerivAt_eq_zero hd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (mul_eq_zero.1 h0).resolve_left (inv_ne_zero (by exact_mod_cast hn.ne'))

/-- **Asymptotic normality of the maximum likelihood estimator.** Under the hypotheses of
`mle_isAsymptoticallyLinear_of_root` and measurability of each `θh n`, `√n (θh n - θ₀)`
converges in distribution to every random variable with law `N(0, I(θ₀)⁻¹)`. -/
theorem mle_tendstoInDistribution [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = F.law θ₀) (hreg : F.IsRegularAt θ₀) {r : ℝ}
    (hs : F.IsScoreRegular θ₀ r) (hI : 0 < F.fisherInfo θ₀) {θh : ℕ → Ω → ℝ}
    (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : IsConsistent θh θ₀ μ)
    (hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, F.score (θh n ω) (O i ω) = 0}))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (F.fisherInfo θ₀)⁻¹.toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (θh n ω - θ₀)) atTop Y (fun _ ↦ μ) P' := by
  have h := mle_isAsymptoticallyLinear_of_root hO hlaw hreg hs hI hθ hroot
  refine h.tendstoInDistribution hO hθm ?_
  have hvar : μ[fun ω ↦ ((F.fisherInfo θ₀)⁻¹ * F.score θ₀ (O 0 ω)) ^ 2] =
      (F.fisherInfo θ₀)⁻¹ := by
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_score_sq_eq_fisherInfo (hO.aemeasurable 0) hlaw
      hs.measurable_score]
    field_simp
  rw [hvar]
  exact hY

end ParametricFamily

end CausalInference
