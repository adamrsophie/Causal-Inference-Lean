/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MEstimator
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Asymptotic linearity and normality of Z-estimators

Let `θh n` be a consistent approximate root of the estimating equation
`n⁻¹ ∑_{i < n} ψ (O i) θ = 0` for a real parameter, with `ψ z` differentiable near the true value
`θ₀` (derivative `ψ' z θ`, continuous in `θ` and dominated by an integrable envelope),
`E ψ (O 0) θ₀ = 0`, `E ψ (O 0) θ₀² < ∞`, and nonzero bread `A = -E ψ' (O 0) θ₀`. Then `θh` is
asymptotically linear at `θ₀` with influence function `A⁻¹ ψ (·) θ₀`
(`CausalInference.IsAsymptoticallyLinear`); asymptotic normality with the sandwich variance
`E ψ² / A²`, the delta method and Wald intervals then follow from the existing theorems on
asymptotically linear estimators.

## Main definitions

* `CausalInference.sandwichBread ν ψ' θ`: the bread `-∫ ψ' z θ dν`.

## Main results

* `CausalInference.tendstoInMeasure_sub_of_linearization`: the linearization step in a normed
  space: from `‖A Y n - S n‖ ≤ η ‖Y n‖ + ‖r n‖` with probability tending to one for every
  `η > 0`, `S n` bounded in probability and `r n → 0`, it follows that `Y n - A⁻¹ S n → 0`.
* `CausalInference.zEstimator_linearization`: the mean value step for a real parameter.
* `CausalInference.zEstimator_isAsymptoticallyLinear`: **asymptotic linearity of a Z-estimator**
  with an approximate root, and `CausalInference.zEstimator_isAsymptoticallyLinear_of_root` with
  an exact root on events of probability tending to one.
* `CausalInference.zEstimator_tendstoInDistribution`: **asymptotic normality** with limit
  `N(0, E ψ (O 0) θ₀² / A²)`.
* `CausalInference.mEstimator_isAsymptoticallyLinear`: the same for an M-estimator that is a
  local maximizer of the sample criterion with probability tending to one, through the first
  order condition.
* Instances in which every hypothesis is checked are in
  `CausalInference.Estimation.ZEstimatorExamples`: the sample mean (`ψ z θ = f z - θ`, and least
  squares) and `log_sampleMean_isAsymptoticallyLinear` (the nonlinear estimating function
  `ψ z θ = f z - exp θ`, whose root is the logarithm of the sample mean).

The consistency of `θh` and the approximate root condition are explicit hypotheses of the
general theorems; the instances verify them.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5 (Theorem 5.21 states
asymptotic normality of Z-estimators under a Lipschitz condition in place of the derivative
conditions used here); P. J. Huber (1967), *The behavior of maximum likelihood estimates under
nonstandard conditions*, Proceedings of the Fifth Berkeley Symposium.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A sequence whose norms are bounded in probability stays below some level `K > 0` with
probability at least `1 - κ` for all large `n`. -/
theorem BoundedInProbability.exists_norm_lt {E : Type*} [Norm E] {X : ℕ → Ω → E}
    (hX : BoundedInProbability μ (fun n ω ↦ ‖X n ω‖)) {κ : ℝ≥0∞} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, μ {ω | ‖X n ω‖ < K}ᶜ ≤ κ := by
  obtain ⟨M, hM, h⟩ := hX κ hκ
  refine ⟨M, hM, h.mono fun n hn ↦ le_trans (measure_mono fun ω hω ↦ ?_) hn⟩
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
  exact hω.trans (le_abs_self _)

/-- **The linearization step.** Let `A` have the left inverse `Ainv`, let the norms of `S n` be
bounded in probability and `r n → 0` in probability, and suppose that for every `η > 0`, with
probability tending to one, `‖A (Y n) - S n‖ ≤ η ‖Y n‖ + ‖r n‖`. Then `Y n - Ainv (S n) → 0` in
probability. With `‖Ainv‖ η ≤ 1 / 2` the bound first gives
`‖Y n‖ ≤ 2 ‖Ainv‖ (‖S n‖ + ‖r n‖)`, and then `‖Y n - Ainv (S n)‖ ≤ ‖Ainv‖ (η ‖Y n‖ + ‖r n‖)` is
small. -/
theorem tendstoInMeasure_sub_of_linearization {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Y S r : ℕ → Ω → E} {A Ainv : E →L[ℝ] E} (hinv : ∀ v, Ainv (A v) = v)
    (hS : BoundedInProbability μ (fun n ω ↦ ‖S n ω‖))
    (hr : TendstoInMeasure μ r atTop (fun _ ↦ 0))
    (hlin : ∀ η : ℝ, 0 < η →
      WithProbTendingToOne μ (fun n ↦ {ω | ‖A (Y n ω) - S n ω‖ ≤ η * ‖Y n ω‖ + ‖r n ω‖})) :
    TendstoInMeasure μ (fun n ω ↦ Y n ω - Ainv (S n ω)) atTop (fun _ ↦ 0) := by
  set c : ℝ := ‖Ainv‖ + 1 with hc_def
  have hc : 0 < c := by positivity
  have hAinv : ∀ w, ‖Ainv w‖ ≤ c * ‖w‖ := fun w ↦
    (Ainv.le_opNorm w).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg w))
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ ↦ ?_
  have hκ3 : 0 < κ / 3 := ENNReal.div_pos hκ.ne' (by simp)
  obtain ⟨K, hK, hSK⟩ := hS.exists_norm_lt hκ3
  set η : ℝ := min (1 / (2 * c)) (ε / (4 * c ^ 2 * (K + 1))) with hη_def
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  set ρ : ℝ := min 1 (ε / (4 * c)) with hρ_def
  have hρ : 0 < ρ := lt_min one_pos (by positivity)
  have hr' := (hr.withProbTendingToOne_dist_lt hρ).eventually_le hκ3
  have hl' := (hlin η hη).eventually_le hκ3
  refine ⟨fun n ↦ ({ω | ‖S n ω‖ < K} ∩ {ω | dist (r n ω) 0 < ρ}) ∩
    {ω | ‖A (Y n ω) - S n ω‖ ≤ η * ‖Y n ω‖ + ‖r n ω‖}, ?_, ?_⟩
  · filter_upwards [hSK, hr', hl'] with n h1 h2 h3
    rw [Set.compl_inter, Set.compl_inter]
    calc μ (({ω | ‖S n ω‖ < K}ᶜ ∪ {ω | dist (r n ω) 0 < ρ}ᶜ) ∪
          {ω | ‖A (Y n ω) - S n ω‖ ≤ η * ‖Y n ω‖ + ‖r n ω‖}ᶜ)
        ≤ μ {ω | ‖S n ω‖ < K}ᶜ + μ {ω | dist (r n ω) 0 < ρ}ᶜ +
          μ {ω | ‖A (Y n ω) - S n ω‖ ≤ η * ‖Y n ω‖ + ‖r n ω‖}ᶜ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ κ / 3 + κ / 3 + κ / 3 := add_le_add (add_le_add h1 h2) h3
      _ = κ := ENNReal.add_thirds κ
  · refine Eventually.of_forall fun n ω hω ↦ ?_
    obtain ⟨⟨hS1, hr1⟩, hl1⟩ := hω
    simp only [Set.mem_ofPred_eq, dist_zero_right] at hS1 hr1 hl1
    have hη1 : c * η ≤ 1 / 2 := by
      calc c * η ≤ c * (1 / (2 * c)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
        _ = 1 / 2 := by field_simp
    have hρ1 : ρ ≤ 1 := min_le_left _ _
    have hY : ‖Y n ω‖ ≤ 2 * c * (K + 1) := by
      have h1 : ‖Y n ω‖ ≤ c * ‖A (Y n ω)‖ := by simpa [hinv] using hAinv (A (Y n ω))
      have h2 : ‖A (Y n ω)‖ ≤ η * ‖Y n ω‖ + ‖r n ω‖ + ‖S n ω‖ := by
        calc ‖A (Y n ω)‖ = ‖(A (Y n ω) - S n ω) + S n ω‖ := by rw [sub_add_cancel]
          _ ≤ ‖A (Y n ω) - S n ω‖ + ‖S n ω‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have h3 : c * (η * ‖Y n ω‖) ≤ 1 / 2 * ‖Y n ω‖ := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hη1 (norm_nonneg _)
      nlinarith
    have heq : Y n ω - Ainv (S n ω) = Ainv (A (Y n ω) - S n ω) := by
      rw [map_sub, hinv]
    rw [heq, dist_zero_right]
    have hη2 : c * η * (2 * c * (K + 1)) ≤ ε / 2 := by
      have : c * η * (2 * c * (K + 1)) ≤
          c * (ε / (4 * c ^ 2 * (K + 1))) * (2 * c * (K + 1)) := by
        gcongr; exact min_le_right _ _
      refine this.trans (le_of_eq ?_)
      field_simp
      ring
    have hρ2 : c * ρ ≤ ε / 4 := by
      calc c * ρ ≤ c * (ε / (4 * c)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le
        _ = ε / 4 := by field_simp
    calc ‖Ainv (A (Y n ω) - S n ω)‖ ≤ c * ‖A (Y n ω) - S n ω‖ := hAinv _
      _ ≤ c * (η * ‖Y n ω‖ + ‖r n ω‖) := mul_le_mul_of_nonneg_left hl1 hc.le
      _ ≤ c * (η * (2 * c * (K + 1)) + ρ) := by gcongr
      _ = c * η * (2 * c * (K + 1)) + c * ρ := by ring
      _ < ε := by linarith

variable {𝒪 : Type*} [MeasurableSpace 𝒪] {O : ℕ → Ω → 𝒪}

/-- The bread `-∫ ψ' z θ dν` of the sandwich variance, for the derivative `ψ'` of a real
estimating function with respect to the parameter. -/
noncomputable def sandwichBread (ν : Measure 𝒪) (ψ' : 𝒪 → ℝ → ℝ) (θ : ℝ) : ℝ :=
  -∫ z, ψ' z θ ∂ν

/-- **The mean value step.** Let `ψ z` have derivative `ψ' z θ` on a closed ball around `θ₀` for
almost every observation value, let `n⁻¹ ∑_{i < n} ψ' (O i) θ → M θ` uniformly on the ball in
probability with `M` continuous at `θ₀`, and let `θh n → θ₀` in probability. Then for every
`η > 0`, with probability tending to one,
`|-M θ₀ √n (θh n - θ₀) - √n Ψₙ θ₀| ≤ η |√n (θh n - θ₀)| + |√n Ψₙ (θh n)|`, where
`Ψₙ θ = n⁻¹ ∑_{i < n} ψ (O i) θ`. The mean value inequality is applied to `θ ↦ Ψₙ θ - M θ₀ θ`;
no intermediate point is chosen. -/
theorem zEstimator_linearization (hO : IsIIDSample O μ) {ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ}
    (hr : 0 < r) (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r,
      HasDerivAt (ψ z) (ψ' z θ) θ) {M : ℝ → ℝ}
    (hunif : TendstoUniformlyOnInProbability μ (fun n ω θ ↦ sampleMean (fun z ↦ ψ' z θ) O n ω) M
      (Metric.closedBall θ₀ r))
    (hM : ContinuousAt M θ₀) {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ) {η : ℝ}
    (hη : 0 < η) :
    WithProbTendingToOne μ (fun n ↦ {ω | ‖-M θ₀ * (√(n : ℝ) * (θh n ω - θ₀)) -
      √(n : ℝ) * sampleMean (fun z ↦ ψ z θ₀) O n ω‖ ≤
        η * ‖√(n : ℝ) * (θh n ω - θ₀)‖ +
          ‖√(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω‖}) := by
  obtain ⟨δ, hδ, hMδ⟩ := Metric.continuousAt_iff.1 hM (η / 2) (by positivity)
  have hδr : 0 < min δ r := lt_min hδ hr
  refine (((TendstoInMeasure.withProbTendingToOne_dist_lt hθ hδr).inter
    (hunif (η / 2) (by positivity))).inter
    (WithProbTendingToOne.of_ae (hO.ae_forall hderiv))).mono fun n ω hω ↦ ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 ⊢
  have hsub : Metric.ball θ₀ (min δ r) ⊆ Metric.closedBall θ₀ r :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (min_le_right _ _))
  set G : ℝ → ℝ := fun θ ↦ sampleMean (fun z ↦ ψ z θ) O n ω - M θ₀ * θ with hG_def
  have hG : ∀ θ ∈ Metric.ball θ₀ (min δ r), HasDerivWithinAt G
      (sampleMean (fun z ↦ ψ' z θ) O n ω - M θ₀) (Metric.ball θ₀ (min δ r)) θ := by
    intro θ hθs
    have hsum : HasDerivAt (fun θ ↦ ∑ i ∈ range n, ψ (O i ω) θ)
        (∑ i ∈ range n, ψ' (O i ω) θ) θ :=
      HasDerivAt.fun_sum (fun i _ ↦ h3 i θ (hsub hθs))
    have := (hsum.const_mul (n : ℝ)⁻¹).fun_sub ((hasDerivAt_id' θ).const_mul (M θ₀))
    simpa [G, sampleMean] using this.hasDerivWithinAt
  have hbound : ∀ θ ∈ Metric.ball θ₀ (min δ r),
      ‖sampleMean (fun z ↦ ψ' z θ) O n ω - M θ₀‖ ≤ η := by
    intro θ hθs
    have ha := h2 θ (hsub hθs)
    have hb := hMδ (lt_of_lt_of_le (Metric.mem_ball.1 hθs) (min_le_left _ _))
    rw [Real.dist_eq] at ha hb
    rw [Real.norm_eq_abs]
    calc |sampleMean (fun z ↦ ψ' z θ) O n ω - M θ₀|
        ≤ |sampleMean (fun z ↦ ψ' z θ) O n ω - M θ| + |M θ - M θ₀| := abs_sub_le _ _ _
      _ ≤ η := by linarith
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hG hbound (convex_ball _ _)
    (Metric.mem_ball_self hδr) (Metric.mem_ball.2 h1)
  have key : -M θ₀ * (√(n : ℝ) * (θh n ω - θ₀)) - √(n : ℝ) * sampleMean (fun z ↦ ψ z θ₀) O n ω
      = √(n : ℝ) * (G (θh n ω) - G θ₀) -
        √(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω := by
    simp only [hG_def]; ring
  rw [key]
  have hs := Real.sqrt_nonneg (n : ℝ)
  calc ‖√(n : ℝ) * (G (θh n ω) - G θ₀) - √(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω‖
      ≤ ‖√(n : ℝ) * (G (θh n ω) - G θ₀)‖ +
        ‖√(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω‖ := norm_sub_le _ _
    _ ≤ η * ‖√(n : ℝ) * (θh n ω - θ₀)‖ +
        ‖√(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω‖ := by
      gcongr
      rw [norm_mul, norm_mul, Real.norm_of_nonneg hs]
      calc √(n : ℝ) * ‖G (θh n ω) - G θ₀‖ ≤ √(n : ℝ) * (η * ‖θh n ω - θ₀‖) :=
            mul_le_mul_of_nonneg_left hmvt hs
        _ = η * (√(n : ℝ) * ‖θh n ω - θ₀‖) := by ring

omit [MeasurableSpace 𝒪] in
/-- `√n` times the sample mean is the normalized sum `n^{-1/2} ∑_{i < n}`. -/
lemma sqrt_mul_sampleMean (f : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) :
    √(n : ℝ) * sampleMean f O n ω = (√(n : ℝ))⁻¹ * ∑ i ∈ range n, f (O i ω) := by
  rw [sampleMean, ← mul_assoc, sqrt_mul_inv_self]

/-- **Asymptotic linearity of a Z-estimator.** Let `O` be an i.i.d. sample under a probability
measure and `ψ : 𝒪 → ℝ → ℝ` a real estimating function with the following properties on a closed
ball `B` of radius `r > 0` around `θ₀`: for almost every observation value `z`, `ψ z` has
derivative `ψ' z θ` at every `θ ∈ B` and `ψ' z` is continuous on `B`; `z ↦ ψ' z θ` is measurable
for `θ ∈ B` and `|ψ' z θ| ≤ H z` on `B` for an integrable envelope `H`. Assume `z ↦ ψ z θ₀` is
measurable, `ψ (O 0) θ₀` is square integrable with mean zero, and the bread
`A = sandwichBread (μ.map (O 0)) ψ' θ₀` is nonzero.

Two high level conditions are hypotheses: `θh` is consistent for `θ₀`, and `θh n` is an
approximate root, `√n n⁻¹ ∑_{i < n} ψ (O i) (θh n) → 0` in probability (see
`zEstimator_isAsymptoticallyLinear_of_root` for an exact root). Then `θh` is asymptotically
linear at `θ₀` with influence function `z ↦ A⁻¹ ψ z θ₀`. -/
theorem zEstimator_isAsymptoticallyLinear [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ} (hr : 0 < r) (hψm : Measurable fun z ↦ ψ z θ₀)
    (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (ψ z) (ψ' z θ) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : sandwichBread (μ.map (O 0)) ψ' θ₀ ≠ 0) {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ)
    (hroot : TendstoInMeasure μ
      (fun (n : ℕ) ω ↦ √(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω) atTop (fun _ ↦ 0)) :
    IsAsymptoticallyLinear θh θ₀ (fun z ↦ (sandwichBread (μ.map (O 0)) ψ' θ₀)⁻¹ * ψ z θ₀) O μ := by
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall θ₀ r)
    (ψ := fun z θ ↦ ψ' z θ) hψ'm hcont hH hdom
  have hMat : ContinuousAt (fun θ ↦ ∫ z, ψ' z θ ∂(μ.map (O 0))) θ₀ :=
    hMc.continuousAt (Metric.closedBall_mem_nhds θ₀ hr)
  set a := sandwichBread (μ.map (O 0)) ψ' θ₀ with ha_def
  let A : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
  let Ainv : ℝ →L[ℝ] ℝ := a⁻¹ • ContinuousLinearMap.id ℝ ℝ
  have hinv : ∀ v, Ainv (A v) = v := fun v ↦ by
    simp only [A, Ainv, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
  have hS : BoundedInProbability μ
      (fun (n : ℕ) ω ↦ ‖√(n : ℝ) * sampleMean (fun z ↦ ψ z θ₀) O n ω‖) := by
    intro η hη
    obtain ⟨M, hM, h⟩ := normalizedSum_bounded hO hψm hB hzero η hη
    refine ⟨M, hM, Eventually.of_forall fun n ↦ le_trans (le_of_eq ?_) (h n)⟩
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_abs, sqrt_mul_sampleMean, normalizedSum]
  have hlin : ∀ η : ℝ, 0 < η → WithProbTendingToOne μ (fun n ↦
      {ω | ‖A (√(n : ℝ) * (θh n ω - θ₀)) - √(n : ℝ) * sampleMean (fun z ↦ ψ z θ₀) O n ω‖ ≤
        η * ‖√(n : ℝ) * (θh n ω - θ₀)‖ +
          ‖√(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω‖}) := by
    intro η hη
    refine (zEstimator_linearization hO hr hderiv hunif hMat hθ hη).mono fun n ω h ↦ ?_
    simpa [A, ha_def, sandwichBread] using h
  have hdiff := tendstoInMeasure_sub_of_linearization hinv hS hroot hlin
  refine ⟨hψm.const_mul _, hB.const_mul _, by rw [integral_const_mul, hzero, mul_zero], ?_⟩
  refine hdiff.congr' (Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ ?_)
    EventuallyEq.rfl
  simp only [Ainv, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    sqrt_mul_sampleMean, ← mul_sum]
  ring

/-- **Asymptotic linearity of a Z-estimator with an exact root.** The form of
`zEstimator_isAsymptoticallyLinear` in which `θh n` solves `∑_{i < n} ψ (O i) (θh n) = 0` on
events of probability tending to one (for instance the score equation of maximum likelihood). -/
theorem zEstimator_isAsymptoticallyLinear_of_root [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ} (hr : 0 < r) (hψm : Measurable fun z ↦ ψ z θ₀)
    (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (ψ z) (ψ' z θ) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : sandwichBread (μ.map (O 0)) ψ' θ₀ ≠ 0) {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ)
    (hroot : WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, ψ (O i ω) (θh n ω) = 0})) :
    IsAsymptoticallyLinear θh θ₀ (fun z ↦ (sandwichBread (μ.map (O 0)) ψ' θ₀)⁻¹ * ψ z θ₀) O μ := by
  refine zEstimator_isAsymptoticallyLinear hO hr hψm hψ'm hderiv hcont hH hdom hzero hB hA hθ
    ((tendstoInMeasure_const (μ := μ) (0 : ℝ)).congr_withProbTendingToOne hroot fun n ω hω ↦ ?_)
  simp only [Set.mem_ofPred_eq] at hω
  simp [sampleMean, hω]

/-- **Asymptotic normality of a Z-estimator.** Under the hypotheses of
`zEstimator_isAsymptoticallyLinear` and measurability of each `θh n`, `√n (θh n - θ₀)` converges
in distribution to every random variable whose law is the centered Gaussian with the sandwich
variance `E ψ (O 0) θ₀² / A²`. -/
theorem zEstimator_tendstoInDistribution [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ} (hr : 0 < r) (hψm : Measurable fun z ↦ ψ z θ₀)
    (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (ψ z) (ψ' z θ) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : sandwichBread (μ.map (O 0)) ψ' θ₀ ≠ 0) {θh : ℕ → Ω → ℝ}
    (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : IsConsistent θh θ₀ μ)
    (hroot : TendstoInMeasure μ
      (fun (n : ℕ) ω ↦ √(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω) atTop (fun _ ↦ 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0
      (μ[fun ω ↦ ψ (O 0 ω) θ₀ ^ 2] / sandwichBread (μ.map (O 0)) ψ' θ₀ ^ 2).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (θh n ω - θ₀)) atTop Y (fun _ ↦ μ) P' := by
  have h := zEstimator_isAsymptoticallyLinear hO hr hψm hψ'm hderiv hcont hH hdom hzero hB hA hθ
    hroot
  refine h.tendstoInDistribution hO hθm ?_
  have hvar : μ[fun ω ↦ ((sandwichBread (μ.map (O 0)) ψ' θ₀)⁻¹ * ψ (O 0 ω) θ₀) ^ 2] =
      μ[fun ω ↦ ψ (O 0 ω) θ₀ ^ 2] / sandwichBread (μ.map (O 0)) ψ' θ₀ ^ 2 := by
    simp_rw [mul_pow, inv_pow]
    rw [integral_const_mul, inv_mul_eq_div]
  rw [hvar]
  exact hY

/-- **Asymptotic linearity of an M-estimator through the first order condition.** Let
`ψ z θ` be the derivative of the criterion `m z` at every `θ` of the closed ball `B` around `θ₀`
for almost every observation value, and let `θh n` be a local maximizer of the sample criterion
`θ ↦ n⁻¹ ∑_{i < n} m (O i) θ` on events of probability tending to one. Under the remaining
hypotheses of `zEstimator_isAsymptoticallyLinear` for `ψ` (consistency of `θh` is again an
explicit hypothesis), `θh` is asymptotically linear at `θ₀` with influence function
`z ↦ A⁻¹ ψ z θ₀`: with probability tending to one `θh n` lies inside `B`, where the derivative of
the sample criterion vanishes, so `θh n` is a root of the estimating equation. -/
theorem mEstimator_isAsymptoticallyLinear [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {m ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ} (hr : 0 < r)
    (hdm : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (m z) (ψ z θ) θ)
    (hψm : Measurable fun z ↦ ψ z θ₀)
    (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (ψ z) (ψ' z θ) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hA : sandwichBread (μ.map (O 0)) ψ' θ₀ ≠ 0) {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ)
    (hmax : WithProbTendingToOne μ
      (fun n ↦ {ω | IsLocalMax (fun θ ↦ sampleMean (fun z ↦ m z θ) O n ω) (θh n ω)})) :
    IsAsymptoticallyLinear θh θ₀ (fun z ↦ (sandwichBread (μ.map (O 0)) ψ' θ₀)⁻¹ * ψ z θ₀) O μ := by
  refine zEstimator_isAsymptoticallyLinear_of_root hO hr hψm hψ'm hderiv hcont hH hdom hzero hB
    hA hθ (((hmax.inter (TendstoInMeasure.withProbTendingToOne_dist_lt hθ hr)).inter
      (WithProbTendingToOne.of_ae (hO.ae_forall hdm))).mono fun n ω hω ↦ ?_)
  obtain ⟨⟨h1, h2⟩, h3⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2 h3 ⊢
  have hin : θh n ω ∈ Metric.closedBall θ₀ r := Metric.mem_closedBall.2 h2.le
  have hd : HasDerivAt (fun θ ↦ sampleMean (fun z ↦ m z θ) O n ω)
      ((n : ℝ)⁻¹ * ∑ i ∈ range n, ψ (O i ω) (θh n ω)) (θh n ω) :=
    (HasDerivAt.fun_sum fun i _ ↦ h3 i _ hin).const_mul _
  have h0 := h1.hasDerivAt_eq_zero hd
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn.ne')
    exact (mul_eq_zero.1 h0).resolve_left hn'

end CausalInference
