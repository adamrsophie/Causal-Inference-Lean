/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ZEstimatorNormality
public import CausalInference.Estimation.ConfidenceInterval

/-!
# The sandwich variance estimator

For a Z-estimator `θh` of a real parameter with estimating function `ψ` and derivative `ψ'`, the
asymptotic variance of `√n (θh n - θ₀)` is the sandwich `B / A²` with bread
`A = -E ψ' (O 0) θ₀` and meat `B = E ψ (O 0) θ₀²` (`zEstimator_tendstoInDistribution`). The
plug-in estimators replace expectations by sample means and `θ₀` by `θh n`.

## Main definitions

* `CausalInference.sandwichMeat ν ψ θ`: the meat `∫ ψ z θ² dν`.
* `CausalInference.breadHat`, `CausalInference.meatHat`: the empirical bread
  `-n⁻¹ ∑_{i < n} ψ' (O i) (θh n)` and meat `n⁻¹ ∑_{i < n} ψ (O i) (θh n)²`.
* `CausalInference.sandwichVarianceHat`: the sandwich variance estimate
  `n⁻¹ Âₙ⁻¹ B̂ₙ Âₙ⁻¹` of the variance of `θh n`; `CausalInference.sandwichSD`: the scale
  estimate `√B̂ₙ / |Âₙ|` of the asymptotic standard deviation.

At a finite sample size the empirical bread may vanish; there `Âₙ⁻¹ = 0` and `√B̂ₙ / 0 = 0` by
the conventions of division. This affects no result below: the empirical bread converges to the
nonzero bread, so these values occur only on events of probability tending to zero.

## Main results

* `CausalInference.breadHat_isConsistent`, `CausalInference.meatHat_isConsistent`: the empirical
  bread and meat are consistent, through the uniform law of large numbers.
* `CausalInference.sandwichVarianceHat_isConsistent`: `n` times the sandwich variance estimate is
  consistent for `B / A²`; `CausalInference.sandwichSD_isConsistent`: the scale estimate is
  consistent for `√B / |A|`.
* `CausalInference.zEstimator_tendsto_waldInterval_coverage`: the Wald interval built from a
  Z-estimator and the sandwich scale has asymptotic coverage `1 - α`.

References: P. J. Huber (1967), *The behavior of maximum likelihood estimates under nonstandard
conditions*; H. White (1980), *A heteroskedasticity-consistent covariance matrix estimator and a
direct test for heteroskedasticity*, Econometrica; L. A. Stefanski and D. D. Boos (2002),
*The calculus of M-estimation*, The American Statistician.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  {O : ℕ → Ω → 𝒪}

/-- The meat `∫ ψ z θ² dν` of the sandwich variance. -/
noncomputable def sandwichMeat (ν : Measure 𝒪) (ψ : 𝒪 → ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ z, ψ z θ ^ 2 ∂ν

/-- The empirical bread `-n⁻¹ ∑_{i < n} ψ' (O i) (θh n)`. -/
noncomputable def breadHat (O : ℕ → Ω → 𝒪) (ψ' : 𝒪 → ℝ → ℝ) (θh : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  -sampleMean (fun z ↦ ψ' z (θh n ω)) O n ω

/-- The empirical meat `n⁻¹ ∑_{i < n} ψ (O i) (θh n)²`. -/
noncomputable def meatHat (O : ℕ → Ω → 𝒪) (ψ : 𝒪 → ℝ → ℝ) (θh : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  sampleMean (fun z ↦ ψ z (θh n ω) ^ 2) O n ω

/-- The sandwich variance estimate `n⁻¹ Âₙ⁻¹ B̂ₙ Âₙ⁻¹` of the variance of `θh n`. Where the
empirical bread vanishes its inverse is `0`. -/
noncomputable def sandwichVarianceHat (O : ℕ → Ω → 𝒪) (ψ ψ' : 𝒪 → ℝ → ℝ) (θh : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ((breadHat O ψ' θh n ω)⁻¹ * meatHat O ψ θh n ω * (breadHat O ψ' θh n ω)⁻¹)

/-- The sandwich scale estimate `√B̂ₙ / |Âₙ|` of the asymptotic standard deviation of
`√n (θh n - θ₀)`. Where the empirical bread vanishes it is `0`. -/
noncomputable def sandwichSD (O : ℕ → Ω → 𝒪) (ψ ψ' : 𝒪 → ℝ → ℝ) (θh : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  √(meatHat O ψ θh n ω) / |breadHat O ψ' θh n ω|

/-- **Consistency of the empirical bread.** If `z ↦ ψ' z θ` is measurable on a closed ball `B`
around `θ₀`, continuous on `B` for almost every observation value and dominated there by an
integrable envelope, and `θh` is consistent for `θ₀`, then the empirical bread is consistent for
the bread `sandwichBread (μ.map (O 0)) ψ' θ₀`. -/
theorem breadHat_isConsistent [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {ψ' : 𝒪 → ℝ → ℝ}
    {θ₀ r : ℝ} (hr : 0 < r) (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ) :
    IsConsistent (breadHat O ψ' θh) (sandwichBread (μ.map (O 0)) ψ' θ₀) μ := by
  have hK := Metric.closedBall_mem_nhds θ₀ hr
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall θ₀ r)
    (ψ := fun z θ ↦ ψ' z θ) hψ'm hcont hH hdom
  exact (hunif.comp_tendstoInMeasure hK (hMc.continuousAt hK) hθ).comp_continuousAt
    (g := fun x : ℝ ↦ -x) continuous_neg.continuousAt

/-- **Consistency of the empirical meat.** If `ψ z` is continuous on a closed ball `B` around `θ₀`
for almost every observation value, `z ↦ ψ z θ` is measurable for `θ ∈ B`,
`ψ z θ² ≤ G z` on `B` for an integrable envelope `G`, and `θh` is consistent for `θ₀`, then the
empirical meat is consistent for the meat `sandwichMeat (μ.map (O 0)) ψ θ₀`. -/
theorem meatHat_isConsistent [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {ψ : 𝒪 → ℝ → ℝ}
    {θ₀ r : ℝ} (hr : 0 < r) (hψm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ z θ)
    (hcontψ : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ z) (Metric.closedBall θ₀ r))
    {G : 𝒪 → ℝ} (hG : Integrable G (μ.map (O 0)))
    (hdomG : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ψ z θ ^ 2 ≤ G z)
    {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ) :
    IsConsistent (meatHat O ψ θh) (sandwichMeat (μ.map (O 0)) ψ θ₀) μ := by
  have hK := Metric.closedBall_mem_nhds θ₀ hr
  have hcont2 : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (fun θ ↦ ψ z θ ^ 2)
      (Metric.closedBall θ₀ r) :=
    hcontψ.mono fun z hz ↦ hz.pow 2
  obtain ⟨hNc, hunif⟩ := uniform_law_of_large_numbers_real hO (isCompact_closedBall θ₀ r)
    (ψ := fun z θ ↦ ψ z θ ^ 2) (fun θ hθ ↦ (hψm θ hθ).pow_const 2) hcont2 hG
    (hdomG.mono fun z hz θ hθ ↦ by rw [abs_of_nonneg (sq_nonneg _)]; exact hz θ hθ)
  exact hunif.comp_tendstoInMeasure hK (hNc.continuousAt hK) hθ

/-- **Consistency of the sandwich variance estimate.** Under the hypotheses of
`breadHat_isConsistent` and `meatHat_isConsistent` and a nonzero bread `A`, `n` times the
sandwich variance estimate is consistent for `B / A²`, the asymptotic variance of
`√n (θh n - θ₀)`. -/
theorem sandwichVarianceHat_isConsistent [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ} (hr : 0 < r)
    (hψm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ z θ)
    (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (ψ z) (ψ' z θ) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    {G : 𝒪 → ℝ} (hG : Integrable G (μ.map (O 0)))
    (hdomG : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ψ z θ ^ 2 ≤ G z)
    (hA : sandwichBread (μ.map (O 0)) ψ' θ₀ ≠ 0) {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ) :
    IsConsistent (fun n ω ↦ (n : ℝ) * sandwichVarianceHat O ψ ψ' θh n ω)
      (sandwichMeat (μ.map (O 0)) ψ θ₀ / sandwichBread (μ.map (O 0)) ψ' θ₀ ^ 2) μ := by
  have h1 := breadHat_isConsistent hO hr hψ'm hcont hH hdom hθ
  have h2 := meatHat_isConsistent hO hr hψm
    (hderiv.mono fun z hz θ hθ ↦ (hz θ hθ).continuousAt.continuousWithinAt) hG hdomG hθ
  set a := sandwichBread (μ.map (O 0)) ψ' θ₀
  set b := sandwichMeat (μ.map (O 0)) ψ θ₀
  have hc : ContinuousAt (fun p : ℝ × ℝ ↦ p.1⁻¹ * p.2 * p.1⁻¹) (a, b) :=
    ((continuousAt_fst.inv₀ hA).mul continuousAt_snd).mul (continuousAt_fst.inv₀ hA)
  have h3 := (TendstoInMeasure.prodMk h1 h2).comp_continuousAt hc
  have hlim : a⁻¹ * b * a⁻¹ = b / a ^ 2 := by field_simp
  rw [hlim] at h3
  refine h3.congr_withProbTendingToOne
    (A := fun n ↦ {ω | (n : ℝ) ≠ 0}) ?_ fun n ω hω ↦ ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : {ω : Ω | (n : ℝ) ≠ 0}ᶜ = ∅ := by
      ext ω; simp [Nat.pos_iff_ne_zero.1 hn]
    rw [this, measure_empty]
  · simp only [Set.mem_ofPred_eq] at hω
    simp [sandwichVarianceHat, ← mul_assoc, mul_inv_cancel₀ hω]

/-- **Consistency of the sandwich scale.** Under the hypotheses of
`sandwichVarianceHat_isConsistent`, the sandwich scale `√B̂ₙ / |Âₙ|` is consistent for
`√B / |A|`. -/
theorem sandwichSD_isConsistent [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ} (hr : 0 < r)
    (hψm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ z θ)
    (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (ψ z) (ψ' z θ) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    {G : 𝒪 → ℝ} (hG : Integrable G (μ.map (O 0)))
    (hdomG : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ψ z θ ^ 2 ≤ G z)
    (hA : sandwichBread (μ.map (O 0)) ψ' θ₀ ≠ 0) {θh : ℕ → Ω → ℝ} (hθ : IsConsistent θh θ₀ μ) :
    IsConsistent (sandwichSD O ψ ψ' θh)
      (√(sandwichMeat (μ.map (O 0)) ψ θ₀) / |sandwichBread (μ.map (O 0)) ψ' θ₀|) μ := by
  have h1 := breadHat_isConsistent hO hr hψ'm hcont hH hdom hθ
  have h2 := meatHat_isConsistent hO hr hψm
    (hderiv.mono fun z hz θ hθ ↦ (hz θ hθ).continuousAt.continuousWithinAt) hG hdomG hθ
  have hc : ContinuousAt (fun p : ℝ × ℝ ↦ √p.2 / |p.1|)
      (sandwichBread (μ.map (O 0)) ψ' θ₀, sandwichMeat (μ.map (O 0)) ψ θ₀) :=
    (Real.continuous_sqrt.continuousAt.comp continuousAt_snd).div continuousAt_fst.abs
      (abs_ne_zero.2 hA)
  exact (TendstoInMeasure.prodMk h1 h2).comp_continuousAt hc

/-- **The Wald interval of a Z-estimator with the sandwich scale.** Under the hypotheses of
`zEstimator_isAsymptoticallyLinear` (with the measurability, continuity and envelope conditions
on the whole closed ball `B`), an integrable envelope `ψ z θ² ≤ G z` on `B`, a positive meat
`E ψ (O 0) θ₀² > 0`, measurable `θh n` and sandwich scales `sandwichSD O ψ ψ' θh n`, and a critical
value `z ≥ 0` with `Φ(z) = 1 - α / 2`, the interval
`[θh n - z σhat n / √n, θh n + z σhat n / √n]` with `σhat = sandwichSD O ψ ψ' θh` covers `θ₀`
with probability tending to `1 - α`. -/
theorem zEstimator_tendsto_waldInterval_coverage [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {ψ ψ' : 𝒪 → ℝ → ℝ} {θ₀ r : ℝ} (hr : 0 < r)
    (hψm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ z θ)
    (hψ'm : ∀ θ ∈ Metric.closedBall θ₀ r, Measurable fun z ↦ ψ' z θ)
    (hderiv : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, HasDerivAt (ψ z) (ψ' z θ) θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ' z) (Metric.closedBall θ₀ r))
    {H : 𝒪 → ℝ} (hH : Integrable H (μ.map (O 0)))
    (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, |ψ' z θ| ≤ H z)
    {G : 𝒪 → ℝ} (hG : Integrable G (μ.map (O 0)))
    (hdomG : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ Metric.closedBall θ₀ r, ψ z θ ^ 2 ≤ G z)
    (hzero : μ[fun ω ↦ ψ (O 0 ω) θ₀] = 0) (hB : MemLp (fun ω ↦ ψ (O 0 ω) θ₀) 2 μ)
    (hBpos : 0 < μ[fun ω ↦ ψ (O 0 ω) θ₀ ^ 2])
    (hA : sandwichBread (μ.map (O 0)) ψ' θ₀ ≠ 0) {θh : ℕ → Ω → ℝ}
    (hθm : ∀ n, AEMeasurable (θh n) μ) (hθ : IsConsistent θh θ₀ μ)
    (hroot : TendstoInMeasure μ
      (fun (n : ℕ) ω ↦ √(n : ℝ) * sampleMean (fun z ↦ ψ z (θh n ω)) O n ω) atTop (fun _ ↦ 0))
    (hσm : ∀ n, AEMeasurable (sandwichSD O ψ ψ' θh n) μ) {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ μ.real {ω | θ₀ ∈ waldInterval (θh n ω) (sandwichSD O ψ ψ' θh n ω) z n})
      atTop (𝓝 (1 - α)) := by
  have hθ₀B : θ₀ ∈ Metric.closedBall θ₀ r := Metric.mem_closedBall_self hr.le
  have hAL := zEstimator_isAsymptoticallyLinear hO hr (hψm θ₀ hθ₀B) hψ'm hderiv hcont hH hdom
    hzero hB hA hθ hroot
  have hσ := sandwichSD_isConsistent hO hr hψm hψ'm hderiv hcont hH hdom hG hdomG hA hθ
  set a := sandwichBread (μ.map (O 0)) ψ' θ₀
  have hmeat : sandwichMeat (μ.map (O 0)) ψ θ₀ = μ[fun ω ↦ ψ (O 0 ω) θ₀ ^ 2] :=
    integral_map (hO.aemeasurable 0) ((hψm θ₀ hθ₀B).pow_const 2).aestronglyMeasurable
  rw [hmeat] at hσ
  refine hAL.tendsto_waldInterval_coverage hO hθm (by positivity) ?_ hz hzα hσ hσm
  simp_rw [mul_pow, inv_pow]
  rw [integral_const_mul, div_pow, Real.sq_sqrt hBpos.le, sq_abs, inv_mul_eq_div]

end CausalInference
