/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ConjugateNormalSample

/-!
# Shrinkage estimates and their mean squared error

In the normal hierarchical model `θ = μ + b`, `y = θ + ε`, with `b` of second moment `τ²`,
`ε` of second moment `v > 0` and `E[b ε] = 0`, the marginal law of the data is the random effects
model (for Gaussian components it is `IsGaussianRandomEffectsModel.hasLaw_pi`). The **shrinkage
estimate** of a unit parameter is

  `θ̂ = B μ + (1 - B) y`, `B = v / (v + τ²)`,

the posterior mean under the prior `N(μ, τ²)` (`priorWeight_one`, with `posterior_iidNormal` for
one observation). Empirical Bayes replaces `μ` and `τ²` by estimates (Efron and Morris 1975).

* **Smaller mean squared error, averaged over the units** (`integral_sq_shrinkage_sub`):
  `E[(θ̂ - θ)²] = v τ² / (v + τ²)`, while the unshrunk estimate has `E[(y - θ)²] = v`, and
  `v τ² / (v + τ²) < v`. The expectation is over both `b` and `ε`.
* **For a fixed unit it can be larger** (`integral_sq_shrinkage_sub_fixed`,
  `shrinkage_mse_gt_iff`): given `θ`, `E[(θ̂ - θ)² | θ] = B² (θ - μ)² + (1 - B)² v`, and this
  exceeds `v` exactly when `(θ - μ)² > v + 2 τ²`.
* **Plugging in estimates** (`shrinkageEstimate_zero`, `tendsto_shrinkageEstimate_atTop`): with
  the plug in value `τ² = 0` (for example a truncated moment estimate) every unit is estimated by
  the plug in mean, for instance the pooled estimate; as `τ² → ∞` the shrinkage estimate tends to
  the unshrunk `y`. Only these limiting facts are proved here: the mean squared error of the
  shrinkage estimate with estimated `μ` and `τ²` is not computed.

## Main definitions

* `shrinkageFactor`, `shrinkageEstimate`.

## Main results

* `priorWeight_one`, `integral_sq_shrinkage_sub`, `IsRandomEffectsModel.integral_sq_shrinkage_sub`,
  `IsGaussianRandomEffectsModel.hasLaw_unit`, `integral_sq_shrinkage_sub_fixed`,
  `shrinkage_mse_gt_iff`, `shrinkageEstimate_zero`, `tendsto_shrinkageEstimate_atTop`.

## References

* B. Efron and C. Morris, *Data analysis using Stein's estimator and its generalizations*,
  Journal of the American Statistical Association 70 (1975).
* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The **shrinkage factor** `B = v / (v + τ²)`. -/
noncomputable def shrinkageFactor (v τ2 : ℝ) : ℝ := v / (v + τ2)

/-- The **shrinkage estimate** `B μ + (1 - B) y` of a unit parameter. -/
noncomputable def shrinkageEstimate (μ v τ2 y : ℝ) : ℝ :=
  shrinkageFactor v τ2 * μ + (1 - shrinkageFactor v τ2) * y

/-- With one observation the prior weight of the conjugate normal update is the shrinkage
factor: `priorWeight τ² v 1 = v / (v + τ²)`. -/
theorem priorWeight_one {v τ2 : ℝ} (hv : 0 < v) (hτ : 0 < τ2) :
    priorWeight τ2 v 1 = shrinkageFactor v τ2 := by
  simp only [priorWeight, shrinkageFactor, Nat.cast_one]
  field_simp

/-- **Shrinkage lowers the mean squared error averaged over the units**: for `b`, `ε` square
integrable with `E[b²] = τ²`, `E[ε²] = v > 0` and `E[b ε] = 0`, `θ = μ + b`, `y = θ + ε`,
the shrinkage estimate has `E[(θ̂ - θ)²] = v τ² / (v + τ²)`, the unshrunk estimate has
`E[(y - θ)²] = v`, and the first is strictly smaller. -/
theorem integral_sq_shrinkage_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {b ε : Ω → ℝ} (hb : MemLp b 2 P) (hε : MemLp ε 2 P) {v τ2 : ℝ} (hv : 0 < v)
    (hb2 : ∫ ω, b ω ^ 2 ∂P = τ2) (hε2 : ∫ ω, ε ω ^ 2 ∂P = v) (hbε : ∫ ω, b ω * ε ω ∂P = 0)
    (μ : ℝ) :
    ∫ ω, (shrinkageEstimate μ v τ2 (μ + b ω + ε ω) - (μ + b ω)) ^ 2 ∂P = v * τ2 / (v + τ2) ∧
      ∫ ω, (μ + b ω + ε ω - (μ + b ω)) ^ 2 ∂P = v ∧ v * τ2 / (v + τ2) < v := by
  have hτ : 0 ≤ τ2 := hb2 ▸ integral_nonneg fun ω => sq_nonneg (b ω)
  have hs : 0 < v + τ2 := by linarith
  set B := shrinkageFactor v τ2
  have e : ∀ ω, (shrinkageEstimate μ v τ2 (μ + b ω + ε ω) - (μ + b ω)) ^ 2 =
      (1 - B) ^ 2 * ε ω ^ 2 + (-(2 * B * (1 - B))) * (b ω * ε ω) + B ^ 2 * b ω ^ 2 :=
    fun ω => by simp only [shrinkageEstimate, B]; ring
  have i1 := hε.integrable_sq
  have i2 : Integrable (fun ω => b ω * ε ω) P := hb.integrable_mul hε
  have i3 := hb.integrable_sq
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [e]
    rw [integral_add ?_ (i3.const_mul _), integral_add (i1.const_mul _) (i2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, hb2, hε2, hbε]
    swap
    · exact (i1.const_mul _).add (i2.const_mul _)
    simp only [B, shrinkageFactor]
    field_simp
    ring
  · simp_rw [add_sub_cancel_left]
    exact hε2
  · rw [div_lt_iff₀ hs]
    nlinarith

/-- **Shrinkage in the random effects model**: in the moment form of the random effects model
with `vᵢ > 0`, the shrinkage estimate of the unit parameter `θ + bᵢ` from `Yᵢ = θ + bᵢ + εᵢ` has
mean squared error `vᵢ τ² / (vᵢ + τ²) < vᵢ`, the mean squared error of `Yᵢ`. -/
theorem IsRandomEffectsModel.integral_sq_shrinkage_sub {ι Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {b ε : ι → Ω → ℝ} {τ2 : ℝ} {v : ι → ℝ}
    (h : IsRandomEffectsModel P b ε τ2 v) (hv : ∀ i, 0 < v i) (θ : ℝ) (i : ι) :
    ∫ ω, (shrinkageEstimate θ (v i) τ2 (θ + b i ω + ε i ω) - (θ + b i ω)) ^ 2 ∂P =
        v i * τ2 / (v i + τ2) ∧
      ∫ ω, (θ + b i ω + ε i ω - (θ + b i ω)) ^ 2 ∂P = v i ∧ v i * τ2 / (v i + τ2) < v i := by
  have := h.isProbabilityMeasure
  have hb2 : ∫ ω, b i ω ^ 2 ∂P = τ2 := by
    rw [← h.variance_b i, variance_of_integral_eq_zero (h.memLp_b i).aemeasurable (h.integral_b i)]
  have hε2 : ∫ ω, ε i ω ^ 2 ∂P = v i := by
    rw [← h.variance_ε i,
      variance_of_integral_eq_zero (h.memLp_ε i).aemeasurable (h.integral_ε i)]
  have hbε : ∫ ω, b i ω * ε i ω ∂P = 0 := by
    have := h.cov_bε i i
    rw [covariance_eq_sub (h.memLp_b i) (h.memLp_ε i), h.integral_b i, zero_mul, sub_zero] at this
    exact this
  exact MetaAnalysis.integral_sq_shrinkage_sub (h.memLp_b i) (h.memLp_ε i) (hv i) hb2 hε2 hbε θ

/-- **The marginal law of one unit**: in the Gaussian random effects model, `Yᵢ = θ + bᵢ + εᵢ`
has the law `N(θ, vᵢ + τ²)` (the `i`th coordinate of `IsGaussianRandomEffectsModel.hasLaw_pi`),
so the shrinkage factor `vᵢ / (vᵢ + τ²)` is the ratio of the within study variance to the
marginal variance. -/
theorem IsGaussianRandomEffectsModel.hasLaw_unit {ι Ω : Type*} [Fintype ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {b ε : ι → Ω → ℝ} {τ2 : ℝ} {v : ι → ℝ}
    (h : IsGaussianRandomEffectsModel P b ε τ2 v) (θ : ℝ) (i : ι) :
    HasLaw (fun ω => θ + b i ω + ε i ω) (gaussianReal θ (v i + τ2).toNNReal) P :=
  (measurePreserving_eval (fun i => gaussianReal θ (v i + τ2).toNNReal) i).hasLaw.comp
    (h.hasLaw_pi θ)

/-- **The mean squared error for a fixed unit**: given `θ`, for `ε` square integrable with
`E[ε] = 0` and `E[ε²] = v` under a probability measure,
`E[(θ̂ - θ)²] = B² (θ - μ)² + (1 - B)² v`. -/
theorem integral_sq_shrinkage_sub_fixed {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ε : Ω → ℝ} (hε : MemLp ε 2 P) {v : ℝ}
    (hε1 : ∫ ω, ε ω ∂P = 0) (hε2 : ∫ ω, ε ω ^ 2 ∂P = v) (μ τ2 θ : ℝ) :
    ∫ ω, (shrinkageEstimate μ v τ2 (θ + ε ω) - θ) ^ 2 ∂P =
      shrinkageFactor v τ2 ^ 2 * (θ - μ) ^ 2 + (1 - shrinkageFactor v τ2) ^ 2 * v := by
  set B := shrinkageFactor v τ2
  have e : ∀ ω, (shrinkageEstimate μ v τ2 (θ + ε ω) - θ) ^ 2 =
      B ^ 2 * (θ - μ) ^ 2 + (-(2 * B * (1 - B) * (θ - μ))) * ε ω + (1 - B) ^ 2 * ε ω ^ 2 :=
    fun ω => by simp only [shrinkageEstimate, B]; ring
  have i1 := hε.integrable one_le_two
  have i2 := hε.integrable_sq
  simp_rw [e]
  rw [integral_add ?_ (i2.const_mul _), integral_add (integrable_const _) (i1.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, hε1, hε2]
  · simp
  · exact (integrable_const _).add (i1.const_mul _)

/-- **When shrinkage hurts a fixed unit**: for `v > 0` and `τ² ≥ 0`, the conditional mean
squared error `B² (θ - μ)² + (1 - B)² v` exceeds the unshrunk `v` exactly when
`(θ - μ)² > v + 2 τ²`. Proof: the difference is `(v / (v + τ²))² ((θ - μ)² - v - 2 τ²)`. -/
theorem shrinkage_mse_gt_iff {v τ2 : ℝ} (hv : 0 < v) (hτ : 0 ≤ τ2) (d : ℝ) :
    v < shrinkageFactor v τ2 ^ 2 * d + (1 - shrinkageFactor v τ2) ^ 2 * v ↔ v + 2 * τ2 < d := by
  have hs : 0 < v + τ2 := by linarith
  have key : shrinkageFactor v τ2 ^ 2 * d + (1 - shrinkageFactor v τ2) ^ 2 * v - v =
      (v / (v + τ2)) ^ 2 * (d - (v + 2 * τ2)) := by
    simp only [shrinkageFactor]
    field_simp
    ring
  have hpos : 0 < (v / (v + τ2)) ^ 2 := by positivity
  constructor
  · intro h
    have : 0 < (v / (v + τ2)) ^ 2 * (d - (v + 2 * τ2)) := by linarith
    have := (pos_iff_pos_of_mul_pos this).1 hpos
    linarith
  · intro h
    have : 0 < (v / (v + τ2)) ^ 2 * (d - (v + 2 * τ2)) := mul_pos hpos (by linarith)
    linarith

/-- **The plug in value `τ² = 0`** estimates every unit by the plug in mean. -/
theorem shrinkageEstimate_zero {v : ℝ} (hv : 0 < v) (μ y : ℝ) :
    shrinkageEstimate μ v 0 y = μ := by
  simp [shrinkageEstimate, shrinkageFactor, hv.ne']

/-- **As `τ² → ∞` the shrinkage estimate tends to the unshrunk estimate `y`.** -/
theorem tendsto_shrinkageEstimate_atTop (μ v y : ℝ) :
    Tendsto (fun τ2 => shrinkageEstimate μ v τ2 y) atTop (𝓝 y) := by
  have hB : Tendsto (fun τ2 => shrinkageFactor v τ2) atTop (𝓝 0) := by
    simp only [shrinkageFactor]
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ v tendsto_id)
  have := (hB.mul_const μ).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hB).mul_const y)
  simp only [zero_mul, sub_zero, one_mul, zero_add] at this
  exact this

end MetaAnalysis

end CausalInference
